#!/usr/bin/env python3
"""Build an HTML report of Wake County early voting reported wait times from the CSV
written by wake_wait_monitor.py --csv, alongside early voting turnout from the
NC State Board of Elections.

The report is a single self-contained HTML file (no network needed to view it):
  * Right now       - every site's latest reported wait, grouped by town
  * Through the day - site x time heatmap for one day, rows grouped by town,
                      with that day's early votes per site
  * Average wait    - mean reported wait time across sites over the day
  * Turnout by day  - early votes cast per day (county and State Board data)
  * Typical by hour - town x half-hour heatmap averaged over every day collected

Wait labels are shown exactly as the tracker reports them. For averages each
range ("15-30 Minutes") counts as its midpoint and an open-ended label ("2+ Hours")
as its lower bound; for color each wait falls in one of five bands, the last
being "Over 60 min" so longer choices the county may add are still handled.
Labels that can't be read as a time are reported when the script runs.

Turnout comes from the Wake County Board of Elections' unofficial early voting
turnout PDF, which the county refreshes each evening with votes per site per day.
Reading it needs pdftotext (poppler: brew install poppler). Any day the county
file doesn't have yet, or every day if it can't be read, comes from the State
Board's statewide absentee file instead, which is refreshed each morning with
the previous day's early votes. Both files are downloaded to ncsbe_cache/ and
only fetched again when there is a newer copy.

Standard library only. Examples:
    python3 visualize_waits.py
    python3 visualize_waits.py waits.csv -o report.html --open
    python3 visualize_waits.py waits.csv more_waits.csv
    python3 visualize_waits.py --no-turnout
"""

import argparse
import csv
import io
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.request
import webbrowser
import zipfile
from collections import Counter
from datetime import UTC, datetime
from email.utils import formatdate, parsedate_to_datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from run_during_early_voting import FALLBACK_SCHEDULE, parse_clock

TZ = ZoneInfo("America/New_York")
BANDS = ["No wait", "Under 15 min", "15–30 min", "30–60 min", "Over 60 min"]

TRACKER_URL = "https://airtable.com/appAL6KsUEvshj4br/shrQkIIFla4bjdGzh"
COUNTY_URL = "https://wakevotesearly.com"
NCSBE_URL = "https://www.ncsbe.gov/results-data/absentee-and-provisional-data"
VOTER_LOOKUP_URL = "https://vt.ncsbe.gov/RegLkup/"
ELECTION = "20261103"
# Earlier general election to compare daily turnout with, matched by day of early voting.
PRIOR_ELECTION = "20221108"
ABSENTEE_URL = "https://s3.amazonaws.com/dl.ncsbe.gov/ENRS/{d}/absentee_{ymd}.zip"
COUNTY = "WAKE"
COUNTY_TURNOUT_URL = (
    "https://s3.us-west-1.amazonaws.com/wakegov.com.if-us-west-1/s3fs-public/"
    "documents/2026-10/2026EVunofficial_3.pdf"
)
COUNTY_ELECTION_URL = (
    "https://www.wake.gov/departments-government/board-elections/"
    "election-information/2026-general-election"
)
# State Board site_name -> tracker site name, for any pair the word match gets wrong or misses.
SITE_ALIASES = {}
# Words too generic to identify a site.
STOPWORDS = {
    "the",
    "and",
    "of",
    "at",
    "community",
    "center",
    "recreation",
    "rec",
    "park",
    "building",
    "annex",
    "town",
    "county",
    "nc",
    "site",
}


def wait_minutes(label):
    """Return (minutes, band_index) for a wait label, or (None, None) if it isn't a time.

    Handles "No Wait", "5-15 Minutes", "45 Minutes - 1 Hour", "1-2 Hours", and
    open-ended labels such as "2+ Hours" or "More than 90 minutes". A number with
    no unit takes the next unit in the label ("1-2 Hours" -> 60-120 minutes).
    """
    text = label.strip().lower()
    if "no wait" in text:
        return 0.0, 0
    tokens = re.findall(r"(\d+(?:\.\d+)?)\+?\s*(h(?:ou)?rs?\b|min(?:ute)?s?\b)?", text)
    if not tokens:
        return None, None
    values, pending = [], []
    for num, unit in tokens:
        pending.append(float(num))
        if unit:
            values += [n * (60 if unit.startswith("h") else 1) for n in pending]
            pending = []
    values += pending  # trailing numbers with no unit: assume minutes
    lo, hi = min(values), max(values)
    open_ended = bool(re.search(r"\+|more|over|longer|greater|at least", text))
    minutes, top = (lo, lo) if open_ended or lo == hi else ((lo + hi) / 2, hi)
    if open_ended and lo >= 60:
        top = lo + 1  # "60+" belongs in the over-60 band
    band = 1 if top <= 15 else 2 if top <= 30 else 3 if top <= 60 else 4
    return minutes, band


def city_of(address):
    """'125 Avery St, Garner, NC 27529' -> 'Garner'."""
    parts = [p.strip() for p in address.split(",")]
    return parts[-2] if len(parts) >= 3 else "Unknown"


def load_rows(path):
    rows = []
    with open(path, newline="") as f:
        for r in csv.DictReader(f):
            polled = datetime.fromisoformat(r["polled_at"]).astimezone(TZ)
            minutes, band = wait_minutes(r["wait"])
            updated = r.get("site_updated_at") or ""
            if updated:
                updated = datetime.fromisoformat(updated).astimezone(TZ)
                updated = updated.strftime("%Y-%m-%dT%H:%M")
            rows.append(
                {
                    "t": polled.strftime("%Y-%m-%dT%H:%M"),
                    "site": r["site"],
                    "city": city_of(r.get("address", "")),
                    "addr": r.get("address", ""),
                    "wait": r["wait"],
                    "min": minutes,
                    "band": band,
                    "u": updated,
                }
            )
    return rows


def fetch(url, path):
    """Download url to path if it changed; return (path, last_modified) or (None, None)."""
    cache_dir = path.parent
    headers = {"User-Agent": "Mozilla/5.0"}
    if path.exists():
        headers["If-Modified-Since"] = formatdate(path.stat().st_mtime, usegmt=True)
    try:
        with urllib.request.urlopen(
            urllib.request.Request(url, headers=headers), timeout=120
        ) as resp:
            cache_dir.mkdir(exist_ok=True)
            tmp = path.with_suffix(".part")
            with open(tmp, "wb") as f:
                while chunk := resp.read(1 << 20):
                    f.write(chunk)
            tmp.replace(path)
            modified = resp.headers.get("Last-Modified")
            if modified:
                ts = parsedate_to_datetime(modified).timestamp()
                os.utime(path, (ts, ts))
            print(f"downloaded {url}")
    except urllib.error.HTTPError as e:
        if e.code != 304:
            print(f"turnout: could not download {url} ({e})", file=sys.stderr)
    except OSError as e:
        print(f"turnout: could not download {url} ({e})", file=sys.stderr)
    if not path.exists():
        return None, None
    return path, datetime.fromtimestamp(path.stat().st_mtime, UTC).astimezone(TZ)


def fetch_absentee(election, cache_dir):
    url = ABSENTEE_URL.format(
        d=f"{election[:4]}_{election[4:6]}_{election[6:]}", ymd=election
    )
    return fetch(url, cache_dir / f"absentee_{election}.zip")


def find_pdftotext():
    # launchd's PATH leaves out Homebrew, so look there too.
    return shutil.which("pdftotext") or next(
        (
            p
            for p in ("/opt/homebrew/bin/pdftotext", "/usr/local/bin/pdftotext")
            if os.path.exists(p)
        ),
        None,
    )


def load_county_turnout(pdf_path, year):
    """Read early votes by (county site name, ISO date) from the county's turnout PDF.

    The first page is a table with a row per day ("10/15  1,534  1,201 ... 21,736")
    and one column per site, the site names stacked a word per line above it.
    Each header word goes to the column whose numbers it sits over. Returns
    (counts, refreshed), or (None, None) if the table can't be read.
    """
    exe = find_pdftotext()
    if not exe:
        print(
            "turnout: pdftotext not found (brew install poppler); skipping county turnout",
            file=sys.stderr,
        )
        return None, None
    try:
        text = subprocess.run(
            [exe, "-layout", str(pdf_path), "-"],
            capture_output=True,
            text=True,
            check=True,
            timeout=60,
        ).stdout
    except (OSError, subprocess.SubprocessError) as e:
        print(f"turnout: could not read {pdf_path} ({e})", file=sys.stderr)
        return None, None
    # "Last Refresh" and its time sit on separate lines.
    refreshed = re.search(r"(\d+/\d+/\d{4} \d+:\d+:\d+ [AP]M)", text)
    refreshed = (
        datetime.strptime(refreshed[1], "%m/%d/%Y %I:%M:%S %p").replace(tzinfo=TZ)
        if refreshed
        else None
    )
    counts, names = Counter(), None
    for page in text.split("\f"):
        lines = page.splitlines()
        head = next(
            (i for i, ln in enumerate(lines) if re.match(r"\s*Vote\b", ln)), None
        )
        data = [
            i
            for i, ln in enumerate(lines)
            if re.match(r"\s*\d{1,2}/\d{1,2}\s+[\d,]", ln)
        ]
        if not data:
            continue
        # Column centers from the first day's numbers; the last column is the total.
        cells = list(re.finditer(r"\S+", lines[data[0]]))[1:]
        centers = [(m.start() + m.end()) / 2 for m in cells]
        if head is not None:
            cols = [[] for _ in centers]
            for ln in lines[head : data[0]]:
                for m in re.finditer(r"\S+", ln):
                    c = (m.start() + m.end()) / 2
                    if c < centers[0] - 8:
                        continue  # the "Vote Date" label column
                    cols[
                        min(range(len(centers)), key=lambda k: abs(centers[k] - c))
                    ].append(m[0])
            names = [" ".join(ws) for ws in cols]
        if not names or names[-1].lower() != "total" or len(names) != len(centers):
            print(
                f"turnout: county table in {pdf_path} has an unexpected layout",
                file=sys.stderr,
            )
            return None, None
        for i in data:
            day, *nums = re.findall(r"\S+", lines[i])
            nums = [int(n.replace(",", "")) for n in nums]
            if len(nums) != len(names):
                print(
                    f"turnout: skipping county row '{lines[i].strip()}'",
                    file=sys.stderr,
                )
                continue
            m, d = map(int, day.split("/"))
            for name, n in zip(names[:-1], nums):
                counts[name, f"{year}-{m:02d}-{d:02d}"] += n
            if sum(nums[:-1]) != nums[-1]:
                print(
                    f"turnout: county row {day} doesn't add up to its total",
                    file=sys.stderr,
                )
    if not counts:
        print(f"turnout: no daily rows found in {pdf_path}", file=sys.stderr)
        return None, None
    return counts, refreshed


def load_turnout(zip_path):
    """Count accepted in-person early votes in COUNTY by (State Board site name, ISO date)."""
    counts = Counter()
    with zipfile.ZipFile(zip_path) as z:
        name = next(n for n in z.namelist() if n.endswith(".csv"))
        with z.open(name) as raw:
            for r in csv.DictReader(
                io.TextIOWrapper(raw, encoding="latin-1", newline="")
            ):
                if (
                    r["county_desc"] == COUNTY
                    # "ONE-STOP" in older files, such as 2022's
                    and r["ballot_req_type"] in ("EARLY VOTING", "ONE-STOP")
                    and r["ballot_rtn_status"].startswith("ACCEPTED")
                    and r["ballot_rtn_dt"].strip()
                ):
                    d = (
                        datetime.strptime(r["ballot_rtn_dt"].strip(), "%m/%d/%Y")
                        .date()
                        .isoformat()
                    )
                    counts[r["site_name"].strip(), d] += 1
    return counts


def load_prior_turnout(election, cache_dir):
    """Early votes by (State Board site name, ISO date) for a past election. Its file no
    longer changes, so the counts are cached next to it rather than re-read on every build."""
    path, _ = fetch_absentee(election, cache_dir)
    if not path:
        return None
    cache = cache_dir / f"turnout_{election}.json"
    if cache.exists() and cache.stat().st_mtime >= path.stat().st_mtime:
        return Counter({(s, d): n for s, d, n in json.loads(cache.read_text())})
    counts = load_turnout(path)
    cache.write_text(json.dumps(sorted([s, d, n] for (s, d), n in counts.items())))
    return counts


def words(text):
    text = re.sub(
        r"^[A-Z0-9]{1,4} - ", "", text
    )  # State Board names start with a site code, "CA - ..."
    return {
        w
        for w in re.findall(r"[a-z0-9]+", text.lower())
        if w not in STOPWORDS and len(w) > 1
    }


def match_sites(board_names, tracker_cities):
    """Map State Board site names to tracker site names by words unique to one tracker site.

    A tracker site's words include its town, so "HS - HOLLY SPRINGS - HUNT COMMUNITY CENTER"
    finds "W.E. Hunt Recreation Center" in Holly Springs. Words shared by several tracker
    sites ("wake", "raleigh") don't count. Each tracker site is used at most once.
    """
    tw = {s: words(s) | words(c) for s, c in tracker_cities.items()}
    seen = Counter(w for ws in tw.values() for w in ws)
    unique = {s: {w for w in ws if seen[w] == 1} for s, ws in tw.items()}
    out = {b: SITE_ALIASES[b] for b in board_names if b in SITE_ALIASES}
    pairs = sorted(
        (
            (len(words(b) & unique[s]), b, s)
            for b in board_names
            if b not in out
            for s in tracker_cities
        ),
        reverse=True,
    )
    used = set(out.values())
    for score, b, s in pairs:
        if score and b not in out and s not in used:
            out[b] = s
            used.add(s)
    return out


def to_tracker(counts, tracker, source):
    """Re-key {(source site name, day): n} by tracker site name, logging the matches."""
    names = sorted({b for b, _ in counts})
    mapping = match_sites(names, tracker)
    for b in names:
        if b not in mapping:
            print(
                f"turnout: no tracker site matches {source} site '{b}' (add it to SITE_ALIASES if it should)",
                file=sys.stderr,
            )
    for b, s in sorted(mapping.items()):
        print(f"turnout: {source} '{b}' -> '{s}'")
    by = Counter()
    for (b, d), n in counts.items():
        by[mapping.get(b, b), d] += n
    return by


def build_turnout(rows, election, cache_dir):
    """Early votes by tracker site and day: the county's file where it has the day,
    the State Board's for any day it doesn't."""
    tracker = {r["site"]: r["city"] for r in rows}
    county, refreshed = None, None
    path, _ = fetch(COUNTY_TURNOUT_URL, cache_dir / "wake_ev_unofficial.pdf")
    if path:
        counts, refreshed = load_county_turnout(path, int(election[:4]))
        if counts:
            county = to_tracker(counts, tracker, "county")
    board, modified = None, None
    path, modified = fetch_absentee(election, cache_dir)
    if path:
        board = to_tracker(load_turnout(path), tracker, "State Board")
    if county is None and board is None:
        return None

    county_days = {d for _, d in county or ()}
    by = Counter({k: n for k, n in (board or {}).items() if k[1] not in county_days})
    by.update(county or {})
    board_days = sorted({d for _, d in board or ()} - county_days)
    # The two count slightly differently (ballots cast vs. accepted), so log, don't fail.
    for d in sorted(county_days & {d for _, d in board or ()}):
        c = sum(n for (_, x), n in county.items() if x == d)
        b = sum(n for (_, x), n in board.items() if x == d)
        print(f"turnout: {d} county {c:,} vs State Board {b:,} ({c - b:+,})")
    return {
        "rows": [
            {"site": s, "city": tracker.get(s), "d": d, "n": n}
            for (s, d), n in sorted(by.items())
        ],
        "county": county is not None,
        "countyUpdated": refreshed.strftime("%a %b %-d %-I:%M %p")
        if county and refreshed
        else None,
        "boardUpdated": modified.strftime("%a %b %-d %-I:%M %p")
        if board is not None
        else None,
        "boardDays": board_days,
    }


def main():
    here = Path(__file__).resolve().parent
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument(
        "csv",
        nargs="*",
        default=[here / "waits.csv"],
        help="input CSV(s); several are combined (default waits.csv)",
    )
    p.add_argument(
        "-o",
        "--output",
        default=None,
        help="output HTML (default waits_report.html next to the CSV)",
    )
    p.add_argument(
        "--open", action="store_true", help="open the report in a browser when done"
    )
    p.add_argument(
        "--no-turnout",
        action="store_true",
        help="skip county and State Board turnout data",
    )
    p.add_argument(
        "--election",
        default=ELECTION,
        help=f"election date YYYYMMDD for turnout (default {ELECTION})",
    )
    args = p.parse_args()

    srcs = [Path(c) for c in args.csv]
    rows, seen = [], set()
    for src in srcs:
        for r in load_rows(src):  # drop exact duplicates if files overlap
            key = (r["t"], r["site"])
            if key not in seen:
                seen.add(key)
                rows.append(r)
    if not rows:
        sys.exit(f"no rows in {', '.join(map(str, srcs))}")
    # The monitor polls a little before opening and after closing; those polls aren't
    # missing data, just closed sites, so leave them out of every chart.
    hours = {
        d.isoformat(): tuple(h * 60 + m for h, m in map(parse_clock, oc))
        for d, oc in FALLBACK_SCHEDULE.items()
    }
    rows = [
        r
        for r in rows
        if r["t"][:10] not in hours
        or hours[r["t"][:10]][0]
        <= int(r["t"][11:13]) * 60 + int(r["t"][14:16])
        < hours[r["t"][:10]][1]
    ]
    if not rows:
        sys.exit("no rows during polling hours")
    odd = sorted({r["wait"] for r in rows if r["min"] is None})
    if odd:
        print(
            f"note: wait labels not read as a time (shown as 'Other'): {', '.join(odd)}",
            file=sys.stderr,
        )
    turnout = (
        None
        if args.no_turnout
        else build_turnout(rows, args.election, here / "ncsbe_cache")
    )
    if turnout:
        prior = load_prior_turnout(PRIOR_ELECTION, here / "ncsbe_cache")
        if prior:
            daily = Counter()
            for (_, d), n in prior.items():
                daily[d] += n
            # Day N of this election's early voting lines up with day N of the earlier one.
            turnout["prior"] = {
                "year": int(PRIOR_ELECTION[:4]),
                "days": [{"d": d, "n": n} for d, n in sorted(daily.items())],
            }
            turnout["evDays"] = [d.isoformat() for d in sorted(FALLBACK_SCHEDULE)]
    addresses = {}
    for r in rows:  # keep one address per site rather than repeating it on every row
        addresses[r["site"]] = r.pop("addr") or addresses.get(r["site"], "")
    out = Path(args.output) if args.output else srcs[0].with_name("waits_report.html")
    data = {
        "rows": rows,
        "bands": BANDS,
        "turnout": turnout,
        "addresses": addresses,
        "links": {
            "tracker": TRACKER_URL,
            "county": COUNTY_URL,
            "countyTurnout": COUNTY_ELECTION_URL,
            "countyPdf": COUNTY_TURNOUT_URL,
            "voterLookup": VOTER_LOOKUP_URL,
            "ncsbe": NCSBE_URL,
        },
        "sources": [s.name for s in srcs],
        # Closing time per day, minutes after midnight, for "polls close at" in Right now.
        # Opening time per day, for counting each site's first report back to opening.
        "opens": {
            d.isoformat(): h * 60 + m
            for d, (open_, _) in FALLBACK_SCHEDULE.items()
            for h, m in [parse_clock(open_)]
        },
        "closes": {
            d.isoformat(): h * 60 + m
            for d, (_, close) in FALLBACK_SCHEDULE.items()
            for h, m in [parse_clock(close)]
        },
        "generated": datetime.now(TZ).strftime("%a %b %-d, %Y %-I:%M %p"),
    }
    payload = json.dumps(data, separators=(",", ":")).replace("</", "<\\/")
    out.write_text(TEMPLATE.replace("/*__DATA__*/null", payload))
    days = len({r["t"][:10] for r in rows})
    sites = len({r["site"] for r in rows})
    votes = sum(r["n"] for r in turnout["rows"]) if turnout else 0
    print(
        f"wrote {out} ({len(rows)} observations, {sites} sites, {days} day(s); {votes} early votes)"
    )
    if args.open:
        webbrowser.open(out.resolve().as_uri())


TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Wake Reported Wait Times</title>
<style>
:root {
  color-scheme: light;
  --page: #f9f9f7; --surface: #fcfcfb;
  --ink: #0b0b0b; --ink-2: #52514e; --muted: #898781;
  --grid: #e1e0d9; --axis: #c3c2b7; --ring: rgba(11,11,11,0.10);
  --none: #ecebe6;
  --b0: #75c6a1; --b1: #22af7d; --b2: #078f64; --b3: #066f4d; --b4: #00432c;
  --line: #199e70; --line-soft: #afddc6; --turn: #199e70; --turn-soft: #afddc6; --prior: #4a3aa7;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    color-scheme: dark;
    --page: #0d0d0d; --surface: #1a1a19;
    --ink: #ffffff; --ink-2: #c3c2b7; --muted: #898781;
    --grid: #2c2c2a; --axis: #383835; --ring: rgba(255,255,255,0.10);
    --none: #262624;
    --b0: #036042; --b1: #078f64; --b2: #22af7d; --b3: #75c6a1; --b4: #c8e9d8;
    --line: #199e70; --line-soft: #036042; --turn: #199e70; --turn-soft: #036042; --prior: #9085e9;
  }
}
:root[data-theme="dark"] {
  color-scheme: dark;
  --page: #0d0d0d; --surface: #1a1a19;
  --ink: #ffffff; --ink-2: #c3c2b7; --muted: #898781;
  --grid: #2c2c2a; --axis: #383835; --ring: rgba(255,255,255,0.10);
  --none: #262624;
  --b0: #036042; --b1: #078f64; --b2: #22af7d; --b3: #75c6a1; --b4: #c8e9d8;
  --line: #199e70; --line-soft: #036042; --turn: #199e70; --turn-soft: #036042; --prior: #9085e9;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--page); color: var(--ink);
  font: 14px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 1100px; margin: 0 auto; padding: 24px 16px 48px; }
h1 { font-size: 22px; margin: 0 0 4px; }
h2 { font-size: 16px; margin: 0 0 2px; }
.sub { color: var(--ink-2); margin: 0 0 12px; }
.closes { font-weight: 600; margin: -4px 0 8px; }
.card { background: var(--surface); border: 1px solid var(--ring); border-radius: 10px;
  padding: 16px; margin-top: 16px; }
.filters { display: flex; flex-wrap: wrap; gap: 12px; align-items: center; margin-top: 16px; }
.filters label { color: var(--ink-2); font-size: 13px; display: flex; gap: 6px; align-items: center; }
select { font: inherit; color: var(--ink); background: var(--surface); border: 1px solid var(--axis);
  border-radius: 6px; padding: 4px 8px; }
.foot { color: var(--muted); font-size: 12px; margin: 10px 0 0; }
.disclaimer { color: var(--muted); font-size: 12px; text-align: center; margin: 24px 0 0; }
.legend { display: flex; flex-wrap: wrap; gap: 14px; font-size: 12px; color: var(--ink-2); margin: 8px 0 4px; }
.legend.pick button { font: inherit; color: var(--ink-2); background: none; border: 0; padding: 2px 0; cursor: pointer;
  display: inline-flex; align-items: center; gap: 6px; }
.legend.pick button:hover { color: var(--ink); }
.legend.pick button.on { color: var(--ink); font-weight: 600; }
.legend span { display: inline-flex; align-items: center; gap: 6px; }
.sw { width: 12px; height: 12px; border-radius: 3px; display: inline-block; }
.scroll { overflow-x: auto; }
svg { display: block; }
svg text { fill: var(--muted); font-size: 11px; font-variant-numeric: tabular-nums; }
svg .lbl { fill: var(--ink-2); font-size: 12px; }
svg .num { fill: var(--ink-2); font-size: 12px; }
svg .city { fill: var(--ink); font-size: 12px; font-weight: 600; }
.kpis { display: flex; flex-wrap: wrap; gap: 24px; margin: 8px 0 4px; }
.kpi .v { font-size: 28px; font-weight: 600; }
.kpi .k { color: var(--ink-2); font-size: 12px; }
.now { columns: 300px; column-gap: 32px; }
.town { break-inside: avoid; padding-bottom: 6px; }
.now h3 { font-size: 12px; text-transform: uppercase; letter-spacing: .04em;
  color: var(--ink-2); margin: 10px 0 2px; }
.site { display: flex; align-items: center; gap: 8px; padding: 3px 0; }
a { color: inherit; text-decoration-color: var(--axis); text-underline-offset: 2px; }
a:hover { text-decoration-color: currentColor; }
.links { margin: -4px 0 0; font-size: 13px; color: var(--ink-2); }
.links a { color: var(--line); font-weight: 600; text-decoration: none; margin-right: 16px; }
.links a:hover { text-decoration: underline; }
svg a:hover text { fill: var(--line); text-decoration: underline; }
.site .n { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.site .w { color: var(--ink-2); font-size: 12px; white-space: nowrap; }
#tip { position: fixed; pointer-events: none; background: var(--surface); color: var(--ink);
  border: 1px solid var(--ring); border-radius: 8px; padding: 8px 10px; font-size: 12px;
  box-shadow: 0 4px 16px rgba(0,0,0,.15); display: none; z-index: 10; max-width: 280px; }
#tip b { display: block; margin-bottom: 2px; }
#tip .m { color: var(--ink-2); }
.empty { color: var(--muted); padding: 16px 0; }
</style>
</head>
<body>
<main>
  <h1>Wake County early voting reported wait times</h1>
  <p class="sub" id="meta"></p>
  <p class="links" id="links"></p>

  <section class="card" aria-labelledby="h-now">
    <h2 id="h-now">Right now</h2>
    <p class="closes" id="now-closes" hidden></p>
    <p class="sub" id="now-sub"></p>
    <div class="now" id="now"></div>
  </section>

  <div class="filters">
    <label>Day <select id="f-day"></select></label>
    <label>Town <select id="f-city"></select></label>
  </div>

  <section class="card" aria-labelledby="h-heat">
    <h2 id="h-heat">Through the day, by site</h2>
    <p class="sub" id="heat-sub"></p>
    <div class="legend" id="legend"></div>
    <div class="scroll" id="heat"></div>
  </section>

  <section class="card" aria-labelledby="h-avg">
    <h2 id="h-avg">Average reported wait time</h2>
    <p class="sub" id="avg-sub"></p>
    <div class="kpis" id="kpis"></div>
    <div class="legend pick" id="avg-legend"></div>
    <div id="avg"></div>
  </section>

  <section class="card" aria-labelledby="h-turn" id="turn-card">
    <h2 id="h-turn">Early votes cast per day</h2>
    <p class="sub" id="turn-sub"></p>
    <div class="kpis" id="turn-kpis"></div>
    <div class="legend" id="turn-legend"></div>
    <div id="turn"></div>
  </section>

  <section class="card" aria-labelledby="h-tod">
    <h2 id="h-tod">Typical reported wait time by time of day, by town</h2>
    <p class="sub" id="tod-sub"></p>
    <div class="scroll" id="tod"></div>
    <p class="foot">Sites post when their wait changes, so a reading stands from the time it was posted until the next post, and a site's first post of the day covers the time back to opening.</p>
  </section>

  <footer class="disclaimer">This page uses data from the Wake County Board of Elections and the North Carolina
    State Board of Elections but is not affiliated with or endorsed by either.</footer>
</main>
<div id="tip" role="tooltip"></div>
<script>
const DATA = /*__DATA__*/null;
const ROWS = DATA.rows, BANDS = DATA.bands, TURN = DATA.turnout, LINKS = DATA.links;
// Directions to a site from its address (the tracker's own directions link isn't in the CSV).
const mapUrl = site => DATA.addresses[site]
  ? "https://www.google.com/maps/dir/?api=1&destination=" + encodeURIComponent(DATA.addresses[site]) : null;
const siteLink = (site, cls = "") => { const u = mapUrl(site);
  return u ? `<a class="${cls}" href="${u}" target="_blank" rel="noopener" title="${DATA.addresses[site]} (directions)">${site}</a>`
    : `<span class="${cls}" title="${site}">${site}</span>`; };
function svgSiteLabel(svg, x, y, site, label) {  // site name in an SVG chart, linked to directions
  const u = mapUrl(site), parent = u ? el("a", { href: u, target: "_blank", rel: "noopener" }, svg) : svg;
  const t = text(parent, x, y, label, { class: "lbl" });
  if (u) el("title", {}, t).textContent = `${DATA.addresses[site]} (directions)`;
}
// votes[site][day] from the county or State Board file; sites the tracker doesn't list keep their file's name.
const VOTES = {}, TURN_CITY = {};
(TURN ? TURN.rows : []).forEach(r => { (VOTES[r.site] = VOTES[r.site] || {})[r.d] = r.n; TURN_CITY[r.site] = r.city; });
const fmtN = n => n == null ? "—" : n.toLocaleString();
const NS = "http://www.w3.org/2000/svg";
const bandVar = b => b == null ? "var(--none)" : `var(--b${b})`;
const bandOf = m => m == null ? null : m === 0 ? 0 : m <= 15 ? 1 : m <= 30 ? 2 : m <= 60 ? 3 : 4;
const day = t => t.slice(0, 10);
const mins = t => +t.slice(11, 13) * 60 + +t.slice(14, 16);
const clock = m => { const h = Math.floor(m / 60), mm = m % 60, h12 = (h + 11) % 12 + 1;
  return `${h12}${mm ? ":" + String(mm).padStart(2, "0") : ""} ${h < 12 ? "AM" : "PM"}`; };
const fmtMin = m => m == null ? "—" : `${Math.round(m)} min`;
const fmtDay = d => new Date(d + "T12:00").toLocaleDateString(undefined, { weekday: "short", month: "short", day: "numeric" });
// Typical spacing between polls, used as the width of each day's last poll.
const POLL_GAP = (() => { const ts = [...new Set(ROWS.map(r => r.t))].sort(), d = [];
  for (let i = 1; i < ts.length; i++) if (ts[i].slice(0, 10) === ts[i - 1].slice(0, 10)) d.push(mins(ts[i]) - mins(ts[i - 1]));
  d.sort((a, b) => a - b); return d.length ? d[d.length >> 1] || 5 : 5; })();
const mean = a => a.length ? a.reduce((s, x) => s + x, 0) / a.length : null;
const el = (tag, attrs = {}, parent) => { const e = document.createElementNS(NS, tag);
  for (const k in attrs) e.setAttribute(k, attrs[k]); if (parent) parent.appendChild(e); return e; };
const text = (parent, x, y, s, attrs = {}) => { const t = el("text", { x, y, ...attrs }, parent); t.textContent = s; return t; };

// Town order: most sites first, then alphabetical; sites alphabetical within a town.
const siteCity = {};
ROWS.forEach(r => siteCity[r.site] = r.city);
const cityCount = {};
Object.values(siteCity).forEach(c => cityCount[c] = (cityCount[c] || 0) + 1);
const CITIES = Object.keys(cityCount).sort((a, b) => cityCount[b] - cityCount[a] || a.localeCompare(b));
const DAYS = [...new Set(ROWS.map(r => day(r.t)))].sort();
const SLOT = 15;
// Averaged days for the Day picker: every day, and weekdays, Saturdays and Sundays separately, since
// their hours and crowds differ.
const dow = d => new Date(d + "T12:00").getDay();
const AVG_KINDS = {
  avg: { label: "Average day", noun: "day", has: d => true },
  "avg-wk": { label: "Average weekday", noun: "weekday", has: d => dow(d) % 6 !== 0 },
  "avg-sat": { label: "Average Saturday", noun: "Saturday", has: d => dow(d) === 6 },
  "avg-sun": { label: "Average Sunday", noun: "Sunday", has: d => dow(d) === 0 },
};
const isAvg = d => d in AVG_KINDS;
const kindDays = k => DAYS.filter(AVG_KINDS[k].has);
const dayLabel = d => { if (!isAvg(d)) return fmtDay(d); const n = kindDays(d).length, k = AVG_KINDS[d];
  return `an average ${k.noun} (${n} day${n > 1 ? "s" : ""})`; };
// Each site's reading in every slot of every day, timed by when the site reported it (not when it was
// polled) and standing until its next report: per[site][slot] = [minutes, one per day].
// A reading carried over from an earlier day counts from the day's first poll. Before a site's first
// wait time of the day, it counts that first one back to opening rather than leaving the slots empty.
function slotReadings(size, days = DAYS) {
  const polls = {}, per = {}, want = new Set(days);
  ROWS.forEach(r => { const d = day(r.t); if (want.has(d)) ((polls[d] = polls[d] || {})[r.site] = polls[d][r.site] || []).push(r); });
  let s0 = Infinity, s1 = -Infinity;
  for (const d in polls) for (const site in polls[d]) {
    let rs = polls[d][site].map(r => ({ r, m: r.u && day(r.u) === d ? Math.min(mins(r.u), mins(r.t)) : mins(r.t) }))
      .sort((a, b) => a.m - b.m || (a.r.t < b.r.t ? -1 : 1));
    const first = rs.findIndex(x => x.r.min != null);
    if (first < 0) continue;
    // Nothing counts before opening: a post made earlier stands from opening, as does the first post.
    const open = (DATA.opens || {})[d];
    rs = rs.slice(first).map(x => open == null ? x : { ...x, m: Math.max(x.m, open) });
    if (open != null) rs[0] = { ...rs[0], m: Math.min(rs[0].m, open) };
    const end = Math.max(...rs.map(x => mins(x.r.t)));
    for (let m = Math.floor(rs[0].m / size) * size, i = 0; m <= end; m += size) {
      while (i + 1 < rs.length && rs[i + 1].m < m + size) i++;
      if (rs[i].m >= m + size || rs[i].r.min == null) continue;
      ((per[site] = per[site] || {})[m] = per[site][m] || []).push(rs[i].r.min);
      s0 = Math.min(s0, m); s1 = Math.max(s1, m);
    }
  }
  return { per, s0, s1 };
}
// A weekday, Saturday or Sunday average only shows once it differs from the overall one, e.g. no
// "Average weekday" until the first weekend day is collected.
const AVGS = {}; for (const k in AVG_KINDS) { const n = kindDays(k).length;
  if (k === "avg" ? n : n && n < DAYS.length) AVGS[k] = slotReadings(SLOT, kindDays(k)); }
const avgVotes = (s, k) => { const v = Object.entries(VOTES[s] || {}).filter(([d]) => AVG_KINDS[k].has(d)).map(([, n]) => n);
  return v.length ? Math.round(mean(v)) : null; };

// Tooltip
const tip = document.getElementById("tip");
function showTip(ev, html) { tip.innerHTML = html; tip.style.display = "block"; moveTip(ev); }
function moveTip(ev) { const pad = 14, w = tip.offsetWidth, h = tip.offsetHeight;
  let x = ev.clientX + pad, y = ev.clientY + pad;
  if (x + w > innerWidth - 8) x = ev.clientX - w - pad;
  if (y + h > innerHeight - 8) y = ev.clientY - h - pad;
  tip.style.left = x + "px"; tip.style.top = y + "px"; }
const hideTip = () => tip.style.display = "none";
function hover(node, html) { node.addEventListener("mouseenter", e => showTip(e, html()));
  node.addEventListener("mousemove", moveTip); node.addEventListener("mouseleave", hideTip); }

// Header + legend
const last = ROWS.reduce((a, r) => r.t > a ? r.t : a, "");
document.getElementById("meta").textContent =
  `${Object.keys(siteCity).length} sites in ${CITIES.length} towns · ${DAYS.length} day${DAYS.length > 1 ? "s" : ""} of data · ` +
  `last poll ${fmtDay(day(last))} ${clock(mins(last))} · report built ${DATA.generated}`;
document.getElementById("legend").innerHTML = BANDS.map((b, i) =>
  `<span><i class="sw" style="background:var(--b${i})"></i>${b}</span>`).join("") +
  `<span><i class="sw" style="background:var(--none);box-shadow:inset 0 0 0 1px var(--axis)"></i>No data or other</span>`;

document.getElementById("links").innerHTML =
  `<a href="${LINKS.tracker}" target="_blank" rel="noopener">Live wait tracker ↗</a>` +
  `<a href="${LINKS.county}" target="_blank" rel="noopener">Early voting sites &amp; hours ↗</a>` +
  `<a href="${LINKS.countyPdf}" target="_blank" rel="noopener">Unofficial turnout report (Wake County BOE) ↗</a>` +
  `<a href="${LINKS.voterLookup}" target="_blank" rel="noopener">Voter lookup &amp; ballot status ↗</a>`;

// Right now: latest poll per site, grouped by town, worst first within the town.
(function renderNow() {
  const latest = {};
  ROWS.forEach(r => { if (!latest[r.site] || r.t > latest[r.site].t) latest[r.site] = r; });
  document.getElementById("now-sub").textContent = `As of ${fmtDay(day(last))} ${clock(mins(last))}. Towns ordered by number of sites.`;
  // Today's closing time, judged by the viewer's clock in Eastern time (the page is static).
  const nowET = new Date().toLocaleString("sv-SE", { timeZone: "America/New_York" }),
    close = (DATA.closes || {})[nowET.slice(0, 10)];
  if (close != null) { const c = document.getElementById("now-closes");
    c.textContent = `Polls ${mins(nowET) < close ? "close" : "closed"} at ${clock(close)} today`; c.hidden = false; }
  const box = document.getElementById("now");
  box.innerHTML = CITIES.map(c => {
    const sites = Object.values(latest).filter(r => r.city === c)
      .sort((a, b) => (b.min ?? -1) - (a.min ?? -1) || a.site.localeCompare(b.site));
    return `<div class="town"><h3>${c}</h3>` + sites.map(r =>
      `<div class="site"><i class="sw" style="background:${bandVar(r.band)}"></i>` +
      `${siteLink(r.site, "n")}<span class="w">${r.wait}</span></div>`).join("") + `</div>`;
  }).join("");
})();

// Filters
const fDay = document.getElementById("f-day"), fCity = document.getElementById("f-city");
fDay.innerHTML = Object.keys(AVGS).map(k => `<option value="${k}">${AVG_KINDS[k].label}</option>`).join("") +
  DAYS.map(d => `<option value="${d}">${fmtDay(d)}</option>`).reverse().join("");
fCity.innerHTML = `<option value="">All towns</option>` + CITIES.map(c => `<option>${c}</option>`).join("");
// The town is remembered; the day opens on the average day and only survives this tab's auto-reloads.
try { const s = JSON.parse(localStorage.getItem("wait-filters") || "{}"), d = sessionStorage.getItem("wait-day");
  if (DAYS.includes(d) || d in AVGS) fDay.value = d; if (CITIES.includes(s.city)) fCity.value = s.city; } catch (e) {}
function onFilter() {
  try { localStorage.setItem("wait-filters", JSON.stringify({ city: fCity.value }));
    sessionStorage.setItem("wait-day", fDay.value); } catch (e) {}
  renderHeat(); renderAvg(); renderTurnout();
}
fDay.onchange = fCity.onchange = onFilter;

function timeAxis(svg, x0, width, t0, t1, y, gridTop, gridBottom) {
  const span = Math.max(t1 - t0, 1), step = span > 360 ? 120 : span > 120 ? 60 : span > 60 ? 30 : 15;
  for (let m = Math.ceil(t0 / step) * step; m <= t1; m += step) {
    const x = x0 + (m - t0) / span * width;
    if (gridBottom != null) el("line", { x1: x, x2: x, y1: gridTop, y2: gridBottom, stroke: "var(--grid)" }, svg);
    text(svg, x, y, clock(m), { "text-anchor": "middle" });
  }
}

// Through the day: rows = sites grouped by town, columns = polls on the chosen day (each holding
// until the next, since a reading stands until the site posts a new one) or 15-minute slots of the
// averaged day.
function renderHeat() {
  const host = document.getElementById("heat"); host.innerHTML = "";
  const d = fDay.value, city = fCity.value, avg = isAvg(d), AVG = AVGS[d];
  document.getElementById("heat-sub").textContent = (avg
    ? `Each cell is a site's average reading in that 15 minutes across ${dayLabel(d).replace(/^an average \w+ \((.*)\)$/, "$1")}. ` +
      "Sites post when their wait changes, so a reading stands until the next post, and a site's first post of the day covers the time back to opening."
    : "Each cell is one poll of the county's tracker, holding until the next.") +
    " Sites are grouped by town; hover a cell for details.";
  const rows = ROWS.filter(r => (avg ? AVG_KINDS[d].has(day(r.t)) : day(r.t) === d) && (!city || r.city === city));
  if (!rows.length) { host.innerHTML = `<p class="empty">No polls for this selection.</p>`; return; }
  const cols = [];
  if (avg) for (let m = AVG.s0; m <= AVG.s1; m += SLOT) cols.push({ m0: m, m1: m + SLOT });
  else { const times = [...new Set(rows.map(r => r.t))].sort();
    times.forEach((t, i) => cols.push({ t, m0: mins(t), m1: i + 1 < times.length ? mins(times[i + 1]) : mins(t) + POLL_GAP })); }
  const cell = {}; rows.forEach(r => cell[r.site + "|" + r.t] = r);
  const lines = [];
  (city ? [city] : CITIES).forEach(c => {
    const sites = Object.keys(siteCity).filter(s => siteCity[s] === c).sort();
    if (!sites.length) return;
    lines.push({ city: c });
    sites.forEach(s => lines.push({ site: s }));
  });
  const labelW = Math.min(300, Math.max(180, host.clientWidth * 0.32)), rowH = 18, cityH = 24, top = 4;
  const votesW = TURN ? 64 : 0;
  const plotW = Math.max(host.clientWidth - labelW - votesW - 8, cols.length * 4);
  const t0 = cols[0].m0, tLast = cols[cols.length - 1].m0, t1 = cols[cols.length - 1].m1;
  const x = m => labelW + (m - t0) / (t1 - t0) * plotW;
  let y = top; lines.forEach(l => { l.y = y; y += l.city ? cityH : rowH; });
  const H = y + 22;
  const svg = el("svg", { width: labelW + plotW + votesW + 8, height: H, role: "img",
    "aria-label": `Reported wait times by site on ${dayLabel(d)}` }, host);
  const vx = labelW + plotW + votesW;
  lines.forEach((l, i) => {
    if (l.city) {
      text(svg, 0, l.y + cityH - 7, l.city, { class: "city" });
      if (TURN && i === 0) text(svg, vx, l.y + cityH - 7, avg ? "Votes/day" : "Early votes", { "text-anchor": "end" });
      return;
    }
    if (TURN) text(svg, vx, l.y + rowH / 2 + 4, fmtN(avg ? avgVotes(l.site, d) : (VOTES[l.site] || {})[d]), { class: "num", "text-anchor": "end" });
    const name = l.site.length > 38 ? l.site.slice(0, 36) + "…" : l.site;
    svgSiteLabel(svg, 12, l.y + rowH / 2 + 4, l.site, name);
    cols.forEach(({ t, m0, m1 }) => {
      const xa = x(m0), xb = x(m1);
      if (avg) {
        const vals = (AVG.per[l.site] || {})[m0], v = vals ? mean(vals) : null;
        const rect = el("rect", { x: xa, y: l.y + 1, width: Math.max(xb - xa - 1, 1), height: rowH - 2,
          rx: 2, fill: bandVar(bandOf(v)) }, svg);
        hover(rect, () => `<b>${l.site}</b><span class="m">${clock(m0)}–${clock(m1)}, ${AVG_KINDS[d].label.toLowerCase()}</span><br>` +
          (vals ? `Average ${fmtMin(v)}<br><span class="m">over ${vals.length} day${vals.length > 1 ? "s" : ""}</span>` : "No data"));
        return;
      }
      const r = cell[l.site + "|" + t];
      const rect = el("rect", { x: xa, y: l.y + 1, width: Math.max(xb - xa - 1, 1), height: rowH - 2,
        rx: 2, fill: bandVar(r ? r.band : null) }, svg);
      hover(rect, () => `<b>${l.site}</b><span class="m">${fmtDay(d)} ${clock(mins(t))}</span><br>` +
        (r ? `${r.wait}${r.u ? `<br><span class="m">site last updated ${r.u.slice(0, 10) === d ? clock(mins(r.u)) : fmtDay(day(r.u)) + " " + clock(mins(r.u))}</span>` : ""}${r.min == null ? `<br><span class="m">not read as a time</span>` : ""}` : "No poll"));
    });
  });
  const axisY = y + 14;
  timeAxis(svg, labelW, x(tLast) - labelW, t0, tLast, axisY);
}

// Average reported wait time across sites (midpoint of each range) in 15-minute slots. Every day
// and every average is drawn: the Day picker's choice bold in teal, the other averages as gray dashed
// lines, the other days faint. The legend selects a series.
const DAY_SLOTS = {}; DAYS.forEach(d => DAY_SLOTS[d] = slotReadings(SLOT, [d]));
const DASH = { avg: "", "avg-wk": "6 4", "avg-sat": "2 3", "avg-sun": "9 3 2 3" };
function seriesPts(key, city) {  // [{m, v, n, long}] for a day or an average kind
  const S = isAvg(key) ? AVGS[key] : DAY_SLOTS[key], pts = [];
  if (!S) return pts;
  const sites = Object.keys(siteCity).filter(s => !city || siteCity[s] === city);
  for (let m = S.s0; m <= S.s1; m += SLOT) {
    const vs = sites.map(s => (S.per[s] || {})[m]).filter(Boolean).map(mean);
    if (vs.length) pts.push({ m, v: mean(vs), n: vs.length, long: vs.filter(v => v >= 30).length });
  }
  return pts;
}
const seriesName = k => isAvg(k) ? AVG_KINDS[k].label : fmtDay(k);
function renderAvg() {
  const host = document.getElementById("avg"); host.innerHTML = "";
  const d = fDay.value, city = fCity.value, avg = isAvg(d);
  const rows = ROWS.filter(r => (avg ? AVG_KINDS[d].has(day(r.t)) : day(r.t) === d) && (!city || r.city === city) && r.min != null);
  document.getElementById("avg-sub").textContent = `${city || "All towns"}. Bold: ${dayLabel(d)}; dashed: the averages; faint: each other day. ` +
    "Each site's standing reading in every 15-minute slot is averaged across sites (and across days for an average). " +
    `Each reported range counts as its midpoint (15–30 min → 22.5 min); an open-ended wait like "60+" counts as its lower bound.`;
  const kp = document.getElementById("kpis"), lg = document.getElementById("avg-legend");
  const keys = [...Object.keys(AVGS), ...DAYS];
  const all = {}; keys.forEach(k => all[k] = seriesPts(k, city));
  const pts = all[d] || [];
  if (!rows.length || !pts.length) { kp.innerHTML = lg.innerHTML = ""; host.innerHTML = `<p class="empty">No polls for this selection.</p>`; return; }
  const peak = pts.reduce((a, p) => p.v > a.v ? p : a);
  const worst = rows.reduce((a, r) => r.min > a.min ? r : a);
  kp.innerHTML = [
    [fmtMin(mean(pts.map(p => p.v))), "average over the day"],
    [`${fmtMin(peak.v)} at ${clock(peak.m)}`, avg ? "busiest time of day" : "busiest time"],
    [worst.wait.replace(/ Minutes?/i, " min"), `longest reported wait (${worst.site}, ${avg ? fmtDay(day(worst.t)) + " " : ""}${clock(mins(worst.t))})`],
  ].map(([v, k]) => `<div class="kpi"><div class="v">${v}</div><div class="k">${k}</div></div>`).join("");

  // Legend: every series, clickable. A short line sample shows each one's style.
  const sample = (k, sel) => `<svg width="22" height="10" aria-hidden="true"><line x1="1" x2="21" y1="5" y2="5" ` +
    `stroke="${sel ? "var(--line)" : isAvg(k) ? "var(--ink-2)" : "var(--line)"}" stroke-width="${sel ? 3 : isAvg(k) ? 2 : 1.5}" ` +
    `${!sel && isAvg(k) && DASH[k] ? `stroke-dasharray="${DASH[k]}"` : ""} ${!sel && !isAvg(k) ? 'opacity="0.35"' : ""}/></svg>`;
  lg.innerHTML = keys.filter(k => all[k].length).map(k =>
    `<button type="button" data-k="${k}" class="${k === d ? "on" : ""}" aria-pressed="${k === d}">${sample(k, k === d)}${seriesName(k)}</button>`).join("");
  lg.querySelectorAll("button").forEach(b => b.onclick = () => { fDay.value = b.dataset.k; onFilter(); });

  const W = Math.max(host.clientWidth, 320), H = 220, L = 40, R = 12, T = 10, B = 24;
  const ms = keys.flatMap(k => all[k].map(p => p.m));
  const t0 = Math.min(...ms), t1 = Math.max(...ms), span = Math.max(t1 - t0, 1);
  const vmax = Math.max(15, Math.ceil(Math.max(...keys.flatMap(k => all[k].map(p => p.v))) / 15) * 15);
  const X = m => L + (m - t0) / span * (W - L - R), Y = v => T + (1 - v / vmax) * (H - T - B);
  const svg = el("svg", { width: W, height: H, role: "img", "aria-label": `Average reported wait time over the day, ${seriesName(d)} highlighted` }, host);
  for (let v = 0; v <= vmax; v += 15) {
    el("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: v ? "var(--grid)" : "var(--axis)" }, svg);
    text(svg, L - 6, Y(v) + 4, v + "m", { "text-anchor": "end" });
  }
  timeAxis(svg, L, W - L - R, t0, t1, H - 6);
  const pathOf = ps => ps.map((p, i) => `${i ? "L" : "M"}${X(p.m).toFixed(1)},${Y(p.v).toFixed(1)}`).join("");
  // Context first (faint days, then dashed averages), the selection on top.
  DAYS.filter(k => k !== d && all[k].length).forEach(k =>
    el("path", { d: pathOf(all[k]), fill: "none", stroke: "var(--line)", "stroke-width": 1.5, opacity: 0.3, "stroke-linejoin": "round" }, svg));
  Object.keys(AVGS).filter(k => k !== d && all[k].length).forEach(k =>
    el("path", { d: pathOf(all[k]), fill: "none", stroke: "var(--ink-2)", "stroke-width": 1.5, "stroke-dasharray": DASH[k],
      opacity: 0.8, "stroke-linejoin": "round" }, svg));
  const path = pathOf(pts);
  if (pts.length > 1) el("path", { d: path + `L${X(pts[pts.length - 1].m)},${Y(0)}L${X(pts[0].m)},${Y(0)}Z`,
    fill: "var(--line)", opacity: 0.12 }, svg);
  el("path", { d: path, fill: "none", stroke: "var(--line)", "stroke-width": 3, "stroke-linejoin": "round" }, svg);

  const cross = el("line", { y1: T, y2: H - B, stroke: "var(--axis)", visibility: "hidden" }, svg);
  const dot = el("circle", { r: 4, fill: "var(--line)", stroke: "var(--surface)", "stroke-width": 2, visibility: "hidden" }, svg);
  const hit = el("rect", { x: L, y: T, width: W - L - R, height: H - T - B, fill: "transparent" }, svg);
  hit.addEventListener("mousemove", e => {
    const bx = svg.getBoundingClientRect(), m = t0 + Math.round((e.clientX - bx.left - L) / (W - L - R) * span / SLOT) * SLOT;
    const at = k => all[k].find(p => p.m === m), p = at(d);
    cross.setAttribute("x1", X(m)); cross.setAttribute("x2", X(m)); cross.setAttribute("visibility", "visible");
    if (p) { dot.setAttribute("cx", X(m)); dot.setAttribute("cy", Y(p.v)); dot.setAttribute("visibility", "visible"); }
    else dot.setAttribute("visibility", "hidden");
    const others = Object.keys(AVGS).filter(k => k !== d && at(k)).map(k => `${seriesName(k)}: ${fmtMin(at(k).v)}`);
    const days = DAYS.filter(k => k !== d && at(k)).map(k => [k, at(k).v]);
    const dayTxt = days.length <= 7 ? days.map(([k, v]) => `${fmtDay(k)}: ${fmtMin(v)}`)
      : [`Other days: ${fmtMin(Math.min(...days.map(x => x[1])))}–${fmtMin(Math.max(...days.map(x => x[1])))}`];
    showTip(e, `<b>${clock(m)}–${clock(m + SLOT)}</b>` +
      (p ? `${seriesName(d)}: ${fmtMin(p.v)}<br><span class="m">${p.n} sites reporting · ${p.long} ${avg ? "averaging" : "at"} 30+ min</span>`
        : `${seriesName(d)}: no data`) +
      ([...others, ...dayTxt].length ? `<br><span class="m">${[...others, ...dayTxt].join("<br>")}</span>` : ""));
  });
  hit.addEventListener("mouseleave", () => { hideTip(); cross.setAttribute("visibility", "hidden"); dot.setAttribute("visibility", "hidden"); });
}

// Early votes per day (county, else State Board), following the Town filter; the chosen day is emphasized.
function renderTurnout() {
  const card = document.getElementById("turn-card");
  if (!TURN) { card.style.display = "none"; return; }
  const host = document.getElementById("turn"); host.innerHTML = "";
  const city = fCity.value, sel = fDay.value;
  const sites = Object.keys(VOTES).filter(s => !city || TURN_CITY[s] === city);
  const posted = new Set(TURN.rows.map(r => r.d));
  // Days with wait data but no votes yet still get a slot, marked as not posted yet. With an
  // earlier election to compare, every early voting day gets one.
  const PRIOR = TURN.prior, EV = TURN.evDays || [], showPrior = !!PRIOR && !city;
  const days = [...new Set([...posted, ...DAYS, ...(showPrior ? EV : [])])].sort();
  const waiting = DAYS.filter(d => !posted.has(d));  // tracked days the county hasn't posted votes for
  const priorOf = d => { const i = EV.indexOf(d); return PRIOR && i >= 0 ? PRIOR.days[i] : null; };
  const tot = days.map(d => ({ d, n: sites.reduce((a, s) => a + (VOTES[s][d] || 0), 0),
    top: sites.map(s => [s, VOTES[s][d] || 0]).filter(x => x[1]).sort((a, b) => b[1] - a[1]).slice(0, 3) }));
  const board = `<a href="${LINKS.ncsbe}" target="_blank" rel="noopener">NC State Board of Elections</a>`;
  const fromBoard = TURN.boardDays.length ? TURN.boardDays.map(fmtDay).join(", ") : "";
  document.getElementById("turn-sub").innerHTML = `${city || "All Wake County sites"}. ` + (TURN.county
    ? `Unofficial early votes from the <a href="${LINKS.countyTurnout}" target="_blank" rel="noopener">Wake County Board of Elections</a>` +
      (TURN.countyUpdated ? `, refreshed ${TURN.countyUpdated}` : "") +
      `. The county posts each day's votes that evening.` +
      (fromBoard ? ` ${fromBoard} from the ${board} (accepted votes, file updated ${TURN.boardUpdated}).` : "")
    : `Accepted in-person early votes from the ${board}, file updated ${TURN.boardUpdated}. ` +
      `The State Board posts each day's votes the next morning.`) +
    (PRIOR ? (showPrior ? ` Purple bars are the ${PRIOR.year} general election, matched by day of early voting (both began on a Thursday).` +
        (waiting.length ? ` ${waiting.map(fmtDay).join(", ")} ${EV[0].slice(0, 4)} count${waiting.length > 1 ? "s" : ""} not posted yet.` : "")
      : ` The ${PRIOR.year} comparison is for all towns only.`) : "");
  document.getElementById("turn-legend").innerHTML = showPrior
    ? `<span><i class="sw" style="background:var(--turn)"></i>${EV[0].slice(0, 4)}</span>` +
      `<span><i class="sw" style="background:var(--prior)"></i>${PRIOR.year}</span>` : "";
  const kp = document.getElementById("turn-kpis");
  if (!posted.size) { kp.innerHTML = ""; host.innerHTML = `<p class="empty">No early votes reported yet. The first day's votes appear after polls close.</p>`; return; }
  tot.forEach(x => x.pending = !posted.has(x.d));
  const total = tot.reduce((a, x) => a + x.n, 0), best = tot.reduce((a, x) => x.n > a.n ? x : a);
  const selN = tot.find(x => x.d === sel && !x.pending);
  const avgKpi = k => { const ns = tot.filter(x => !x.pending && AVG_KINDS[k].has(x.d)).map(x => x.n);
    return ns.length ? [fmtN(Math.round(mean(ns))), `average per ${AVG_KINDS[k].noun}`] : null; };
  // Running total so far against the same early voting days last time.
  const done = tot.filter(x => !x.pending && priorOf(x.d)), was = done.reduce((a, x) => a + priorOf(x.d).n, 0);
  const pct = (a, b) => `${a >= b ? "+" : "−"}${Math.abs(Math.round((a / b - 1) * 100))}%`;
  const vsPrior = showPrior && was ? [pct(done.reduce((a, x) => a + x.n, 0), was),
    `vs ${PRIOR.year} through day ${EV.indexOf(done[done.length - 1].d) + 1} (${fmtN(was)} then)`] : null;
  kp.innerHTML = [[fmtN(total), `early votes over ${posted.size} day${posted.size > 1 ? "s" : ""}`], vsPrior,
    [fmtN(best.n), `busiest day (${fmtDay(best.d)})`],
    isAvg(sel) ? avgKpi(sel) : selN ? [fmtN(selN.n), `on ${fmtDay(sel)}`] : null]
    .filter(Boolean)
    .map(([v, k]) => `<div class="kpi"><div class="v">${v}</div><div class="k">${k}</div></div>`).join("");

  const W = Math.max(host.clientWidth, 320), H = 200, L = 52, R = 8, T = 10, B = 24;
  const vmax = Math.max(...tot.map(x => Math.max(x.n, showPrior && priorOf(x.d) ? priorOf(x.d).n : 0)), 1);
  const stepRaw = vmax / 4, mag = 10 ** Math.floor(Math.log10(stepRaw));
  const step = [1, 2, 2.5, 5, 10].map(f => f * mag).find(x => x >= stepRaw), top = Math.ceil(vmax / step) * step;
  const Y = v => T + (1 - v / top) * (H - T - B), bw = (W - L - R) / days.length;
  // Paired with the earlier election, each day holds two bars 2px apart.
  const barW = showPrior ? Math.max(Math.min((bw - 6) / 2, 24), 2) : Math.max(Math.min(bw - 2, 40), 2);
  const bar = (xl, v, fill) => { const y0 = Y(0), h = y0 - Y(v), r = Math.min(4, barW / 2, h);
    // Rounded top, square baseline.
    el("path", { d: `M${xl},${y0}V${y0 - h + r}Q${xl},${y0 - h} ${xl + r},${y0 - h}H${xl + barW - r}` +
      `Q${xl + barW},${y0 - h} ${xl + barW},${y0 - h + r}V${y0}Z`, fill }, svg); };
  const svg = el("svg", { width: W, height: H, role: "img", "aria-label": "Early votes cast per day" }, host);
  for (let v = 0; v <= top; v += step) {
    el("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: v ? "var(--grid)" : "var(--axis)" }, svg);
    text(svg, L - 6, Y(v) + 4, fmtN(v), { "text-anchor": "end" });
  }
  const every = Math.ceil(days.length / Math.max(1, Math.floor((W - L - R) / 70)));
  tot.forEach((x, i) => {
    const cx = L + i * bw + bw / 2, y0 = Y(0), pr = showPrior ? priorOf(x.d) : null;
    const xl = showPrior ? cx - barW - 1 : cx - barW / 2;
    if (x.pending) { if (DAYS.includes(x.d) && !showPrior) text(svg, cx, y0 - 6, "not posted yet",
      { "text-anchor": "middle", fill: "var(--muted)" }); }
    else bar(xl, x.n, (isAvg(sel) ? AVG_KINDS[sel].has(x.d) : x.d === sel || !tot.some(t => t.d === sel && !t.pending)) ? "var(--turn)" : "var(--turn-soft)");
    if (pr) bar(cx + 1, pr.n, "var(--prior)");
    if (i % every === 0) text(svg, cx, H - 6, fmtDay(x.d).replace(/^\w+, /, ""), { "text-anchor": "middle" });
    const hit = el("rect", { x: L + i * bw, y: T, width: bw, height: H - T - B, fill: "transparent" }, svg);
    hover(hit, () => { const pr = showPrior ? priorOf(x.d) : null, yr = EV[0] ? EV[0].slice(0, 4) : "";
      return `<b>${fmtDay(x.d)}</b>` + (pr ? `<span class="m">day ${EV.indexOf(x.d) + 1} of early voting</span><br>` : "") +
        (x.pending ? (DAYS.includes(x.d) ? "Not posted yet; the county posts each day's votes that evening." : "Not yet")
          : `${pr ? yr + ": " : ""}${fmtN(x.n)} early votes`) +
        (pr ? `<br>${PRIOR.year} (${fmtDay(pr.d)}): ${fmtN(pr.n)}` + (x.pending ? "" : ` <span class="m">(${pct(x.n, pr.n)})</span>`) : "") +
        (x.top.length ? `<br><span class="m">${x.top.map(([s, n]) => `${s}: ${fmtN(n)}`).join("<br>")}</span>` : ""); });
    if (DAYS.includes(x.d)) { hit.style.cursor = "pointer"; hit.onclick = () => { fDay.value = x.d; onFilter(); }; }
  });
}

// Typical by time of day: town x half-hour, each site's standing reading averaged over every day,
// then over the town's sites.
(function renderTod() {
  const host = document.getElementById("tod");
  document.getElementById("tod-sub").textContent =
    `Mean reported wait time in each half hour across all ${DAYS.length} day${DAYS.length > 1 ? "s" : ""} collected and all sites in the town. ` +
    (DAYS.length < 3 ? "This view gets more useful as more days are collected." : "");
  const T = slotReadings(30);
  if (T.s0 > T.s1) { host.innerHTML = `<p class="empty">No data.</p>`; return; }
  const acc = {};
  for (const site in T.per) for (const m in T.per[site]) (acc[siteCity[site] + "|" + m] = acc[siteCity[site] + "|" + m] || []).push(...T.per[site][m]);
  const s0 = T.s0, s1 = T.s1, cols = (s1 - s0) / 30 + 1;
  const labelW = 130, rowH = 22, top = 4;
  const cw = Math.max(18, Math.min(44, (host.clientWidth - labelW - 8) / cols));
  const W = labelW + cols * cw + 8, H = top + CITIES.length * rowH + 22;
  const svg = el("svg", { width: W, height: H, role: "img", "aria-label": "Typical reported wait time by town and time of day" }, host);
  CITIES.forEach((c, i) => {
    const y = top + i * rowH;
    text(svg, 0, y + rowH / 2 + 4, `${c} (${cityCount[c]})`, { class: "lbl" });
    for (let j = 0; j < cols; j++) {
      const m = s0 + j * 30, vals = acc[c + "|" + m], v = vals ? mean(vals) : null;
      const rect = el("rect", { x: labelW + j * cw, y: y + 1, width: cw - 2, height: rowH - 2, rx: 3,
        fill: bandVar(bandOf(v)) }, svg);
      hover(rect, () => `<b>${c}, ${clock(m)}–${clock(m + 30)}</b>` +
        (vals ? `Average ${fmtMin(v)}<br><span class="m">${vals.length} site-day${vals.length > 1 ? "s" : ""}</span>` : "No data"));
    }
  });
  for (let j = 0; j < cols; j++) {
    const m = s0 + j * 30;
    if (m % 60 === 0 && (cw >= 30 || m % 120 === 0)) text(svg, labelW + j * cw, H - 6, clock(m), { "text-anchor": "start" });
  }
})();

// Reload every 5 minutes to pick up republished reports. Filters survive (localStorage) and the
// browser restores the scroll position. A hidden tab waits until it's viewed again.
const RELOAD_MS = 5 * 60 * 1000;
let reloadDue = false;
setTimeout(() => { reloadDue = true; if (!document.hidden) location.reload(); }, RELOAD_MS);
document.addEventListener("visibilitychange", () => { if (reloadDue && !document.hidden) location.reload(); });

onFilter();
let rz; addEventListener("resize", () => { clearTimeout(rz); rz = setTimeout(() => { renderHeat(); renderAvg(); renderTurnout(); }, 150); });
</script>
</body>
</html>
"""


if __name__ == "__main__":
    main()
