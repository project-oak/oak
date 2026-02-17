#!/usr/bin/env python3
"""Generate Rust Crates dependency version report.

Analyze crate versions by comparing requested versions in Bazel config, actual
versions in Cargo.lock, and the latest versions on crates.io.

Usage Examples:
    # Run analysis using default 'Cargo.bazel.lock' and fetch latest from
    crates.io:
    python3 scripts/analyze_crate_versions.py

    # Analyze a specific lock file:
    python3 scripts/analyze_crate_versions.py path/to/Cargo.lock

    # Force update the versions cache:
    python3 scripts/analyze_crate_versions.py --update
"""

import argparse
import json
import os
import pathlib
import re
import ssl
import sys
import time
import urllib.request


def parse_oak_crates(file_path):
  """Parse the bazel/crates/oak_crates.bzl file to extract crate names and requested versions."""
  with open(file_path, "r") as f:
    content = f.read()

  crates = {}
  # Match "name": crate.spec(...)
  pattern = r'"([^"]+)":\s*crate\.spec\((.*?)\)'
  for name, spec_content in re.findall(pattern, content, re.DOTALL):
    version_match = re.search(r'version\s*=\s*"([^"]+)"', spec_content)
    if version_match:
      version = version_match.group(1)
      if name not in crates or version_key(version) > version_key(crates[name]):
        crates[name] = version
    elif "git =" in spec_content:
      crates[name] = "git"

  return crates


def parse_cargo_lock(file_path):
  """Parse Cargo.lock to extract actual crate versions currently installed."""
  if not os.path.exists(file_path):
    return {}
  with open(file_path, "r") as f:
    lines = f.readlines()

  packages = {}
  current_package = None
  current_version = None

  for line in lines:
    line = line.strip()
    if line == "[[package]]":
      if current_package and current_version:
        packages.setdefault(current_package, []).append(current_version)
      current_package = None
      current_version = None
    elif line.startswith("name = "):
      current_package = line.split("=")[1].strip().strip('"')
    elif line.startswith("version = "):
      current_version = line.split("=")[1].strip().strip('"')

  if current_package and current_version:
    packages.setdefault(current_package, []).append(current_version)

  return packages


def is_pre_release(v):
  """Check if a version string indicates a pre-release version."""
  if v == "*" or v == "git":
    return False
  # Remove leading characters often found in requested versions
  v = v.lstrip("=^~")
  # SemVer pre-release is a hyphen after the patch version, before any plus.
  return "-" in v.split("+")[0]


def version_key(v):
  """Convert a version string into a comparable key."""
  if v == "*" or v == "git":
    return [-1]
  # Remove leading '=' or other prefixes
  v = v.lstrip("=^~")
  # Split version and build metadata
  v = v.split("+")[0]

  # Check for pre-release
  pre_release = False
  if "-" in v:
    pre_release = True
    v = v.split("-", 1)[0]

  parts = []
  for p in v.split("."):
    m = re.match(r"(\d+)", p)
    if m:
      parts.append(int(m.group(1)))
    else:
      parts.append(0)

  # Ensure at least 3 parts for major.minor.patch
  while len(parts) < 3:
    parts.append(0)

  # Append stability bit: 1 for stable, 0 for pre-release
  parts.append(0 if pre_release else 1)
  return parts


def is_lower(actual, requested):
  if requested == "*" or requested == "git":
    return False
  return version_key(actual) < version_key(requested)


# Create a global SSL context that ignores certificate validation
ssl_context = ssl.create_default_context()
ssl_context.check_hostname = False
ssl_context.verify_mode = ssl.CERT_NONE


def get_crate_versions(crate_name):
  """Get all versions of a crate from crates.io."""
  url = f"https://crates.io/api/v1/crates/{crate_name}"
  req = urllib.request.Request(
      url, headers={"User-Agent": "Oak-Crate-Analyzer/0.1"}
  )
  with urllib.request.urlopen(req, timeout=5, context=ssl_context) as response:
    data = json.loads(response.read().decode())
    # Return list of (version_string, is_yanked)
    return [(v["num"], v["yanked"]) for v in data.get("versions", [])]


def find_latest_updates(actual_v, all_versions):
  """Find the latest Major, Minor, and Patch updates available based on the provided info."""
  act = version_key(actual_v)
  if act == [-1]:
    return {}

  # Normalize to 3 parts for comparison
  act_parts = (act + [0, 0, 0])[:3]

  updates = {"Major": None, "Minor": None, "Patch": None}

  for v_str in all_versions:
    v = version_key(v_str)
    if v == [-1] or v <= act:
      continue

    v_parts = (v + [0, 0, 0])[:3]

    # Major update
    if v_parts[0] > act_parts[0]:
      if not updates["Major"] or v > version_key(updates["Major"]):
        updates["Major"] = v_str
    # Minor update
    elif v_parts[1] > act_parts[1]:
      if not updates["Minor"] or v > version_key(updates["Minor"]):
        updates["Minor"] = v_str
    # Patch update
    elif v_parts[2] > act_parts[2] or (v_parts[2] == act_parts[2] and v > act):
      if not updates["Patch"] or v > version_key(updates["Patch"]):
        updates["Patch"] = v_str

  return {k: v for k, v in updates.items() if v}


def collect_crate_data(
    bzl_file, lock_file, filter_str=None, cached_versions=None
):
  """Collect crate version data from Bazel config, Cargo.lock, and crates.io."""
  requested_crates = parse_oak_crates(bzl_file)
  actual_crates = parse_cargo_lock(lock_file)

  crate_names = sorted(requested_crates.keys())
  if filter_str:
    crate_names = [n for n in crate_names if filter_str.lower() in n.lower()]

  total = len(crate_names)
  data = []
  cached_versions = cached_versions or {}

  fetched_any = False
  for i, name in enumerate(crate_names, 1):
    requested = requested_crates[name]
    actual_list = actual_crates.get(name, [])

    if name in cached_versions:
      versions = cached_versions[name]
    else:
      fetched_any = True
      print(
          f"[{i}/{total}] Fetching versions for {name}...",
          end="\r",
          file=sys.stderr,
      )
      versions = get_crate_versions(name)
      # Small delay to be nice to crates.io
      time.sleep(0.05)

    data.append({
        "name": name,
        "requested": requested,
        "actual": actual_list,
        "versions": versions,
    })
  if fetched_any:
    print(f"\nFinished fetching data for {total} crates.", file=sys.stderr)
  return data


def strip_metadata(v):
  """Remove build metadata (anything after +) from a version string."""
  if not isinstance(v, str) or v == "*" or v == "git":
    return v
  return v.split("+", 1)[0]


def print_report(
    data,
    total_count=None,
    include_pre_release=False,
    versions_path=None,
    cache_age=None,
):
  """Print a report of crate versions and available updates."""
  # Define a shared format string for the table to ensure perfect alignment
  row_fmt = "{:<30} | {:<12} | {:<12} | {:<12} | {:<12} | {:<12}"

  if not include_pre_release:
    data = [d for d in data if not is_pre_release(d["requested"])]

  print(
      row_fmt.format(
          "Crate",
          "Requested",
          "Actual",
          "Latest (P)",
          "Latest (m)",
          "Latest (M)",
      )
  )
  print("-" * 110)

  summary = {"Major": 0, "Minor": 0, "Patch": 0}

  for entry in data:
    name = entry["name"]
    requested = strip_metadata(entry["requested"])
    actual_list = entry["actual"]
    versions_info = entry.get("versions", [])

    # Filter out yanked versions
    all_versions = [v for v, yanked in versions_info if not yanked]

    if not include_pre_release:
      all_versions = [v for v in all_versions if not is_pre_release(v)]
      actual_list = [v for v in actual_list if not is_pre_release(v)]

    l_patch = "-"
    l_minor = "-"
    l_major = "-"

    if not actual_list:
      max_v = max(all_versions, key=version_key) if all_versions else "N/A"
      l_major = strip_metadata(max_v)
    else:
      highest_actual = max(actual_list, key=version_key)
      updates = find_latest_updates(highest_actual, all_versions)

      if updates.get("Patch"):
        l_patch = strip_metadata(updates["Patch"])
        summary["Patch"] += 1
      if updates.get("Minor"):
        l_minor = strip_metadata(updates["Minor"])
        summary["Minor"] += 1
      if updates.get("Major"):
        l_major = strip_metadata(updates["Major"])
        summary["Major"] += 1

    if not actual_list:
      print(
          row_fmt.format(name, requested, "MISSING", l_patch, l_minor, l_major)
      )
    else:
      for i, v in enumerate(actual_list):
        display_v = strip_metadata(v)
        if is_lower(v, requested):
          display_v += " (<)"
        if i == 0:
          print(
              row_fmt.format(
                  name, requested, display_v, l_patch, l_minor, l_major
              )
          )
        else:
          print(row_fmt.format("", "", display_v, "", "", ""))

  print("-" * 110)
  print("\nUpdate Summary:")
  print(f"  Crates with Major Updates: {summary['Major']}")
  print(f"  Crates with Minor Updates: {summary['Minor']}")
  print(f"  Crates with Patch Updates: {summary['Patch']}")

  if total_count is not None and total_count != len(data):
    print(f"  Showing {len(data)} crates (filtered from {total_count})")
  else:
    print(f"  Total Crates Analyzed:     {len(data)}")

  if versions_path:
    age_str = (
        f" (updated {format_age(cache_age)} ago)"
        if cache_age is not None
        else ""
    )
    print(f"\nVersions Cache: {versions_path}{age_str}")
    print("To update the cache, run with the --update or -u flag.")


def format_age(seconds):
  """Format a time duration in seconds into a human-readable string."""
  if seconds < 60:
    return f"{int(seconds)}s"
  if seconds < 3600:
    return f"{int(seconds // 60)}m"
  if seconds < 86400:
    return f"{int(seconds // 3600)}h"
  return f"{int(seconds // 86400)}d"


def main():
  parser = argparse.ArgumentParser(
      description=(
          "Analyze crate versions and generate reports. Uses a local cache to"
          " store internet data."
      ),
      epilog="""
Report columns:
  Latest (P): Highest available Patch update.
  Latest (m): Highest available Minor update.
  Latest (M): Highest available Major update.

A dash (-) indicates that no update of that type is available (e.g., you are already on the latest patch).
""",
      formatter_class=argparse.RawDescriptionHelpFormatter,
  )
  parser.add_argument(
      "lock_file",
      nargs="?",
      default="Cargo.bazel.lock",
      help="Path to Cargo.lock or Cargo.bazel.lock",
  )
  parser.add_argument(
      "--versions_file", help="Path to a custom versions cache file"
  )
  parser.add_argument(
      "--update",
      "-u",
      action="store_true",
      help="Force update the versions cache from crates.io",
  )
  parser.add_argument(
      "--filter", "-f", help="Filter report by crate name (substring match)"
  )
  parser.add_argument(
      "--include-pre-release",
      action="store_true",
      help="Include pre-release versions in the report",
  )
  args = parser.parse_args()

  bzl_file = "bazel/crates/oak_crates.bzl"

  default_cache_path = (
      pathlib.Path.home() / ".cache" / "oak" / "crate_cache.json"
  )
  versions_path = (
      pathlib.Path(args.versions_file)
      if args.versions_file
      else default_cache_path
  )

  cached_versions = {}
  cache_age = None
  if versions_path.exists() and not args.update:
    cache_age = time.time() - versions_path.stat().st_mtime
    with open(versions_path, "r") as f:
      loaded_data = json.load(f)
      if isinstance(loaded_data, list):
        # Support old format (list of dicts)
        for entry in loaded_data:
          if "name" in entry and "versions" in entry:
            cached_versions[entry["name"]] = entry["versions"]
      elif isinstance(loaded_data, dict):
        # New format (dict of name -> versions)
        cached_versions = loaded_data
  elif args.update:
    print(
        f"Forcing update of versions from crates.io to {versions_path}...",
        file=sys.stderr,
    )
  else:
    print(
        f"Versions cache {versions_path} not found. Fetching from crates.io...",
        file=sys.stderr,
    )

  if not os.path.exists(bzl_file):
    print(f"Error: {bzl_file} not found")
    sys.exit(1)
  if not os.path.exists(args.lock_file):
    print(f"Error: {args.lock_file} not found")
    sys.exit(1)

  # If we need to populate or update the cache, we collect everything.
  # If we have a cache and are not updating, we can filter during collection.
  need_full_fetch = not versions_path.exists() or args.update
  collect_filter = None if need_full_fetch else args.filter

  try:
    data = collect_crate_data(
        bzl_file,
        args.lock_file,
        filter_str=collect_filter,
        cached_versions=cached_versions,
    )
  except Exception as e:  # pylint: disable=broad-exception-caught
    print(f"Error during data collection: {e}")
    sys.exit(1)

  # Save/Update the cache if we did a full fetch or it was missing
  if need_full_fetch:
    # Ensure directory exists for the cache
    versions_path.parent.mkdir(parents=True, exist_ok=True)
    save_data = {entry["name"]: entry["versions"] for entry in data}
    with open(versions_path, "w") as f:
      json.dump(save_data, f, indent=2)
    cache_age = 0

  total_count = len(data)
  report_data = data
  if args.filter:
    report_data = [d for d in data if args.filter.lower() in d["name"].lower()]

  print_report(
      report_data,
      total_count=total_count,
      include_pre_release=args.include_pre_release,
      versions_path=versions_path,
      cache_age=cache_age,
  )


if __name__ == "__main__":
  main()
