"""Generate Rust Crates dependency version report.

Analyze crate versions by comparing requested versions in Bazel config, actual
versions in Cargo.lock, and the latest versions on crates.io.

Usage Examples:
    # Run analysis using default 'Cargo.bazel.lock' and fetch latest from
    crates.io:
    python3 scripts/analyze_crate_versions.py

    # Run analysis and save the results to a file for later use:
    python3 scripts/analyze_crate_versions.py --save crate_report.json

    # Load previously saved data to explore the report without re-fetching from
    crates.io:
    python3 scripts/analyze_crate_versions.py --load crate_report.json

    # Analyze a specific lock file:
    python3 scripts/analyze_crate_versions.py path/to/Cargo.lock
"""

import argparse
import json
import os
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
  with urllib.request.urlopen(
      req, timeout=5, context=ssl_context
  ) as response:
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


def collect_crate_data(bzl_file, lock_file, filter_str=None):
  """Collect crate version data from Bazel config, Cargo.lock, and crates.io."""
  requested_crates = parse_oak_crates(bzl_file)
  actual_crates = parse_cargo_lock(lock_file)

  crate_names = sorted(requested_crates.keys())
  if filter_str:
    crate_names = [n for n in crate_names if filter_str.lower() in n.lower()]

  total = len(crate_names)
  data = []
  for i, name in enumerate(crate_names, 1):
    print(
        f"[{i}/{total}] Fetching versions for {name}...",
        end="\r",
        file=sys.stderr,
    )
    requested = requested_crates[name]
    actual_list = actual_crates.get(name, [])

    versions = get_crate_versions(name)
    # Small delay to be nice to crates.io
    time.sleep(0.05)

    data.append({
        "name": name,
        "requested": requested,
        "actual": actual_list,
        "versions": versions,
    })
  print(f"\nFinished fetching data for {total} crates.", file=sys.stderr)
  return data


def print_report(data, total_count=None, exclude_pre_release=False):
  """Print a report of crate versions and available updates."""
  # Define a shared format string for the table to ensure perfect alignment
  row_fmt = "{:<30} | {:<12} | {:<12} | {:<12} | {:<12} | {:<12}"

  if exclude_pre_release:
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
    requested = entry["requested"]
    actual_list = entry["actual"]
    versions_info = entry.get("versions", [])

    # Filter out yanked versions
    all_versions = [v for v, yanked in versions_info if not yanked]

    if exclude_pre_release:
      all_versions = [v for v in all_versions if not is_pre_release(v)]
      actual_list = [v for v in actual_list if not is_pre_release(v)]

    l_patch = "-"
    l_minor = "-"
    l_major = "-"

    if not actual_list:
      max_v = max(all_versions, key=version_key) if all_versions else "N/A"
      l_major = max_v
    else:
      highest_actual = max(actual_list, key=version_key)
      updates = find_latest_updates(highest_actual, all_versions)

      if updates.get("Patch"):
        l_patch = updates["Patch"]
        summary["Patch"] += 1
      if updates.get("Minor"):
        l_minor = updates["Minor"]
        summary["Minor"] += 1
      if updates.get("Major"):
        l_major = updates["Major"]
        summary["Major"] += 1

    if not actual_list:
      print(
          row_fmt.format(name, requested, "MISSING", l_patch, l_minor, l_major)
      )
    else:
      for i, v in enumerate(actual_list):
        if i == 0:
          print(row_fmt.format(name, requested, v, l_patch, l_minor, l_major))
        else:
          print(row_fmt.format("", "", v, "", "", ""))

  print("-" * 110)
  print("\nUpdate Summary:")
  print(f"  Crates with Major Updates: {summary['Major']}")
  print(f"  Crates with Minor Updates: {summary['Minor']}")
  print(f"  Crates with Patch Updates: {summary['Patch']}")

  if total_count is not None and total_count != len(data):
    print(f"  Showing {len(data)} crates (filtered from {total_count})")
  else:
    print(f"  Total Crates Analyzed:     {len(data)}")


def main():
  parser = argparse.ArgumentParser(
      description=(
          "Analyze crate versions and generate reports. This tool can create"
          " JSON data structures for offline analysis."
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
  parser.add_argument("--save", help="Save crate data to a JSON file")
  parser.add_argument("--load", help="Load crate data from a JSON file")
  parser.add_argument(
      "--filter", "-f", help="Filter report by crate name (substring match)"
  )
  parser.add_argument(
      "--exclude-pre-release",
      action="store_true",
      help="Exclude pre-release versions from the report",
  )
  args = parser.parse_args()

  bzl_file = "bazel/crates/oak_crates.bzl"

  if args.load:
    if not os.path.exists(args.load):
      print(f"Error: {args.load} not found")
      sys.exit(1)
    with open(args.load, "r") as f:
      data = json.load(f)
  else:
    if not os.path.exists(bzl_file):
      print(f"Error: {bzl_file} not found")
      sys.exit(1)
    if not os.path.exists(args.lock_file):
      print(f"Error: {args.lock_file} not found")
      sys.exit(1)

    # If saving, we collect everything.
    # If not, we can speed up by filtering during collection.
    collect_filter = None if args.save else args.filter
    try:
      data = collect_crate_data(
          bzl_file, args.lock_file, filter_str=collect_filter
      )
    except Exception as e:   # pylint: disable=broad-exception-caught
      print(f"Error during data collection: {e}")
      sys.exit(1)

  if args.save:
    with open(args.save, "w") as f:
      json.dump(data, f, indent=2)

  total_count = len(data)
  report_data = data
  if args.filter:
    report_data = [d for d in data if args.filter.lower() in d["name"].lower()]

  print_report(
      report_data,
      total_count=total_count,
      exclude_pre_release=args.exclude_pre_release,
  )


if __name__ == "__main__":
  main()
