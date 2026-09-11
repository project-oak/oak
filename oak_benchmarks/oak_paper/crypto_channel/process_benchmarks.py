#!/usr/bin/env python3
"""
Benchmark Processor for Crypto Channel Benchmarks

This script parses the output of the Criterion benchmark suite, generates
a Markdown table summary, and creates a throughput plot.

Dependencies: matplotlib, numpy
"""

import re
import json
import argparse
import os
import matplotlib.pyplot as plt


def convert_to_mib(value, unit):
  """Convert throughput values to MiB/s."""
  value = float(value)
  if unit == "B/s":
    return value / (1024 * 1024)
  elif unit == "KiB/s":
    return value / 1024
  elif unit == "MiB/s":
    return value
  elif unit == "GiB/s":
    return value * 1024
  else:
    raise ValueError(f"Unknown unit: {unit}")


# Criterion picks the unit per row, so a table is the only way to read the
# numbers back. It emits "us" only when the output stream is not UTF-8.
TIME_UNITS_S = {
    "ps": 1e-12,
    "ns": 1e-9,
    "µs": 1e-6,
    "us": 1e-6,
    "ms": 1e-3,
    "s": 1.0,
}


def convert_to_seconds(value, unit):
  """Convert a Criterion time value to seconds."""
  if unit not in TIME_UNITS_S:
    raise ValueError(f"Unknown unit: {unit}")
  return float(value) * TIME_UNITS_S[unit]


def parse_log(log_file):
  """Parse Criterion log file and extract time and throughput."""
  # Regex patterns
  # These have to change together with the benchmark names in `benchmark.rs`.
  # A pattern that stops matching does not raise, it silently drops every row
  # it used to match. The parentheses in "TLS (rustls)" are literal. The VM
  # legs carry their networking mode in brackets, e.g. "VM TCP [vhost-net]",
  # and stay separate series because the two modes differ by more than an order
  # of magnitude at large payloads.
  bench_pattern = re.compile(
      r"Benchmarking (?P<env>RK|Local TCP|VM TCP)(?: \[(?P<net>[^]]+)\])?"
      r" (?P<protocol>Plaintext|Noise|TLS \(rustls\)) Message"
      r" Exchange/(?P<size>\d+)"
  )

  results = {}
  current_env = None
  current_protocol = None
  current_size = None

  if not os.path.exists(log_file):
    print(f"Error: Log file not found: {log_file}")
    return results

  with open(log_file, "r") as f:
    for line in f:
      bench_match = bench_pattern.search(line)
      if bench_match:
        env = bench_match["env"].replace(" TCP", "")
        if bench_match["net"]:
          env = f"{env} ({bench_match['net']})"
        current_env = env
        current_protocol = bench_match["protocol"]
        current_size = int(bench_match["size"])
        key = (current_env, current_protocol, current_size)
        if key not in results:
          results[key] = {}
        continue

      # Any other benchmark announcement ends the current group. Without this
      # the parser stays latched on the last Message Exchange row and the next
      # `time:` line it sees overwrites it -- and there is such a line: the
      # `Setup` groups emit "Benchmarking <env> <protocol> Setup/setup", which
      # `bench_pattern` deliberately does not match. The symptom is a table
      # whose largest-payload row shows a handshake time of a few microseconds
      # beside a GiB/s throughput, which is silently wrong rather than absent.
      if line.startswith("Benchmarking "):
        current_env = None
        current_protocol = None
        current_size = None
        continue

      if "thrpt:" in line and current_env:
        # Extract mean throughput (middle value in brackets)
        # Example: [31.858 KiB/s 32.232 KiB/s 32.733 KiB/s]
        try:
          parts = line.split("[")[1].split("]")[0].split()
          if len(parts) >= 4:
            val = parts[2]
            unit = parts[3]
            mib_val = convert_to_mib(val, unit)
            results[(current_env, current_protocol, current_size)][
                "thrpt_mib"
            ] = mib_val
            results[(current_env, current_protocol, current_size)][
                "thrpt_raw"
            ] = f"{val} {unit}"
        except (IndexError, ValueError) as e:
          pass  # Skip lines with unexpected format

      if "time:" in line and current_env:
        try:
          parts = line.split("[")[1].split("]")[0].split()
          if len(parts) >= 4:
            val = parts[2]
            unit = parts[3]
            results[(current_env, current_protocol, current_size)][
                "time_raw"
            ] = f"{val} {unit}"
            results[(current_env, current_protocol, current_size)]["time_s"] = (
                convert_to_seconds(val, unit)
            )
        except IndexError:
          pass

  return results


def format_exchange_rate(time_s):
  """Format the request rate a single sequential client can sustain.

  `benchmark_wrapper` reports `(send + recv) / 2`, so a full exchange takes
  `2 * time_s` and the rate is `1 / (2 * time_s)`. Dividing into the reported
  figure directly would overstate the rate by exactly a factor of two.

  This is a closed-loop rate for one client, not server capacity: the harness
  never has more than one exchange in flight, so it says nothing about what the
  server sustains under concurrency.
  """
  if not time_s:
    return "N/A"
  rate = 1.0 / (2.0 * time_s)
  if rate >= 1000:
    return f"{rate / 1000:,.1f}k"
  return f"{rate:,.1f}"


def print_markdown_table(results):
  """Print results as a Markdown table."""
  print("\n## Performance Benchmark Results\n")
  print(
      "| Protocol | Environment | Size (Bytes) | Time (Mean) | Throughput"
      " (Mean) | Exchanges/s |"
  )
  print("| :--- | :--- | ---: | ---: | ---: | ---: |")

  sorted_keys = sorted(results.keys(), key=lambda x: (x[1], x[0], x[2]))

  current_p = None
  current_e = None

  for key in sorted_keys:
    env, protocol, size = key
    data = results[key]

    p_str = f"**{protocol}**" if protocol != current_p else ""
    e_str = f"**{env}**" if env != current_e or protocol != current_p else ""

    time_str = data.get("time_raw", "N/A")
    thrpt_str = data.get("thrpt_raw", "N/A")
    rate_str = format_exchange_rate(data.get("time_s"))

    print(
        f"| {p_str} | {e_str} | {size:,} | {time_str} | {thrpt_str} |"
        f" {rate_str} |"
    )

    current_p = protocol
    current_e = env

  print(
      "\n`Exchanges/s` is the rate one client achieves by sending the next"
      " message only after the previous reply arrives: `1 / (send + recv)`."
      " It is not server capacity, which is bounded by concurrency this"
      " harness does not exercise."
  )


def generate_plot(results, output_image):
  """Generate and save throughput plot."""
  # Prepare data for plotting
  graph_data = {}
  for key, data in results.items():
    env, protocol, size = key
    label = f"{protocol} {env}"
    if label not in graph_data:
      graph_data[label] = {"sizes": [], "thrpt": []}
    if "thrpt_mib" in data:
      graph_data[label]["sizes"].append(size)
      graph_data[label]["thrpt"].append(data["thrpt_mib"])

  # Sort by size
  for label in graph_data:
    zipped = sorted(zip(graph_data[label]["sizes"], graph_data[label]["thrpt"]))
    graph_data[label]["sizes"] = [z[0] for z in zipped]
    graph_data[label]["thrpt"] = [z[1] for z in zipped]

  plt.figure(figsize=(12, 7))

  # Marker per leg, line style and colour per protocol. The two VM legs differ
  # only in host networking, so they get neighbouring markers. Plain "VM" is
  # what logs from before the two legs were split look like; the regex still
  # accepts them, so the plot has to as well.
  leg_markers = {
      "Local": "o",
      "VM": "s",
      "VM (user-mode net)": "s",
      "VM (vhost-net)": "D",
      "RK": "^",
  }
  # Any leg can in principle run in a TEE, and listing the combinations would
  # need a marker per combination. A TEE variant instead keeps the marker of
  # the leg it is a variant of and is drawn hollow, which stays readable as
  # more legs gain one, and means a new variant plots without a change here.
  env_markers = {leg: (marker, "full") for leg, marker in leg_markers.items()}
  for leg, marker in leg_markers.items():
    for tee in ("sev", "sev-es", "sev-snp"):
      # "RK [sev-snp]" parses to "RK (sev-snp)", and a VM leg carrying both a
      # networking mode and a TEE to "VM (vhost-net, sev-snp)".
      key = f"{leg[:-1]}, {tee})" if leg.endswith(")") else f"{leg} ({tee})"
      env_markers[key] = (marker, "none")
  protocol_styles = {
      "Plaintext": ("-", "tab:blue"),
      "Noise": ("--", "tab:orange"),
      "TLS (rustls)": (":", "tab:green"),
  }
  styles = {
      f"{protocol} {env}": (f"{marker}{line}", colour, fill)
      for protocol, (line, colour) in protocol_styles.items()
      for env, (marker, fill) in env_markers.items()
  }

  # A series the table shows but the plot has no style for would otherwise just
  # vanish from the graph.
  unstyled = sorted(set(graph_data) - set(styles))
  if unstyled:
    raise ValueError(f"no plot style for: {', '.join(unstyled)}")

  plot_count = 0
  for label, style_color in styles.items():
    if label in graph_data and graph_data[label]["sizes"]:
      sizes = graph_data[label]["sizes"]
      thrpt = graph_data[label]["thrpt"]
      style, color, fill = style_color
      plt.plot(sizes, thrpt, style, label=label, color=color, fillstyle=fill)
      plot_count += 1

  if plot_count == 0:
    print("Warning: No valid data found to plot.")
    return

  # Formatting
  plt.xscale("log")
  plt.yscale("log")
  plt.xlabel("Message Size (Bytes)")
  plt.ylabel("Throughput (MiB/s)")
  plt.title("Crypto Channel Throughput vs Message Size")
  plt.grid(True, which="both", ls="--")
  plt.legend()

  # Save
  plt.savefig(output_image)
  print(f"\nGraph saved to {output_image}")


def main():
  parser = argparse.ArgumentParser(
      description="Process Criterion benchmark logs and generate plots."
  )
  parser.add_argument("log_file", help="Path to the benchmark log file")
  parser.add_argument(
      "--output-image",
      default="throughput_graph.png",
      help="Output path for the plot image",
  )

  args = parser.parse_args()

  results = parse_log(args.log_file)

  if results:
    print_markdown_table(results)
    generate_plot(results, args.output_image)
  else:
    print("No results parsed. Please check the log file format.")


if __name__ == "__main__":
  main()
