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


def parse_log(log_file):
  """Parse Criterion log file and extract time and throughput."""
  # Regex patterns
  bench_pattern = re.compile(
      r"Benchmarking (RK|Local TCP|VM TCP) (Plaintext|Noise|BoringSSL) Message"
      r" Exchange/(\d+)"
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
        env, protocol, size = bench_match.groups()
        current_env = env.replace(" TCP", "")
        current_protocol = protocol
        current_size = int(size)
        key = (current_env, current_protocol, current_size)
        if key not in results:
          results[key] = {}
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
        except IndexError:
          pass

  return results


def print_markdown_table(results):
  """Print results as a Markdown table."""
  print("\n## Performance Benchmark Results\n")
  print(
      "| Protocol | Environment | Size (Bytes) | Time (Mean) | Throughput"
      " (Mean) |"
  )
  print("| :--- | :--- | ---: | ---: | ---: |")

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

    print(f"| {p_str} | {e_str} | {size:,} | {time_str} | {thrpt_str} |")

    current_p = protocol
    current_e = env


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

  # Define styles for consistency
  styles = {
      "Plaintext Local": ("o-", "tab:blue"),
      "Plaintext VM": ("s-", "tab:blue"),
      "Plaintext RK": ("^-", "tab:blue"),
      "Noise Local": ("o--", "tab:orange"),
      "Noise VM": ("s--", "tab:orange"),
      "Noise RK": ("^--", "tab:orange"),
      "BoringSSL Local": ("o:", "tab:green"),
      "BoringSSL VM": ("s:", "tab:green"),
  }

  plot_count = 0
  for label, style_color in styles.items():
    if label in graph_data and graph_data[label]["sizes"]:
      sizes = graph_data[label]["sizes"]
      thrpt = graph_data[label]["thrpt"]
      style, color = style_color
      plt.plot(sizes, thrpt, style, label=label, color=color)
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
