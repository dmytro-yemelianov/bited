#!/usr/bin/env python3
"""Render article figures from recorded results; requires matplotlib."""
import json
import re
from pathlib import Path
from xml.sax.saxutils import quoteattr

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "docs/articles/assets"
OUT.mkdir(parents=True, exist_ok=True)
report = json.loads((ROOT / "verification/performance/results.json").read_text())


def portable_svg(path):
    """Use SVG presentation attributes so standalone charts need no inline CSS."""
    svg = path.read_text()
    svg = re.sub(r"<style\b[^>]*>.*?</style>", "", svg, flags=re.S)

    def attributes(match):
        declarations = [item.split(":", 1) for item in match[1].split(";") if item.strip()]
        return " ".join(f"{key.strip()}={quoteattr(value.strip())}" for key, value in declarations)

    svg = re.sub(r'style="([^"]*)"', attributes, svg)
    svg = svg.replace("<svg ", '<svg stroke-linejoin="round" stroke-linecap="butt" ', 1)
    path.write_text(svg)

rows = {(r["dataset"], r["implementation"]): r for r in report["results"] if r["operation"] == "encode"}
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11, "svg.fonttype": "none"})
colors = ["#087f8c", "#627185", "#c05621", "#7952b3"]
datasets = ["length-1", "short-80-15-5", "full-width", "large-full-width"]
labels = ["One-byte", "Short 80/15/5", "Full-width", "Large full-width"]
fig, ax = plt.subplots(figsize=(11, 5.7), layout="constrained")
fig.get_layout_engine().set(rect=(0, .065, 1, .935))
for i, (impl, label) in enumerate(zip(["Verified", "Previous", "Leb128", "IntegerEncoding"], ["bited", "Previous", "leb128 0.2.5", "integer-encoding 4.1.0"])):
    data = [rows[d, impl] for d in datasets]
    means = np.array([r["mean_thread_cpu_ns_per_value"] for r in data])
    limits = np.array([r["thread_cpu_approx_95_percent_interval_ns"] for r in data])
    ax.barh(np.arange(4) + (i-1.5)*.19, means, height=.18, color=colors[i], label=label,
            xerr=np.array([means-limits[:, 0], limits[:, 1]-means]), capsize=2)
ax.set_yticks(range(4), labels)
ax.invert_yaxis()
ax.set_xlabel("Thread CPU nanoseconds / value · lower is faster")
ax.set_title("Encoding u64: recorded comparison on Apple M5", loc="left", fontweight="bold")
ax.legend(loc="upper right")
ax.grid(axis="x", alpha=.2)
ax.set_axisbelow(True)
fig.text(.01, .005, "Rust 1.88 · 15 rotating repetitions · approximate 95% intervals · 12 Oct 2026", fontsize=9)
for suffix in ["svg", "png"]:
    fig.savefig(OUT / f"encode-comparison.{suffix}", dpi=170)
portable_svg(OUT / "encode-comparison.svg")
plt.close(fig)

s_old = rows["length-1", "Previous"]["mean_thread_cpu_ns_per_value"]
s_new = rows["length-1", "Verified"]["mean_thread_cpu_ns_per_value"]
l_old = rows["full-width", "Previous"]["mean_thread_cpu_ns_per_value"]
l_new = rows["full-width", "Verified"]["mean_thread_cpu_ns_per_value"]
cross = (l_old-l_new) / ((s_new-s_old)+(l_old-l_new))
fig, axes = plt.subplots(1, 2, figsize=(11, 4.8), layout="constrained")
fig.get_layout_engine().set(rect=(0, .065, 1, .935))
for ax, low in zip(axes, [0, .97]):
    p = np.linspace(low, 1, 400)
    for short, long, label, color in [(s_new, l_new, "bited", colors[0]), (s_old, l_old, "Previous", colors[1])]:
        ax.plot(p*100, p*short+(1-p)*long, label=label, color=color, linewidth=2.5)
    ax.axvline(cross*100, color="#c05621", linestyle="--", linewidth=1)
    ax.set_xlabel("One-byte share (%)")
    ax.set_ylabel("Modeled thread CPU ns / value")
    ax.grid(alpha=.2)
    ax.legend()
axes[0].set_title("Two-population weighted mean", loc="left")
axes[1].set_title(f"Crossover: {cross*100:.2f}% one-byte", loc="left")
fig.suptitle("Weight time per value, not percentage speedups", fontweight="bold")
fig.text(.01, .005, "Remaining inputs follow the measured full-width distribution; point estimates, not a confidence bound.", fontsize=9)
for suffix in ["svg", "png"]:
    fig.savefig(OUT / f"weighted-crossover.{suffix}", dpi=170)
portable_svg(OUT / "weighted-crossover.svg")
print(f"Crossover: {cross:.8%}; short/long ratio: {cross/(1-cross):.2f}")
