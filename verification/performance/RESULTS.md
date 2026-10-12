# Bounded-capacity encoder specialization

Measured 2026-10-12T09:57:46.829324+00:00 on Apple M5, Rust 1.88, one thread, optimization 3, overflow checks enabled, no LTO. Fifteen rotating matched repetitions compare the production encoder with the verified pre-specialization source at `0fdaadf304e6e53ad38942b2ca820c14b8ab771d`. The complete slice is opaque; the library itself checks capacity and exposes a ten-byte subview.

## CPU time per value

Mean thread CPU ns/value ± approximate 95% half-width. Raw CPU/wall samples and source/binary metadata are in results.json.

| Dataset | Operation | Current | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.466 ± 0.116 | 1.561 ± 0.089 | 2.531 ± 0.124 | 1.492 ± 0.104 |
| length-1 | decode | 3.091 ± 0.427 | 5.651 ± 0.058 | 6.457 ± 0.077 | 2.950 ± 0.548 |
| short-80-15-5 | encode | 1.576 ± 0.094 | 1.559 ± 0.102 | 3.411 ± 0.198 | 1.652 ± 0.114 |
| short-80-15-5 | decode | 5.673 ± 0.119 | 5.781 ± 0.127 | 6.433 ± 0.120 | 5.845 ± 0.127 |
| full-width | encode | 3.536 ± 0.332 | 7.072 ± 0.354 | 20.444 ± 1.161 | 6.491 ± 0.297 |
| full-width | decode | 9.563 ± 0.149 | 9.376 ± 0.130 | 9.037 ± 0.200 | 9.712 ± 0.210 |
| large-full-width | encode | 4.747 ± 0.274 | 7.864 ± 0.446 | 22.054 ± 0.920 | 6.998 ± 0.347 |
| large-full-width | decode | 9.514 ± 0.362 | 9.377 ± 0.283 | 9.798 ± 0.430 | 9.672 ± 0.449 |

## Paired encoder change

Mean reduction versus Previous, pairing fifteen repetitions; approximate t(14) intervals:

- length-1: +5.4% reduction [-3.4%, +14.2%].

- short-80-15-5: -2.2% reduction [-10.1%, +5.7%].

- full-width: +50.0% reduction [+46.2%, +53.8%].

- large-full-width: +39.2% reduction [+35.2%, +43.3%].

## Scope and tradeoff

Full-width encoding is about twice as fast in this matched executable. Large traversal improves by about 39%. The short-mixture interval crosses zero; this run does not establish a short-mixture benefit or regression. Short-input costs remain part of the tradeoff rather than a reason to discard the long-input benefit. The historical capacity controls demonstrated one-byte slowdowns of a few percent, but their local adapters/code layout differ from this actual library comparison.

The binary checks canonical bytes, decoded values and consumption counts before timing and captures twelve statistical stack profiles. Shared-host CPU time excludes descheduling but not migration, frequency or cache contention. Decode source is unchanged; decode timing changes reflect optimizer/layout/noise and are not a claimed decoder improvement. No cycle, PMU, universal ranking, native signed-wrapper/u32 or other-CPU speed claim is made.

The Rust library keeps zero runtime dependencies, no_std, safe checked accesses, exact errors and full suffix/atomicity contracts. The new Lean correspondence reconstructs the caller slice after bounded-prefix mutation. Object-code sections grow from 4084/4880/3956 to 4596/5541/4644 bytes on aarch64/WASI/RISC-V; static library call-path observations remain 64/16/32 bytes. These are compiler observations, not whole-application sizes or formal stack bounds.
