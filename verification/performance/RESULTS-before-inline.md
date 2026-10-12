# Measured comparison — Apple M5

This is a shared-host measurement, not an idle-machine performance ranking. Other heavy tasks ran concurrently. CPU time excludes descheduling but not frequency/cache/core effects. Both timing channels and all 15 samples are retained in `results.json`.

Production source and its formal proof package were not changed. The earlier release manifest still describes its original source snapshot.

## Selected results

CPU nanoseconds/value, mean ± approximate 95% half-width; smaller is faster. Wall time is separately recorded in the raw report.

| Dataset | Operation | Our library | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|
| length-1 | encode | 2.39 ± 0.15 | 2.62 ± 0.11 | 1.62 ± 0.06 |
| length-1 | decode | 3.07 ± 0.58 | 6.59 ± 0.05 | 3.14 ± 0.68 |
| short-80-15-5 | encode | 2.79 ± 0.19 | 4.03 ± 0.14 | 1.80 ± 0.09 |
| short-80-15-5 | decode | 6.13 ± 0.09 | 6.80 ± 0.20 | 6.14 ± 0.09 |
| full-width | encode | 11.66 ± 0.46 | 23.30 ± 0.59 | 7.48 ± 0.40 |
| full-width | decode | 10.70 ± 0.20 | 10.84 ± 0.38 | 11.30 ± 0.30 |
| large-full-width | encode | 10.05 ± 0.17 | 19.85 ± 0.50 | 6.64 ± 0.24 |
| large-full-width | decode | 9.98 ± 0.52 | 10.41 ± 0.66 | 10.34 ± 0.59 |

Our encoding was about 1.5–1.6× slower than integer-encoding on the mixed/full-width datasets in this run. Full-width encoding took about half leb128’s CPU time. Decoding intervals often overlap, so this run does not establish a reliable decoding winner.

## Correctness and contract

All 6,979,584 pre-timing implementation/value checks passed: identical canonical bytes and identical decoded values/consumption. These include 2,326,528 dataset entries, each checked with all three implementations; entries are not all unique.

Both external decoders accept redundant zero `[0x80, 0]`; ours rejects it under Canonical and reports it as noncanonical under BoundedNonCanonical. All reject the tested truncation/overflow cases, with different error reporting. On eleven continuation bytes ours consumes ten then reports TooLong; leb128 consumes eleven and reports EOF. All prefix APIs accept `[0, 1]` as zero with one byte consumed; trailing-byte rejection belongs to our separate exact API.

This is a comparison of shared valid-input public APIs with different validation contracts. It is not evidence that permissive decoding is defective. Existing Lean proofs and the 351 conformance cases provide our library’s broader contract evidence.

## Profiles

- encode / full-width: `verified_varint::encode::encode_u64_into::hdff5795c1189421d` is the leaf in 91.0% of main-thread samples.
- decode / full-width: `verified_varint::decode::decode_u64::h59260388cb403ad9` is the leaf in 93.3% of main-thread samples.
- decode / short-80-15-5: `verified_varint::decode::decode_u64::h59260388cb403ad9` is the leaf in 67.2% of main-thread samples.

The profiles locate hot codec functions. Source/disassembly inspection shows our public decoder remains a separate call while competitor adapters can inline. Call/return, result handling, bounds and canonical checks are candidates for controlled experiments; samples do not prove their individual cost or branch-miss rates. Optimizing them requires new benchmarks and renewed proof/release validation.

## Reproduce

Run `./scripts/compare-performance` on an idle macOS host with the pinned Rust toolchain. See README.md for settings and scope. These timings cover u64 wire operations; native signed-wrapper, u32, incremental and malformed-input throughput comparisons remain outside this run.
