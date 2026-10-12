# Reproduction from release archives

The sidecar binds the source commit, both archives, original contract inputs,
exact source/model/module/statement digests, tool and dependency locks, logical
assumptions, and test/fuzz/benchmark evidence. It is external to the archives
whose final hashes it names. Verify those hashes before unpacking.

For ordinary Rust use, unpack the `.crate` and run `cargo build --locked`.
The Lean archive is a normal Lake source package with its locked dependencies;
run `lake build` after installing its pinned Lean toolchain/dependencies.

For the combined verification workspace:

```sh
mkdir reproduction
# Substitute paths to the supplied release archives.
tar -xzf bited-0.1.0.crate --strip-components=1 -C reproduction
tar -xzf bited-lean-0.1.0.tar.gz --strip-components=1 -C reproduction
cd reproduction
cp Cargo.toml.orig Cargo.toml
# Install pinned tools/dependencies as described in README.md.
export AENEAS_HOME=/absolute/path/to/pinned/aeneas
./scripts/verify
```

Cargo normalizes its packaged manifest; `Cargo.toml.orig` retains the source
manifest. The source/model/claim checks compare the original manifest identity,
and archived Rust re-extraction separately validates the normalized package.
A combined reproduction without `.git` records a null commit identity and
source digests that can be compared with the original sidecar.

The automatic Lean reproduction check creates a fresh project directory,
unpacks the actual archive, builds all project modules, audits their exact
statements/axioms against the original inventory, and replays their stored proofs.
Only pristine dependency sources/build caches at locked Git revisions are shared.
It does not reuse project `.olean` files or describe itself as another-machine
verification. The same-kernel replay and compiler/runtime assumptions remain
explicit in the trust boundary.

All formal claims concern the documented scalar extraction configuration.
Portable host/WASI execution and RISC-V compilation are evidence for additional
configurations, not target-independent machine-code proofs. Runtime speed and
compiler stack measurements are recorded separately from formal contracts.
