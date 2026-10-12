# Preparing and publishing bited releases

Rust and Lean ship together. The initial version is 0.1.0. For each later release,
update `Cargo.toml` and `lakefile.toml` to the same version, update all three Cargo
lockfiles without unrelated dependency upgrades, add a changelog entry and
`docs/releases/<version>.md`, and regenerate the Rust model when its inputs change.
The shared release metadata check rejects mismatched package names or versions.

## Preparation

1. Run formatting, lint, API docs, examples and the full verification workflow.
2. Commit all release inputs. A release archive must point to a clean source commit.
3. Run the strict gate and prepare the release:

```sh
AENEAS_HOME=/absolute/path/to/pinned/aeneas ./scripts/verify
./scripts/prepare-release
```

The gate includes all eighteen proof obligations, source re-extraction, transitive
axiom audit, fresh stored-proof replay, host/WASI tests, RISC-V compilation,
200,000 seeded ASan fuzz executions, benchmarks and fresh archived-package checks.
The preparation command checks every recorded source/evidence/archive digest,
requires the current clean Git commit, runs Cargo publication dry-run, and creates
an immutable local bundle under `target/releases/`. Its directory includes a
verification digest, allowing distinct verified candidates without overwriting.
Re-running preparation validates and reuses an identical bundle. Cargo publication
dry-run reads registry metadata over the network but aborts before uploading. The
verification workflow builds Rust with locked offline dependencies.

The bundle contains the Rust crate, Lean source archive, evidence archive,
verification JSON, release notes, changelog, dry-run log and SHA256SUMS. Check it:

```sh
cd target/releases/<prepared-bundle>
shasum -a 256 -c SHA256SUMS
```

`release.json` records the package version, suggested Git tag, source commit,
repository URL and publication status. Preparation never uploads files or creates
tags. Repository metadata must point to the actual public project before publishing.

## Publication

Publish the exact verified source commit under `v<version>`, attach the prepared
assets to its public release, and upload the Rust package with `cargo publish
--locked`. Registry authentication stays outside repository files. Record the public
repository/tag, crate version and asset checksums after successful publication.
Use the chosen release bundle's source commit; changing any source/metadata after
verification requires a new strict gate and bundle.

Cargo versions are immutable; publication is a separate explicit action. See the
[Cargo publishing guide](https://doc.rust-lang.org/cargo/reference/publishing.html).

## Compatibility and CI

The portable workflow runs on the repository-scoped `bited-ci-x64` self-hosted
runner on `raps-ci`, using the `self-hosted`, `Linux`, and `X64` labels. Rust 1.88.0
is installed by a commit-pinned action. Cargo and rustup state live beside the
checkout, isolated from other runner instances. Jobs have a 20-minute timeout;
a newer run on the same ref cancels the previous one.

The host runs `/home/runner/bited-runner` under the persistent user service
`bited-runner.service`. Inspect it with `systemctl --user status bited-runner`
and `journalctl --user -u bited-runner`; user lingering keeps it running after
SSH logout and across host reboots. Runner credentials remain on the host.

During 0.x development, an incompatible API, decoding-policy, error-precedence or
consumption-contract change requires a minor version increment. Patch releases keep
those contracts. Performance changes retain source correspondence and explicitly
report distribution/code-size tradeoffs. Shortest base-128 length and runtime speed
remain separate claims.

GitHub Actions runs portable Rust/MSRV checks, examples, documentation and no_std
target compilation. It does not claim full formal release verification or WASI
execution. The full gate currently uses pinned tools on the documented Apple ARM
profile; other machines need their own recorded executable verification profile.
