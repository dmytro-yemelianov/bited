"""Shared release identities; Rust and Lean always ship at the same version."""
import re
import tomllib


def package_metadata(root):
    rust = tomllib.loads((root / "Cargo.toml").read_text())["package"]
    lean = tomllib.loads((root / "lakefile.toml").read_text())
    if rust["name"] != "bitet" or lean["name"] != "bitet":
        raise SystemExit("Rust and Lean package names must both be bitet")
    version = rust["version"]
    if lean["version"] != version:
        raise SystemExit("Rust and Lean release versions differ")
    if not re.fullmatch(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(?:-[0-9A-Za-z.-]+)?", version):
        raise SystemExit("Unsupported release version")
    return {"name": rust["name"], "version": version,
            "stem": f"bitet-{version}", "lean_stem": f"bitet-lean-{version}",
            "tag": f"v{version}", "repository": rust.get("repository")}
