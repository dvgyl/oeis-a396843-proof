#!/usr/bin/env python3
"""Build a public source ZIP from an explicit file list and check its bytes."""

import hashlib
import json
from pathlib import Path
import zipfile


ROOT_FILES = [".gitignore", "CITATION.cff", "CONTRIBUTING.md", "Makefile", "README.md"]
SOURCE_DIRS = ["docs", "lean", "manuscript", "scripts", "tests", "validation"]
EVIDENCE_FILES = [
    "reproducibility/README.md",
    "reproducibility/parser_tests.log",
    "reproducibility/verification_100.json",
    "reproducibility/manuscript/inspection.json",
    "reproducibility/manuscript/build-1.log",
    "reproducibility/manuscript/build-2.log",
]
EVIDENCE_LOGS = [
    "report.json", "toolchain.log", "clean.log", "build.log", "types.log",
    "axioms.log", "GeneratedTypes.lean", "GeneratedAxiomAudit.lean",
]
EXCLUDED_SUFFIXES = {".olean", ".ilean", ".pyc", ".o", ".a", ".so", ".dylib"}
PRIVATE_MARKERS = [("/" + "Users/").encode(), ("/" + "home/").encode(), ("." + "audit/").encode()]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    root = Path(__file__).resolve().parents[1]
    names = ROOT_FILES + EVIDENCE_FILES
    for directory in SOURCE_DIRS:
        names += [path.relative_to(root).as_posix() for path in (root / directory).rglob("*")
                  if path.is_file() and ".lake" not in path.parts
                  and "__pycache__" not in path.parts and path.suffix not in EXCLUDED_SUFFIXES]
    for mode in ("baseline", "complete"):
        names += [f"reproducibility/lean_{mode}/{name}" for name in EVIDENCE_LOGS]
    names.append("reproducibility/lean_complete/contracts.log")
    names = sorted(set(names))
    files = {}
    for name in names:
        path = root / name
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"Missing or symbolic file: {name}")
        data = path.read_bytes()
        if path.suffix in {".md", ".txt", ".json", ".log", ".py", ".lean", ".tex", ".cff", ".toml"}:
            if any(marker in data for marker in PRIVATE_MARKERS):
                raise SystemExit(f"Private path in public file: {name}")
        files[name] = data
    inventory_name = "reproducibility/delivery_manifest.json"
    inventory = {
        "scope": "SHA-256 of every ZIP file except this inventory",
        "files": {name: digest(data) for name, data in files.items()},
    }
    inventory_bytes = (json.dumps(inventory, indent=2) + "\n").encode()
    (root / inventory_name).write_bytes(inventory_bytes)
    files[inventory_name] = inventory_bytes

    destination = root / "dist"
    destination.mkdir(exist_ok=True)
    archive = destination / "oeis-a396843-proof-v1.0.0-source.zip"
    prefix = "oeis-a396843-proof/"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as output:
        for name, data in sorted(files.items()):
            item = zipfile.ZipInfo(prefix + name, date_time=(2026, 10, 22, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            output.writestr(item, data)
    with zipfile.ZipFile(archive) as output:
        if output.testzip() is not None:
            raise SystemExit("ZIP checksum check failed")
        if set(output.namelist()) != {prefix + name for name in files}:
            raise SystemExit("ZIP file list check failed")
        for name, data in files.items():
            if output.read(prefix + name) != data:
                raise SystemExit(f"ZIP byte check failed: {name}")
    result = {
        "status": "passed", "archive": archive.name,
        "sha256": digest(archive.read_bytes()), "included_files": len(files),
        "size_bytes": archive.stat().st_size,
        "checks": ["ZIP checksums", "exact file list", "all included bytes"],
    }
    (destination / (archive.name + ".sha256")).write_text(
        f"{result['sha256']}  {archive.name}\n")
    (destination / "package_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
