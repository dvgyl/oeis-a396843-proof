#!/usr/bin/env python3
"""Package the final individually organized OEIS proof collection.

The archive deliberately omits downloaded dependency caches and compiler
binaries. Run the formal checker before packaging. SHA256SUMS covers every
payload file except itself; ZIP CRCs and the embedded hashes are rechecked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import zipfile

from check_formalization import source_snapshot
from verify_final_collection import read_collection, validate_manuscripts, validate_preservation


EXCLUDED_PARTS = {".lake", ".git", "__pycache__", ".pytest_cache"}
EXCLUDED_SUFFIXES = {".pyc", ".aux", ".out", ".synctex", ".fls", ".fdb_latexmk"}
RETAINED_ARCHIVES = {
    "prior_work/oeis_congruence_proofs_Dev_Goyal_v1.zip",
    "prior_work/oeis_proofs_complete_Dev_Goyal_v2.zip",
    "prior_work/oeis_proofs_complete_Dev_Goyal_v3.zip",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def payload(root: Path) -> list[Path]:
    result = []
    for path in root.rglob("*"):
        rel = path.relative_to(root)
        if any(part in EXCLUDED_PARTS for part in rel.parts):
            continue
        if path.is_symlink():
            raise ValueError(f"Unexpected symlink in release payload: {rel}")
        if not path.is_file() or path.suffix in EXCLUDED_SUFFIXES:
            continue
        if "reproducibility" in rel.parts and path.suffix.lower() in {".pdf", ".png", ".jpg", ".jpeg"}:
            continue  # Render/build copies are temporary; final papers are in manuscripts/.
        if path.name == "SHA256SUMS" or (path.suffix == ".zip" and rel.as_posix() not in RETAINED_ARCHIVES):
            continue
        result.append(path)
    return sorted(result)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.repo.resolve()
    archive = (args.output or root.parent / "OEIS_Final_Collection_Dev_Goyal.zip").resolve()
    if archive.is_relative_to(root):
        raise ValueError("Write the archive outside its own payload directory")
    entries, entry_names = read_collection(root)
    validate_preservation(root)
    manuscript_checks = validate_manuscripts(root)
    final_directory = root / "reproducibility/final_collection"
    final_report = json.loads((final_directory / "report.json").read_text())
    if final_report.get("status") != "final_collection_verified":
        raise ValueError("The final collection verification has not passed")
    if final_report.get("entry_theorems") != entry_names:
        raise ValueError("The verified entry-theorem list does not match the catalogue")
    if final_report.get("entry_count") != len(entries):
        raise ValueError("The verified entry count does not match the catalogue")
    if final_report.get("manuscript_quality_checks") != manuscript_checks:
        raise ValueError("The verified manuscript checks do not match the final papers")
    if final_report.get("catalogue_sha256") != digest(root / "catalogue/entries.json"):
        raise ValueError("The catalogue changed after verification")
    if final_report.get("sources_before") != final_report.get("sources_after"):
        raise ValueError("Final source snapshots disagree")
    if final_report.get("sources_after") != source_snapshot(root, final_directory):
        raise ValueError("Final payload sources changed after verification")
    for command in final_report.get("commands", []):
        if command["exit_code"] != 0 or digest(final_directory / command["log"]) != command["log_sha256"]:
            raise ValueError("A final verification command or log does not match")
    if final_report.get("complete_report_sha256") != digest(root / "reproducibility/lean_complete/report.json"):
        raise ValueError("The full mathematical verification report changed")
    report = json.loads((root / "reproducibility/lean_complete/report.json").read_text())
    if report.get("status") != "mechanical_checks_passed":
        raise ValueError("The formal verification report does not record a successful run")
    before = report.get("sources_before")
    after = report.get("sources_after")
    if not before or before != after:
        raise ValueError("Missing or unequal source snapshots in the verification report")
    for rel, expected in after.items():
        if digest(root / rel) != expected:
            raise ValueError(f"Source changed after formal validation: {rel}")
    for command in report.get("commands", []):
        if command["exit_code"] != 0:
            raise ValueError("Verification command failed")
        log = root / "reproducibility/lean_complete" / command["log"]
        if digest(log) != command["log_sha256"]:
            raise ValueError(f"Verification log changed: {log.name}")
    for filename, expected in report.get("numeric_evidence", {}).items():
        evidence = root / "reproducibility/lean_complete" / filename
        if digest(evidence) != expected:
            raise ValueError(f"Numerical evidence changed: {filename}")
    forced = report.get("forced_source_reelaboration", [])
    expected_sources = {
        str(path.relative_to(root / "lean"))
        for path in (root / "lean").rglob("*.lean")
        if ".lake" not in path.relative_to(root / "lean").parts
        and path.relative_to(root / "lean").as_posix() != "ContractChecks.lean"
    }
    actual_sources = [entry["source"] for entry in forced]
    if (len(actual_sources) != len(set(actual_sources)) or
            set(actual_sources) != expected_sources or
            report.get("forced_source_module_count") != len(expected_sources)):
        raise ValueError("Missing or duplicate forced first-party source-compilation records")
    for entry in forced:
        if not entry.get("new_object_created") or \
                digest(root / "lean" / entry["source"]) != entry["source_sha256"]:
            raise ValueError("A forced source-compilation record does not match the release")
    files = payload(root)
    expected_hashes = {path: digest(path) for path in files}
    for path, expected in expected_hashes.items():
        relative = path.relative_to(root).as_posix()
        if relative in after and expected != after[relative]:
            raise ValueError(f"A source changed while preparing the archive: {relative}")
    sums = "".join(f"{expected_hashes[path]}  {path.relative_to(root).as_posix()}\n" for path in files)
    checksum_file = root / "SHA256SUMS"
    checksum_file.write_text(sums)
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as out:
        for path in [*files, checksum_file]:
            name = f"{root.name}/{path.relative_to(root).as_posix()}"
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 24, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = (0o100644 << 16)
            out.writestr(info, path.read_bytes())
    with zipfile.ZipFile(archive) as check:
        bad = check.testzip()
        if bad is not None:
            raise ValueError(f"Archive CRC failed: {bad}")
        if check.read(f"{root.name}/SHA256SUMS").decode() != sums:
            raise ValueError("The archived checksum file differs from the fixed payload hashes")
        for path in files:
            name = f"{root.name}/{path.relative_to(root).as_posix()}"
            actual = hashlib.sha256(check.read(name)).hexdigest()
            if actual != expected_hashes[path]:
                raise ValueError(f"Archive payload mismatch: {name}")
    if final_report.get("sources_after") != source_snapshot(root, final_directory):
        raise ValueError("First-party sources changed while the archive was created")
    print(json.dumps({
        "status": "archive_verified",
        "archive": str(archive),
        "files": len(files) + 1,
        "bytes": archive.stat().st_size,
        "sha256": digest(archive),
        "formal_source_hashes_verified": len(after),
        "separate_oeis_manuscripts": len(entries),
        "separate_lean_interfaces": len(entries),
        "original_endpoints": report["endpoint_count"],
        "entry_interface_theorems": len(entry_names),
    }, indent=2))


if __name__ == "__main__":
    main()
