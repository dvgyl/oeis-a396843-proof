#!/usr/bin/env python3
"""Verify every per-entry paper/interface and rerun the complete Lean audit.

This is the consolidation gate. The unchanged mathematical checker still
checks all 339 original endpoints and freshly elaborates every first-party
module, including the new per-entry interfaces. This script additionally
checks the fixed 34-entry inventory, preservation of all 66 v4 Lean files,
paired manuscripts, and every new interface's full type and transitive axioms.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from audit_axioms import AuditError, audit_text
from check_formalization import DIAGNOSTIC, FINAL_NAMES, source_snapshot


EXPECTED_IDS = frozenset("""
A052895 A064618 A080253 A167137 A195194 A305550 A306082 A354242
A378580 A378581 A380056 A380060 A380680 A389474 A389475 A389536
A389537 A389542 A392210 A393171 A393172 A393856 A393857 A393858
A393859 A396093 A396099 A396102 A396797 A396798 A396807 A396843
A396844 A397588
""".split())
BASELINE_SHA256 = "18f002efa5f66a8283e3dcb2309fd457575c94830a2bc4408ff4ba2dfefc9a4c"
EXPECTED_INTERFACE_THEOREM_COUNT = 262
EXPECTED_INTERFACE_NAMES_SHA256 = "b905776e3639174bfa54a1fca9df0181f4ea37a5166b3e0d85d8fee812e01031"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_collection(root: Path) -> tuple[list[dict], list[str]]:
    document = json.loads((root / "catalogue/entries.json").read_text())
    entries = document["entries"]
    ids = [item["oeis_id"] for item in entries]
    if len(ids) != len(EXPECTED_IDS) or set(ids) != EXPECTED_IDS:
        raise AuditError("The final collection must retain all 34 distinct named entries.")
    if ids != sorted(ids):
        raise AuditError("The entry catalogue must be sorted by OEIS identifier.")
    all_names = []
    for entry in entries:
        oeis_id = entry["oeis_id"]
        expected_paths = {
            "manuscript_pdf": f"manuscripts/{oeis_id}.pdf",
            "manuscript_tex": f"manuscripts/{oeis_id}.tex",
            "lean_file": f"lean/Entries/{oeis_id}.lean",
        }
        for key, expected in expected_paths.items():
            if entry.get(key) != expected:
                raise AuditError(f"Unexpected {key} path for {oeis_id}.")
            path = root / expected
            if not path.is_file() or path.is_symlink():
                raise AuditError(f"Missing regular deliverable: {expected}.")
        tex = (root / entry["manuscript_tex"]).read_text()
        if "\\begin{document}" not in tex or "\\end{document}" not in tex:
            raise AuditError(f"The manuscript for {oeis_id} is not a complete TeX document.")
        if re.search(r"\\(?:input|include)\s*\{", tex):
            raise AuditError(f"The manuscript for {oeis_id} has a project-local TeX dependency.")
        if "ChatGPT" not in tex or "Dev Goyal" not in tex:
            raise AuditError(f"The manuscript for {oeis_id} omits authorship or AI disclosure.")
        if not (root / entry["manuscript_pdf"]).read_bytes().startswith(b"%PDF-"):
            raise AuditError(f"Invalid PDF header for {oeis_id}.")
        if not entry.get("original_endpoints") or not entry.get("new_endpoints"):
            raise AuditError(f"The proof map for {oeis_id} is empty.")
        if not set(entry["original_endpoints"]) <= set(FINAL_NAMES):
            raise AuditError(f"The proof map for {oeis_id} names an unaudited original endpoint.")
        lean_text = (root / entry["lean_file"]).read_text()
        namespace = f"FinalCollection.{oeis_id}"
        if f"namespace {namespace}" not in lean_text:
            raise AuditError(f"The interface namespace for {oeis_id} is missing.")
        for name in entry["new_endpoints"]:
            if not name.startswith(namespace + "."):
                raise AuditError(f"Unexpected interface theorem namespace: {name}.")
            short_name = name.removeprefix(namespace + ".")
            if not re.search(r"\btheorem\s+" + re.escape(short_name) + r"(?:\s|\()", lean_text):
                raise AuditError(f"Advertised theorem is not declared in its entry file: {name}.")
        all_names.extend(entry["new_endpoints"])
    if len(all_names) != len(set(all_names)):
        raise AuditError("Duplicate per-entry theorem names in the catalogue.")
    name_hash = hashlib.sha256(("\n".join(all_names) + "\n").encode()).hexdigest()
    if len(all_names) != EXPECTED_INTERFACE_THEOREM_COUNT or name_hash != EXPECTED_INTERFACE_NAMES_SHA256:
        raise AuditError("The final catalogue must retain every reviewed per-entry theorem in order.")
    return entries, all_names


def validate_manuscripts(root: Path) -> dict:
    path = root / "validation/manuscript_checks.json"
    checks = json.loads(path.read_text())
    if checks.get("status") != "all_individual_manuscripts_checked":
        raise AuditError("The manuscript validation record is incomplete.")
    entries = checks["entries"]
    ids = [entry["oeis_id"] for entry in entries]
    if len(ids) != 34 or set(ids) != EXPECTED_IDS:
        raise AuditError("The manuscript record does not cover all 34 entries.")
    for entry in entries:
        if not entry.get("all_final_pages_visually_inspected") or entry.get("pages", 0) < 1:
            raise AuditError(f"Missing page review: {entry['oeis_id']}.")
        if entry.get("out_of_page_words") != 0 or not entry.get("source_id_and_disclosure_present"):
            raise AuditError(f"Failed manuscript checks: {entry['oeis_id']}.")
        for kind, suffix in (("pdf", ".pdf"), ("tex", ".tex")):
            if digest(root / "manuscripts" / (entry["oeis_id"] + suffix)) != entry[kind + "_sha256"]:
                raise AuditError(f"The reviewed manuscript changed: {entry['oeis_id']} {kind}.")
    reviewed_sources = checks.get("semantic_reviewed_files", {})
    expected_reviewed_sources = {
        path for oeis_id in EXPECTED_IDS
        for path in (f"manuscripts/{oeis_id}.tex", f"lean/Entries/{oeis_id}.lean")
    }
    if not isinstance(reviewed_sources, dict) or set(reviewed_sources) != expected_reviewed_sources:
        raise AuditError("The semantic review must bind all 68 manuscript and Lean interface source hashes.")
    for relative, expected in reviewed_sources.items():
        if digest(root / relative) != expected:
            raise AuditError(f"A source changed after semantic review: {relative}.")
    expected_records = {
        "group_quality_reports": {
            f"reproducibility/final_collection/{group}_pdf_qa.json"
            for group in ("original", "second", "recent")
        },
        "semantic_review_reports": {
            "reproducibility/final_collection/second_review_of_original.md",
            "reproducibility/final_collection/recent_review_of_second.md",
            "reproducibility/final_collection/original_review_of_recent.md",
        },
    }
    for field, required_paths in expected_records.items():
        records = checks.get(field, {})
        if set(records) != required_paths:
            raise AuditError(f"The manuscript record is missing a required {field} file.")
        for relative, expected in records.items():
            if digest(root / relative) != expected:
                raise AuditError(f"A manuscript review record changed: {relative}.")
    return {"record_sha256": digest(path), "manuscript_count": len(entries),
            "total_pages": sum(entry["pages"] for entry in entries)}


def validate_preservation(root: Path) -> dict:
    path = root / "validation/consolidation_baseline.json"
    if digest(path) != BASELINE_SHA256:
        raise AuditError("The fixed v4 source-preservation manifest changed.")
    baseline = json.loads(path.read_text())
    sources = baseline["preserved_lean_sources"]
    if len(sources) != 66:
        raise AuditError("The baseline must contain all 66 v4 Lean source files.")
    for relative, expected in sources.items():
        if digest(root / relative) != expected:
            raise AuditError(f"A preserved formal proof was changed: {relative}.")
    return {
        "baseline_sha256": BASELINE_SHA256,
        "v4_archive_sha256": baseline["archive_sha256"],
        "original_lean_files_preserved": len(sources),
        "original_endpoints_retained": len(FINAL_NAMES),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    root = args.repo.resolve()
    project = root / "lean"
    output = root / "reproducibility/final_collection"
    output.mkdir(parents=True, exist_ok=True)
    report = {"status": "failed", "commands": [], "scope": "Final 34-entry consolidation"}

    def run(command: list[str], log_name: str, env: dict, cwd: Path = project) -> str:
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = output / log_name
        log.write_text(result.stdout)
        report["commands"].append({
            "command": command, "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": log_name, "log_sha256": digest(log),
        })
        if result.returncode or DIAGNOSTIC.search(result.stdout):
            raise AuditError(f"Verification failed; see {log}.")
        return result.stdout

    try:
        entries, names = read_collection(root)
        report["preservation"] = validate_preservation(root)
        report["manuscript_quality_checks"] = validate_manuscripts(root)
        report["entry_count"] = len(entries)
        report["original_endpoint_count"] = len(FINAL_NAMES)
        report["entry_theorem_count"] = len(names)
        report["entry_theorems"] = names
        report["catalogue_sha256"] = digest(root / "catalogue/entries.json")
        report["sources_before"] = source_snapshot(root, output)
        lake = shutil.which(args.lake)
        if lake is None:
            raise AuditError("Lake is unavailable; use the pinned toolchain or --lake.")
        lake = str(Path(lake).absolute())
        env = os.environ.copy()
        env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        print("Rebuilding all original proofs and every per-entry source...", flush=True)
        run([sys.executable, str(root / "scripts/check_formalization.py"),
             "--repo", str(root), "--lake", lake], "complete_check.log", env, root)
        core_path = root / "reproducibility/lean_complete/report.json"
        core = json.loads(core_path.read_text())
        if core.get("status") != "mechanical_checks_passed" or core.get("endpoint_count") != 339:
            raise AuditError("The complete mathematical proof audit did not pass.")
        report["complete_report_sha256"] = digest(core_path)
        report["forced_source_module_count"] = core["forced_source_module_count"]
        report["numerical_suite_count"] = len(core["numeric_evidence"])
        # This additional Lake target ensures the separately named entry files
        # can also be imported normally after 'lake build Entries'. The main
        # mathematical audit already forced fresh source elaboration of them.
        print("Building the named entry library and auditing its theorem interfaces...", flush=True)
        run([lake, "build", "Entries"], "entries_build.log", env)
        isolated = core["isolated_compiler"]
        fresh_env = env.copy()
        fresh_env["LEAN_PATH"] = isolated["effective_lean_path"]
        lean = isolated["executable"]
        prefix = "import Entries\n\n"
        types_file = output / "EntryTypes.lean"
        types_file.write_text(prefix + "set_option pp.all true\n\n" +
                              "\n".join("#check " + name for name in names) + "\n")
        run([lean, str(types_file)], "entry_types.log", fresh_env)
        audit_file = output / "EntryAxioms.lean"
        audit_file.write_text(prefix + "\n".join("#print axioms " + name for name in names) + "\n")
        text = run([lean, str(audit_file)], "entry_axioms.log", fresh_env)
        report["entry_axiom_dependencies"] = audit_text(text, names)
        report["generated_types_sha256"] = digest(types_file)
        report["generated_axiom_audit_sha256"] = digest(audit_file)
        report["deliverables"] = {
            item["oeis_id"]: {
                key: {"path": item[key], "sha256": digest(root / item[key])}
                for key in ("manuscript_pdf", "manuscript_tex", "lean_file")
            }
            for item in entries
        }
        report["sources_after"] = source_snapshot(root, output)
        if report["sources_before"] != report["sources_after"]:
            raise AuditError("The final collection changed during verification.")
        if core["sources_after"] != report["sources_after"]:
            raise AuditError("Final and core verification did not check identical sources.")
        read_collection(root)
        validate_preservation(root)
        validate_manuscripts(root)
        report["status"] = "final_collection_verified"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["failure"] = str(error)
    report["completed_utc"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in (
        "status", "entry_count", "original_endpoint_count", "entry_theorem_count",
        "forced_source_module_count", "failure") if k in report}, indent=2))
    return 0 if report["status"] == "final_collection_verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
