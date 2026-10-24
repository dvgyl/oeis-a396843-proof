#!/usr/bin/env python3
"""Rebuild Lean results, compile contracts, record types, and audit axioms.

Baseline mode checks only the existing nine foundational declarations.
Complete mode requires every agreed manuscript endpoint and ContractChecks.lean.
Success is a mechanical check, not an automatic review of mathematical meaning.
"""

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

from audit_axioms import AuditError, NAME, audit_text, required_theorems


FINAL_NAMES = ["Hanna.Acceptance." + suffix for suffix in (
    "existence_uniqueness", "compositional_inverse",
    "coefficient_polynomial_specialization", "parity_odd", "parity_even",
    "mod_parameter_squared", "binary_divisibility_polynomial",
    "inverse_binary_divisibility_polynomial", "binary_divisibility_integer",
    "inverse_binary_divisibility_integer", "power_of_two_index",
    "prime_divisibility_lower_bound", "prime_exponent_exists_unique",
    "minimum_prime_exponent_iff", "residues_parameter_three",
    "residues_parameter_four",
)]
DIAGNOSTIC = re.compile(r"\b(?:warning|error):", re.IGNORECASE)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot(repo, output):
    """Hash first-party proof, specification, manuscript, and checker sources."""
    roots = [repo / name for name in ("lean", "scripts", "tests", "validation", "docs", "manuscript")]
    included = {}
    suffixes = {".lean", ".py", ".json", ".toml", ".md", ".tex", ".pdf"}
    for root in roots:
        if not root.exists():
            continue
        for path in root.rglob("*"):
            if not path.is_file() or any(part in {".lake", ".git", "__pycache__"} for part in path.parts):
                continue
            if path.resolve().is_relative_to(output):
                continue
            if path.suffix not in suffixes and path.name != "lean-toolchain":
                continue
            if path.is_symlink():
                raise AuditError(f"First-party source must not be a symlink: {path}")
            included[str(path.relative_to(repo))] = digest(path)
    return dict(sorted(included.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["baseline", "complete"], default="complete")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute path")
    parser.add_argument("--output", type=Path, help="Directory for freshly generated evidence")
    args = parser.parse_args()
    repo = args.repo.resolve()
    project = repo / "lean"
    output = (args.output or repo / "reproducibility" / ("lean_" + args.mode)).resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {
        "mode": args.mode,
        "status": "failed",
        "commands": [],
        "scope": "Mechanical build, type-recording, and axiom checks only.",
        "semantic_review": "Required: compare typed contracts and definitions with docs/THEOREM_SPEC.md.",
    }

    def run(command, name, env):
        start = time.monotonic()
        completed = subprocess.run(
            command, cwd=project, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        log = output / name
        log.write_text(completed.stdout)
        report["commands"].append({
            "command": command, "working_directory": "lean",
            "exit_code": completed.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": name, "log_sha256": digest(log),
        })
        if completed.returncode:
            raise AuditError(f"Command failed; see {log}.")
        if DIAGNOSTIC.search(completed.stdout):
            raise AuditError(f"Compiler warning/error output is not accepted; see {log}.")
        return completed.stdout

    try:
        manifest_path = repo / "validation" / (
            "baseline_theorems.json" if args.mode == "baseline" else "final_theorems.json"
        )
        manifest = json.loads(manifest_path.read_text())
        names = required_theorems(manifest)
        if manifest.get("mode") != args.mode:
            raise AuditError("Manifest mode does not match the requested mode.")
        imports = manifest.get("imports")
        if not isinstance(imports, list) or not imports or any(
            not isinstance(name, str) or not NAME.fullmatch(name) for name in imports
        ):
            raise AuditError("Manifest imports must be explicit module identifiers.")
        if args.mode == "complete":
            if names != FINAL_NAMES:
                raise AuditError("The complete-mode manifest must retain all 16 agreed endpoints in order.")
            if imports != ["Hanna.Acceptance"]:
                raise AuditError("Complete mode must import Hanna.Acceptance.")
            if manifest.get("contract_check_file") != "ContractChecks.lean":
                raise AuditError("Complete mode requires the fixed ContractChecks.lean contract file.")
            contract = project / "ContractChecks.lean"
            if not contract.is_file() or not contract.read_text().strip():
                raise AuditError("Complete mode is not ready: lean/ContractChecks.lean is missing or empty.")
            specification = repo / "docs/THEOREM_SPEC.md"
            if not specification.is_file() or not specification.read_text().strip():
                raise AuditError("The manuscript statement specification is missing or empty.")
        report["required_theorems"] = names
        report["requirements_sha256"] = digest(manifest_path)
        pinned = (project / "lean-toolchain").read_text().strip()
        if pinned != manifest.get("expected_toolchain"):
            raise AuditError("The pinned toolchain differs from the reviewed requirements.")
        report["pinned_toolchain"] = pinned
        lake = shutil.which(args.lake)
        if lake is None:
            raise AuditError("Lake is unavailable; install the pinned toolchain or pass --lake.")
        # Preserve an Elan shim's invocation name if it is a symlink.
        lake = str(Path(lake).absolute())
        env = os.environ.copy()
        env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
        report["sources_before"] = source_snapshot(repo, output)
        version = run([lake, "env", "lean", "--version"], "toolchain.log", env)
        expected_version = pinned.rsplit(":v", 1)
        if len(expected_version) != 2 or not re.search(
            r"\bversion " + re.escape(expected_version[1]) + r"(?:\s|,|\))", version
        ):
            raise AuditError("The executing Lean version does not match the pinned release.")
        # Clean this package only; preserve pinned Mathlib dependency caches.
        run([lake, "clean", "hanna"], "clean.log", env)
        run([lake, "build"], "build.log", env)
        if args.mode == "complete":
            run([lake, "env", "lean", "-o", str(output / "ContractChecks.olean"),
                 "ContractChecks.lean"], "contracts.log", env)
            report["contract_compiled"] = True
            report["contract_object_sha256"] = digest(output / "ContractChecks.olean")
        else:
            report["contract_compiled"] = False
        prefix = "\n".join("import " + module for module in imports) + "\n\n"
        types_file = output / "GeneratedTypes.lean"
        types_file.write_text(prefix + "set_option pp.all true\n\n" + "\n".join(
            "#check " + name for name in names
        ) + "\n")
        run([lake, "env", "lean", str(types_file)], "types.log", env)
        audit_file = output / "GeneratedAxiomAudit.lean"
        audit_file.write_text(prefix + "\n".join("#print axioms " + name for name in names) + "\n")
        text = run([lake, "env", "lean", str(audit_file)], "axioms.log", env)
        report["axiom_dependencies"] = audit_text(text, names)
        report["generated_types_sha256"] = digest(types_file)
        report["generated_axiom_audit_sha256"] = digest(audit_file)
        report["sources_after"] = source_snapshot(repo, output)
        if report["sources_before"] != report["sources_after"]:
            raise AuditError("First-party sources changed during validation; repeat on a stable tree.")
        report["status"] = "mechanical_checks_passed"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["failure"] = str(error)
    report["completed_utc"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("mode", "status", "scope")}, indent=2))
    print(f"Evidence directory: {output}")
    if "failure" in report:
        print(report["failure"], file=sys.stderr)
    return 0 if report["status"] == "mechanical_checks_passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
