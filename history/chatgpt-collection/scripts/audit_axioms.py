#!/usr/bin/env python3
"""Strictly check Lean's transitive axiom reports for an explicit theorem list.

This checks dependency reports, not whether theorem statements faithfully
formalize a mathematical manuscript. The latter needs reviewed typed contracts.
Use check_formalization.py to generate reports from a fresh successful build.
"""

import argparse
import json
from pathlib import Path
import re
import sys


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
RECORD = re.compile(
    r"'(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)'\s+"
    r"(?:does not depend on any axioms|"
    r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\])"
)


class AuditError(ValueError):
    """An incomplete, malformed, or disallowed axiom report."""


def required_theorems(manifest):
    """Validate the explicit, nonempty list; never infer it from a log."""
    if manifest.get("schema_version") != 1:
        raise AuditError("Requirements must use schema_version 1.")
    names = manifest.get("required_theorems")
    if not isinstance(names, list) or not names:
        raise AuditError("required_theorems must be a nonempty list.")
    if any(not isinstance(name, str) or not NAME.fullmatch(name) for name in names):
        raise AuditError("Required theorem names must be explicit qualified identifiers.")
    if len(set(names)) != len(names):
        raise AuditError("Duplicate required theorem names are not permitted.")
    if any("." not in name for name in names):
        raise AuditError("Use fully qualified theorem names.")
    return names


def audit_text(text, names):
    """Return all checked dependencies, failing closed on unrecognized output.

    Lean 4.19 output may wrap an axiom list over several lines. Whitespace is
    ignored between complete records; all other unparsed output is rejected.
    This rejects warnings/errors and avoids silently accepting truncated logs.
    """
    names = required_theorems({"schema_version": 1, "required_theorems": names})
    records = {}
    cursor = 0
    for match in RECORD.finditer(text):
        if text[cursor:match.start()].strip():
            raise AuditError("Unrecognized output before an axiom record.")
        name = match.group("name")
        if name in records:
            raise AuditError(f"Duplicate axiom report for {name}.")
        body = match.group("axioms")
        axioms = [] if body is None or not body.strip() else [
            item.strip() for item in body.split(",")
        ]
        if any(not NAME.fullmatch(item) for item in axioms):
            raise AuditError(f"Malformed axiom list for {name}.")
        if len(set(axioms)) != len(axioms):
            raise AuditError(f"Duplicate entries in the axiom list for {name}.")
        forbidden = sorted(set(axioms) - ALLOWED_AXIOMS)
        if forbidden:
            raise AuditError(f"Disallowed dependencies for {name}: {', '.join(forbidden)}.")
        records[name] = axioms
        cursor = match.end()
    if text[cursor:].strip():
        raise AuditError("Unrecognized or truncated output after an axiom record.")
    missing = sorted(set(names) - set(records))
    extra = sorted(set(records) - set(names))
    if missing or extra:
        raise AuditError(f"Theorem coverage mismatch; missing={missing}, unexpected={extra}.")
    return {name: records[name] for name in names}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--requirements", type=Path, required=True)
    parser.add_argument("--audit-log", type=Path, required=True)
    args = parser.parse_args()
    try:
        manifest = json.loads(args.requirements.read_text())
        records = audit_text(args.audit_log.read_text(), required_theorems(manifest))
    except (OSError, ValueError) as error:
        print(f"AXIOM AUDIT FAILED: {error}", file=sys.stderr)
        return 1
    print(json.dumps({
        "status": "axiom_dependency_audit_passed",
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "checked_theorems": records,
        "scope": "Dependencies only; theorem meanings and typed contracts require review."
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
