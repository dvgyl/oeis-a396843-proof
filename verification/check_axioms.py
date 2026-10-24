"""Check the output of `lake env lean ../verification/AxiomAudit.lean`.

Usage (from the lean/ folder):

    lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
    python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt

Every theorem listed in AxiomAudit.lean must appear in the output, and may
depend only on Lean's three standard axioms. Exits nonzero otherwise.
"""
import pathlib
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

here = pathlib.Path(__file__).resolve().parent
expected = re.findall(r"^#print axioms (\S+)", (here / "AxiomAudit.lean").read_text(), re.M)
text = pathlib.Path(sys.argv[1]).read_text()

found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S):
    found[name] = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()

missing = [n for n in expected if n not in found]
bad = {n: sorted(found[n] - ALLOWED) for n in expected if n in found and found[n] - ALLOWED}
errors = [l for l in text.splitlines() if "error" in l.lower()]

print(f"theorems listed: {len(expected)}; reported: {sum(n in found for n in expected)}")
used = set().union(*found.values()) if found else set()
print("axioms used overall:", ", ".join(sorted(used)) or "none")
for n in missing:
    print("MISSING:", n)
for n, a in bad.items():
    print("NON-STANDARD AXIOMS:", n, a)
for l in errors:
    print("ERROR LINE:", l)
ok = not missing and not bad and not errors
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
