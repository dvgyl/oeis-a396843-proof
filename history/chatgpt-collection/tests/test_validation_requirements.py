"""Regression tests ensuring complete validation cannot silently lose scope."""

import json
from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from audit_axioms import AuditError
from check_formalization import (
    BASELINE_ARCHIVE, PREVIOUS_V2_ARCHIVE, PREVIOUS_V2_SHA256,
    PREVIOUS_V3_ARCHIVE, PREVIOUS_V3_SHA256, FINAL_NAMES,
    first_party_compile_order, source_snapshot, validate_baseline, validate_manifest,
)


class ValidationRequirementTests(unittest.TestCase):
    def manifest(self):
        return json.loads((ROOT / "validation/final_theorems.json").read_text())

    def test_complete_manifest_retains_fixed_endpoints(self):
        self.assertEqual(validate_manifest(self.manifest()), FINAL_NAMES)

    def test_missing_endpoint_rejected(self):
        manifest = self.manifest()
        manifest["required_theorems"].pop()
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_replaced_endpoint_rejected(self):
        manifest = self.manifest()
        manifest["required_theorems"][0] = "Consecutive.unrelated_theorem"
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_weakened_imports_rejected(self):
        manifest = self.manifest()
        manifest["imports"] = ["Hanna.Acceptance"]
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_substitute_contract_file_rejected(self):
        manifest = self.manifest()
        manifest["contract_check_file"] = "OtherContracts.lean"
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_changed_pins_rejected(self):
        for key in ("expected_toolchain", "expected_mathlib_revision", "package_name"):
            with self.subTest(key=key):
                manifest = self.manifest()
                manifest[key] = "other"
                with self.assertRaises(AuditError):
                    validate_manifest(manifest)

    def test_baseline_mode_rejected(self):
        manifest = self.manifest()
        manifest["mode"] = "baseline"
        with self.assertRaises(AuditError):
            validate_manifest(manifest)

    def test_snapshot_includes_root_docs_and_final_pdf(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            (repo / "README.md").write_text("reviewed documentation")
            (repo / "manuscript").mkdir()
            (repo / "manuscript/paper.pdf").write_bytes(b"test document")
            output = repo / "reproducibility/lean_complete"
            output.mkdir(parents=True)
            (output / "report.json").write_text("generated output")
            before = source_snapshot(repo, output)
            self.assertEqual(set(before), {"README.md", "manuscript/paper.pdf"})
            (repo / "README.md").write_text("changed documentation")
            self.assertNotEqual(before, source_snapshot(repo, output))

    def test_snapshot_rejects_first_party_symlink(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            (repo / "proof.lean").write_text("import Mathlib")
            (repo / "alias.lean").symlink_to(repo / "proof.lean")
            with self.assertRaises(AuditError):
                source_snapshot(repo, repo / "reproducibility/lean_complete")

    def test_complete_previous_release_is_preserved(self):
        result = validate_baseline(ROOT)
        self.assertEqual(result["previous_endpoint_count"], 67)
        self.assertTrue(result["original_zip_preserved_verbatim"])

    def test_complete_version_two_is_preserved(self):
        result = validate_baseline(ROOT, PREVIOUS_V2_ARCHIVE, PREVIOUS_V2_SHA256)
        self.assertEqual(result["previous_endpoint_count"], 130)
        self.assertTrue(result["original_zip_preserved_verbatim"])

    def test_complete_version_three_is_preserved(self):
        result = validate_baseline(ROOT, PREVIOUS_V3_ARCHIVE, PREVIOUS_V3_SHA256)
        self.assertEqual(result["previous_endpoint_count"], 226)
        self.assertTrue(result["original_zip_preserved_verbatim"])

    def test_snapshot_includes_all_previous_archives(self):
        snapshot = source_snapshot(ROOT, ROOT / "reproducibility/lean_complete")
        self.assertIn(BASELINE_ARCHIVE, snapshot)
        self.assertEqual(snapshot[PREVIOUS_V2_ARCHIVE], PREVIOUS_V2_SHA256)
        self.assertEqual(snapshot[PREVIOUS_V3_ARCHIVE], PREVIOUS_V3_SHA256)

    def test_changed_version_three_proof_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            baseline = repo / PREVIOUS_V3_ARCHIVE
            baseline.parent.mkdir(parents=True)
            baseline.write_bytes((ROOT / PREVIOUS_V3_ARCHIVE).read_bytes())
            with zipfile.ZipFile(baseline) as old:
                prefix = "oeis-congruence-proofs/"
                for name in old.namelist():
                    if name.startswith(prefix + "lean/") and name.endswith(".lean"):
                        target = repo / name[len(prefix):]
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes(old.read(name))
            altered = repo / "lean/Round3/ThetaSubstitution.lean"
            altered.write_text(altered.read_text() + "\n-- changed version-three proof source\n")
            with self.assertRaisesRegex(AuditError, "Previous formal proof source was changed"):
                validate_baseline(repo, PREVIOUS_V3_ARCHIVE, PREVIOUS_V3_SHA256)

    def test_changed_version_two_proof_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            baseline = repo / PREVIOUS_V2_ARCHIVE
            baseline.parent.mkdir(parents=True)
            baseline.write_bytes((ROOT / PREVIOUS_V2_ARCHIVE).read_bytes())
            with zipfile.ZipFile(baseline) as old:
                prefix = "oeis-congruence-proofs/"
                for name in old.namelist():
                    if name.startswith(prefix + "lean/") and name.endswith(".lean"):
                        target = repo / name[len(prefix):]
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes(old.read(name))
            altered = repo / "lean/More/CubicConsequences.lean"
            altered.write_text(altered.read_text() + "\n-- changed version-two proof source\n")
            with self.assertRaisesRegex(AuditError, "Previous formal proof source was changed"):
                validate_baseline(repo, PREVIOUS_V2_ARCHIVE, PREVIOUS_V2_SHA256)

    def test_forced_compilation_keeps_isolated_modules_and_orders_dependencies(self):
        with tempfile.TemporaryDirectory() as folder:
            project = Path(folder)
            (project / "A.lean").write_text("import Z\n")
            (project / "Z.lean").write_text("import Mathlib\n")
            (project / "Isolated.lean").write_text("import Std\n")
            (project / "ContractChecks.lean").write_text("import A\n")
            deps = project / ".lake/packages/external"
            deps.mkdir(parents=True)
            (deps / "External.lean").write_text("import Std\n")
            names = [name for name, _ in first_party_compile_order(project)]
            self.assertEqual(set(names), {"A", "Z", "Isolated"})
            self.assertLess(names.index("Z"), names.index("A"))

    def test_forced_compilation_rejects_local_import_cycles(self):
        with tempfile.TemporaryDirectory() as folder:
            project = Path(folder)
            (project / "A.lean").write_text("import B\n")
            (project / "B.lean").write_text("import A\n")
            with self.assertRaisesRegex(AuditError, "Cyclic"):
                first_party_compile_order(project)

    def test_changed_previous_proof_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            baseline = repo / BASELINE_ARCHIVE
            baseline.parent.mkdir(parents=True)
            baseline.write_bytes((ROOT / BASELINE_ARCHIVE).read_bytes())
            with zipfile.ZipFile(baseline) as old:
                prefix = "oeis-congruence-proofs/"
                for name in old.namelist():
                    if name.startswith(prefix + "lean/") and name.endswith(".lean"):
                        target = repo / name[len(prefix):]
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes(old.read(name))
            altered = repo / "lean/Consecutive/Modular.lean"
            altered.write_text(altered.read_text() + "\n-- changed old proof source\n")
            with self.assertRaisesRegex(AuditError, "Previous formal proof source was changed"):
                validate_baseline(repo)


if __name__ == "__main__":
    unittest.main()
