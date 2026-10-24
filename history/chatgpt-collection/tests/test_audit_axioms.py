#!/usr/bin/env python3
"""Tests for strict transitive-axiom coverage and fail-closed report parsing."""

import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from audit_axioms import AuditError, audit_text, required_theorems


class AxiomAuditTests(unittest.TestCase):
    names = ["Hanna.Acceptance.parity_odd", "Hanna.Acceptance.parity_even"]

    def valid(self):
        return (
            "'Hanna.Acceptance.parity_odd' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
            "'Hanna.Acceptance.parity_even' does not depend on any axioms\n"
        )

    def test_allowed_axioms_and_axiom_free_theorem(self):
        result = audit_text(self.valid(), self.names)
        self.assertEqual(list(result), self.names)
        self.assertEqual(result[self.names[1]], [])

    def test_wrapped_axiom_list(self):
        text = self.valid().replace("[propext, Classical.choice, Quot.sound]",
                                    "[propext,\n Classical.choice,\n Quot.sound]")
        self.assertEqual(len(audit_text(text, self.names)), 2)

    def test_empty_list_format(self):
        text = self.valid().replace("does not depend on any axioms", "depends on axioms: []")
        self.assertEqual(audit_text(text, self.names)[self.names[1]], [])

    def test_sorry_axiom_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().replace("Quot.sound", "sorryAx"), self.names)

    def test_custom_mathematical_axiom_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().replace("Quot.sound", "Hanna.assumed_parity"), self.names)

    def test_unlisted_standard_dependency_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().replace("Quot.sound", "Lean.ofReduceBool"), self.names)

    def test_missing_theorem_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().splitlines()[0] + "\n", self.names)

    def test_unexpected_theorem_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid() + "'Other.trivial' does not depend on any axioms\n", self.names)

    def test_duplicate_report_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid() + self.valid().splitlines()[0], self.names)

    def test_warning_rejected(self):
        with self.assertRaises(AuditError):
            audit_text("warning: declaration uses 'sorry'\n" + self.valid(), self.names)

    def test_truncated_report_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().replace("Quot.sound]", "Quot.sound"), self.names)

    def test_empty_log_rejected(self):
        with self.assertRaises(AuditError):
            audit_text("", self.names)

    def test_empty_requirement_list_rejected(self):
        with self.assertRaises(AuditError):
            required_theorems({"schema_version": 1, "required_theorems": []})

    def test_duplicate_requirements_rejected(self):
        with self.assertRaises(AuditError):
            required_theorems({"schema_version": 1, "required_theorems": self.names * 2})

    def test_missing_fully_qualified_name_rejected(self):
        with self.assertRaises(AuditError):
            required_theorems({"schema_version": 1, "required_theorems": ["parity_odd"]})

    def test_malformed_axiom_item_rejected(self):
        with self.assertRaises(AuditError):
            audit_text(self.valid().replace("Quot.sound", "Quot.sound,"), self.names)


if __name__ == "__main__":
    unittest.main()
