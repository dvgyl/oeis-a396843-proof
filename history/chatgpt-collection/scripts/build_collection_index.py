#!/usr/bin/env python3
"""Build the final entry catalogue and navigable paper/proof index.

Run before verify_final_collection.py. This changes first-party sources and
therefore intentionally invalidates an earlier final verification snapshot.
"""

from __future__ import annotations

import json
from pathlib import Path
import re

from check_formalization import FINAL_NAMES
from verify_final_collection import EXPECTED_IDS


def clean(value) -> str:
    if isinstance(value, list):
        value = " ".join(value)
    return str(value).replace("\n", " ").replace("|", "\\|")


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    entries = []
    for name in ("original_entries.json", "second_entries.json", "recent_entries.json"):
        entries.extend(json.loads((root / "catalogue" / name).read_text()))
    entries.sort(key=lambda item: item["oeis_id"])
    if len(entries) != 34 or {item["oeis_id"] for item in entries} != EXPECTED_IDS:
        raise ValueError("Incomplete or duplicated final inventory")
    document = {
        "schema_version": 1,
        "title": "Final OEIS collection: individual manuscripts and Lean proofs",
        "author": "Dev Goyal",
        "prepared_date": "2026-10-24",
        "ai_disclosure": "ChatGPT generated the developments and consolidation in response to Dev Goyal's prompts, with retained upstream and historical credits. Independent human review is pending.",
        "entry_count": len(entries),
        "entry_count_is_not_new_open_problem_count": True,
        "lean_toolchain": "leanprover/lean4:v4.19.0",
        "mathlib_revision": "c44e0c8ee63ca166450922a373c7409c5d26b00b",
        "entries": entries,
    }
    (root / "catalogue/entries.json").write_text(json.dumps(document, indent=2, ensure_ascii=False) + "\n")
    imports = ["import Entries." + item["oeis_id"] for item in entries]
    (root / "lean/Entries.lean").write_text("\n".join(imports) + "\n\n/-! All 34 individually named OEIS proof interfaces. See ../INDEX.md. -/\n")

    modules = {}
    for path in (root / "lean").rglob("*.lean"):
        relative = path.relative_to(root / "lean")
        if ".lake" not in relative.parts:
            modules[".".join(relative.with_suffix("").parts)] = path

    def dependencies(name: str, seen: set[str]) -> None:
        if name in seen or name not in modules:
            return
        seen.add(name)
        for line in modules[name].read_text().splitlines():
            match = re.match(r"\s*import\s+(.+?)(?:\s*--.*)?$", line)
            if match:
                for imported in match.group(1).split():
                    dependencies(imported, seen)

    dependency_map = {}
    for entry in entries:
        module = "Entries." + entry["oeis_id"]
        seen = set()
        dependencies(module, seen)
        dependency_map[entry["oeis_id"]] = {
            "entry_module": module,
            "all_local_modules": sorted(seen),
            "shared_proof_files": sorted(str(modules[n].relative_to(root)) for n in seen if n != module),
            "external_dependency": "Pinned Mathlib and Lean standard libraries",
        }
    (root / "catalogue/dependency_map.json").write_text(json.dumps(dependency_map, indent=2) + "\n")
    linked = {name for item in entries for name in item["original_endpoints"]}
    entry_names = [name for item in entries for name in item["new_endpoints"]]
    inventory = {
        "original_endpoint_count": len(FINAL_NAMES),
        "original_endpoints": FINAL_NAMES,
        "entry_interface_theorem_count": len(entry_names),
        "entry_interface_theorems": entry_names,
        "shared_original_endpoints_without_a_single_entry_assignment": [name for name in FINAL_NAMES if name not in linked],
        "scope": "Every original endpoint is retained and audited, including general supporting results. Per-entry theorems restate or specialize completed mathematics; they are not counted as new discoveries.",
    }
    (root / "catalogue/theorem_inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")

    lines = [
        "# Index of the final OEIS collection", "",
        "**34 entries, each with a separate PDF, editable LaTeX manuscript, and explicitly typed Lean proof file.** All supporting proof code is included in the shared Lean project.", "",
        "Author: Dev Goyal. AI-generated mathematics, formalization, and exposition, with historical and upstream contributions credited. Independent human review is pending. See [README.md](README.md) for build instructions and [AI_DISCLOSURE.md](AI_DISCLOSURE.md) for contribution details.", "",
        "The entry count includes known results, standard consequences, and corrected false statements. It is not a new-open-problem count. Source status reflects the previously retrieved material, not an exhaustive novelty determination.", "",
        "## Papers and proofs", "",
        "| OEIS entry | Manuscript | Editable source | Lean proof | Coverage/status |",
        "|---|---|---|---|---|",
    ]
    for entry in entries:
        lines.append(f"| [{entry['oeis_id']}]({entry['source_url']}) | [PDF]({entry['manuscript_pdf']}) | [LaTeX]({entry['manuscript_tex']}) | [Lean]({entry['lean_file']}) | {clean(entry['status']).replace('_', ' ')} |")
    lines += ["", "## Result summaries and qualifications", ""]
    for entry in entries:
        lines += [f"### {entry['oeis_id']} — {clean(entry['title'])}", "",
                  clean(entry["summary"]), "", clean(entry["qualifications"]), "",
                  f"The typed interface contains {len(entry['new_endpoints'])} named theorems. The full original implementation and source-contract references are listed in [the catalogue](catalogue/entries.json); all local dependencies are listed in [the dependency map](catalogue/dependency_map.json).", ""]
    lines += [
        "## General theorems and retained combined papers", "",
        "Each individual paper repeats the definitions and arguments needed for its results. The general constructions and shared results also remain in the original combined presentations:", "",
        "| Paper | Main shared mathematics |",
        "|---|---|",
        "| [Compositional congruences](manuscript/compositional_congruences.pdf) | Consecutive composition iterates, positive and negative iterates, rational comparison series, and the scaled-inverse family. |",
        "| [Further OEIS proofs](manuscript/further_oeis_proofs.pdf) | Rational parity, the cubic family, inverse iterates, and the known general weighted-Stirling periodicity theorem. |",
        "| [Six more OEIS proofs](manuscript/six_more_oeis_proofs.pdf) | Differential and Mahler recursions, lacunary inversion, square reversion, and theta substitution. |",
        "| [More proofs and corrections](manuscript/more_oeis_proofs_and_corrections.pdf) | Infinite nested reversion, Catalan composition, integral binomial convolution, and rational theta sums. |",
        "", "The A396843 and A396844 individual papers also document the original parameter family, parity, binary divisibility, and exact residue classifications. All generic and supporting endpoints remain in [the complete theorem inventory](catalogue/theorem_inventory.json).", "",
        "## Verification evidence", "",
        "- [Complete mathematical verification](reproducibility/lean_complete/report.json): all 339 original endpoints and forced source elaboration of the entire final Lean tree.",
        f"- [Final collection verification](reproducibility/final_collection/report.json): all 34 paper/proof pairs and all {len(entry_names)} explicitly typed per-entry theorem interfaces.",
        "- [Consolidation review](docs/FINAL_COLLECTION_REVIEW.md): coverage, unchanged source preservation, manuscript checks, and material limitations.",
        "- [Integrity checksums](SHA256SUMS): every archived payload file.", "",
    ]
    (root / "INDEX.md").write_text("\n".join(lines))
    print(json.dumps({"entries": len(entries), "entry_theorems": len(entry_names),
                      "original_endpoints": len(FINAL_NAMES), "local_modules": len(modules)}, indent=2))


if __name__ == "__main__":
    main()
