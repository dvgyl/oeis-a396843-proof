# Final OEIS collection — Dev Goyal

This is the final consolidated collection of the work completed in this conversation. It contains **34 separately organized OEIS entries**, including the original A396843 work, its A396844 specialization, the credited A396797 case, and every completed entry from all four cumulative releases.

**Start with [INDEX.md](INDEX.md)**. It links each entry to its own mathematical paper and its own Lean proof interface. Each entry has:

- `manuscripts/Axxxxxx.pdf`: a separate paper, with definitions, precise statements, mathematical proofs, sources, formalization scope, and AI disclosure.
- `manuscripts/Axxxxxx.tex`: the editable, self-contained LaTeX source for that paper; no other project-local TeX file is needed to compile it.
- `lean/Entries/Axxxxxx.lean`: explicitly typed, kernel-checked theorems for that entry, proved using the full shared formalization included in the same archive.

The Lean files are organized as a single pinned project. A per-entry file imports its mathematical dependencies; it is not intended to compile after being copied away from the project. All original proof implementations are present in `lean/Hanna/` (including `Hanna/Related/`), `lean/Consecutive/`, `lean/More/`, `lean/Round3/`, and `lean/Round4/`. No earlier archive needs to be opened to use the current proofs or papers.

## Contribution and status

**ChatGPT (OpenAI) generated the mathematical developments, Lean proofs, manuscripts, and verification tools in response to Dev Goyal's prompts, subject to the retained upstream and historical credits.** This final organization and its separate papers and theorem interfaces were also AI-generated. Dev Goyal is the sole human author. **Independent human review is pending.** See [AI_DISCLOSURE.md](AI_DISCLOSURE.md).

The 34 entries are a coverage count, not a count of newly solved open problems. Each paper identifies its actual status. In particular:

- A396797 is a specialization whose earlier proof is credited to Shiva Priyan Shanmuga Sundaram.
- A052895, A064618, A080253, A167137, A305550, A306082, and A354242 are formalizations of known Stirling-periodicity results; Payam Danesh's prior theorem and the adapted Mathlib source are credited.
- A396798 contains a correction to a false literal starting phase. A380680 contains a counterexample to the source conjecture and a corrected theorem. These are not presented as proofs of the false statements.
- Standard Frobenius consequences and the elementary A392210 observation are labeled accordingly.
- Statements of source correspondence have their actual scope. In particular, the Stirling EGF-to-transform derivation is explained mathematically but is not itself a Lean theorem, and the rational-theta papers formalize the source's positive-index formula rather than a separate Laurent-series equivalence.

This consolidation does not add a new research round. It preserves the completed mathematics and makes each named result independently readable. No global novelty, exclusive priority, journal acceptance, OEIS acceptance, or completed human review is asserted. No submission or publication was made by this workflow.

## What is included

| Location | Contents |
|---|---|
| `INDEX.md` | All 34 entries, linked papers, proof files, result summaries, and qualifications. |
| `manuscripts/` | 34 individual PDFs and 34 complete LaTeX sources. |
| `lean/Entries/` | 34 separately named theorem interfaces, one per entry. |
| `lean/Entries.lean` | One import of the entire per-entry collection. |
| Other `lean/` modules | All preserved constructions, general theorems, proof implementations, and source contracts. |
| `catalogue/entries.json` | Machine-readable paper-to-proof and theorem map. |
| `catalogue/dependency_map.json` | The local proof dependencies of each entry. |
| `manuscript/` | The four earlier combined papers and their sources, retained unchanged for the general families and historical presentation. |
| `docs/` | Original coverage ledgers, source credits, limitations, proof reviews, and the final consolidation review. |
| `validation/` | All 339 original audited endpoints, per-family evidence, and preservation records. |
| `reproducibility/lean_complete/` | Fresh complete mathematical verification: source compilation, contracts, full theorem types, axiom audits, and numerical checks. |
| `reproducibility/final_collection/` | Individual-paper QA, the additional interface audit, and the final report. |
| `prior_work/` | Original repository provenance and earlier release archives retained as historical evidence. |
| `third_party/mathlib/` | Upstream attribution and license notices. |

The original 66 Lean source files from the fourth release are byte-for-byte preserved. The separate entry files add readable interfaces; they do not replace or weaken the existing proofs. All 339 original endpoints are still audited. Those endpoints include construction, uniqueness, source-equation, and supporting results and must not be interpreted as 339 open problems.

## Build and verify

The project pins **Lean 4.19.0** and **Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Install the pinned Lean toolchain through Elan and use Python 3.11 or later. Compiler binaries and downloaded dependency caches are omitted from the ZIP.

From this directory:

```sh
cd lean
lake exe cache get
lake build
lake build Entries
cd ..
python3 scripts/verify_final_collection.py
```

To inspect or recheck one individual interface after building the project:

```sh
cd lean
lake env lean Entries/A396843.lean
```

Replace the identifier with any entry in the index. To import everything in another Lean file in this project, use `import Entries`.

The complete verifier reruns the original numerical suites and validation regression tests, deletes only the project's build cache, rebuilds the original libraries, and directly elaborates every first-party module in dependency order into a new empty object directory. It excludes the old project-object directory from that verification import path. It checks all original typed contracts, prints full types, and audits the transitive axioms of all original endpoints and every new entry theorem using those fresh objects. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. The report records the actual counts and hashes.

The mathematical theorems are unbounded in their stated index ranges. The finite numerical suites are separate corroboration, not substitutes for proofs. A successful kernel check validates the formal statements against the included definitions; the source-to-definition correspondence and paper exposition also require mathematical review.

Each individual paper can be rebuilt with pdfLaTeX, for example:

```sh
mkdir -p /tmp/oeis-paper
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/oeis-paper manuscripts/A396843.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/oeis-paper manuscripts/A396843.tex
```

The supplied PDFs were compiled, rendered, and visually reviewed. No document-generation runtime is needed merely to read them. The optional document-inspection script `scripts/check_manuscript_files.py` uses PyMuPDF; the Lean verification scripts use only Python's standard library.

After verification, the final archive can be reproduced with:

```sh
python3 scripts/package_release.py
```

The packager requires matching successful verification reports, the complete entry inventory, unchanged source hashes, and the recorded verification logs. `SHA256SUMS` covers every payload file except itself. After extraction, `sha256sum -c SHA256SUMS` checks archive integrity.

## Attribution and provenance

The reference repository is [dvgyl/oeis-a396843-proof](https://github.com/dvgyl/oeis-a396843-proof), revision `995e55adcbe06b2a913e24f12ff73a7faf362f06`. Source entries and conjecture authors are credited in each paper and in the retained ledgers. Earlier papers, source metadata, and disclosure text retain their historical context. No original DOI is reassigned to this expanded collection, and no new DOI, affiliation, credential, or publication venue is inferred.
