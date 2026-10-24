# Provenance and scope

## Reference project

- Owner and sole human author: **Dev Goyal**.
- Reference repository: <https://github.com/dvgyl/oeis-a396843-proof>.
- Inspected revision: `995e55adcbe06b2a913e24f12ff73a7faf362f06`.
- Author metadata source: the repository's `CITATION.cff` at that revision.
- New package date: 24 October 2026.

The reference project's DOI, `10.5281/zenodo.23567463`, belongs to the earlier A396843 work. It has **not** been assigned to this new package. The reference project has no declared affiliation in its citation metadata, so this package supplies none.

The original `lean/Hanna` sources are retained, with new files under `Hanna/Related`. In particular the existing formal-power-series, substitution, filtration, triangular recursion, and inverse constructions are reused. The old `Hanna.Acceptance` theorems are checked as regression endpoints and are not presented as new discoveries. The original manuscript source and README appear under `prior_work` as reference material. Their author-review statements concern that earlier project only.

New mathematics and formalization live under `lean/Consecutive` and `lean/Hanna/Related`. Their canonical sequences are constructed from their own original functional equations. They are not aliases for the rational comparison series. Equality with a comparison series after coefficient reduction is a proved theorem.

## First-release scope, retained unchanged

The main target is A396099, defined by F = X + F composed twice times F composed three times. All four listed assertions are treated as universal statements. The general consecutive-iterate result covers every natural parameter and every nonnegative iterate, and the signed-iterate extension uses actual compositional inverses.

Direct applications include A396798 and A396807. One A396798 statement is false with its published starting phase: the corrected coefficient block begins at n = 2. The other seven statements follow from the general theorem. The r = 3 case A396797 was already proved by Sundaram and is credited as prior work.

A separate division-free scaled-substitution family gives six assertions from A393856–A393859. The source ledger identifies every original statement and its index range.

No claim is made that every conjecture in OEIS or every conjecture adjacent to these entries has been resolved. The scope is the explicit statement list in `docs/THEOREM_SPEC.md`, with exact formal coverage in `docs/COVERAGE.md` and `validation/final_theorems.json`.

## Reproducibility boundaries

The archive contains first-party source, the pinned Lean and Mathlib versions, the mathematical PDF and its LaTeX source, and the fresh verification evidence. It omits downloaded compiler binaries and dependency caches. The setup commands fetch those exact pinned dependencies.

Compilation and axiom audits establish the proof terms against their formal types. The typed contracts and definition review document how those types correspond to the mathematical questions. Finite coefficient checks are separate computational corroboration. All preparation and review in this session were AI-assisted; independent human review remains pending.

## Expanded version 2

The additions live in `lean/More` and address the exact statements listed in `docs/ROUND2_COVERAGE.md`. There are seven conjectural statements across A396093, A389474, A389475, and A396102. The two cube assertions are applications of standard Frobenius. The seven factorial-Stirling periodicity cases are covered by earlier mathematical work and are reported as formalizations of known results, with explicit credit to Payam Danesh's 26 August 2026 Theorem 4.1 and Corollary 4.2, DOI <https://doi.org/10.33774/coe-2026-4d6jr>. The claim count does not establish global novelty or publication priority.

The exact previous ZIP is retained at `prior_work/oeis_congruence_proofs_Dev_Goyal_v1.zip` with SHA-256 `04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c`. The complete checker verifies that hash, keeps the original 67 endpoint names in order, verifies that every original Lean proof module is unchanged, and checks preservation of the original typed contracts. The expanded fixed requirement set has 130 endpoints.

The additional Stirling recurrence and part of its power-expansion proof adapt later upstream Mathlib code. See `third_party/mathlib/NOTICE.md` for the original authors, exact revision, changes, and Apache-2.0 license. The manuscript's mathematical EGF identification is distinct from the finite-transform statement formalized in Lean.
