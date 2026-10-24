# Independent AI review of version-four integration

Reviewed on 24 October 2026 by a ChatGPT agent separate from the agent
responsible for package integration, for Dev Goyal. This is an AI review;
independent human review remains pending.

**Result: the frozen integration satisfies the reviewed scope and
preservation requirements. No integration change was requested.** The
reviewer read the checker, axiom auditor, packager, Lake configuration,
aggregate imports, root contract, endpoint fragments, and regression tests,
then independently executed the static consistency and preservation
checks described below.

This review evaluates the verification procedure and the exact code listed
in the hash table. The final successful execution, command logs, numerical
evidence, and transitive axiom reports are recorded separately in
`reproducibility/lean_complete/report.json`. Source review does not itself
constitute a completed full Lean run.

## Exact theorem scope

The complete manifest has **339 distinct, fully qualified endpoints**.
Its initial 226 names are the complete version-three list in the same
order. The new suffix is exactly the concatenation of the four reviewed
manifest fragments:

| Fragment | Endpoints |
|---|---:|
| `validation/round4_nested_endpoints.json` | 18 |
| `validation/round4_catalan_endpoints.json` | 39 |
| `validation/round4_exp_cosine_endpoints.json` | 25 |
| `validation/round4_theta_rational_endpoints.json` | 31 |
| **New endpoints** | **113** |

The reviewer independently checked that `226+113=339`, that the ordered
fragment concatenation equals the full manifest's suffix, and that the
full manifest groups exactly equal the checker's fixed groups. These are
endpoint counts, not counts of distinct mathematical conjectures.

The checker retains a fixed endpoint list in code and rejects a changed,
reordered, missing, duplicated, malformed, or substituted requirement set.
It requires complete mode, the exact package imports, the root
`ContractChecks.lean`, and the reviewed Lean and Mathlib pins. The axiom
auditor requires exactly one parseable report for every fixed endpoint;
missing, extra, duplicated, malformed, warning, or truncated output fails
the audit. Its allowed dependencies remain exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Preservation of the three earlier releases

The reviewer invoked the preservation check independently against all
three embedded archives, including ZIP CRC verification. Each complete
archive matches its previously delivered SHA-256:

| Release | Prior endpoints | Prior Lean files | SHA-256 |
|---|---:|---:|---|
| v1 | 67 | 30 | `04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c` |
| v2 | 130 | 42 | `b28c6de12f53e862b670d37d79d8b5f11333ce3d7acd44e61cb27eb2b99dbc10` |
| v3 | 226 | 54 | `6a0cbeb94076a90e8938627a156ed4152f6cc3fd88546d0d2e29cd9331744d41` |

Every previous Lean module is retained byte for byte. The intentional
exception is the root contract file, where the new version is **exactly**
`import Round4.Contracts` followed by a newline and the complete original
version-three bytes. The reviewer checked this stronger exact-prefix-plus-
suffix identity, in addition to the checker's retained-text test. No old
typed contract was edited or removed.

All three archives are included in both the source snapshot and the release
payload. Thus the cumulative ZIP retains the complete historical packages,
not merely their current proof sources.

## Module and contract coverage

All six libraries remain default Lake targets: `Hanna`, `Consecutive`,
`Related`, `More`, `Round3`, and `Round4`. `Round4.lean` imports
`Round4.Contracts`, which imports all four new contract modules. The root
contract also imports that aggregate before the unchanged earlier content.

An independent enumeration found **65 local Lean modules**, excluding only
the separately compiled root contract. Every local import precedes its
dependent module in the checker's ordering. The 12 newly included local
modules are:

- `Round4.NestedReversion` and `Round4.NestedContracts`.
- `Round4.SquareComposition`, `Round4.CatalanComposition`,
  `Round4.NestedBinomial`, and `Round4.CatalanContracts`.
- `Round4.ExpCosine` and `Round4.ExpCosineContracts`.
- `Round4.ThetaRational` and `Round4.ThetaRationalContracts`.
- `Round4.Contracts` and `Round4`.

The module enumeration scans all first-party `.lean` files, including a
module that is not reachable from a default library import. It excludes
dependency caches and the separately handled root contract, rejects local
source symlinks, and rejects cyclic local imports. The reviewed sources use
the ordinary one-line import syntax supported by this dependency parser.

## Mandatory fresh source compilation

The stronger isolated-compilation gate introduced in version three remains
mandatory:

1. Check the executing Lean version, pinned Mathlib revision, and clean
   tracked Mathlib source; run the required tests and numerical programs.
2. Clean this package's build directory and run the full Lake build.
3. Obtain Lake's selected compiler executable and dependency search path.
4. Create a fresh temporary directory for first-party proof objects. Resolve
   the search paths, remove the old root project object directory, and place
   the new empty directory first.
5. Invoke the selected Lean executable **directly** on every local source
   in dependency order, with an explicit new `.olean` output path. These
   invocations are not wrapped in `lake env`, which could restore a
   different search-path precedence.
6. Require each object to be absent before compilation and to exist with a
   new modification time afterward; record source and object hashes.
7. Compile the root contract, print the complete types of all 339 endpoints,
   and audit all their transitive axiom dependencies under that same
   isolated environment.

For this release that means all **65 local modules plus the root contract**
are explicitly re-elaborated. Cached external dependencies remain pinned;
the root project's previous compiled objects cannot satisfy the local
imports through the removed search-path entry.

All compiler commands must return zero. Warning or error output is rejected.
The checker also requires complete before-and-after source snapshots to
match, preventing acceptance if a first-party file changes during the run.
This includes manuscripts, root documentation, validation requirements,
and the three retained archives, while excluding generated evidence and
dependency/build caches.

## Numerical and regression gates

The checker has **13 mandatory numerical suites**: the nine retained suites
and the new nested-reversion, Catalan-composition, exponential-cosine, and
rational-theta suites. The reviewer independently inspected the configured
list and confirmed that all four new programs are included with their
intended defaults. Each output receives a recorded content hash. These
finite programs corroborate source interpretation and implementation; they
do not replace universal Lean proofs.

The regression suite contains **41 test cases**. The reviewed tests retain
the earlier scope-reduction, pin, contract, source-snapshot, symlink, prior
proof, and compilation-order checks. New version-three preservation checks
include deliberate alteration of a retained Round3 proof, which must be
rejected. The full checker executes the entire test suite as a required
gate; it does not depend on test discovery alone.

## Release packaging

The version-four packager defaults to
`oeis_proofs_complete_Dev_Goyal_v4.zip`, outside its own payload directory.
It requires a successful complete report, matching stable source
snapshots, unchanged recorded sources, successful command records,
unchanged logs, and unchanged numerical evidence.

It also independently enumerates the release's local Lean modules and
requires an exact, duplicate-free correspondence with the fresh source-
compilation records. Every record must affirm new object creation and
contain the current source hash. A missing, duplicated, or stale proof
record therefore prevents packaging.

The payload excludes compiler/dependency caches and transient build
products while retaining all three prior ZIPs. A `SHA256SUMS` file covers
every payload file except itself. After construction, the packager verifies
ZIP CRCs and checks every archived payload hash against its local source.
The complete archive hash is then reported for delivery.

## Scope of this review

The preceding checks found no omitted endpoint fragment, lost historical
proof, wrong target, weakened axiom gate, or stale-object fallback in the
reviewed integration. This is a source and verification-process review;
the final report is the evidence of actual full-run success. Separate
mathematical reviews cover source correspondence and the meaning of the
new theorem statements. None of these reviews establishes worldwide
historical novelty or OEIS acceptance.

README, citation metadata, and the final coverage ledger were being finished
separately and are not included in the hashes below. The full checker will
hash their finalized contents with the rest of the release source.

## Reviewed integration file hashes

- `scripts/check_formalization.py`: `7c6bf5dd92c9518ca2a304165806e37c4aa3b14829fbf781286ee185e995e1ce`
- `scripts/audit_axioms.py`: `b01372d4ffa07cc3236ef641cc3beef90d0667ed755103fcee4cc2927d6ee89f`
- `scripts/package_release.py`: `5eae9c77183280e0892ae85a06503eb11018a407fc67a9a3b89e09839bc4638b`
- `validation/final_theorems.json`: `c6f4d4c4d3427e74dbdb578202a88a0afbe137872137b9febbea0669c427865f`
- `validation/round4_nested_endpoints.json`: `ef6a533fff86728b68651a07f96e31cb06064ca20d2215363775ecdecfe3cd98`
- `validation/round4_catalan_endpoints.json`: `e8f3e2fd5c47bf378e8d760ae2e372ccc2f4d98b39b23c41990f6506d177e9c7`
- `validation/round4_exp_cosine_endpoints.json`: `d3c662ff7f4a472bf361317045e346368cdbc225ac279dc2011cff58b4fdc6e7`
- `validation/round4_theta_rational_endpoints.json`: `41f1e5a762e6667d19c1ce2c87ed10011b0ddb23f54cf5bd2f19dd51d34b6780`
- `lean/lakefile.toml`: `824e2b35061ecdfd6c5dc8192d60aa2ed0993b37c9925da99d6f138047d73467`
- `lean/lake-manifest.json`: `bc1a60e6355183dfb8efa78a5d49ddcdf2108c4dbc85a3ab9bcab1904054f3ea`
- `lean/lean-toolchain`: `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea`
- `lean/Round4.lean`: `258bcde6c31ce7319dafff745699fcf9f0a94be9799671665c220c77397f881b`
- `lean/Round4/Contracts.lean`: `a57d84c49003035d7af9030976a532d1bea3732076c8ca7aba184e353f31ed57`
- `lean/ContractChecks.lean`: `152b951d3c77492db7dc49d17f0358ad50c654bcdf2be0aee7f1c956bb22796e`
- `tests/test_validation_requirements.py`: `6d09185a545829b67393d890cd8489825f3ed01727cfd8ada41a16109f12b26f`
