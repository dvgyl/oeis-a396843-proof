# Attribution for the Stirling helper

`lean/More/StirlingNumbers.lean` adapts the second-kind Stirling-number definitions
and the descending-factorial power-expansion proof from the Mathlib module
`Mathlib.Combinatorics.Enumerative.Stirling` at commit
`4ed598f443601d8b5abccc2a14e3ba408ae47056`.

Original source:
https://github.com/leanprover-community/mathlib4/blob/4ed598f443601d8b5abccc2a14e3ba408ae47056/Mathlib/Combinatorics/Enumerative/Stirling.lean

Original copyright: Copyright (c) 2025 Beibei Xiong. All rights reserved.

Original authors: Beibei Xiong, Yu Shao, Weijie Jiang, Zhengfeng Yang.

Original license: Apache License, Version 2.0. Its full text is included as
`Apache-2.0.txt` in this directory. This adapted source file remains subject to
that license, irrespective of the license applied to other original files in
this package.

Changes made by OpenAI ChatGPT for Dev Goyal on 24 October 2026:

- Retained only the needed second-kind Stirling recurrence and lemmas.
- Changed the namespace to `More.Stirling` and renamed declarations to avoid
  depending on a Mathlib module absent from the pinned Lean 4.19 library.
- Adapted the proof syntax and imports to the older pinned library.
- Supplied `descFactorial_mul_self`, a compatibility lemma missing there.
- Added the truncated binomial-coefficient form `power_expansion_choose`.

The generic modular column-transfer and transform proofs in
`More/StirlingTransform.lean`, the source-specific definitions, and the
periodicity endpoints were generated in this development. The mathematical
periodicity theorem itself is already known: see the attribution to Payam Danesh
and Benjamin Schreyer in `docs/STIRLING_PERIODICITY.md`. The AI contribution
statement does not claim authorship of the upstream Mathlib code or original
priority for known mathematics.
