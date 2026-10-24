# Exact finite verification

The program `scripts/verify_coefficients.py` uses only the Python standard library. It constructs integer coefficients from the two defining equations, before comparing any coefficient with a claimed residue formula.

For the r-family, the coefficient of degree `n` in `F^(circ r) * F^(circ(r+1))` uses only earlier coefficients of `F`; this determines the next coefficient directly. For the q-family, temporarily setting the next coefficient to zero leaves a residual in `G(X-X*L_q(G))`; negating that residual gives the next coefficient because its leading multiplier is one. Neither construction uses the candidate rational reduction or the power-of-two parity pattern.

## Commands

From the package root:

```sh
python3 -m unittest discover -s tests -p 'test_verify_coefficients.py'
python3 scripts/verify_coefficients.py --terms 40 --output reproducibility/coefficients_40.json
```

The first command runs seven unit tests covering exact multiplication, composition orientation, invalid formal substitution, independent source prefixes for both families, a small end-to-end verification, and invalid parameter ranges.

The second command checks degrees zero through 40 with parameters `r=1,...,8` and `q=1,...,8`. For each `r`, it checks all natural iterate indices from zero through `2*r+2`; it also includes every iterate needed by the defining equation and the named OEIS assertions. The report records the actual index range, the number of individual coefficient checks, the script hash, hashes of the constructed coefficient lists, source-prefix matches, and elapsed time.

For a smaller targeted run:

```sh
python3 scripts/verify_coefficients.py --terms 20 --r 2,4,5 --q 4,5,6,7 --iterate-max 12
```

Without `--output`, the full JSON report is printed. A failed comparison returns a nonzero exit status. The program uses explicit exceptions, so Python's `-O` option cannot disable its checks.

## Checks included

- The exact r-family equation through the requested degree.
- The general r-family formula for every natural iterate within the recorded finite range.
- All four named A396099 consequences, including the initial terms of the cancellation identity.
- A396798's seven iterate consequences, the corrected period beginning at index two, and the exact third coefficient nine that refutes the source's stated phase.
- A396807's coefficient congruence and natural-iterate cases within the checked range.
- The exact q-family equation and its reverse inverse identity.
- The congruence modulo `q+1` for all checked positive indices.
- The complete parity pattern in the checked range, covering the two original q-family parity conjectures at parameters four and six.
- Eight initial coefficients from each of the eight mapped OEIS entries.

The finite report does not certify a statement for every index, test negative composition iterates, establish priority, or establish that Lean compiled. Those are separate matters. The manuscript supplies all-index mathematical proofs; the formal coverage report records machine-checked statements.
