# Record 3201: owner support zero-extension

This record closes the support part of the 3200 window mismatch.

The Lean theorem `correctedPhysical_eq_zero_of_abs_ge_ownerRadius3201` proves
that the same-owner corrected physical family is exactly zero whenever
`storedWidth 4 ^ 2 <= |position|`. The proof uses the stored support ordering:
all non-owner squared widths are at most `6`, while owner family 4 has squared
width strictly greater than `6`.

The theorem `ownerRadius_lt_diagnosticRadius3201` proves that the Python
Taylor-6 diagnostic radius `65536001 / 10000000` is larger than the exact Lean
owner radius. Consequently, the extra outer region is pointwise zero for the
owner family. The theorem does not yet prove equality of interval integrals;
that next bridge must supply interval integrability and split the two outer
intervals with `intervalIntegral.integral_add_adjacent_intervals`.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAOwnerWindowZeroExtension3201.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerWindowZeroExtension3201Audit.lean`
- `build-logs/3201_wsl_build_target.log`
- `build-logs/3201_wsl_audit.log`

The WSL gate used `leanprover/lean4:v4.30.0` and Lean `4.30.0`. The audited
leaves use exactly `[propext, Classical.choice, Quot.sound]`. This remains a
support bridge only: no JSONL import, producer certificate, `SourceRH`, or RH
claim is established.