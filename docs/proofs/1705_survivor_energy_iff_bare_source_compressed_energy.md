# Record 1705 — survivor energy reduces to the bare source-compressed detector

## Result

The new theorem

`g8SurvivorCoframe_energy_iff_bareSourceCompressed_energy`

proves, on every named source Hilbert basis and every finite visible-prime
family, that the survivor coframe diagonal square-sum is equivalent to the
uncoframed source-compressed square-sum:

`sum ||C (survivorCoframe e_i)||^2 < infinity`

if and only if

`sum ||J† C J e_i||^2 < infinity`.

## Proof mechanism

Record 1704 supplies that the source-side Schur leg `s_S` is an `IsUnit`.
The generic `summable_normSq_comp_iff_of_isUnit` lemma applies the existing
bounded-precomposition Hilbert–Schmidt transport in both directions, using
the explicit bounded inverse supplied by `IsUnit`.
The earlier Pythagoras and selected-root leakage consumer already equate the
coframed energy with the in-Sonin leg after `s_S`; composing the two facts
removes `s_S` exactly.

## Route effect

WO-S/S3 is now in its sharpest normal form: the only remaining analytic
producer is square-summability of the bare source-compressed detector
`J† C J` on the healthy `CompactLog` owner. No Schur transport estimate,
coframe estimate, or inverse-Gram estimate remains. This is a formal
reduction, not an S3 closure and not an RH claim.

Classification: formal, machine-checked reduction.
