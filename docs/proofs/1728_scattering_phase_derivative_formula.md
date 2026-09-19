# 1728 — Exact derivative formula for the scattering phase

## Result

The new theorem `deriv_ccm24ArchimedeanScatteringPhase_formula` proves the
exact real derivative of the committed scattering quotient:

```text
phase' = (factor' * conj factor - factor * conj factor') / (conj factor)^2.
```

The proof uses the real-linear conjugation equivalence and the previously
formalized differentiability and nonvanishing of the Gamma factor. No
Stirling estimate, derivative-growth bound, or unproved analytic input is
introduced.

## Route meaning

This is the smallest useful bridge from the formal C1 multiplier interface to
the future second-derivative/integrability estimate needed by S3. It does not
identify the L2 Hardy output with the selected Schwartz core and does not prove
the cutoff-uniform kernel-diagonal majorant. The healthy CompactLog B5 route
therefore remains open at that quantitative analytic producer.

## Acceptance

The paired Audit leaf prints the new theorem and its axioms. The focused WSL
build completed successfully (2964 jobs), with zero `error:` and zero
`sorryAx`; the only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
