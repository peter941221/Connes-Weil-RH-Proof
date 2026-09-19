# 1732 — Critical Mellin first-derivative Fourier-L2 consumer

## Result

The concrete first-derivative profile is now an `Integrable` function, is
differentiable, and has an integrable derivative supplied by the formal
second-derivative majorant from record 1731.  The existing Sobolev consumer
therefore proves
`memLp_two_fourier_ccm24CriticalMellinLogProfileFirstDerivFormula`.

## Route meaning

This closes the concrete Schwartz-core Fourier-L2 consumer needed by the
quadratic tail-rate route. It still does not identify the arbitrary
source-carrier Hardy output with this concrete profile, nor does it provide
the cutoff-uniform kernel-diagonal estimate. S3 and RH remain open at that
operator-level transfer.

## Acceptance

The paired Audit leaf prints the new Fourier-L2 theorem and its axioms. The
focused build completed successfully (2967 jobs), with zero `error:` and zero
`sorryAx`; only `propext`, `Classical.choice`, and `Quot.sound` occur.
