# 2219 — Binary64 exp-cell scope no-go

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector and its actual-owner
same-owner `qw >= 0` producer. This probe targets only the machine-semantics
sub-obligation beneath the 2218 relative-error interface.

An exact-Fraction Taylor certificate was constructed for three representative
exponent atoms on the 2217 binding node (families 0, 15, and 29; central GL
point). Each real and imaginary component was compared with the exact
midpoint cell between adjacent binary64 values around NumPy's returned value.

```text
atoms checked                         3
component containment                 5 / 6
scoped failure                        family 0, imaginary component
q_real                                -2111062323327249/70368744177664
q_imag                                -5582445713859697/2361183241434822606848
```

The exact interval arithmetic itself completed; the failure is not a Taylor
timeout. It shows that the hypothesis “NumPy complex `exp` is the correctly
rounded binary64 value of mathematical `exp`” is too strong for this atom.
The result is a scoped no-go for the rounding-cell-only assembly, not a
no-go for the exponential function or for the RH route. The real channel and
the other two atoms passed.

Status: `NUMPY-EXP-CELL-ONLY-SCOPED-NO-GO`.
Reopen only with a certified implementation remainder for the transcendental
library call or a correctly-rounded MPFR/binary64 backend. The input exponent
construction, finite summation, complete-owner transfer, and signed producer
margin remain open.

Artifacts:

- `results/2219_binary64_exp_atom.json`
- `results/20260929_2219_binary64_exp_atom_pass4.log`
- script: `scripts/routea_weighted_zero_binary64_exp_atom_2219.py`
