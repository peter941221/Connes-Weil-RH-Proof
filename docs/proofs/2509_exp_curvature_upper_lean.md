# Record 2509 — exponential upper propagation

The 2509 Lean lemma turns one inequality
`exp (-x) ≤ upper` into the three nonnegative slot inequalities needed by
`weightedCurvature2348`: value, first-factor, and second-factor slots.  It
removes that repeated algebra from each future hcell proof.

It is an analytic interface only; it does not assert the 2501 table entries or
close the hcell margin.
