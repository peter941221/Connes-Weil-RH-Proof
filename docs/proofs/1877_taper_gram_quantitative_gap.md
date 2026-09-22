# 1877 - Taper Gram quantitative spectral gap

Date: 2026-09-23.

Status: Formally verified in Lean; qualitative taper gap upgraded to a
strict quantitative lower bound.

The new declarations in `C1WindowTaperLift.lean` are:

- `windowTaperGram_energy_smul`, the real-scalar homogeneity of the tapered
  quadratic;
- `windowTaperGram_energy_continuous`, continuity in the coefficient vector;
- `windowTaperGram_energy_strict_pos`, strict positivity from a nonnegative
  taper that equals one on a nonempty sub-window;
- `windowTaperGram_gap`, the sphere-minimum argument producing `alpha > 0`
  with `alpha * ||v||^2 <= Re(<v, T v>)` for every coefficient vector.

The strict branch uses the existing same-owner exponential independence
theorem on the taper-one sub-window.  The gap is therefore not a numerical
claim and does not assume a Friedrichs estimate or a precomputed eigenvalue.

Verification: WSL focused build `taper-gap-20260923b.log` and paired Audit
build `taper-gap-audit-20260923.log`; both completed successfully with zero
`error:` lines and zero `sorryAx`.  The audited declarations use only
`[propext, Classical.choice, Quot.sound]`.

This closes the taper-Gram gap interface but does not yet bound the inverse
coefficient vector by the strict contraction budget.  Detector-specific
semi-local positivity and RH remain open.
