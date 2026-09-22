# 1875 - Explicit taper owner zero-order seminorm bridge

Date: 2026-09-23.

Status: Formally verified in Lean; explicit-owner seminorm bridge.

The theorem `windowTaperCorrection_seminorm_zero_zero_le` proves that the
explicit smooth taper owner satisfies

```text
seminorm(0,0, taperCorrection)
  <= ||coeff|| * windowTaperBound(a,b,nodes).
```

The proof uses the support of the taper, the pointwise bounds `0 <= tau <= 1`,
and the existing uniform representer estimate.  It connects the Gram-selected
owner to the zero-order seminorm language used by the geometric contraction
consumer.

Verification: WSL focused build `taper-seminorm-1875d.log`; successful footer
for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired Audit
declaration uses only `[propext, Classical.choice, Quot.sound]`.

This does not bound the Gram inverse coefficient vector, establish a strict
budget, prove detector-specific semi-local positivity, or prove RH.
