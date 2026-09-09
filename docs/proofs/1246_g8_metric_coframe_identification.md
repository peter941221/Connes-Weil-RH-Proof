# Proof 1246 — G8 metric-coframe identification

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

The source compression of the G8 adjoint-shear Gram is exactly the existing
metric-coframe Gram.  Writing

```text
J = sourceInclusion,   L = sourcePhysicalCoframeLeakage,
N = finiteEulerPulledObliqueShear,   W = detectorOperator,
```

the previously proved identities give `N = J L†` and `J†J = I`.  Hence

```text
(I + N†) J = J + L = finiteEulerMetricCoframe,
```

and therefore

```text
J† G8 J = (finiteEulerMetricCoframe)† W
          (finiteEulerMetricCoframe).
```

This is a formal structural identity, not a `qw` readback, a cutoff-limit
theorem, or a finite-visible-prime sign result.  It does not by itself kill
G8, but it removes the claim that G8 supplies a new source-side kernel: its
four-channel completion is the existing coframe Gram written in shear form.
The admissible next question is whether a finite-window/internal counterterm
built from this same owner has the required `qw` readback and finite-prime
positivity.

Audit evidence: `/home/peter/rh/build-logs/1246_g8_metric_coframe_final.log`.
The owning module and audit build completed successfully with standard axioms
only and no `error:` or `sorryAx`.

RH is not claimed.
