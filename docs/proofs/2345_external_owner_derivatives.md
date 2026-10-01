# 2345 - Interior derivative formula for the external owner

Date: 2026-10-01.

Status: INTERIOR-SECOND-DERIVATIVE-CERTIFIED / ZERO-EXTENSION-OPEN.

Record 2344 proved the symbolic external owner is the same function as correctedPhysical. Record 2345 proves, in Lean, the derivative chain used by the interval evaluator at every strict interior point of each family support.

The proof defines q = 1 - (x / radius)^2, proves q > 0 inside the support, and derives the first and second logarithmic factors and complex phase product. The resulting second derivative is the exact algebraic structure used by the 2342 evaluator.

This result is scoped to strict interior points. At support boundaries and outside the support, the zero extension needs a separate proof through the smooth glued function. That is not claimed here.

Validation:

- Focused Linux Lake build completes 3709 build-plan jobs.
- Ten audited theorem leaves report exactly [propext, Classical.choice, Quot.sound].
- The final build uses explicit unfolding and ring normalization.
- Existing dependency warnings remain; no new source error remains.

Evidence: ConnesWeilRH/Dev/C1RouteAExternalOwnerDerivatives.lean, ConnesWeilRH/Dev/C1RouteAExternalOwnerDerivativesAudit.lean, and build-logs/2345_external_owner_derivatives_build_v2.log.

```text
interior derivative formula              proved in Lean
support-boundary / zero-branch formula   still open
Python interval evaluator equivalence    still open
endpoint numerical inequalities         still external
selected signed-kernel budget            still open
producer GO / RH                         not claimed
```

Next steps:

1. Prove the zero-extension second-derivative statement using the existing expNegInvGlue smoothness and support lemmas.
2. Port the same derivative expression into a checked evaluator contract; show that first, second, and derivative_factor are this formula.
3. Instantiate the endpoint norm certificate and return to the signed detector kernel. Norm bounds control magnitude; the RH route still requires the selected detector's sign.
