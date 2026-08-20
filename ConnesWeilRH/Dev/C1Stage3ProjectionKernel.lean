/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport

/-!
# C1 Stage-3 projection kernel (active namespace)

The Stage-3 same-owner positive-square producer needs a genuinely positive
operator on the common logarithmic carrier `cc20GlobalLogCrossingL2` whose
finite-window trace can be read back to `C1SameOwnerWeil.qw g`.  The most
promising candidate is a projection square

```text
K_S = P_radial · P_semilocal(S) · P_radial − Gram_Sonin   (>= 0)
A_g,n = C_{g,n}† ∘ K_S^{1/2}        so that A_g,n ∘ A_g,n† ... reads Tr(A_g,n†A_g,n).
```

This module isolates the **positive core** `K_S` in the active C1 namespace by
reusing the concrete CCM24 positivity brick directly, instead of pulling in the
frozen Gate-3U residual ledger (`CCM24FiniteSProjectionTrace.sameObjectResidual`,
whose trace-class status alone does not force its trace to vanish).

Scope guard: this file proves the positive core `K_S.IsPositive` (Gate 0) and, as
Gate 1, that conjugating `K_S` by any bounded factor stays positive
(`stage3ProjectionKernel_adjointConj_isPositive`).  It does NOT yet assert the same-owner
trace readback to `qw g`, nor any remainder limit.  Those are Gates 2-4 of docs/1039.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3ProjectionKernel

open CC20Concrete

noncomputable section

/-- The Stage-3 positive projection kernel on the common logarithmic carrier:
the semilocal Fourier-support compression, minus the gram-corrected target Sonin
projection.  This is exactly the operator whose positivity is already established
concretely in `CCM24SemilocalFourierSupport`. -/
noncomputable def stage3ProjectionKernel
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
      (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection ∘L
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection -
    (concreteCCM24SoninTransportData lambda S).gramCorrectedTargetSoninProjection)

/-- The positive core of the Stage-3 candidate is genuinely positive.  This is a
delegation to the concrete CCM24 brick; it is non-circular because that brick does
not reference `C1SameOwnerWeil.qw` or any RH-facing statement. -/
theorem stage3ProjectionKernel_isPositive
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (stage3ProjectionKernel lambda S).IsPositive := by
  simpa only [stage3ProjectionKernel] using
    concreteCCM24_target_compression_sub_gramCorrected_isPositive lambda S

/-- Gate 1 (operator identity / algebraic backbone of the projection-square route):
conjugating the positive Stage-3 kernel by any bounded finite-window factor `C` keeps the
resulting operator positive on the source space.  Concretely, for the same owner and a
finite-window factor `C : H → cc20GlobalLogCrossingL2`,

```text
C † ∘ K_S ∘ C   is IsPositive on H      (self-adjoint + nonnegative quadratic form)
```

This is what makes `C† K_S C` a legitimate positive-trace target for an *arbitrary*
factor, before any remainder estimate.  It is pure algebra: it reuses the mathlib fact that
a positive operator stays positive under adjoint conjugation (`IsPositive.adjoint_conj`).
If this failed at the algebra level, the projection-square candidate would be dead on
arrival (doc 1039, Gate 1). -/
theorem stage3ProjectionKernel_adjointConj_isPositive
    {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : H →L[ℂ] cc20GlobalLogCrossingL2)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (C.adjoint ∘L stage3ProjectionKernel lambda S ∘L C).IsPositive := by
  exact ContinuousLinearMap.IsPositive.adjoint_conj
    (stage3ProjectionKernel_isPositive lambda S) C

end
end C1Stage3ProjectionKernel
end Source
end ConnesWeilRH
