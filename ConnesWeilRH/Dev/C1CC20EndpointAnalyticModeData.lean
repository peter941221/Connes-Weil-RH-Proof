/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20EndpointSpectralOwnerGuard

/-!
# Genuine derivative ownership for the CC20 endpoint modes

The equation-(99) series uses both an analytic mode and its derivative.  This
leaf adds the first indispensable analytic law: the stored derivative really
is the derivative of the stored mode at every real point.  It then proves
that this law removes the arbitrary replacement exposed by
`C1CC20EndpointSpectralOwnerGuard`.

This is deliberately weaker than a full prolate realization.  The truncated
Fourier eigenrelation, orthonormality, completeness, and convergence laws are
still separate mathematical obligations; endpoint positivity is not stored
as data.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointAnalyticModeData

open CC20Concrete
open C1CC20EndpointSpectralOwnerGuard

/-- Spectral formula data whose purported derivatives are genuine derivatives.

This is the minimum honest owner needed before differentiating or integrating
the equation-(99) modes. -/
structure CC20EndpointAnalyticModeData where
  spectral : CC20EndpointSpectralData
  analyticMode_hasDerivAt : forall n x,
    HasDerivAt (spectral.analyticMode n) (spectral.analyticModeDeriv n x) x

/-- A real function has at most one derivative at a point.  Consequently two
honest owners over the same modes cannot disagree in their derivative field. -/
theorem analyticModeDeriv_eq_of_hasDerivAt
    (data : CC20EndpointSpectralData)
    (deriv : Nat -> Real -> Real)
    (hdata : forall n x,
      HasDerivAt (data.analyticMode n) (data.analyticModeDeriv n x) x)
    (hderiv : forall n x,
      HasDerivAt (data.analyticMode n) (deriv n x) x) :
    deriv = data.analyticModeDeriv := by
  funext n x
  exact (hderiv n x).unique (hdata n x)

/-- Replacing the derivative field preserves genuine derivative ownership if
and only if the replacement is pointwise the original derivative. -/
theorem replaceAnalyticModeDeriv_hasDerivAt_iff
    (owner : CC20EndpointAnalyticModeData)
    (deriv : Nat -> Real -> Real) :
    (forall n x,
      HasDerivAt
        ((replaceAnalyticModeDeriv owner.spectral deriv).analyticMode n)
        ((replaceAnalyticModeDeriv owner.spectral deriv).analyticModeDeriv n x)
        x) ↔
      deriv = owner.spectral.analyticModeDeriv := by
  constructor
  · intro h
    apply analyticModeDeriv_eq_of_hasDerivAt owner.spectral deriv
      owner.analyticMode_hasDerivAt
    simpa only [replaceAnalyticModeDeriv_analyticMode,
      replaceAnalyticModeDeriv_deriv] using h
  · intro h
    subst deriv
    simpa only [replaceAnalyticModeDeriv_analyticMode,
      replaceAnalyticModeDeriv_deriv] using owner.analyticMode_hasDerivAt

/-- In particular, a genuinely different derivative replacement cannot form
an analytic-mode owner.  This is the negative guard missing from the formula
layer. -/
theorem not_hasDerivAt_replaceAnalyticModeDeriv_of_ne
    (owner : CC20EndpointAnalyticModeData)
    (deriv : Nat -> Real -> Real)
    (hne : deriv ≠ owner.spectral.analyticModeDeriv) :
    ¬ (forall n x,
      HasDerivAt
        ((replaceAnalyticModeDeriv owner.spectral deriv).analyticMode n)
        ((replaceAnalyticModeDeriv owner.spectral deriv).analyticModeDeriv n x)
        x) := by
  intro h
  exact hne ((replaceAnalyticModeDeriv_hasDerivAt_iff owner deriv).mp h)

end C1CC20EndpointAnalyticModeData
end Source
end ConnesWeilRH
