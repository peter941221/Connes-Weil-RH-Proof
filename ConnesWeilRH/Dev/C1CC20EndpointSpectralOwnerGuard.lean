/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.EndpointKernelFormula

/-!
# Guard: endpoint derivative data needs analytic ownership

The current formula owner stores the mode derivative independently of the
mode.  This leaf makes that freedom explicit.  Any proof of the endpoint sign
must first add the prolate derivative/eigenfunction laws; it cannot infer them
from `CC20EndpointSpectralData` as currently defined.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointSpectralOwnerGuard

open CC20Concrete

/-- Replace every purported mode derivative without changing any field used
to certify the eigenvalues, endpoint slope, or its convergent spectral sum. -/
noncomputable def replaceAnalyticModeDeriv
    (data : CC20EndpointSpectralData)
    (deriv : Nat -> Real -> Real) : CC20EndpointSpectralData where
  eigenvalue := data.eigenvalue
  analyticMode := data.analyticMode
  analyticModeDeriv := deriv
  endpointSlope := data.endpointSlope
  eigenvalue_sq_lt_one := data.eigenvalue_sq_lt_one
  endpointSlope_summable := data.endpointSlope_summable
  endpointSlope_eq_spectral := data.endpointSlope_eq_spectral
  endpointSlope_pos := data.endpointSlope_pos

@[simp] theorem replaceAnalyticModeDeriv_eigenvalue
    (data : CC20EndpointSpectralData) (deriv : Nat -> Real -> Real) :
    (replaceAnalyticModeDeriv data deriv).eigenvalue = data.eigenvalue := rfl

@[simp] theorem replaceAnalyticModeDeriv_analyticMode
    (data : CC20EndpointSpectralData) (deriv : Nat -> Real -> Real) :
    (replaceAnalyticModeDeriv data deriv).analyticMode = data.analyticMode := rfl

@[simp] theorem replaceAnalyticModeDeriv_endpointSlope
    (data : CC20EndpointSpectralData) (deriv : Nat -> Real -> Real) :
    (replaceAnalyticModeDeriv data deriv).endpointSlope = data.endpointSlope := rfl

@[simp] theorem replaceAnalyticModeDeriv_deriv
    (data : CC20EndpointSpectralData) (deriv : Nat -> Real -> Real) :
    (replaceAnalyticModeDeriv data deriv).analyticModeDeriv = deriv := rfl

end C1CC20EndpointSpectralOwnerGuard
end Source
end ConnesWeilRH

