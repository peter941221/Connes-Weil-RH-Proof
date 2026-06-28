/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm

/-!
# CCM25 fixed-lambda finite-prime certificate

This module combines two separate finite-prime obligations:

* source prime-power support at one fixed `lambda`;
* pointwise finite-prime atom normalization.

The result is still fixed-`lambda`. It does not prove the broader
`forall lambda` source interface.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeCertificate

structure FixedLambdaFinitePrimeCertificate
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  support :
    PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda W f g lambda
  terms : PrimePowerTerm.SourcePrimePowerTermNormalization W f g

def source_prime_power_support_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportAtLambda W f g lambda :=
  PrimePowerSupport.source_prime_power_support_of_skeleton h.support
    (PrimePowerTerm.finite_prime_term_normalization_of_source_terms h.terms)

def exact_support_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  PrimePowerSupport.exact_support_of_source_prime_power_support
    (source_prime_power_support_of_certificate h)

theorem visibility_at_lambda_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement W f g lambda :=
  FinitePrimeExact.visibility_at_lambda_of_exact_support
    (exact_support_of_certificate h)

end FinitePrimeCertificate
end CCM25Concrete
end Source
end ConnesWeilRH
