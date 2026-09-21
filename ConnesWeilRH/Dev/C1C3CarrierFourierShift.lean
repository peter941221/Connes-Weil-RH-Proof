/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3CarrierTransport
import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerReadback

/-!
# C3' carrier Fourier shift

The Archimedean sigma-floor is a frequency-shift argument.  This file lands
the exact algebraic front of that argument on the same `CompactLogTest`
owner: multiplying by `exp (-i γ x)` shifts the real Fourier frequency by
`γ / (2*pi)`.  No sigma identity or sign estimate is assumed here.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3CarrierTransport

open MeasureTheory
open ConnesWeilRH.Source.C1XiArithmeticPrimePowerReadback
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

noncomputable def c3FourierIntegral
    (f : CompactLogTest) (ξ : Real) : Complex :=
  ∫ x : Real,
    f.test x * Complex.exp
      (-(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I))

noncomputable def c3CarrierFourierIntegral
    (γ : Real) (f : CompactLogTest) (ξ : Real) : Complex :=
  c3FourierIntegral (carrierModulate γ f) ξ

theorem c3FourierIntegral_eq_fourierLaplace
    (f : CompactLogTest) (ξ : Real) :
    c3FourierIntegral f ξ =
      fourierLaplace f.test (-2 * Real.pi * ξ) := by
  unfold c3FourierIntegral fourierLaplace
  apply integral_congr_ae
  filter_upwards with x
  have hphase :
      -(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I) =
        (((-2 * Real.pi * ξ : Real) : Complex) * (x : Complex) * Complex.I) := by
    push_cast
    ring
  rw [hphase]
  ring

theorem c3CarrierFourierIntegral_eq_frequency_shift
    (γ : Real) (f : CompactLogTest) (ξ : Real) :
    c3CarrierFourierIntegral γ f ξ =
      c3FourierIntegral f (ξ + γ / (2 * Real.pi)) := by
  unfold c3CarrierFourierIntegral c3FourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  rw [carrierModulate_apply]
  unfold carrierExp
  have hpi : (Real.pi : Real) ≠ 0 := Real.pi_ne_zero
  have hphase :
      -(((2 * Real.pi * (ξ + γ / (2 * Real.pi)) * x : Real) : Complex) *
          Complex.I) =
        ((-γ * x : Real) : Complex) * Complex.I +
          -(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I) := by
    push_cast
    field_simp [hpi]
    ring
  calc
    Complex.exp (((-γ * x : Real) : Complex) * Complex.I) * f.test x *
          Complex.exp (-(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I)) =
        f.test x * (Complex.exp (((-γ * x : Real) : Complex) * Complex.I) *
          Complex.exp (-(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I))) := by
            ring
    _ = f.test x * Complex.exp
          (((( -γ * x : Real) : Complex) * Complex.I) +
            -(((2 * Real.pi * ξ * x : Real) : Complex) * Complex.I)) := by
            rw [← Complex.exp_add]
    _ = f.test x * Complex.exp
          (-(((2 * Real.pi * (ξ + γ / (2 * Real.pi)) * x : Real) : Complex) *
            Complex.I)) := by
            rw [hphase]

theorem c3CarrierFourierIntegral_zero_frequency_shift
    (γ : Real) (f : CompactLogTest) :
    c3CarrierFourierIntegral γ f 0 =
      c3FourierIntegral f (γ / (2 * Real.pi)) := by
  simpa using c3CarrierFourierIntegral_eq_frequency_shift γ f 0

theorem c3CarrierFourierIntegral_eq_fourierLaplace_shift
    (γ : Real) (f : CompactLogTest) (ξ : Real) :
    c3CarrierFourierIntegral γ f ξ =
      fourierLaplace f.test
        (-2 * Real.pi * (ξ + γ / (2 * Real.pi))) := by
  rw [c3CarrierFourierIntegral_eq_frequency_shift,
    c3FourierIntegral_eq_fourierLaplace]

end C1C3CarrierTransport
end Dev
end ConnesWeilRH
