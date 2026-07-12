/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernel

/-!
# Same-object L2 owner for the ordinary CC20 regular kernel

This file binds the concrete kernel, the real compact coordinate domain, and
the actual square-integrability proof in one data-bearing object. It
deliberately does not claim an integral-operator action or a Hilbert--Schmidt
continuous linear map.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

structure RegularKernelL2Data where
  kernel : ℝ × ℝ → ℝ
  domain : Set (ℝ × ℝ)
  kernel_eq : kernel = cc20RegularKernelReal
  domain_eq : domain = cc20RealSqrtIRectangle
  squareIntegrable : IntegrableOn (fun p => ‖kernel p‖ ^ 2) domain

noncomputable def cc20RegularKernelL2Data : RegularKernelL2Data where
  kernel := cc20RegularKernelReal
  domain := cc20RealSqrtIRectangle
  kernel_eq := rfl
  domain_eq := rfl
  squareIntegrable := integrableOn_cc20RegularKernelReal_sq_sqrtIRectangle

@[simp]
theorem cc20RegularKernelL2Data_kernel :
    cc20RegularKernelL2Data.kernel = cc20RegularKernelReal :=
  cc20RegularKernelL2Data.kernel_eq

@[simp]
theorem cc20RegularKernelL2Data_domain :
    cc20RegularKernelL2Data.domain = cc20RealSqrtIRectangle :=
  cc20RegularKernelL2Data.domain_eq

theorem cc20RegularKernelL2Data_squareIntegrable :
    IntegrableOn
      (fun p => ‖cc20RegularKernelL2Data.kernel p‖ ^ 2)
      cc20RegularKernelL2Data.domain := by
  simpa [cc20RegularKernelL2Data] using
    integrableOn_cc20RegularKernelReal_sq_sqrtIRectangle

theorem cc20RegularKernelL2Data_hasFiniteSquareIntegral :
    HasFiniteIntegral
      (fun p => ‖cc20RegularKernelL2Data.kernel p‖ ^ 2)
      (volume.restrict cc20RegularKernelL2Data.domain) := by
  exact cc20RegularKernelL2Data_squareIntegrable.hasFiniteIntegral

end CC20Concrete
end Source
end ConnesWeilRH
