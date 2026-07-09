/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCoreBase

/-!
# Shared source analytic core

This module introduces the common source-facing analytic objects needed by the
CCM24, CCM25, and CC20 source-model discharges.  The shared route-level
`TestFunction` is Mathlib's Schwartz space on `ℝ` with complex values; the
`LegacyTestEquiv` field keeps source-specific test objects aligned with that
carrier while downstream theorem rows are drilled to concrete semantics.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open scoped ArithmeticFunction

namespace SourceSupportWindowData

def soninSpaceComparison
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Prop :=
  S.supportCarrier S.sourceTest ⊆ S.windowCarrier I ∧
    S.fourierSupportCarrier S.sourceTest ⊆ S.windowCarrier I

@[simp] theorem soninSpaceComparison_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.soninSpaceComparison I ↔
      S.supportCarrier S.sourceTest ⊆ S.windowCarrier I ∧
        S.fourierSupportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  Iff.rfl

theorem soninSpaceComparison_of_subsets
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSupport : S.supportCarrier S.sourceTest ⊆ S.windowCarrier I)
    (hFourier : S.fourierSupportCarrier S.sourceTest ⊆
      S.windowCarrier I) :
    S.soninSpaceComparison I :=
  ⟨hSupport, hFourier⟩

theorem supportCarrier_subset_windowCarrier_of_soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSonin : S.soninSpaceComparison I) :
    S.supportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  hSonin.1

theorem fourierSupportCarrier_subset_windowCarrier_of_soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSonin : S.soninSpaceComparison I) :
    S.fourierSupportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  hSonin.2

theorem supportInWindow_of_soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSonin : S.soninSpaceComparison I) :
    S.supportInWindow S.sourceTest I :=
  hSonin.1

theorem fourierSupportInWindow_of_soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSonin : S.soninSpaceComparison I) :
    S.fourierSupportInWindow S.sourceTest I :=
  hSonin.2

structure SourceSupportCoordinateScaleModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  supportKernel : A.Test → ℝ × ℝ → ℝ
  supportValue_eq_kernel :
    ∀ (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x =
        supportKernel f
          (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate
              x I,
            S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
  supportFootprint : A.Test → Set (ℝ × ℝ)
  kernel_ne_zero_mem_footprint :
    ∀ (f : A.Test) (z : ℝ × ℝ),
      supportKernel f z ≠ 0 → z ∈ supportFootprint f
  footprint_coordinateLower :
    ∀ (f : A.Test) (z : ℝ × ℝ),
      z ∈ supportFootprint f →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          z.1
  footprint_coordinateUpper :
    ∀ (f : A.Test) (z : ℝ × ℝ),
      z ∈ supportFootprint f →
        z.1 ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I
  footprint_logScale_eq_zero :
    ∀ (f : A.Test) (z : ℝ × ℝ),
      z ∈ supportFootprint f → z.2 = 0

def closedWindowZeroSet
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set (ℝ × ℝ) :=
  {z |
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        z.1 ∧
      z.1 ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I ∧
      z.2 = 0}

noncomputable def closedWindowZeroKernel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (rawKernel : A.Test → ℝ × ℝ → ℝ)
    (f : A.Test) (z : ℝ × ℝ) : ℝ :=
  by
    classical
    exact if z ∈ closedWindowZeroSet S I then rawKernel f z else 0

structure SourceSupportClosedWindowZeroKernelModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  rawSupportKernel : A.Test → ℝ × ℝ → ℝ
  supportValue_eq_cutoffKernel :
    ∀ (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x =
        closedWindowZeroKernel S I rawSupportKernel f
          (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate
              x I,
            S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)

namespace SourceSupportClosedWindowZeroKernelModel

noncomputable def supportKernel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) : ℝ :=
  closedWindowZeroKernel S I M.rawSupportKernel f z

def supportFootprint
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) : Set (ℝ × ℝ) :=
  {z | M.supportKernel f z ≠ 0}

theorem mem_supportFootprint_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ} :
    z ∈ M.supportFootprint f ↔ M.supportKernel f z ≠ 0 := by
  rfl

theorem supportFootprint_eq_setOf_supportKernel_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) :
    M.supportFootprint f = {z | M.supportKernel f z ≠ 0} := by
  rfl

theorem supportKernel_ne_zero_mem_supportFootprint
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : M.supportKernel f z ≠ 0) :
    z ∈ M.supportFootprint f := by
  exact hz

theorem mem_closedWindowZeroSet_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {z : ℝ × ℝ} :
    z ∈ closedWindowZeroSet S I ↔
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          z.1 ∧
        z.1 ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I ∧
        z.2 = 0 :=
  Iff.rfl

theorem closedWindowZeroSet_mk
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {z : ℝ × ℝ}
    (hLower :
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        z.1)
    (hUpper :
      z.1 ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : z.2 = 0) :
    z ∈ closedWindowZeroSet S I :=
  ⟨hLower, hUpper, hLog⟩

theorem closedWindowZeroSet_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {z : ℝ × ℝ}
    (hz : z ∈ closedWindowZeroSet S I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      z.1 :=
  hz.1

theorem closedWindowZeroSet_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {z : ℝ × ℝ}
    (hz : z ∈ closedWindowZeroSet S I) :
    z.1 ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  hz.2.1

theorem closedWindowZeroSet_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {z : ℝ × ℝ}
    (hz : z ∈ closedWindowZeroSet S I) :
    z.2 = 0 :=
  hz.2.2

theorem supportKernel_eq_raw_of_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : z ∈ closedWindowZeroSet S I) :
    M.supportKernel f z = M.rawSupportKernel f z := by
  simp [supportKernel, closedWindowZeroKernel, hz]

theorem supportKernel_eq_zero_of_not_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : z ∉ closedWindowZeroSet S I) :
    M.supportKernel f z = 0 := by
  simp [supportKernel, closedWindowZeroKernel, hz]

theorem supportKernel_eq_ite
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) : by
      classical
      exact M.supportKernel f z =
        if z ∈ closedWindowZeroSet S I then M.rawSupportKernel f z else 0 := by
  rfl

theorem supportKernel_eq_zero_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) :
    M.supportKernel f z = 0 ↔
      z ∉ closedWindowZeroSet S I ∨ M.rawSupportKernel f z = 0 := by
  classical
  by_cases hz : z ∈ closedWindowZeroSet S I
  · simp [supportKernel, closedWindowZeroKernel, hz]
  · simp [supportKernel, closedWindowZeroKernel, hz]

theorem supportKernel_ne_zero_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) :
    M.supportKernel f z ≠ 0 ↔
      z ∈ closedWindowZeroSet S I ∧ M.rawSupportKernel f z ≠ 0 := by
  classical
  by_cases hz : z ∈ closedWindowZeroSet S I
  · simp [supportKernel, closedWindowZeroKernel, hz]
  · simp [supportKernel, closedWindowZeroKernel, hz]

theorem supportKernel_ne_zero_of_mem_raw_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hzMem : z ∈ closedWindowZeroSet S I)
    (hzRaw : M.rawSupportKernel f z ≠ 0) :
    M.supportKernel f z ≠ 0 := by
  exact (M.supportKernel_ne_zero_iff f z).2 ⟨hzMem, hzRaw⟩

theorem rawSupportKernel_ne_zero_of_supportKernel_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : M.supportKernel f z ≠ 0) :
    M.rawSupportKernel f z ≠ 0 := by
  exact (M.supportKernel_ne_zero_iff f z).1 hz |>.2

theorem supportKernel_ne_zero_closedWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : M.supportKernel f z ≠ 0) :
    z ∈ closedWindowZeroSet S I := by
  exact (M.supportKernel_ne_zero_iff f z).1 hz |>.1

theorem supportKernel_eq_raw_iff_mem_or_raw_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) :
    M.supportKernel f z = M.rawSupportKernel f z ↔
      z ∈ closedWindowZeroSet S I ∨ M.rawSupportKernel f z = 0 := by
  classical
  by_cases hz : z ∈ closedWindowZeroSet S I
  · simp [supportKernel, closedWindowZeroKernel, hz]
  · simp only [supportKernel, closedWindowZeroKernel, hz, if_false, false_or]
    exact eq_comm

theorem supportKernel_eq_raw_of_raw_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : M.rawSupportKernel f z = 0) :
    M.supportKernel f z = M.rawSupportKernel f z := by
  exact (M.supportKernel_eq_raw_iff_mem_or_raw_zero f z).2 (Or.inr hz)

theorem mem_closedWindowZeroSet_of_supportKernel_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : M.supportKernel f z ≠ 0) :
    z ∈ closedWindowZeroSet S I := by
  by_contra hNot
  exact hz (M.supportKernel_eq_zero_of_not_mem hNot)

theorem supportFootprint_subset_closedWindowZeroSet
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) :
    M.supportFootprint f ⊆ closedWindowZeroSet S I := by
  intro z hz
  exact M.mem_closedWindowZeroSet_of_supportKernel_ne_zero hz

theorem supportFootprint_mem_iff_closedWindow_raw_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (z : ℝ × ℝ) :
    z ∈ M.supportFootprint f ↔
      z ∈ closedWindowZeroSet S I ∧ M.rawSupportKernel f z ≠ 0 := by
  exact M.supportKernel_ne_zero_iff f z

theorem supportFootprint_subset_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) :
    M.supportFootprint f ⊆
      {z | S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤ z.1} := by
  intro z hz
  exact closedWindowZeroSet_lower
    (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportFootprint_subset_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) :
    M.supportFootprint f ⊆
      {z | z.1 ≤ S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I} := by
  intro z hz
  exact closedWindowZeroSet_upper
    (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportFootprint_subset_logZero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) :
    M.supportFootprint f ⊆ {z | z.2 = 0} := by
  intro z hz
  exact closedWindowZeroSet_logScale_eq_zero
    (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportFootprint_coordinateLower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : z ∈ M.supportFootprint f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      z.1 :=
  closedWindowZeroSet_lower (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportFootprint_coordinateUpper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : z ∈ M.supportFootprint f) :
    z.1 ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  closedWindowZeroSet_upper (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportFootprint_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    {f : A.Test} {z : ℝ × ℝ}
    (hz : z ∈ M.supportFootprint f) :
    z.2 = 0 :=
  closedWindowZeroSet_logScale_eq_zero
    (M.supportFootprint_subset_closedWindowZeroSet f hz)

theorem supportValue_eq_supportKernel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I)
    (f : A.Test) (x : S.SupportPoint) :
    S.supportValue f x =
      M.supportKernel f
        (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate
            x I,
          S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x) := by
  exact M.supportValue_eq_cutoffKernel f x

noncomputable def toCoordinateScaleModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportClosedWindowZeroKernelModel S I) :
    SourceSupportCoordinateScaleModel S I where
  supportKernel := M.supportKernel
  supportValue_eq_kernel := M.supportValue_eq_supportKernel
  supportFootprint := M.supportFootprint
  kernel_ne_zero_mem_footprint := by
    intro f z hz
    exact hz
  footprint_coordinateLower := by
    intro f z hz
    exact M.supportFootprint_coordinateLower hz
  footprint_coordinateUpper := by
    intro f z hz
    exact M.supportFootprint_coordinateUpper hz
  footprint_logScale_eq_zero := by
    intro f z hz
    exact M.supportFootprint_logScale_eq_zero hz

noncomputable def concreteBaseLayer
    (I : SourceConcreteBaseLayer.ConcreteWindow)
    (sourceTest : SourceConcreteBaseLayer.ConcreteTest :=
      SourceConcreteBaseLayer.defaultSourceTest) :
    SourceSupportClosedWindowZeroKernelModel
      (SourceConcreteBaseLayer.concreteSupportWindowData I sourceTest) I where
  rawSupportKernel := SourceConcreteBaseLayer.concreteRawSupportKernel
  supportValue_eq_cutoffKernel := by
    intro f x
    classical
    by_cases hx : SourceConcreteBaseLayer.pointInConcreteWindow I x
    · have hcond : I.1 ≤ x.1 ∧ x.1 ≤ I.2 ∧ x.2 = 0 := by
        simpa [SourceConcreteBaseLayer.pointInConcreteWindow] using hx
      simp [closedWindowZeroKernel, closedWindowZeroSet,
        SourceConcreteBaseLayer.concreteSupportWindowData,
        SourceConcreteBaseLayer.concreteRawSupportKernel,
        SourceConcreteBaseLayer.concreteSupportValue,
        SourceConcreteBaseLayer.pointInConcreteWindow,
        hcond]
    · have hcond : ¬(I.1 ≤ x.1 ∧ x.1 ≤ I.2 ∧ x.2 = 0) := by
        intro h
        exact hx (by
          simpa [SourceConcreteBaseLayer.pointInConcreteWindow] using h)
      simp [closedWindowZeroKernel, closedWindowZeroSet,
        SourceConcreteBaseLayer.concreteSupportWindowData,
        SourceConcreteBaseLayer.concreteSupportValue,
        SourceConcreteBaseLayer.pointInConcreteWindow,
        hcond]

end SourceSupportClosedWindowZeroKernelModel

namespace SourceSupportCoordinateScaleModel

theorem supportValue_mem_footprint
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportCoordinateScaleModel S I)
    {f : A.Test} {x : S.SupportPoint}
    (hx : S.supportValue f x ≠ 0) :
    (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I,
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x) ∈
        M.supportFootprint f := by
  let z : ℝ × ℝ :=
    (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I,
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
  have hKernel : M.supportKernel f z ≠ 0 := by
    simpa [z, M.supportValue_eq_kernel f x] using hx
  exact M.kernel_ne_zero_mem_footprint f z hKernel

theorem supportValue_coordinateLower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportCoordinateScaleModel S I) :
    ∀ (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x ≠ 0 →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I := by
  intro f x hx
  let z : ℝ × ℝ :=
    (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I,
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
  have hz : z ∈ M.supportFootprint f := by
    simpa [z] using M.supportValue_mem_footprint hx
  simpa [z] using M.footprint_coordinateLower f z hz

theorem supportValue_coordinateUpper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportCoordinateScaleModel S I) :
    ∀ (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x ≠ 0 →
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I := by
  intro f x hx
  let z : ℝ × ℝ :=
    (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I,
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
  have hz : z ∈ M.supportFootprint f := by
    simpa [z] using M.supportValue_mem_footprint hx
  simpa [z] using M.footprint_coordinateUpper f z hz

theorem supportValue_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportCoordinateScaleModel S I) :
    ∀ (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x ≠ 0 →
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 := by
  intro f x hx
  let z : ℝ × ℝ :=
    (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I,
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
  have hz : z ∈ M.supportFootprint f := by
    simpa [z] using M.supportValue_mem_footprint hx
  simpa [z] using M.footprint_logScale_eq_zero f z hz

end SourceSupportCoordinateScaleModel

structure SourceFixedWindowCoordinateRows
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  sourceSupportClosedWindowZeroKernelModel :
    SourceSupportClosedWindowZeroKernelModel S I

namespace SourceFixedWindowCoordinateRows

noncomputable def sourceSupportCoordinateScaleModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    SourceSupportCoordinateScaleModel S I :=
  rows.sourceSupportClosedWindowZeroKernelModel.toCoordinateScaleModel

theorem supportCarrier_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.supportCarrier S.sourceTest ⊆ S.coordinateWindowCarrier I := by
  exact
    carrier_subset_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_coordinateLower
          S.sourceTest x hx)
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_coordinateUpper
          S.sourceTest x hx)
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
          S.sourceTest x hx)

theorem fourierSupportCarrier_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.fourierSupportCarrier S.sourceTest ⊆ S.coordinateWindowCarrier I := by
  exact
    carrier_subset_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_coordinateLower
          (A.involution S.sourceTest) x hx)
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_coordinateUpper
          (A.involution S.sourceTest) x hx)
      (fun x hx =>
        rows.sourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
          (A.involution S.sourceTest) x hx)

theorem supportCoordinateLower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.supportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_coordinateLower
      S.sourceTest x hx

theorem supportCoordinateUpper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.supportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_coordinateUpper
      S.sourceTest x hx

theorem supportLogScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.supportCarrier S.sourceTest →
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
      S.sourceTest x hx

theorem fourierCoordinateLower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_coordinateLower
      (A.involution S.sourceTest) x hx

theorem fourierCoordinateUpper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_coordinateUpper
      (A.involution S.sourceTest) x hx

theorem fourierLogScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 := by
  intro x hx
  exact
    rows.sourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
      (A.involution S.sourceTest) x hx

structure SourceFourierSupportInvolutionGeometryData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  carrier_eq_involutionSupport :
    S.fourierSupportCarrier S.sourceTest =
      S.supportCarrier (A.involution S.sourceTest)
  mem_iff_supportValue_involution_ne_zero :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest ↔
        S.supportValue (A.involution S.sourceTest) x ≠ 0
  coordinateLower :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I
  coordinateUpper :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I
  logScale_eq_zero :
    ∀ x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0
  supportInWindow :
    S.supportInWindow S.sourceTest I

namespace SourceFourierSupportInvolutionGeometryData

def ofFixedWindowCoordinateRows
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    SourceFourierSupportInvolutionGeometryData S I where
  carrier_eq_involutionSupport :=
    SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution
      S S.sourceTest
  mem_iff_supportValue_involution_ne_zero := by
    intro x
    exact
      SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
        (S := S) (f := S.sourceTest) (x := x)
  coordinateLower := rows.fourierCoordinateLower
  coordinateUpper := rows.fourierCoordinateUpper
  logScale_eq_zero := rows.fourierLogScale_eq_zero
  supportInWindow :=
    supportInWindow_of_coordinate_bounds_logScale_eq_zero
      rows.supportCoordinateLower rows.supportCoordinateUpper
      rows.supportLogScale_eq_zero

theorem fourierSupportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (D : SourceFourierSupportInvolutionGeometryData S I) :
    S.fourierSupportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  carrier_subset_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    D.coordinateLower D.coordinateUpper D.logScale_eq_zero

theorem fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (D : SourceFourierSupportInvolutionGeometryData S I) :
    S.fourierSupportInWindow S.sourceTest I :=
  fourierSupportInWindow_of_coordinate_bounds_logScale_eq_zero
    D.coordinateLower D.coordinateUpper D.logScale_eq_zero

theorem convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (D : SourceFourierSupportInvolutionGeometryData S I) :
    S.convolutionSupportTransported S.sourceTest I :=
  convolutionSupportTransported_of_coordinate_bounds_logScale_eq_zero
    D.coordinateLower D.coordinateUpper D.logScale_eq_zero

theorem soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (D : SourceFourierSupportInvolutionGeometryData S I) :
    S.soninSpaceComparison I :=
  S.soninSpaceComparison_of_subsets
    D.supportInWindow
    D.fourierSupportCarrier_subset_windowCarrier

end SourceFourierSupportInvolutionGeometryData

def fourierSupportInvolutionGeometryData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    SourceFourierSupportInvolutionGeometryData S I :=
  SourceFourierSupportInvolutionGeometryData.ofFixedWindowCoordinateRows rows

theorem supportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.supportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  carrier_subset_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    rows.supportCoordinateLower rows.supportCoordinateUpper
    rows.supportLogScale_eq_zero

theorem supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.supportInWindow S.sourceTest I :=
  supportInWindow_of_coordinate_bounds_logScale_eq_zero
    rows.supportCoordinateLower rows.supportCoordinateUpper
    rows.supportLogScale_eq_zero

theorem supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.supportTransported S.sourceTest I :=
  supportTransported_of_coordinate_bounds_logScale_eq_zero
    rows.supportCoordinateLower rows.supportCoordinateUpper
    rows.supportLogScale_eq_zero

theorem fourierSupportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.fourierSupportCarrier S.sourceTest ⊆ S.windowCarrier I :=
  rows.fourierSupportInvolutionGeometryData.fourierSupportCarrier_subset_windowCarrier

theorem fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.fourierSupportInWindow S.sourceTest I :=
  rows.fourierSupportInvolutionGeometryData.fourierSupportInWindow

theorem convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.convolutionSupportTransported S.sourceTest I :=
  rows.fourierSupportInvolutionGeometryData.convolutionSupportTransported

theorem soninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (rows : SourceFixedWindowCoordinateRows S I) :
    S.soninSpaceComparison I :=
  rows.fourierSupportInvolutionGeometryData.soninSpaceComparison

theorem windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (_rows : SourceFixedWindowCoordinateRows S I)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    S.windowContainedInLambda I lambda := by
  have hSubset :
      S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
    coordinateWindowCarrier_subset_lambdaCarrier hlambda
  exact
    windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier hSubset

theorem lambdaCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (_rows : SourceFixedWindowCoordinateRows S I)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    S.lambdaCompatible I lambda := by
  have hSubset :
      S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
    coordinateWindowCarrier_subset_lambdaCarrier hlambda
  exact
    lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier hSubset

end SourceFixedWindowCoordinateRows

structure SourcePlaceCarrierData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) where
  placeCarrier : S.PlaceSet → Type
  placeCarrierNormedAddCommGroup :
    ∀ V : S.PlaceSet, NormedAddCommGroup (placeCarrier V)
  placeCarrierInnerProductSpace :
    ∀ V : S.PlaceSet,
      letI := placeCarrierNormedAddCommGroup V
      InnerProductSpace ℝ (placeCarrier V)
  placeCarrierCompleteSpace :
    ∀ V : S.PlaceSet,
      letI := placeCarrierNormedAddCommGroup V
      CompleteSpace (placeCarrier V)
  sourcePlaceCarrierNonempty :
    Nonempty (placeCarrier S.sourcePlaceSet)

namespace SourcePlaceCarrierData

def sourceCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S) : Type :=
  P.placeCarrier S.sourcePlaceSet

theorem sourceCarrier_nonempty
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S) :
    Nonempty P.sourceCarrier :=
  P.sourcePlaceCarrierNonempty

@[reducible] def normedAddCommGroup
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S) (V : S.PlaceSet) :
    NormedAddCommGroup (P.placeCarrier V) :=
  P.placeCarrierNormedAddCommGroup V

@[reducible] def innerProductSpace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S) (V : S.PlaceSet) :
    letI := P.placeCarrierNormedAddCommGroup V
    InnerProductSpace ℝ (P.placeCarrier V) :=
  P.placeCarrierInnerProductSpace V

theorem completeSpace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S) (V : S.PlaceSet) :
    letI := P.placeCarrierNormedAddCommGroup V
    CompleteSpace (P.placeCarrier V) :=
  P.placeCarrierCompleteSpace V

end SourcePlaceCarrierData

structure SourceCanonicalHilbertModelData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (P : SourcePlaceCarrierData S) (V : S.PlaceSet) where
  hilbertCarrier : Type
  instNormedAddCommGroup : NormedAddCommGroup hilbertCarrier
  instInnerProductSpace :
    letI := instNormedAddCommGroup
    InnerProductSpace ℝ hilbertCarrier
  instCompleteSpace :
    letI := instNormedAddCommGroup
    CompleteSpace hilbertCarrier
  placeEquiv :
    letI := instNormedAddCommGroup
    letI := instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    hilbertCarrier ≃L[ℝ] P.placeCarrier V

def canonicalHilbertModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (V : S.PlaceSet) : Prop :=
  ∃ P : SourcePlaceCarrierData S,
    Nonempty (SourceCanonicalHilbertModelData S P V)

namespace SourceCanonicalHilbertModelData

@[reducible] def normedAddCommGroup
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    NormedAddCommGroup H.hilbertCarrier :=
  H.instNormedAddCommGroup

@[reducible] def innerProductSpace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    InnerProductSpace ℝ H.hilbertCarrier :=
  H.instInnerProductSpace

theorem completeSpace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    CompleteSpace H.hilbertCarrier :=
  H.instCompleteSpace

theorem canonicalHilbertModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    S.canonicalHilbertModel V :=
  ⟨P, ⟨H⟩⟩

theorem placeEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.map_zero

theorem placeEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (x + y) = H.placeEquiv x + H.placeEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.map_add x y

theorem placeEquiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (-x) = -H.placeEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.map_neg x

theorem placeEquiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (x - y) = H.placeEquiv x - H.placeEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.map_sub x y

theorem placeEquiv_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (c • x) = c • H.placeEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.map_smul c x

theorem placeEquiv_left_inv
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (H.placeEquiv x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.left_inv x

theorem placeEquiv_right_inv
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (y : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (H.placeEquiv.symm y) = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.right_inv y

theorem placeEquiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Injective H.placeEquiv := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.injective

theorem placeEquiv_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Surjective H.placeEquiv := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.surjective

theorem placeEquiv_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv x = H.placeEquiv y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  constructor
  · intro hxy
    exact H.placeEquiv.injective hxy
  · intro hxy
    rw [hxy]

theorem placeEquiv_symm_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.map_zero

theorem placeEquiv_symm_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (x + y) =
      H.placeEquiv.symm x + H.placeEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.map_add x y

theorem placeEquiv_symm_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (-x) = -H.placeEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.map_neg x

theorem placeEquiv_symm_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (x - y) =
      H.placeEquiv.symm x - H.placeEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.map_sub x y

theorem placeEquiv_symm_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (c : ℝ) (x : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (c • x) = c • H.placeEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.map_smul c x

theorem placeEquiv_symm_left_inv
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (y : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv (H.placeEquiv.symm y) = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.right_inv y

theorem placeEquiv_symm_right_inv
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (H.placeEquiv x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.left_inv x

theorem placeEquiv_symm_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Injective H.placeEquiv.symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.injective

theorem placeEquiv_symm_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Surjective H.placeEquiv.symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact H.placeEquiv.symm.surjective

theorem placeEquiv_symm_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V)
    (x y : P.placeCarrier V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm x = H.placeEquiv.symm y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  constructor
  · intro hxy
    exact H.placeEquiv.symm.injective hxy
  · intro hxy
    rw [hxy]

end SourceCanonicalHilbertModelData

def SourcePlaceCarrierData.canonicalModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (P : SourcePlaceCarrierData S)
    (V : S.PlaceSet) :
    SourceCanonicalHilbertModelData S P V where
  hilbertCarrier := P.placeCarrier V
  instNormedAddCommGroup := P.placeCarrierNormedAddCommGroup V
  instInnerProductSpace := P.placeCarrierInnerProductSpace V
  instCompleteSpace := P.placeCarrierCompleteSpace V
  placeEquiv := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)

structure SourceScalingActionData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) where
  scaleEquiv :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ℝˣ → H.hilbertCarrier ≃L[ℝ] H.hilbertCarrier
  scaleEquiv_one :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    scaleEquiv 1 = ContinuousLinearEquiv.refl ℝ H.hilbertCarrier
  scaleEquiv_mul :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ a b : ℝˣ,
      scaleEquiv (a * b) = (scaleEquiv a).trans (scaleEquiv b)
  scaleAction :
    ℝ →
      letI := H.instNormedAddCommGroup
      letI := H.instInnerProductSpace
      H.hilbertCarrier →L[ℝ] H.hilbertCarrier
  scaleAction_units :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ u : ℝˣ,
      scaleAction (u : ℝ) = (scaleEquiv u).toContinuousLinearMap
  scaleOne :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    scaleAction 1 = ContinuousLinearMap.id ℝ H.hilbertCarrier
  scaleMul :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ a b : ℝ,
      scaleAction (a * b) = (scaleAction a).comp (scaleAction b)

structure SourceScalingCoordinateActionData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateScaleEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ℝˣ → P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateScaleEquiv_one :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateScaleEquiv 1 = ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)
  coordinateScaleEquiv_mul :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ a b : ℝˣ,
      coordinateScaleEquiv (a * b) =
        (coordinateScaleEquiv a).trans (coordinateScaleEquiv b)
  coordinateScaleAction :
    ℝ →
      letI := P.placeCarrierNormedAddCommGroup V
      letI := P.placeCarrierInnerProductSpace V
      P.placeCarrier V →L[ℝ] P.placeCarrier V
  coordinateScaleAction_units :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ u : ℝˣ,
      coordinateScaleAction (u : ℝ) =
        (coordinateScaleEquiv u).toContinuousLinearMap
  coordinateScaleOne :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateScaleAction 1 = ContinuousLinearMap.id ℝ (P.placeCarrier V)
  coordinateScaleMul :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ a b : ℝ,
      coordinateScaleAction (a * b) =
        (coordinateScaleAction a).comp (coordinateScaleAction b)

structure SourceScalarCoordinateScalingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateScaleEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ℝˣ → P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateScaleEquiv_apply :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ (u : ℝˣ) (x : P.placeCarrier V),
      coordinateScaleEquiv u x = (u : ℝ) • x
  coordinateScaleEquiv_one :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateScaleEquiv 1 = ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)
  coordinateScaleEquiv_mul :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ a b : ℝˣ,
      coordinateScaleEquiv (a * b) =
        (coordinateScaleEquiv a).trans (coordinateScaleEquiv b)
  coordinateScaleAction :
    ℝ →
      letI := P.placeCarrierNormedAddCommGroup V
      letI := P.placeCarrierInnerProductSpace V
      P.placeCarrier V →L[ℝ] P.placeCarrier V
  coordinateScaleAction_apply :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ (a : ℝ) (x : P.placeCarrier V),
      coordinateScaleAction a x = a • x
  coordinateScaleAction_units :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ u : ℝˣ,
      coordinateScaleAction (u : ℝ) =
        (coordinateScaleEquiv u).toContinuousLinearMap
  coordinateScaleAction_one :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateScaleAction 1 = ContinuousLinearMap.id ℝ (P.placeCarrier V)
  coordinateScaleAction_mul :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ a b : ℝ,
      coordinateScaleAction (a * b) =
        (coordinateScaleAction a).comp (coordinateScaleAction b)

namespace SourceScalingActionData

theorem scale_equiv_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv 1 = ContinuousLinearEquiv.refl ℝ H.hilbertCarrier :=
  D.scaleEquiv_one

theorem scale_equiv_mul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ a b : ℝˣ,
      D.scaleEquiv (a * b) = (D.scaleEquiv a).trans (D.scaleEquiv b) :=
  D.scaleEquiv_mul

theorem scale_action_units
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ u : ℝˣ,
      D.scaleAction (u : ℝ) = (D.scaleEquiv u).toContinuousLinearMap :=
  D.scaleAction_units

theorem scale_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction 1 = ContinuousLinearMap.id ℝ H.hilbertCarrier :=
  D.scaleOne

theorem scale_mul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ a b : ℝ,
      D.scaleAction (a * b) = (D.scaleAction a).comp (D.scaleAction b) :=
  D.scaleMul

theorem scale_equiv_one_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv 1 x = x := by
  rw [D.scaleEquiv_one]
  rfl

theorem scale_equiv_mul_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a b : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv (a * b) x = D.scaleEquiv b (D.scaleEquiv a x) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simpa using congrArg (fun e => e x) (D.scaleEquiv_mul a b)

theorem scale_action_units_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction (u : ℝ) x = D.scaleEquiv u x := by
  rw [D.scaleAction_units u]
  rfl

theorem scale_action_one_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction 1 x = x := by
  rw [D.scaleOne]
  rfl

theorem scale_action_mul_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a b : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction (a * b) x = D.scaleAction a (D.scaleAction b x) := by
  rw [D.scaleMul a b]
  rfl

theorem scale_action_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a : ℝ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction a 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleAction a).map_zero

theorem scale_action_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a : ℝ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction a (x + y) = D.scaleAction a x + D.scaleAction a y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleAction a).map_add x y

theorem scale_action_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction a (-x) = -D.scaleAction a x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleAction a).map_neg x

theorem scale_action_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a : ℝ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction a (x - y) = D.scaleAction a x - D.scaleAction a y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleAction a).map_sub x y

theorem scale_action_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (a c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction a (c • x) = c • D.scaleAction a x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleAction a).map_smul c x

theorem scale_equiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).map_zero

theorem scale_equiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u (x + y) = D.scaleEquiv u x + D.scaleEquiv u y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).map_add x y

theorem scale_equiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u (-x) = -D.scaleEquiv u x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).map_neg x

theorem scale_equiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u (x - y) = D.scaleEquiv u x - D.scaleEquiv u y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).map_sub x y

theorem scale_equiv_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u (c • x) = c • D.scaleEquiv u x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).map_smul c x

theorem scale_equiv_symm_left
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (D.scaleEquiv u x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).left_inv x

theorem scale_equiv_symm_right
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u ((D.scaleEquiv u).symm x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).right_inv x

theorem scale_equiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective (D.scaleEquiv u) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).injective

theorem scale_equiv_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective (D.scaleEquiv u) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).surjective

theorem scale_equiv_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleEquiv u x = D.scaleEquiv u y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact (D.scaleEquiv u).injective h
  · intro h
    rw [h]

theorem scale_action_units_symm_left
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (D.scaleAction (u : ℝ) x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  rw [D.scaleAction_units u]
  exact (D.scaleEquiv u).left_inv x

theorem scale_action_units_symm_right
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction (u : ℝ) ((D.scaleEquiv u).symm x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  rw [D.scaleAction_units u]
  exact (D.scaleEquiv u).right_inv x

theorem scale_action_units_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective (D.scaleAction (u : ℝ)) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  rw [D.scaleAction_units u]
  exact (D.scaleEquiv u).injective

theorem scale_action_units_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.scaleAction (u : ℝ) x = D.scaleAction (u : ℝ) y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  rw [D.scaleAction_units u]
  exact scale_equiv_apply_eq_iff_eq D u x y

theorem scale_equiv_symm_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.map_zero

theorem scale_equiv_symm_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (x + y) =
      (D.scaleEquiv u).symm x + (D.scaleEquiv u).symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.map_add x y

theorem scale_equiv_symm_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (-x) = -(D.scaleEquiv u).symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.map_neg x

theorem scale_equiv_symm_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (x - y) =
      (D.scaleEquiv u).symm x - (D.scaleEquiv u).symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.map_sub x y

theorem scale_equiv_symm_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm (c • x) = c • (D.scaleEquiv u).symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.map_smul c x

theorem scale_equiv_symm_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective (D.scaleEquiv u).symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.injective

theorem scale_equiv_symm_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective (D.scaleEquiv u).symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.scaleEquiv u).symm.surjective

theorem scale_equiv_symm_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingActionData S H)
    (u : ℝˣ) (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (D.scaleEquiv u).symm x = (D.scaleEquiv u).symm y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact (D.scaleEquiv u).symm.injective h
  · intro h
    rw [h]

end SourceScalingActionData

namespace SourceScalarCoordinateScalingData

theorem coordinateScaleAction_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction 0 = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simpa using D.coordinateScaleAction_apply 0 x

theorem coordinateScaleAction_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a b : ℝ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction (a + b) =
      D.coordinateScaleAction a + D.coordinateScaleAction b := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  rw [D.coordinateScaleAction_apply (a + b) x]
  simp only [ContinuousLinearMap.add_apply]
  rw [D.coordinateScaleAction_apply a x]
  rw [D.coordinateScaleAction_apply b x]
  exact add_smul a b x

theorem coordinateScaleAction_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a : ℝ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction (-a) = -D.coordinateScaleAction a := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  rw [D.coordinateScaleAction_apply (-a) x]
  simp only [ContinuousLinearMap.neg_apply]
  rw [D.coordinateScaleAction_apply a x]
  simp

theorem coordinateScaleAction_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a b : ℝ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction (a - b) =
      D.coordinateScaleAction a - D.coordinateScaleAction b := by
  rw [sub_eq_add_neg]
  rw [D.coordinateScaleAction_add a (-b)]
  rw [D.coordinateScaleAction_neg b]
  simp [sub_eq_add_neg]

theorem coordinateScaleEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (u : ℝˣ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleEquiv u 0 = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleEquiv u).map_zero

theorem coordinateScaleEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (u : ℝˣ) (x y : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleEquiv u (x + y) =
      D.coordinateScaleEquiv u x + D.coordinateScaleEquiv u y := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleEquiv u).map_add x y

theorem coordinateScaleEquiv_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (u : ℝˣ) (c : ℝ) (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleEquiv u (c • x) = c • D.coordinateScaleEquiv u x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleEquiv u).map_smul c x

theorem coordinateScaleAction_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a : ℝ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction a 0 = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleAction a).map_zero

theorem coordinateScaleAction_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a : ℝ) (x y : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction a (x + y) =
      D.coordinateScaleAction a x + D.coordinateScaleAction a y := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleAction a).map_add x y

theorem coordinateScaleAction_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H)
    (a c : ℝ) (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateScaleAction a (c • x) = c • D.coordinateScaleAction a x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.coordinateScaleAction a).map_smul c x

noncomputable def toScalingCoordinateActionData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H) :
    SourceScalingCoordinateActionData S H where
  coordinateScaleEquiv := D.coordinateScaleEquiv
  coordinateScaleEquiv_one := D.coordinateScaleEquiv_one
  coordinateScaleEquiv_mul := D.coordinateScaleEquiv_mul
  coordinateScaleAction := D.coordinateScaleAction
  coordinateScaleAction_units := D.coordinateScaleAction_units
  coordinateScaleOne := D.coordinateScaleAction_one
  coordinateScaleMul := D.coordinateScaleAction_mul

end SourceScalarCoordinateScalingData

namespace SourceScalingCoordinateActionData

noncomputable def toScalingActionData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalingCoordinateActionData S H) :
    SourceScalingActionData S H where
  scaleEquiv := fun u => by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact H.placeEquiv.trans ((D.coordinateScaleEquiv u).trans H.placeEquiv.symm)
  scaleEquiv_one := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearEquiv.ext
    funext x
    simp [D.coordinateScaleEquiv_one]
  scaleEquiv_mul := by
    intro a b
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearEquiv.ext
    funext x
    simp [D.coordinateScaleEquiv_mul]
  scaleAction := fun a => by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact H.placeEquiv.symm.toContinuousLinearMap.comp
      ((D.coordinateScaleAction a).comp H.placeEquiv.toContinuousLinearMap)
  scaleAction_units := by
    intro u
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearMap.ext
    intro x
    simp [D.coordinateScaleAction_units]
  scaleOne := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearMap.ext
    intro x
    simp [D.coordinateScaleOne]
  scaleMul := by
    intro a b
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearMap.ext
    intro x
    simp [D.coordinateScaleMul]

end SourceScalingCoordinateActionData

def scalingActionImplemented
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (V : S.PlaceSet) : Prop :=
  ∃ (P : SourcePlaceCarrierData S)
    (H : SourceCanonicalHilbertModelData S P V),
    Nonempty (SourceScalarCoordinateScalingData S H)

theorem scalingActionImplemented_of_scalar_coordinate_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceScalarCoordinateScalingData S H) :
    S.scalingActionImplemented V :=
  ⟨P, H, ⟨D⟩⟩

structure SourceFourierGradingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) where
  gradeIndex : Type
  gradeSubspace :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    gradeIndex → Submodule ℝ H.hilbertCarrier
  fourierEquiv :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier ≃L[ℝ] H.hilbertCarrier
  fourier_preserves_grade :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ (n : gradeIndex) (x : H.hilbertCarrier),
      x ∈ gradeSubspace n → fourierEquiv x ∈ gradeSubspace n

namespace SourceFourierGradingData

def fourierOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.fourierEquiv.toContinuousLinearMap

def fourierInverseOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.fourierEquiv.symm.toContinuousLinearMap

theorem fourierOperator_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator = D.fourierEquiv.toContinuousLinearMap :=
  rfl

theorem fourierInverseOperator_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator = D.fourierEquiv.symm.toContinuousLinearMap :=
  rfl

theorem fourier_preserves_grade_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    ∀ (n : D.gradeIndex) (x : H.hilbertCarrier),
      x ∈ D.gradeSubspace n → D.fourierOperator x ∈ D.gradeSubspace n :=
  D.fourier_preserves_grade

theorem fourierOperator_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator x = D.fourierEquiv x := by
  rfl

theorem fourierInverseOperator_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator x = D.fourierEquiv.symm x :=
  rfl

theorem fourierOperator_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_zero

theorem fourierInverseOperator_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierInverseOperator.map_zero

theorem fourierOperator_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (x + y) = D.fourierOperator x + D.fourierOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_add x y

theorem fourierInverseOperator_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator (x + y) =
      D.fourierInverseOperator x + D.fourierInverseOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierInverseOperator.map_add x y

theorem fourierOperator_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (-x) = -D.fourierOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_neg x

theorem fourierInverseOperator_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator (-x) = -D.fourierInverseOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierInverseOperator.map_neg x

theorem fourierOperator_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (x - y) = D.fourierOperator x - D.fourierOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_sub x y

theorem fourierInverseOperator_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator (x - y) =
      D.fourierInverseOperator x - D.fourierInverseOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierInverseOperator.map_sub x y

theorem fourierOperator_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (c • x) = c • D.fourierOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_smul c x

theorem fourierInverseOperator_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator (c • x) = c • D.fourierInverseOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierInverseOperator.map_smul c x

theorem fourierInverse_leftInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator.comp D.fourierOperator =
      ContinuousLinearMap.id ℝ H.hilbertCarrier := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  apply ContinuousLinearMap.ext
  intro x
  exact D.fourierEquiv.left_inv x

theorem fourierInverse_rightInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator.comp D.fourierInverseOperator =
      ContinuousLinearMap.id ℝ H.hilbertCarrier := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  apply ContinuousLinearMap.ext
  intro x
  exact D.fourierEquiv.right_inv x

theorem fourierOperator_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.fourierOperator := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.fourierEquiv.symm y, D.fourierEquiv.right_inv y⟩

theorem fourierInverseOperator_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.fourierInverseOperator := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.injective

theorem fourierInverseOperator_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.fourierInverseOperator := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.fourierEquiv y, D.fourierEquiv.left_inv y⟩

theorem fourierInverseOperator_apply_fourierOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator (D.fourierOperator x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.left_inv x

theorem fourierOperator_eq_iff_eq_fourierInverseOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator x = y ↔ x = D.fourierInverseOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.fourierEquiv.left_inv x).symm
  · intro h
    rw [h]
    exact D.fourierEquiv.right_inv y

theorem fourierInverseOperator_eq_iff_eq_fourierOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator x = y ↔ x = D.fourierOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.fourierEquiv.right_inv x).symm
  · intro h
    rw [h]
    exact D.fourierEquiv.left_inv y

theorem fourierOperator_apply_fourierInverseOperator
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (D.fourierInverseOperator x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.right_inv x

theorem fourierOperator_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_zero

theorem fourierOperator_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (x + y) = D.fourierOperator x + D.fourierOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_add x y

theorem fourierOperator_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (-x) = -D.fourierOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_neg x

theorem fourierOperator_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (x - y) = D.fourierOperator x - D.fourierOperator y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_sub x y

theorem fourierOperator_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator (c • x) = c • D.fourierOperator x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierOperator.map_smul c x

theorem fourierEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.map_zero

theorem fourierEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv (x + y) = D.fourierEquiv x + D.fourierEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.map_add x y

theorem fourierEquiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv (-x) = -D.fourierEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.map_neg x

theorem fourierEquiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv (x - y) = D.fourierEquiv x - D.fourierEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.map_sub x y

theorem fourierEquiv_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv (c • x) = c • D.fourierEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.map_smul c x

theorem fourierEquiv_symm_left
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm (D.fourierEquiv x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.left_inv x

theorem fourierEquiv_symm_right
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv (D.fourierEquiv.symm x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.right_inv x

theorem fourierEquiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.fourierEquiv := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.injective

theorem fourierEquiv_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv x = D.fourierEquiv y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.fourierEquiv.injective h
  · intro h
    rw [h]

theorem fourierOperator_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.fourierOperator := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro x y h
  exact D.fourierEquiv.injective h

theorem fourierOperator_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierOperator x = D.fourierOperator y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.fourierOperator_injective h
  · intro h
    rw [h]

theorem fourierInverseOperator_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierInverseOperator x = D.fourierInverseOperator y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.fourierInverseOperator_injective h
  · intro h
    rw [h]

theorem fourierEquiv_symm_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.map_zero

theorem fourierEquiv_symm_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm (x + y) =
      D.fourierEquiv.symm x + D.fourierEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.map_add x y

theorem fourierEquiv_symm_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm (-x) = -D.fourierEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.map_neg x

theorem fourierEquiv_symm_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm (x - y) =
      D.fourierEquiv.symm x - D.fourierEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.map_sub x y

theorem fourierEquiv_symm_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv.symm (c • x) = c • D.fourierEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.fourierEquiv.symm.map_smul c x

theorem fourier_preserves_grade_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) (x : H.hilbertCarrier)
    (hx : x ∈ D.gradeSubspace n) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.fourierEquiv x ∈ D.gradeSubspace n :=
  D.fourier_preserves_grade n x hx

theorem grade_zero_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (0 : H.hilbertCarrier) ∈ D.gradeSubspace n := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.gradeSubspace n).zero_mem

theorem grade_add_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) {x y : H.hilbertCarrier}
    (hx : x ∈ D.gradeSubspace n) (hy : y ∈ D.gradeSubspace n) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    x + y ∈ D.gradeSubspace n := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.gradeSubspace n).add_mem hx hy

theorem grade_neg_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) {x : H.hilbertCarrier}
    (hx : x ∈ D.gradeSubspace n) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (-x) ∈ D.gradeSubspace n := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.gradeSubspace n).neg_mem hx

theorem grade_sub_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) {x y : H.hilbertCarrier}
    (hx : x ∈ D.gradeSubspace n) (hy : y ∈ D.gradeSubspace n) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (x - y) ∈ D.gradeSubspace n := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.gradeSubspace n).sub_mem hx hy

theorem grade_smul_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingData S H)
    (n : D.gradeIndex) (c : ℝ) {x : H.hilbertCarrier}
    (hx : x ∈ D.gradeSubspace n) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (c • x) ∈ D.gradeSubspace n := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (D.gradeSubspace n).smul_mem c hx

end SourceFourierGradingData

structure SourceFourierCoordinateGradingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateGradeIndex : Type
  coordinateGradeSubspace :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateGradeIndex → Submodule ℝ (P.placeCarrier V)
  coordinateFourierEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateFourier_preserves_grade :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ (n : coordinateGradeIndex) (x : P.placeCarrier V),
      x ∈ coordinateGradeSubspace n →
        coordinateFourierEquiv x ∈ coordinateGradeSubspace n

structure SourceIdentityFourierCoordinateGradingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} (V : S.PlaceSet) where
  coordinateGradeIndex : Type
  coordinateGradeSubspace :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateGradeIndex → Submodule ℝ (P.placeCarrier V)

abbrev SourceLineFourierCoordinateGradingData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} (_V : S.PlaceSet) :=
  Unit

namespace SourceLineFourierCoordinateGradingData

noncomputable def gradeSubspace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Submodule ℝ (P.placeCarrier V) := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact Submodule.span ℝ ({v} : Set (P.placeCarrier V))

@[simp] theorem gradeSubspace_eq_span_singleton
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.gradeSubspace v = Submodule.span ℝ ({v} : Set (P.placeCarrier V)) := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  rfl

theorem gradeSubspace_coe_eq_range_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ↑(D.gradeSubspace v) = Set.range (fun c : ℝ => c • v) := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  ext x
  simpa [gradeSubspace] using
    (Submodule.mem_span_singleton (R := ℝ) (x := x) (y := v))

theorem gradeSubspace_eq_top_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.gradeSubspace v = ⊤ ↔ ∀ x : P.placeCarrier V, ∃ c : ℝ, c • v = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simpa [gradeSubspace] using
    (Submodule.span_singleton_eq_top_iff (R := ℝ)
      (M := P.placeCarrier V) v)

noncomputable def toIdentityFourierCoordinateGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    SourceIdentityFourierCoordinateGradingData S (P := P) V where
  coordinateGradeIndex := P.placeCarrier V
  coordinateGradeSubspace := D.gradeSubspace

@[simp] theorem toIdentityFourierCoordinateGradingData_gradeIndex
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    D.toIdentityFourierCoordinateGradingData.coordinateGradeIndex =
      P.placeCarrier V := by
  rfl

@[simp] theorem toIdentityFourierCoordinateGradingData_gradeSubspace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    D.toIdentityFourierCoordinateGradingData.coordinateGradeSubspace =
      D.gradeSubspace := by
  rfl

theorem toIdentityFourierCoordinateGradingData_mem_iff_exists_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    x ∈ D.toIdentityFourierCoordinateGradingData.coordinateGradeSubspace v ↔
      ∃ c : ℝ, c • v = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simpa [toIdentityFourierCoordinateGradingData, gradeSubspace] using
    (Submodule.mem_span_singleton (R := ℝ) (x := x) (y := v))

theorem mem_gradeSubspace_iff_exists_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    x ∈ D.gradeSubspace v ↔ ∃ c : ℝ, c • v = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simpa [gradeSubspace] using
    (Submodule.mem_span_singleton (R := ℝ) (x := x) (y := v))

theorem smul_generator_mem_gradeSubspace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) (c : ℝ) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    c • v ∈ D.gradeSubspace v := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (D.mem_gradeSubspace_iff_exists_smul v (c • v)).2 ⟨c, rfl⟩

theorem gradeSubspace_le_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V)
    (W : letI := P.placeCarrierNormedAddCommGroup V
         letI := P.placeCarrierInnerProductSpace V
         Submodule ℝ (P.placeCarrier V)) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.gradeSubspace v ≤ W ↔ v ∈ W := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [gradeSubspace]

theorem gradeSubspace_eq_bot_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.gradeSubspace v = ⊥ ↔ v = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [gradeSubspace]

end SourceLineFourierCoordinateGradingData

namespace SourceIdentityFourierCoordinateGradingData

noncomputable def toFourierCoordinateGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceIdentityFourierCoordinateGradingData S (P := P) V) :
    SourceFourierCoordinateGradingData S H where
  coordinateGradeIndex := D.coordinateGradeIndex
  coordinateGradeSubspace := D.coordinateGradeSubspace
  coordinateFourierEquiv := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)
  coordinateFourier_preserves_grade := by
    intro n x hx
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    simpa using hx

@[simp] theorem toFourierCoordinateGradingData_gradeIndex
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceIdentityFourierCoordinateGradingData S (P := P) V) :
    (D.toFourierCoordinateGradingData (H := H)).coordinateGradeIndex =
      D.coordinateGradeIndex :=
  rfl

@[simp] theorem toFourierCoordinateGradingData_gradeSubspace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceIdentityFourierCoordinateGradingData S (P := P) V) :
    (D.toFourierCoordinateGradingData (H := H)).coordinateGradeSubspace =
      D.coordinateGradeSubspace :=
  rfl

theorem toFourierCoordinateGradingData_fourierEquiv_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceIdentityFourierCoordinateGradingData S (P := P) V)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    (D.toFourierCoordinateGradingData (H := H)).coordinateFourierEquiv x = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [toFourierCoordinateGradingData]

end SourceIdentityFourierCoordinateGradingData

namespace SourceLineFourierCoordinateGradingData

noncomputable def toFourierCoordinateGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    SourceFourierCoordinateGradingData S H :=
  D.toIdentityFourierCoordinateGradingData.toFourierCoordinateGradingData

@[simp] theorem toFourierCoordinateGradingData_gradeIndex
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    (D.toFourierCoordinateGradingData (H := H)).coordinateGradeIndex =
      P.placeCarrier V := by
  rfl

@[simp] theorem toFourierCoordinateGradingData_gradeSubspace
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    (D.toFourierCoordinateGradingData (H := H)).coordinateGradeSubspace =
      D.gradeSubspace := by
  rfl

theorem toFourierCoordinateGradingData_fourierEquiv_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    (D.toFourierCoordinateGradingData (H := H)).coordinateFourierEquiv x = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [toFourierCoordinateGradingData,
    SourceIdentityFourierCoordinateGradingData.toFourierCoordinateGradingData]

end SourceLineFourierCoordinateGradingData

namespace SourceFourierCoordinateGradingData

def toIdentityFourierCoordinateGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierCoordinateGradingData S H) :
    SourceIdentityFourierCoordinateGradingData S (P := P) V where
  coordinateGradeIndex := D.coordinateGradeIndex
  coordinateGradeSubspace := D.coordinateGradeSubspace

noncomputable def toFourierGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierCoordinateGradingData S H) :
    SourceFourierGradingData S H where
  gradeIndex := D.coordinateGradeIndex
  gradeSubspace := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact fun n =>
      Submodule.comap H.placeEquiv.toContinuousLinearMap.toLinearMap
        (D.coordinateGradeSubspace n)
  fourierEquiv := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact H.placeEquiv.trans (D.coordinateFourierEquiv.trans H.placeEquiv.symm)
  fourier_preserves_grade := by
    intro n x hx
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    change
      H.placeEquiv
          ((H.placeEquiv.trans
            (D.coordinateFourierEquiv.trans H.placeEquiv.symm)) x) ∈
        D.coordinateGradeSubspace n
    simpa using D.coordinateFourier_preserves_grade n (H.placeEquiv x) hx

end SourceFourierCoordinateGradingData

namespace SourceLineFourierCoordinateGradingData

noncomputable def toFourierGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    SourceFourierGradingData S H :=
  (D.toFourierCoordinateGradingData (H := H)).toFourierGradingData

theorem toFourierGradingData_mem_gradeSubspace_iff_exists_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    x ∈ (D.toFourierGradingData (H := H)).gradeSubspace v ↔
      ∃ c : ℝ, c • v = H.placeEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  change H.placeEquiv x ∈ D.gradeSubspace v ↔
    ∃ c : ℝ, c • v = H.placeEquiv x
  exact D.mem_gradeSubspace_iff_exists_smul v (H.placeEquiv x)

theorem toFourierGradingData_placeEquiv_symm_smul_mem
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (v : P.placeCarrier V) (c : ℝ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (c • v) ∈
      (D.toFourierGradingData (H := H)).gradeSubspace v := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  change H.placeEquiv (H.placeEquiv.symm (c • v)) ∈ D.gradeSubspace v
  simpa using D.smul_generator_mem_gradeSubspace v c

theorem toFourierGradingData_fourierEquiv_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    (D.toFourierGradingData (H := H)).fourierEquiv x = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [toFourierGradingData, toFourierCoordinateGradingData,
    SourceIdentityFourierCoordinateGradingData.toFourierCoordinateGradingData,
    SourceFourierCoordinateGradingData.toFourierGradingData]

end SourceLineFourierCoordinateGradingData

abbrev SourceFourierGradingEquivData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :=
  SourceFourierGradingData S H

namespace SourceFourierGradingEquivData

def toFourierGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierGradingEquivData S H) :
    SourceFourierGradingData S H :=
  D

end SourceFourierGradingEquivData

def fourierGradingCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (V : S.PlaceSet) : Prop :=
  ∃ (P : SourcePlaceCarrierData S)
    (H : SourceCanonicalHilbertModelData S P V),
    Nonempty (SourceFourierCoordinateGradingData S H)

theorem fourierGradingCompatible_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceFourierCoordinateGradingData S H) :
    S.fourierGradingCompatible V :=
  ⟨P, H, ⟨D⟩⟩

theorem fourierGradingCompatible_of_identity_fourier_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceIdentityFourierCoordinateGradingData S (P := P) V) :
    S.fourierGradingCompatible V :=
  ⟨P, H, ⟨D.toFourierCoordinateGradingData (H := H)⟩⟩

theorem fourierGradingCompatible_of_line_fourier_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceLineFourierCoordinateGradingData S (P := P) V) :
    S.fourierGradingCompatible V :=
  ⟨P, H, ⟨D.toFourierCoordinateGradingData (H := H)⟩⟩

structure SourceBoundedComparisonCoordinateData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateComparisonEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V

structure SourceSignedCoordinateComparisonData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (_H : SourceCanonicalHilbertModelData S P V) where
  coordinateComparisonEquiv :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    P.placeCarrier V ≃L[ℝ] P.placeCarrier V
  coordinateComparisonEquiv_apply :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ x : P.placeCarrier V, coordinateComparisonEquiv x = -x
  coordinateComparisonEquiv_involutive :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ x : P.placeCarrier V,
      coordinateComparisonEquiv (coordinateComparisonEquiv x) = x
  coordinateComparisonEquiv_symm_apply :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    ∀ x : P.placeCarrier V, coordinateComparisonEquiv.symm x = -x
  coordinateComparisonEquiv_comp_self :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    coordinateComparisonEquiv.toContinuousLinearMap.comp
        coordinateComparisonEquiv.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (P.placeCarrier V)

structure SourceBoundedComparisonEquivData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) where
  comparisonEquiv :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier ≃L[ℝ] H.hilbertCarrier

namespace SourceBoundedComparisonEquivData

def comparisonMap
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.comparisonEquiv.toContinuousLinearMap

def comparisonInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.comparisonEquiv.symm.toContinuousLinearMap

theorem comparisonMap_leftInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse.comp D.comparisonMap =
      ContinuousLinearMap.id ℝ H.hilbertCarrier := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  apply ContinuousLinearMap.ext
  intro x
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_rightInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap.comp D.comparisonInverse =
      ContinuousLinearMap.id ℝ H.hilbertCarrier := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  apply ContinuousLinearMap.ext
  intro x
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = D.comparisonEquiv x := by
  rfl

theorem comparisonInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = D.comparisonEquiv.symm x := by
  rfl

theorem comparisonMap_leftInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (D.comparisonMap x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_rightInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (D.comparisonInverse x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_zero

theorem comparisonMap_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (x + y) = D.comparisonMap x + D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_add x y

theorem comparisonMap_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (-x) = -D.comparisonMap x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_neg x

theorem comparisonMap_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (x - y) = D.comparisonMap x - D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_sub x y

theorem comparisonMap_map_smul_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (c • x) = c • D.comparisonMap x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_smul c x

theorem comparisonInverse_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_zero

theorem comparisonInverse_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (x + y) =
      D.comparisonInverse x + D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_add x y

theorem comparisonInverse_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (-x) = -D.comparisonInverse x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_neg x

theorem comparisonInverse_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (x - y) =
      D.comparisonInverse x - D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_sub x y

theorem comparisonInverse_map_smul_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (c • x) = c • D.comparisonInverse x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_smul c x

theorem comparisonEquiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonEquiv := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.injective

theorem comparisonEquiv_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv x = D.comparisonEquiv y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonEquiv.injective h
  · intro h
    rw [h]

theorem comparisonEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_zero

theorem comparisonEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (x + y) =
      D.comparisonEquiv x + D.comparisonEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_add x y

theorem comparisonEquiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (-x) = -D.comparisonEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_neg x

theorem comparisonEquiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (x - y) =
      D.comparisonEquiv x - D.comparisonEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_sub x y

theorem comparisonEquiv_map_smul_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (c • x) = c • D.comparisonEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_smul c x

theorem comparisonEquiv_symm_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_zero

theorem comparisonEquiv_symm_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (x + y) =
      D.comparisonEquiv.symm x + D.comparisonEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_add x y

theorem comparisonEquiv_symm_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (-x) = -D.comparisonEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_neg x

theorem comparisonEquiv_symm_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (x - y) =
      D.comparisonEquiv.symm x - D.comparisonEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_sub x y

theorem comparisonEquiv_symm_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (c • x) =
      c • D.comparisonEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_smul c x

theorem comparisonMap_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonMap := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro x y h
  exact D.comparisonEquiv.injective h

theorem comparisonInverse_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonInverse := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro x y h
  exact D.comparisonEquiv.symm.injective h

theorem comparisonMap_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = D.comparisonMap y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonMap_injective h
  · intro h
    rw [h]

theorem comparisonInverse_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = D.comparisonInverse y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonInverse_injective h
  · intro h
    rw [h]

theorem comparisonMap_eq_iff_eq_comparisonInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = y ↔ x = D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.comparisonEquiv.left_inv x).symm
  · intro h
    rw [h]
    exact D.comparisonEquiv.right_inv y

theorem comparisonInverse_eq_iff_eq_comparisonMap
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = y ↔ x = D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.comparisonEquiv.right_inv x).symm
  · intro h
    rw [h]
    exact D.comparisonEquiv.left_inv y

end SourceBoundedComparisonEquivData

/--
Bounded-comparison model data is the continuous-linear equivalence data itself.

The old `SourceBoundedComparisonData` record duplicated
`SourceBoundedComparisonEquivData` with the same single `comparisonEquiv`
field.  Keeping this as an abbrev removes that extra constructor layer while
preserving the public model-data name used by CCM24 source rows.
-/
abbrev SourceBoundedComparisonData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :=
  SourceBoundedComparisonEquivData S H

namespace SourceSignedCoordinateComparisonData

noncomputable def neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    (H : SourceCanonicalHilbertModelData S P V) :
    SourceSignedCoordinateComparisonData S H where
  coordinateComparisonEquiv := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact (-1 : ℝˣ) • ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)
  coordinateComparisonEquiv_apply := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    intro x
    simp
  coordinateComparisonEquiv_involutive := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    intro x
    simp only [ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply]
    rw [smul_smul]
    norm_num
  coordinateComparisonEquiv_symm_apply := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    intro x
    simp
  coordinateComparisonEquiv_comp_self := by
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply,
      ContinuousLinearMap.id_apply]
    rw [smul_smul]
    norm_num

theorem coordinateComparisonEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv 0 = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.map_zero

theorem coordinateComparisonEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x y : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (x + y) =
      D.coordinateComparisonEquiv x + D.coordinateComparisonEquiv y := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.map_add x y

theorem coordinateComparisonEquiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (-x) = -D.coordinateComparisonEquiv x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.map_neg x

theorem coordinateComparisonEquiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x y : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (x - y) =
      D.coordinateComparisonEquiv x - D.coordinateComparisonEquiv y := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.map_sub x y

theorem coordinateComparisonEquiv_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (c : ℝ) (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (c • x) = c • D.coordinateComparisonEquiv x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.map_smul c x

theorem coordinateComparisonEquiv_symm_left
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv.symm (D.coordinateComparisonEquiv x) = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.left_inv x

theorem coordinateComparisonEquiv_symm_right
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (D.coordinateComparisonEquiv.symm x) = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.right_inv x

theorem coordinateComparisonEquiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Injective D.coordinateComparisonEquiv := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.injective

theorem coordinateComparisonEquiv_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    Function.Surjective D.coordinateComparisonEquiv := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateComparisonEquiv.surjective

theorem coordinateComparisonEquiv_neg_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv (-x) = x := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simpa using D.coordinateComparisonEquiv_apply (-x)

theorem coordinateComparisonEquiv_eq_zero_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv x = 0 ↔ x = 0 := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [D.coordinateComparisonEquiv_apply x]

theorem coordinateComparisonEquiv_symm_eq_self
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv.symm = D.coordinateComparisonEquiv := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearEquiv.ext
  funext x
  rw [D.coordinateComparisonEquiv_symm_apply x]
  exact (D.coordinateComparisonEquiv_apply x).symm

theorem coordinateComparisonEquiv_apply_eq_apply_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H)
    (x y : P.placeCarrier V) :
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    D.coordinateComparisonEquiv x = D.coordinateComparisonEquiv y ↔ x = y := by
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  constructor
  · exact fun h => D.coordinateComparisonEquiv.injective h
  · intro h
    rw [h]

noncomputable def toBoundedComparisonCoordinateData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    SourceBoundedComparisonCoordinateData S H where
  coordinateComparisonEquiv := D.coordinateComparisonEquiv

noncomputable def toEquivData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    SourceBoundedComparisonEquivData S H where
  comparisonEquiv := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact H.placeEquiv.trans (D.coordinateComparisonEquiv.trans H.placeEquiv.symm)

noncomputable def toBoundedComparisonData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceSignedCoordinateComparisonData S H) :
    SourceBoundedComparisonData S H :=
  D.toEquivData

end SourceSignedCoordinateComparisonData

namespace SourceBoundedComparisonCoordinateData

noncomputable def toEquivData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonCoordinateData S H) :
    SourceBoundedComparisonEquivData S H where
  comparisonEquiv := by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact H.placeEquiv.trans (D.coordinateComparisonEquiv.trans H.placeEquiv.symm)

noncomputable def toBoundedComparisonData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonCoordinateData S H) :
    SourceBoundedComparisonData S H :=
  D.toEquivData

end SourceBoundedComparisonCoordinateData

namespace SourceBoundedComparisonData

def ofEquivData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    SourceBoundedComparisonData S H :=
  D

def comparisonMap
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.comparisonEquiv.toContinuousLinearMap

def comparisonInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier →L[ℝ] H.hilbertCarrier :=
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  D.comparisonEquiv.symm.toContinuousLinearMap

theorem comparisonMap_leftInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse.comp D.comparisonMap =
      ContinuousLinearMap.id ℝ H.hilbertCarrier :=
  by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    apply ContinuousLinearMap.ext
    intro x
    simp [comparisonMap, comparisonInverse]

theorem comparisonMap_rightInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap.comp D.comparisonInverse =
      ContinuousLinearMap.id ℝ H.hilbertCarrier :=
  by
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    apply ContinuousLinearMap.ext
    intro x
    simp [comparisonMap, comparisonInverse]

theorem comparisonMap_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = D.comparisonEquiv x := by
  rfl

theorem comparisonInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = D.comparisonEquiv.symm x := by
  rfl

theorem comparisonMap_leftInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (D.comparisonMap x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_rightInverse_apply
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (D.comparisonInverse x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [comparisonMap, comparisonInverse]

theorem comparisonMap_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_zero

theorem comparisonMap_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (x + y) = D.comparisonMap x + D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_add x y

theorem comparisonMap_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (-x) = -D.comparisonMap x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_neg x

theorem comparisonMap_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (x - y) = D.comparisonMap x - D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_sub x y

theorem comparisonInverse_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_zero

theorem comparisonInverse_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (x + y) =
      D.comparisonInverse x + D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_add x y

theorem comparisonInverse_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (-x) = -D.comparisonInverse x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_neg x

theorem comparisonInverse_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (x - y) =
      D.comparisonInverse x - D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_sub x y

theorem comparisonEquiv_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonEquiv := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.injective

theorem comparisonEquiv_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv x = D.comparisonEquiv y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonEquiv.injective h
  · intro h
    rw [h]

theorem comparisonEquiv_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_zero

theorem comparisonEquiv_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (x + y) =
      D.comparisonEquiv x + D.comparisonEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_add x y

theorem comparisonEquiv_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (-x) = -D.comparisonEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_neg x

theorem comparisonEquiv_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (x - y) =
      D.comparisonEquiv x - D.comparisonEquiv y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_sub x y

theorem comparisonEquiv_symm_map_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_zero

theorem comparisonEquiv_symm_map_add
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (x + y) =
      D.comparisonEquiv.symm x + D.comparisonEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_add x y

theorem comparisonEquiv_symm_map_neg
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (-x) = -D.comparisonEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_neg x

theorem comparisonEquiv_symm_map_sub
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (x - y) =
      D.comparisonEquiv.symm x - D.comparisonEquiv.symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_sub x y

theorem comparisonEquiv_symm_map_smul
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (c • x) = c • D.comparisonEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_smul c x

theorem comparisonEquiv_symm_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonEquiv.symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.injective

theorem comparisonEquiv_symm_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm x = D.comparisonEquiv.symm y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonEquiv.symm.injective h
  · intro h
    rw [h]

theorem comparisonMap_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.comparisonMap := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.comparisonEquiv.symm y, D.comparisonEquiv.right_inv y⟩

theorem comparisonInverse_surjective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonEquivData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.comparisonInverse := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.comparisonEquiv y, D.comparisonEquiv.left_inv y⟩

theorem comparisonMap_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonMap := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro x y h
  exact D.comparisonEquiv.injective h

theorem comparisonInverse_injective
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonInverse := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro x y h
  exact D.comparisonEquiv.symm.injective h

theorem comparisonMap_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = D.comparisonMap y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonMap_injective h
  · intro h
    rw [h]

theorem comparisonInverse_apply_eq_iff_eq
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = D.comparisonInverse y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonInverse_injective h
  · intro h
    rw [h]

theorem comparisonMap_eq_iff_eq_comparisonInverse
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap x = y ↔ x = D.comparisonInverse y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.comparisonEquiv.left_inv x).symm
  · intro h
    rw [h]
    exact D.comparisonEquiv.right_inv y

theorem comparisonInverse_eq_iff_eq_comparisonMap
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse x = y ↔ x = D.comparisonMap y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    rw [← h]
    exact (D.comparisonEquiv.right_inv x).symm
  · intro h
    rw [h]
    exact D.comparisonEquiv.left_inv y

theorem comparisonMap_map_smul_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (c • x) = c • D.comparisonMap x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonMap.map_smul c x

theorem comparisonInverse_map_smul_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (c • x) = c • D.comparisonInverse x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonInverse.map_smul c x

theorem comparisonEquiv_map_smul_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (c • x) = c • D.comparisonEquiv x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.map_smul c x

theorem comparisonEquiv_symm_map_smul_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (c • x) = c • D.comparisonEquiv.symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.map_smul c x

theorem comparisonEquiv_symm_injective_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective D.comparisonEquiv.symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.symm.injective

theorem comparisonEquiv_symm_apply_eq_iff_eq_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm x = D.comparisonEquiv.symm y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact D.comparisonEquiv.symm.injective h
  · intro h
    rw [h]

theorem comparisonMap_surjective_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.comparisonMap := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.comparisonEquiv.symm y, D.comparisonEquiv.right_inv y⟩

theorem comparisonInverse_surjective_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective D.comparisonInverse := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  intro y
  exact ⟨D.comparisonEquiv y, D.comparisonEquiv.left_inv y⟩

theorem comparisonEquiv_leftInverse_apply_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv.symm (D.comparisonEquiv x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.left_inv x

theorem comparisonEquiv_rightInverse_apply_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonEquiv (D.comparisonEquiv.symm x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact D.comparisonEquiv.right_inv x

theorem comparisonMap_leftInverse_apply_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonInverse (D.comparisonMap x) = x :=
  D.comparisonMap_leftInverse_apply x

theorem comparisonMap_rightInverse_apply_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    D.comparisonMap (D.comparisonInverse x) = x :=
  D.comparisonMap_rightInverse_apply x

end SourceBoundedComparisonData


def boundedComparisonMap
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (V : S.PlaceSet) : Prop :=
  ∃ (P : SourcePlaceCarrierData S)
    (H : SourceCanonicalHilbertModelData S P V),
    Nonempty (SourceBoundedComparisonData S H)

def boundedComparisonInverse
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (V : S.PlaceSet) : Prop :=
  ∃ (P : SourcePlaceCarrierData S)
    (H : SourceCanonicalHilbertModelData S P V),
    Nonempty (SourceBoundedComparisonData S H)

theorem boundedComparisonMap_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    S.boundedComparisonMap V :=
  ⟨P, H, ⟨D⟩⟩

theorem boundedComparisonInverse_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    S.boundedComparisonInverse V :=
  ⟨P, H, ⟨D⟩⟩

theorem boundedComparisonMap_and_inverse_of_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {P : SourcePlaceCarrierData S} {V : S.PlaceSet}
    {H : SourceCanonicalHilbertModelData S P V}
    (D : SourceBoundedComparisonData S H) :
    S.boundedComparisonMap V ∧ S.boundedComparisonInverse V :=
  ⟨boundedComparisonMap_of_data D, boundedComparisonInverse_of_data D⟩

def fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Prop :=
  S.soninSpaceComparison I ∧
      S.canonicalHilbertModel S.sourcePlaceSet ∧
        (∀ V : S.PlaceSet,
          S.canonicalHilbertModel V → S.scalingActionImplemented V) ∧
          (∀ V : S.PlaceSet,
            S.canonicalHilbertModel V → S.fourierGradingCompatible V) ∧
          (∀ V : S.PlaceSet,
            S.canonicalHilbertModel V → S.boundedComparisonMap V) ∧
            (∀ V : S.PlaceSet,
              S.canonicalHilbertModel V → S.boundedComparisonInverse V)

theorem fixedWindowExhaustionCompatible_of_rows
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hSonin : S.soninSpaceComparison I)
    (hCanonical : S.canonicalHilbertModel S.sourcePlaceSet)
    (hScaling :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.scalingActionImplemented V)
    (hFourier :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.fourierGradingCompatible V)
    (hMap :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonMap V)
    (hInverse :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonInverse V) :
    S.fixedWindowExhaustionCompatible I :=
  ⟨hSonin, hCanonical, hScaling, hFourier, hMap, hInverse⟩

theorem fixedWindowExhaustionCompatible_of_coordinate_model_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (coordinateRows : SourceFixedWindowCoordinateRows S I)
    (placeCarrierData : SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceFourierCoordinateGradingData S H)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceSignedCoordinateComparisonData S H) :
    S.fixedWindowExhaustionCompatible I := by
  let canonicalModelData := placeCarrierData.canonicalModelData S.sourcePlaceSet
  let hCanonical : S.canonicalHilbertModel S.sourcePlaceSet :=
    canonicalModelData.canonicalHilbertModel
  let hScaling :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.scalingActionImplemented V := by
    intro V _hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.scalingActionImplemented_of_scalar_coordinate_data
      (scalingActionModelData V H)
  let hFourier :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.fourierGradingCompatible V := by
    intro V _hModel
    let H := placeCarrierData.canonicalModelData V
    exact
      S.fourierGradingCompatible_of_data
        (fourierGradingModelData V H)
  let hMap :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonMap V := by
    intro V hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.boundedComparisonMap_of_data
      ((boundedComparisonModelData V H).toBoundedComparisonData)
  let hInverse :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonInverse V := by
    intro V hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.boundedComparisonInverse_of_data
      ((boundedComparisonModelData V H).toBoundedComparisonData)
  exact
    fixedWindowExhaustionCompatible_of_rows
      coordinateRows.soninSpaceComparison hCanonical hScaling hFourier hMap
      hInverse

theorem fixedWindowExhaustionCompatible_of_fourier_coordinate_model_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (coordinateRows : SourceFixedWindowCoordinateRows S I)
    (placeCarrierData : SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceFourierCoordinateGradingData S H)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceSignedCoordinateComparisonData S H) :
    S.fixedWindowExhaustionCompatible I := by
  let canonicalModelData := placeCarrierData.canonicalModelData S.sourcePlaceSet
  let hCanonical : S.canonicalHilbertModel S.sourcePlaceSet :=
    canonicalModelData.canonicalHilbertModel
  let hScaling :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.scalingActionImplemented V := by
    intro V _hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.scalingActionImplemented_of_scalar_coordinate_data
      (scalingActionModelData V H)
  let hFourier :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.fourierGradingCompatible V := by
    intro V _hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.fourierGradingCompatible_of_data (fourierGradingModelData V H)
  let hMap :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonMap V := by
    intro V hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.boundedComparisonMap_of_data
      ((boundedComparisonModelData V H).toBoundedComparisonData)
  let hInverse :
      ∀ V : S.PlaceSet,
        S.canonicalHilbertModel V → S.boundedComparisonInverse V := by
    intro V hModel
    let H := placeCarrierData.canonicalModelData V
    exact S.boundedComparisonInverse_of_data
      ((boundedComparisonModelData V H).toBoundedComparisonData)
  exact
    fixedWindowExhaustionCompatible_of_rows
      coordinateRows.soninSpaceComparison hCanonical hScaling hFourier hMap
      hInverse

theorem fixedWindowExhaustionCompatible_of_line_fourier_coordinate_model_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (coordinateRows : SourceFixedWindowCoordinateRows S I)
    (placeCarrierData : SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (_H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceLineFourierCoordinateGradingData S
            (P := placeCarrierData) V)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceSignedCoordinateComparisonData S H) :
    S.fixedWindowExhaustionCompatible I := by
  exact fixedWindowExhaustionCompatible_of_fourier_coordinate_model_data
    coordinateRows placeCarrierData scalingActionModelData
    (fun V H => (fourierGradingModelData V H).toFourierCoordinateGradingData (H := H))
    boundedComparisonModelData

theorem fixedWindowExhaustionCompatible_of_identity_fourier_coordinate_model_data
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (coordinateRows : SourceFixedWindowCoordinateRows S I)
    (placeCarrierData : SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceScalarCoordinateScalingData S H)
    (_fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (_H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceIdentityFourierCoordinateGradingData S
            (P := placeCarrierData) V)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceCanonicalHilbertModelData S placeCarrierData V),
          SourceSignedCoordinateComparisonData S H) :
    S.fixedWindowExhaustionCompatible I :=
  fixedWindowExhaustionCompatible_of_line_fourier_coordinate_model_data
    coordinateRows placeCarrierData scalingActionModelData
    (fun _V _H => ()) boundedComparisonModelData

theorem soninSpaceComparison_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    S.soninSpaceComparison I :=
  hFixed.1

theorem canonicalHilbertModel_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    S.canonicalHilbertModel S.sourcePlaceSet :=
  hFixed.2.1

theorem scalingActionImplemented_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.scalingActionImplemented V :=
  hFixed.2.2.1

theorem fourierGradingCompatible_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.fourierGradingCompatible V :=
  hFixed.2.2.2.1

theorem boundedComparisonMap_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonMap V :=
  hFixed.2.2.2.2.1

theorem boundedComparisonInverse_of_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (hFixed : S.fixedWindowExhaustionCompatible I) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonInverse V :=
  hFixed.2.2.2.2.2

def toSemilocalModelSymbols
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    SemilocalModelSymbols where
  PlaceSet := S.PlaceSet
  sourcePlaceSet := S.sourcePlaceSet
  Window := S.Window
  Test := A.Test
  sourceTest := S.sourceTest
  sourceInvolution := A.involution
  SupportPoint := S.SupportPoint
  supportCarrier := S.supportCarrier
  fourierSupportCarrier := S.fourierSupportCarrier
  fourierSupportCarrier_eq_supportCarrier_involution :=
    S.fourierSupportCarrier_eq_supportCarrier_involution
  windowCarrier := S.windowCarrier
  lambdaCarrier := S.lambdaCarrier
  canonicalHilbertModel := S.canonicalHilbertModel
  scalingActionImplemented := S.scalingActionImplemented
  fourierGradingCompatible := S.fourierGradingCompatible
  boundedComparisonMap := S.boundedComparisonMap
  boundedComparisonInverse := S.boundedComparisonInverse

@[simp] theorem toSemilocalModelSymbols_PlaceSet
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.PlaceSet = S.PlaceSet :=
  rfl

@[simp] theorem toSemilocalModelSymbols_Window
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.Window = S.Window :=
  rfl

@[simp] theorem toSemilocalModelSymbols_Test
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.Test = A.Test :=
  rfl

@[simp] theorem toSemilocalModelSymbols_sourceInvolution
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.sourceInvolution = A.involution :=
  rfl

@[simp] theorem toSemilocalModelSymbols_canonicalHilbertModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.canonicalHilbertModel =
      S.canonicalHilbertModel :=
  rfl

@[simp] theorem toSemilocalModelSymbols_scalingActionImplemented
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.scalingActionImplemented =
      S.scalingActionImplemented :=
  rfl

@[simp] theorem toSemilocalModelSymbols_fourierGradingCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.fourierGradingCompatible =
      S.fourierGradingCompatible :=
  rfl

@[simp] theorem toSemilocalModelSymbols_supportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.supportInWindow = S.supportInWindow :=
  rfl

@[simp] theorem toSemilocalModelSymbols_fourierSupportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.fourierSupportInWindow =
      S.fourierSupportInWindow :=
  rfl

@[simp] theorem toSemilocalModelSymbols_supportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.supportTransported = S.supportTransported :=
  rfl

@[simp] theorem toSemilocalModelSymbols_convolutionSupportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.convolutionSupportTransported =
      S.convolutionSupportTransported :=
  rfl

@[simp] theorem toSemilocalModelSymbols_windowContainedInLambda
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.windowContainedInLambda =
      S.windowContainedInLambda :=
  rfl

@[simp] theorem toSemilocalModelSymbols_lambdaCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.lambdaCompatible = S.lambdaCompatible :=
  rfl

@[simp] theorem toSemilocalModelSymbols_boundedComparisonMap
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.boundedComparisonMap =
      S.boundedComparisonMap :=
  rfl

@[simp] theorem toSemilocalModelSymbols_boundedComparisonInverse
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.boundedComparisonInverse =
      S.boundedComparisonInverse :=
  rfl

@[simp] theorem toSemilocalModelSymbols_soninSpaceComparison
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.soninSpaceComparison =
      S.soninSpaceComparison :=
  rfl

@[simp] theorem toSemilocalModelSymbols_fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    S.toSemilocalModelSymbols.fixedWindowExhaustionCompatible =
      S.fixedWindowExhaustionCompatible :=
  rfl

namespace SourceFixedWindowCoordinateRows
namespace SourceFourierSupportInvolutionGeometryData

def toSemilocalFourierSupportInvolutionGeometryData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (D : SourceFourierSupportInvolutionGeometryData S I) :
    SemilocalModelSymbols.FourierSupportInvolutionGeometryData
      S.toSemilocalModelSymbols I where
  carrier_eq_involutionSupport := by
    exact
      S.toSemilocalModelSymbols.fourierSupportCarrier_eq_supportCarrier_involution
        S.toSemilocalModelSymbols.sourceTest
  fourierSupportInWindow := by
    simpa using D.fourierSupportInWindow
  convolutionSupportTransported := by
    simpa using D.convolutionSupportTransported
  soninSpaceComparison := by
    simpa using D.soninSpaceComparison

end SourceFourierSupportInvolutionGeometryData
end SourceFixedWindowCoordinateRows

end SourceSupportWindowData

open SourceSupportWindowData

def SourceConvolutionSupportTransportStatement
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Prop :=
  S.convolutionSupportTransported S.sourceTest S.sourceSupportWindow

def SourceWindowLambdaCompatibilityStatement
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Prop :=
  ∀ lambda : ℝ,
    1 < lambda → S.lambdaCompatible S.sourceSupportWindow lambda

def SourceSoninWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Type :=
  { I : S.Window // S.soninSpaceComparison I }

/-- CCM24 semilocal rows over the shared source support/window object. -/
structure SourceSemilocalRows
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) where
  sourceFixedWindowCoordinateRows :
    SourceSupportWindowData.SourceFixedWindowCoordinateRows
      S S.sourceSupportWindow
  sourcePlaceCarrierData :
    SourceSupportWindowData.SourcePlaceCarrierData S
  sourceScalingActionModelData :
    ∀ (V : S.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        S sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceScalarCoordinateScalingData S H
  sourceFourierGradingModelData :
    ∀ (V : S.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        S sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceFourierCoordinateGradingData S H
  sourceBoundedComparisonModelData :
    ∀ (V : S.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        S sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceSignedCoordinateComparisonData S H

namespace SourceSemilocalRows

def ofModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (coordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        S S.sourceSupportWindow)
    (placeCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceFourierCoordinateGradingData S H)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData S H) :
    SourceSemilocalRows S where
  sourceFixedWindowCoordinateRows := coordinateRows
  sourcePlaceCarrierData := placeCarrierData
  sourceScalingActionModelData := scalingActionModelData
  sourceFourierGradingModelData := by
    intro V H
    exact fourierGradingModelData V H
  sourceBoundedComparisonModelData := boundedComparisonModelData

def ofFourierCoordinateModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (coordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        S S.sourceSupportWindow)
    (placeCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceFourierCoordinateGradingData S H)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData S H) :
    SourceSemilocalRows S where
  sourceFixedWindowCoordinateRows := coordinateRows
  sourcePlaceCarrierData := placeCarrierData
  sourceScalingActionModelData := scalingActionModelData
  sourceFourierGradingModelData := fourierGradingModelData
  sourceBoundedComparisonModelData := boundedComparisonModelData

noncomputable def ofLineFourierModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (coordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        S S.sourceSupportWindow)
    (placeCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (_H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceLineFourierCoordinateGradingData
            S (P := placeCarrierData) V)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData S H) :
    SourceSemilocalRows S where
  sourceFixedWindowCoordinateRows := coordinateRows
  sourcePlaceCarrierData := placeCarrierData
  sourceScalingActionModelData := scalingActionModelData
  sourceFourierGradingModelData := by
    intro V H
    exact (fourierGradingModelData V H).toFourierCoordinateGradingData (H := H)
  sourceBoundedComparisonModelData := boundedComparisonModelData

noncomputable def ofIdentityFourierModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (coordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        S S.sourceSupportWindow)
    (placeCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (_H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceIdentityFourierCoordinateGradingData
            S (P := placeCarrierData) V)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData S H) :
    SourceSemilocalRows S where
  sourceFixedWindowCoordinateRows := coordinateRows
  sourcePlaceCarrierData := placeCarrierData
  sourceScalingActionModelData := scalingActionModelData
  sourceFourierGradingModelData := by
    intro V H
    exact (fourierGradingModelData V H).toFourierCoordinateGradingData (H := H)
  sourceBoundedComparisonModelData := boundedComparisonModelData

def canonicalModelData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S)
    (V : S.PlaceSet) :
    SourceSupportWindowData.SourceCanonicalHilbertModelData
      S rows.sourcePlaceCarrierData V :=
  rows.sourcePlaceCarrierData.canonicalModelData V

theorem sourceCanonicalModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.canonicalHilbertModel S.sourcePlaceSet := by
  exact (rows.sourcePlaceCarrierData.canonicalModelData S.sourcePlaceSet).canonicalHilbertModel

theorem sourceScalingActionData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.scalingActionImplemented V := by
  intro V hCanonical
  exact
      S.scalingActionImplemented_of_scalar_coordinate_data
        (rows.sourceScalingActionModelData V
          (rows.canonicalModelData V))

theorem sourceFourierGradingData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.fourierGradingCompatible V := by
  intro V hCanonical
  exact
    S.fourierGradingCompatible_of_data
      (rows.sourceFourierGradingModelData V
        (rows.canonicalModelData V))

theorem sourceBoundedComparisonMapData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonMap V := by
  intro V hCanonical
  exact
      S.boundedComparisonMap_of_data
        ((rows.sourceBoundedComparisonModelData V
          (rows.canonicalModelData V)).toBoundedComparisonData)

theorem sourceBoundedComparisonInverseData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
  ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonInverse V := by
  intro V hCanonical
  exact
    S.boundedComparisonInverse_of_data
      ((rows.sourceBoundedComparisonModelData V
        (rows.canonicalModelData V)).toBoundedComparisonData)

theorem sourceSupportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.supportCarrier S.sourceTest ⊆ S.windowCarrier S.sourceSupportWindow :=
  rows.sourceFixedWindowCoordinateRows.supportCarrier_subset_windowCarrier

theorem sourceFourierSupportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.fourierSupportCarrier S.sourceTest ⊆
      S.windowCarrier S.sourceSupportWindow :=
  rows.sourceFixedWindowCoordinateRows.fourierSupportCarrier_subset_windowCarrier

theorem sourceCanonicalSemilocalModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      S.toSemilocalModelSymbols := by
  intro V hCanonical
  exact
    ⟨rows.sourceScalingActionData V hCanonical,
      rows.sourceFourierGradingData V hCanonical⟩

theorem sourceSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.supportInWindow S.sourceTest S.sourceSupportWindow := by
  exact rows.sourceFixedWindowCoordinateRows.supportInWindow

theorem sourceFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.fourierSupportInWindow S.sourceTest S.sourceSupportWindow := by
  exact rows.sourceFixedWindowCoordinateRows.fourierSupportInWindow

theorem sourceSupportAndFourierSupportTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (_rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.SupportTransportStatement
      S.toSemilocalModelSymbols := by
  intro f I hSupport hFourier
  exact
    ⟨S.supportTransported_of_supportInWindow hSupport,
      S.convolutionSupportTransported_of_fourierSupportInWindow hFourier⟩

theorem sourceConvolutionSupportTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SourceConvolutionSupportTransportStatement S := by
  exact rows.sourceFixedWindowCoordinateRows.convolutionSupportTransported

theorem sourceSoninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.soninSpaceComparison S.sourceSupportWindow := by
  exact rows.sourceFixedWindowCoordinateRows.soninSpaceComparison

theorem sourceWindowContainedInLambdaData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
  ∀ lambda : ℝ,
      1 < lambda → S.windowContainedInLambda S.sourceSupportWindow lambda := by
  intro lambda hlambda
  exact rows.sourceFixedWindowCoordinateRows.windowContainedInLambda hlambda

theorem sourceWindowLambdaCompatibility
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SourceWindowLambdaCompatibilityStatement S := by
  intro lambda hlambda
  exact rows.sourceFixedWindowCoordinateRows.lambdaCompatible hlambda

theorem sourceBoundedComparisonTraceClassTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.BoundedComparisonStatement
      S.toSemilocalModelSymbols := by
  intro V hCanonical
  exact
    ⟨rows.sourceBoundedComparisonMapData V hCanonical,
      rows.sourceBoundedComparisonInverseData V hCanonical⟩

theorem sourceFixedWindowSoninExhaustion
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.SoninComparisonStatement
      S.toSemilocalModelSymbols := by
  intro I hSonin
  exact
    ⟨hSonin,
      rows.sourceCanonicalModel,
      rows.sourceScalingActionData,
      rows.sourceFourierGradingData,
      rows.sourceBoundedComparisonMapData,
      rows.sourceBoundedComparisonInverseData⟩

end SourceSemilocalRows

namespace SourceConcreteBaseLayer

theorem concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    (z : ConcreteSupportPoint) :
    SourceSupportWindowData.closedWindowZeroKernel
        (concreteSupportWindowData I sourceTest) I
        concreteRawSupportKernel f z =
      concreteSupportValue I f z := by
  classical
  by_cases hz : pointInConcreteWindow I z
  · have hcond : I.1 ≤ z.1 ∧ z.1 ≤ I.2 ∧ z.2 = 0 := by
      simpa [pointInConcreteWindow] using hz
    simp [SourceSupportWindowData.closedWindowZeroKernel,
      SourceSupportWindowData.closedWindowZeroSet,
      concreteSupportWindowData, concreteRawSupportKernel,
      concreteSupportValue, pointInConcreteWindow, hcond]
  · have hcond : ¬(I.1 ≤ z.1 ∧ z.1 ≤ I.2 ∧ z.2 = 0) := by
      intro h
      exact hz (by simpa [pointInConcreteWindow] using h)
    simp [SourceSupportWindowData.closedWindowZeroKernel,
      SourceSupportWindowData.closedWindowZeroSet,
      concreteSupportWindowData, concreteSupportValue, pointInConcreteWindow,
      hcond]

noncomputable def concreteRealPlaceCarrierData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    SourceSupportWindowData.SourcePlaceCarrierData
      (concreteSupportWindowData I sourceTest) where
  placeCarrier := fun _ => ℝ
  placeCarrierNormedAddCommGroup := fun _ => inferInstance
  placeCarrierInnerProductSpace := fun _ => inferInstance
  placeCarrierCompleteSpace := fun _ => inferInstance
  sourcePlaceCarrierNonempty := ⟨0⟩

noncomputable def concreteRealCanonicalModelData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    SourceSupportWindowData.SourceCanonicalHilbertModelData
      (concreteSupportWindowData I sourceTest)
      (concreteRealPlaceCarrierData I sourceTest) V :=
  (concreteRealPlaceCarrierData I sourceTest).canonicalModelData V

theorem concreteRealCanonicalHilbertModel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    (concreteSupportWindowData I sourceTest).canonicalHilbertModel V :=
  ⟨concreteRealPlaceCarrierData I sourceTest,
    ⟨concreteRealCanonicalModelData I sourceTest V⟩⟩

noncomputable def concreteRealCoordinateScaleEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (u : ℝˣ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact u • ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)

theorem concreteRealCoordinateScaleEquiv_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (u : ℝˣ)
    (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleEquiv I sourceTest V u x = (u : ℝ) • x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateScaleEquiv]

noncomputable def concreteRealCoordinateScaleAction
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V →L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact a • ContinuousLinearMap.id ℝ (P.placeCarrier V)

theorem concreteRealCoordinateScaleAction_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a : ℝ)
    (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V a x = a • x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateScaleAction]

theorem concreteRealCoordinateScaleAction_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V 0 = 0 := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp [concreteRealCoordinateScaleAction]

theorem concreteRealCoordinateScaleAction_add
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a b : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V (a + b) =
      concreteRealCoordinateScaleAction I sourceTest V a +
        concreteRealCoordinateScaleAction I sourceTest V b := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp [concreteRealCoordinateScaleAction, add_smul]

theorem concreteRealCoordinateScaleAction_neg
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V (-a) =
      -concreteRealCoordinateScaleAction I sourceTest V a := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp [concreteRealCoordinateScaleAction]

theorem concreteRealCoordinateScaleAction_sub
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a b : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V (a - b) =
      concreteRealCoordinateScaleAction I sourceTest V a -
        concreteRealCoordinateScaleAction I sourceTest V b := by
  rw [sub_eq_add_neg]
  rw [concreteRealCoordinateScaleAction_add
    (I := I) (sourceTest := sourceTest) (V := V) a (-b)]
  rw [concreteRealCoordinateScaleAction_neg
    (I := I) (sourceTest := sourceTest) (V := V) b]
  rfl

theorem concreteRealCoordinateScaleEquiv_one
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleEquiv I sourceTest V 1 =
      ContinuousLinearEquiv.refl ℝ
        ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearEquiv.ext
  funext x
  simp [concreteRealCoordinateScaleEquiv]

theorem concreteRealCoordinateScaleEquiv_mul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a b : ℝˣ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleEquiv I sourceTest V (a * b) =
      (concreteRealCoordinateScaleEquiv I sourceTest V a).trans
        (concreteRealCoordinateScaleEquiv I sourceTest V b) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearEquiv.ext
  funext x
  simp [concreteRealCoordinateScaleEquiv, mul_smul]

theorem concreteRealCoordinateScaleAction_units
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (u : ℝˣ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V (u : ℝ) =
      (concreteRealCoordinateScaleEquiv I sourceTest V u).toContinuousLinearMap := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp [concreteRealCoordinateScaleAction, concreteRealCoordinateScaleEquiv]

theorem concreteRealCoordinateScaleAction_one
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V 1 =
      ContinuousLinearMap.id ℝ
        ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp [concreteRealCoordinateScaleAction]

theorem concreteRealCoordinateScaleAction_mul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (a b : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateScaleAction I sourceTest V (a * b) =
      (concreteRealCoordinateScaleAction I sourceTest V a).comp
        (concreteRealCoordinateScaleAction I sourceTest V b) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  apply ContinuousLinearMap.ext
  intro x
  simp only [concreteRealCoordinateScaleAction,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [smul_smul]

noncomputable def concreteRealScalarCoordinateScalingData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceScalarCoordinateScalingData
      (concreteSupportWindowData I sourceTest) H :=
  { coordinateScaleEquiv := concreteRealCoordinateScaleEquiv I sourceTest V
    coordinateScaleEquiv_apply := by
      intro u x
      exact concreteRealCoordinateScaleEquiv_apply I sourceTest V u x
    coordinateScaleEquiv_one :=
      concreteRealCoordinateScaleEquiv_one I sourceTest V
    coordinateScaleEquiv_mul :=
      concreteRealCoordinateScaleEquiv_mul I sourceTest V
    coordinateScaleAction := concreteRealCoordinateScaleAction I sourceTest V
    coordinateScaleAction_apply := by
      intro a x
      exact concreteRealCoordinateScaleAction_apply I sourceTest V a x
    coordinateScaleAction_units :=
      concreteRealCoordinateScaleAction_units I sourceTest V
    coordinateScaleAction_one :=
      concreteRealCoordinateScaleAction_one I sourceTest V
    coordinateScaleAction_mul :=
      concreteRealCoordinateScaleAction_mul I sourceTest V }

noncomputable def concreteRealScalingCoordinateActionData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceScalingCoordinateActionData
      (concreteSupportWindowData I sourceTest) H :=
  (concreteRealScalarCoordinateScalingData I sourceTest V H)
    |>.toScalingCoordinateActionData

noncomputable def concreteRealScalingActionData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
      (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceScalingActionData
      (concreteSupportWindowData I sourceTest) H :=
  (concreteRealScalingCoordinateActionData I sourceTest V H).toScalingActionData

noncomputable def concreteRealCoordinateLineGradeSubspace
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    Submodule ℝ ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact Submodule.span ℝ ({v} : Set (P.placeCarrier V))

noncomputable def concreteRealCoordinateFourierEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)

noncomputable def transportedConcreteSourceFourierCoordinateEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)

theorem transportedConcreteSourceFourierCoordinateEquiv_eq_refl_of_source_fourier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    transportedConcreteSourceFourierCoordinateEquiv I sourceTest V =
      ContinuousLinearEquiv.refl ℝ
        ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  rfl

noncomputable def intendedConcreteRealCoordinateFourierEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V :=
  transportedConcreteSourceFourierCoordinateEquiv I sourceTest V

theorem intendedConcreteRealCoordinateFourierEquiv_source_involution
    (f : ConcreteTest) :
    concreteTestAlgebra.involution f = FourierTransform.fourier f :=
  concreteTestAlgebra_involution f

theorem concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateFourierEquiv I sourceTest V =
      transportedConcreteSourceFourierCoordinateEquiv I sourceTest V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  rfl

theorem concreteRealCoordinateFourierEquiv_realizes_source_involution
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateFourierEquiv I sourceTest V =
      intendedConcreteRealCoordinateFourierEquiv I sourceTest V := by
  exact concreteRealCoordinateFourierEquiv_eq_transported_source_fourier
    (I := I) (sourceTest := sourceTest) (V := V)

theorem concreteRealCoordinateLineGradeSubspace_generator_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    v ∈ concreteRealCoordinateLineGradeSubspace I sourceTest V v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact Submodule.subset_span (by simp)

theorem concreteRealCoordinateLineGradeSubspace_mem_iff_exists_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    x ∈ concreteRealCoordinateLineGradeSubspace I sourceTest V v ↔
      ∃ c : ℝ, c • v = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simpa [concreteRealCoordinateLineGradeSubspace] using
    (Submodule.mem_span_singleton (R := ℝ) (x := x) (y := v))

theorem concreteRealCoordinateLineGradeSubspace_smul_generator_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (c : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    c • v ∈ concreteRealCoordinateLineGradeSubspace I sourceTest V v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealCoordinateLineGradeSubspace_mem_iff_exists_smul
      (I := I) (sourceTest := sourceTest) (V := V) v (c • v)).2
      ⟨c, rfl⟩

theorem concreteRealCoordinateLineGradeSubspace_le_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (W : letI := (concreteRealPlaceCarrierData I sourceTest)
          |>.placeCarrierNormedAddCommGroup V
         letI := (concreteRealPlaceCarrierData I sourceTest)
          |>.placeCarrierInnerProductSpace V
         Submodule ℝ ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V)) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateLineGradeSubspace I sourceTest V v ≤ W ↔
      v ∈ W := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateLineGradeSubspace]

theorem concreteRealCoordinateLineGradeSubspace_eq_bot_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateLineGradeSubspace I sourceTest V v = ⊥ ↔
      v = 0 := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateLineGradeSubspace]

theorem concreteRealCoordinateFourierEquiv_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateFourierEquiv I sourceTest V x = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateFourierEquiv]

theorem concreteRealCoordinateFourierEquiv_symm_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealCoordinateFourierEquiv I sourceTest V).symm x = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateFourierEquiv]

theorem concreteRealCoordinateFourier_mem_lineGrade_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateFourierEquiv I sourceTest V x ∈
        concreteRealCoordinateLineGradeSubspace I sourceTest V v ↔
      x ∈ concreteRealCoordinateLineGradeSubspace I sourceTest V v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp [concreteRealCoordinateFourierEquiv]

theorem concreteRealCoordinateFourier_preserves_grade
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    x ∈ concreteRealCoordinateLineGradeSubspace I sourceTest V v →
      concreteRealCoordinateFourierEquiv I sourceTest V x ∈
        concreteRealCoordinateLineGradeSubspace I sourceTest V v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  intro hx
  exact
    (concreteRealCoordinateFourier_mem_lineGrade_iff
      (I := I) (sourceTest := sourceTest) (V := V) v x).2 hx

structure ConcreteRealCoordinateFourierTransformSemanticsData
    (I : ConcreteWindow)
    (sourceTest : ConcreteTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) where
  coordinateGradeIndex : Type
  coordinateGradeSubspace :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    coordinateGradeIndex → Submodule ℝ
      ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
  coordinateFourierEquiv :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V
  coordinateFourier_transform_law :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    coordinateFourierEquiv =
      intendedConcreteRealCoordinateFourierEquiv I sourceTest V
  source_involution_transform_law :
    ∀ f : ConcreteTest,
      concreteTestAlgebra.involution f = FourierTransform.fourier f
  coordinateFourier_preserves_grade :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    ∀ (n : coordinateGradeIndex)
      (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V),
      x ∈ coordinateGradeSubspace n →
        coordinateFourierEquiv x ∈ coordinateGradeSubspace n

namespace ConcreteRealCoordinateFourierTransformSemanticsData

noncomputable def toFourierCoordinateGradingData
    {I : ConcreteWindow}
    {sourceTest : ConcreteTest}
    {V : (concreteSupportWindowData I sourceTest).PlaceSet}
    {H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V}
    (D : ConcreteRealCoordinateFourierTransformSemanticsData I sourceTest V) :
    SourceSupportWindowData.SourceFourierCoordinateGradingData
      (concreteSupportWindowData I sourceTest) H where
  coordinateGradeIndex := D.coordinateGradeIndex
  coordinateGradeSubspace := D.coordinateGradeSubspace
  coordinateFourierEquiv := D.coordinateFourierEquiv
  coordinateFourier_preserves_grade := D.coordinateFourier_preserves_grade

@[simp] theorem toFourierCoordinateGradingData_transform_law
    {I : ConcreteWindow}
    {sourceTest : ConcreteTest}
    {V : (concreteSupportWindowData I sourceTest).PlaceSet}
    {H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V}
    (D : ConcreteRealCoordinateFourierTransformSemanticsData I sourceTest V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (D.toFourierCoordinateGradingData (H := H)).coordinateFourierEquiv =
      intendedConcreteRealCoordinateFourierEquiv I sourceTest V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact D.coordinateFourier_transform_law

end ConcreteRealCoordinateFourierTransformSemanticsData

noncomputable def concreteRealSignedComparisonEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    H.hilbertCarrier ≃L[ℝ] H.hilbertCarrier := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (-1 : ℝˣ) • ContinuousLinearEquiv.refl ℝ H.hilbertCarrier

theorem concreteRealSignedComparisonEquiv_map_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).map_zero

theorem concreteRealSignedComparisonEquiv_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H x = -x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [concreteRealSignedComparisonEquiv]

theorem concreteRealSignedComparisonEquiv_symm_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm x = -x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [concreteRealSignedComparisonEquiv]

theorem concreteRealSignedComparisonEquiv_map_add
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H (x + y) =
      concreteRealSignedComparisonEquiv I sourceTest V H x +
        concreteRealSignedComparisonEquiv I sourceTest V H y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).map_add x y

theorem concreteRealSignedComparisonEquiv_map_neg
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H (-x) =
      -concreteRealSignedComparisonEquiv I sourceTest V H x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).map_neg x

theorem concreteRealSignedComparisonEquiv_map_sub
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H (x - y) =
      concreteRealSignedComparisonEquiv I sourceTest V H x -
        concreteRealSignedComparisonEquiv I sourceTest V H y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).map_sub x y

theorem concreteRealSignedComparisonEquiv_map_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H (c • x) =
      c • concreteRealSignedComparisonEquiv I sourceTest V H x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).map_smul c x

theorem concreteRealSignedComparisonEquiv_injective
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective (concreteRealSignedComparisonEquiv I sourceTest V H) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).injective

theorem concreteRealSignedComparisonEquiv_surjective
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective (concreteRealSignedComparisonEquiv I sourceTest V H) := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).surjective

theorem concreteRealSignedComparisonEquiv_apply_eq_iff_eq
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H x =
        concreteRealSignedComparisonEquiv I sourceTest V H y ↔ x = y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  constructor
  · intro h
    exact (concreteRealSignedComparisonEquiv I sourceTest V H).injective h
  · intro h
    rw [h]

theorem concreteRealSignedComparisonEquiv_symm_map_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm 0 = 0 := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.map_zero

theorem concreteRealSignedComparisonEquiv_symm_map_add
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm (x + y) =
      (concreteRealSignedComparisonEquiv I sourceTest V H).symm x +
        (concreteRealSignedComparisonEquiv I sourceTest V H).symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.map_add x y

theorem concreteRealSignedComparisonEquiv_symm_map_neg
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm (-x) =
      -(concreteRealSignedComparisonEquiv I sourceTest V H).symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.map_neg x

theorem concreteRealSignedComparisonEquiv_symm_map_sub
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x y : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm (x - y) =
      (concreteRealSignedComparisonEquiv I sourceTest V H).symm x -
        (concreteRealSignedComparisonEquiv I sourceTest V H).symm y := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.map_sub x y

theorem concreteRealSignedComparisonEquiv_symm_map_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (c : ℝ) (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    (concreteRealSignedComparisonEquiv I sourceTest V H).symm (c • x) =
      c • (concreteRealSignedComparisonEquiv I sourceTest V H).symm x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.map_smul c x

theorem concreteRealSignedComparisonEquiv_symm_injective
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Injective
      (concreteRealSignedComparisonEquiv I sourceTest V H).symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.injective

theorem concreteRealSignedComparisonEquiv_symm_surjective
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    Function.Surjective
      (concreteRealSignedComparisonEquiv I sourceTest V H).symm := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  exact (concreteRealSignedComparisonEquiv I sourceTest V H).symm.surjective

theorem concreteRealSignedComparisonEquiv_involutive
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    concreteRealSignedComparisonEquiv I sourceTest V H
        (concreteRealSignedComparisonEquiv I sourceTest V H x) = x := by
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  simp [concreteRealSignedComparisonEquiv]

noncomputable def concreteRealCoordinateSignedComparisonEquiv
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealPlaceCarrierData I sourceTest).placeCarrier V ≃L[ℝ]
      (concreteRealPlaceCarrierData I sourceTest).placeCarrier V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact (-1 : ℝˣ) • ContinuousLinearEquiv.refl ℝ (P.placeCarrier V)

theorem concreteRealCoordinateSignedComparisonEquiv_involutive
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    concreteRealCoordinateSignedComparisonEquiv I sourceTest V
        (concreteRealCoordinateSignedComparisonEquiv I sourceTest V x) = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  simp only [concreteRealCoordinateSignedComparisonEquiv,
    ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply]
  rw [smul_smul]
  norm_num

noncomputable def concreteRealBoundedComparisonCoordinateData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceBoundedComparisonCoordinateData
      (concreteSupportWindowData I sourceTest) H :=
    (SourceSupportWindowData.SourceSignedCoordinateComparisonData.neg
        (S := concreteSupportWindowData I sourceTest)
        (P := concreteRealPlaceCarrierData I sourceTest)
        (V := V) H)
      |>.toBoundedComparisonCoordinateData

noncomputable def concreteRealSignedCoordinateComparisonData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceSignedCoordinateComparisonData
      (concreteSupportWindowData I sourceTest) H where
  coordinateComparisonEquiv :=
    concreteRealCoordinateSignedComparisonEquiv I sourceTest V
  coordinateComparisonEquiv_apply := by
    let P := concreteRealPlaceCarrierData I sourceTest
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    intro x
    simp [concreteRealCoordinateSignedComparisonEquiv]
  coordinateComparisonEquiv_involutive := by
    intro x
    exact concreteRealCoordinateSignedComparisonEquiv_involutive
      (I := I) (sourceTest := sourceTest) (V := V) x
  coordinateComparisonEquiv_symm_apply := by
    let P := concreteRealPlaceCarrierData I sourceTest
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    intro x
    simp [concreteRealCoordinateSignedComparisonEquiv]
  coordinateComparisonEquiv_comp_self := by
    let P := concreteRealPlaceCarrierData I sourceTest
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.smul_apply, ContinuousLinearEquiv.refl_apply,
      ContinuousLinearMap.id_apply, concreteRealCoordinateSignedComparisonEquiv]
    rw [smul_smul]
    norm_num

noncomputable def concreteRealIdentityFourierCoordinateGradingData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    SourceSupportWindowData.SourceIdentityFourierCoordinateGradingData
      (concreteSupportWindowData I sourceTest)
      (P := concreteRealPlaceCarrierData I sourceTest) V where
  coordinateGradeIndex := (concreteRealPlaceCarrierData I sourceTest).placeCarrier V
  coordinateGradeSubspace := concreteRealCoordinateLineGradeSubspace I sourceTest V

def concreteRealLineFourierCoordinateGradingData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    SourceSupportWindowData.SourceLineFourierCoordinateGradingData
      (concreteSupportWindowData I sourceTest)
      (P := concreteRealPlaceCarrierData I sourceTest) V :=
  ()

noncomputable def concreteRealCoordinateFourierTransformSemanticsData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    ConcreteRealCoordinateFourierTransformSemanticsData I sourceTest V where
  coordinateGradeIndex := (concreteRealPlaceCarrierData I sourceTest).placeCarrier V
  coordinateGradeSubspace := concreteRealCoordinateLineGradeSubspace I sourceTest V
  coordinateFourierEquiv := concreteRealCoordinateFourierEquiv I sourceTest V
  coordinateFourier_transform_law := by
    let P := concreteRealPlaceCarrierData I sourceTest
    letI := P.placeCarrierNormedAddCommGroup V
    letI := P.placeCarrierInnerProductSpace V
    exact concreteRealCoordinateFourierEquiv_realizes_source_involution
      (I := I) (sourceTest := sourceTest) (V := V)
  source_involution_transform_law := by
    intro f
    exact intendedConcreteRealCoordinateFourierEquiv_source_involution f
  coordinateFourier_preserves_grade := by
    intro v x hx
    exact concreteRealCoordinateFourier_preserves_grade
      (I := I) (sourceTest := sourceTest) (V := V) v x hx

theorem concreteRealLineFourierCoordinateGradingData_gradeSubspace_eq
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v =
      concreteRealCoordinateLineGradeSubspace I sourceTest V v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  rfl

theorem concreteRealLineFourierCoordinateGradingData_mem_iff_exists_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    x ∈ (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v ↔
      ∃ c : ℝ, c • v = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.mem_gradeSubspace_iff_exists_smul v x

theorem concreteRealLineFourierCoordinateGradingData_coe_eq_range_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    ↑((concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v) =
      Set.range (fun c : ℝ => c • v) := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.gradeSubspace_coe_eq_range_smul v

theorem concreteRealLineFourierCoordinateGradingData_eq_top_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v = ⊤ ↔
      ∀ x : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V,
        ∃ c : ℝ, c • v = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.gradeSubspace_eq_top_iff v

theorem concreteRealLineFourierCoordinateGradingData_smul_generator_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (c : ℝ) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    c • v ∈
      (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.smul_generator_mem_gradeSubspace v c

theorem concreteRealLineFourierCoordinateGradingData_le_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (W : letI := (concreteRealPlaceCarrierData I sourceTest)
          |>.placeCarrierNormedAddCommGroup V
         letI := (concreteRealPlaceCarrierData I sourceTest)
          |>.placeCarrierInnerProductSpace V
         Submodule ℝ ((concreteRealPlaceCarrierData I sourceTest).placeCarrier V)) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v ≤ W ↔
      v ∈ W := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.gradeSubspace_le_iff v W

theorem concreteRealLineFourierCoordinateGradingData_eq_bot_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealLineFourierCoordinateGradingData I sourceTest V).gradeSubspace v = ⊥ ↔
      v = 0 := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealLineFourierCoordinateGradingData I sourceTest V)
      |>.gradeSubspace_eq_bot_iff v

noncomputable def concreteRealFourierCoordinateGradingData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceFourierCoordinateGradingData
      (concreteSupportWindowData I sourceTest) H :=
  (concreteRealCoordinateFourierTransformSemanticsData I sourceTest V)
    |>.toFourierCoordinateGradingData (H := H)

noncomputable def concreteRealFourierGradingData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceFourierGradingData
      (concreteSupportWindowData I sourceTest) H :=
  (concreteRealFourierCoordinateGradingData I sourceTest V H).toFourierGradingData

theorem concreteRealCoordinateFourierTransformSemanticsData_transform_law
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealCoordinateFourierTransformSemanticsData I sourceTest V)
        |>.coordinateFourierEquiv =
      intendedConcreteRealCoordinateFourierEquiv I sourceTest V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    (concreteRealCoordinateFourierTransformSemanticsData I sourceTest V)
      |>.coordinateFourier_transform_law

theorem concreteRealFourierCoordinateGradingData_transform_law
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealFourierCoordinateGradingData I sourceTest V H)
        |>.coordinateFourierEquiv =
      intendedConcreteRealCoordinateFourierEquiv I sourceTest V := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  exact
    ConcreteRealCoordinateFourierTransformSemanticsData.toFourierCoordinateGradingData_transform_law
      (D := concreteRealCoordinateFourierTransformSemanticsData I sourceTest V)
      (H := H)

theorem concreteRealFourierCoordinateGradingData_source_involution
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (f : ConcreteTest) :
    concreteTestAlgebra.involution f = FourierTransform.fourier f :=
  (concreteRealCoordinateFourierTransformSemanticsData I sourceTest V)
    |>.source_involution_transform_law f

theorem concreteRealFourierGradingData_mem_gradeSubspace_iff_exists_smul
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    x ∈ (concreteRealFourierGradingData I sourceTest V H).gradeSubspace v ↔
      ∃ c : ℝ, c • v = H.placeEquiv x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  change H.placeEquiv x ∈
      concreteRealCoordinateLineGradeSubspace I sourceTest V v ↔
    ∃ c : ℝ, c • v = H.placeEquiv x
  exact concreteRealCoordinateLineGradeSubspace_mem_iff_exists_smul
    (I := I) (sourceTest := sourceTest) (V := V) v (H.placeEquiv x)

theorem concreteRealFourierGradingData_placeEquiv_symm_smul_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (v : (concreteRealPlaceCarrierData I sourceTest).placeCarrier V)
    (c : ℝ) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    H.placeEquiv.symm (c • v) ∈
      (concreteRealFourierGradingData I sourceTest V H).gradeSubspace v := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  change H.placeEquiv (H.placeEquiv.symm (c • v)) ∈
    concreteRealCoordinateLineGradeSubspace I sourceTest V v
  simpa using concreteRealCoordinateLineGradeSubspace_smul_generator_mem
    (I := I) (sourceTest := sourceTest) (V := V) v c

theorem concreteRealFourierGradingData_fourierEquiv_apply
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V)
    (x : H.hilbertCarrier) :
    letI := H.instNormedAddCommGroup
    letI := H.instInnerProductSpace
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierNormedAddCommGroup V
    letI := (concreteRealPlaceCarrierData I sourceTest)
      |>.placeCarrierInnerProductSpace V
    (concreteRealFourierGradingData I sourceTest V H).fourierEquiv x = x := by
  let P := concreteRealPlaceCarrierData I sourceTest
  letI := H.instNormedAddCommGroup
  letI := H.instInnerProductSpace
  letI := P.placeCarrierNormedAddCommGroup V
  letI := P.placeCarrierInnerProductSpace V
  change H.placeEquiv.symm
      (concreteRealCoordinateFourierEquiv I sourceTest V (H.placeEquiv x)) = x
  rw [concreteRealCoordinateFourierEquiv_apply
    (I := I) (sourceTest := sourceTest) (V := V) (H.placeEquiv x)]
  exact H.placeEquiv.symm_apply_apply x

noncomputable def concreteRealBoundedComparisonData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet)
    (H :
      SourceSupportWindowData.SourceCanonicalHilbertModelData
        (concreteSupportWindowData I sourceTest)
        (concreteRealPlaceCarrierData I sourceTest) V) :
    SourceSupportWindowData.SourceBoundedComparisonData
      (concreteSupportWindowData I sourceTest) H where
  comparisonEquiv :=
    (concreteRealSignedCoordinateComparisonData I sourceTest V H)
      |>.toBoundedComparisonData
      |>.comparisonEquiv

theorem concreteRealScalingActionImplemented
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    (concreteSupportWindowData I sourceTest).scalingActionImplemented V :=
  SourceSupportWindowData.scalingActionImplemented_of_scalar_coordinate_data
    (concreteRealScalarCoordinateScalingData I sourceTest V
      (concreteRealCanonicalModelData I sourceTest V))

theorem concreteRealFourierGradingCompatible
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    (concreteSupportWindowData I sourceTest).fourierGradingCompatible V :=
  SourceSupportWindowData.fourierGradingCompatible_of_data
    (H := concreteRealCanonicalModelData I sourceTest V)
    (concreteRealFourierCoordinateGradingData I sourceTest V
      (concreteRealCanonicalModelData I sourceTest V))

theorem concreteRealBoundedComparisonMap
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    (concreteSupportWindowData I sourceTest).boundedComparisonMap V :=
  SourceSupportWindowData.boundedComparisonMap_of_data
    (concreteRealBoundedComparisonData I sourceTest V
      (concreteRealCanonicalModelData I sourceTest V))

theorem concreteRealBoundedComparisonInverse
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (V : (concreteSupportWindowData I sourceTest).PlaceSet) :
    (concreteSupportWindowData I sourceTest).boundedComparisonInverse V :=
  SourceSupportWindowData.boundedComparisonInverse_of_data
    (concreteRealBoundedComparisonData I sourceTest V
      (concreteRealCanonicalModelData I sourceTest V))

noncomputable def concreteFixedWindowCoordinateRows
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    SourceSupportWindowData.SourceFixedWindowCoordinateRows
      (concreteSupportWindowData I sourceTest) I where
  sourceSupportClosedWindowZeroKernelModel :=
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer
      I sourceTest

theorem concreteBaseLayer_rawSupportKernel_eq_concreteRawSupportKernel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).rawSupportKernel =
      concreteRawSupportKernel := by
  simp [concreteFixedWindowCoordinateRows,
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer]

theorem concreteClosedWindowZeroSet_iff
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (z : ℝ × ℝ) :
    z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I ↔
      I.1 ≤ z.1 ∧ z.1 ≤ I.2 ∧ z.2 = 0 := by
  rfl

theorem concreteClosedWindowZeroSet_mk
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {z : ℝ × ℝ}
    (hLower : I.1 ≤ z.1) (hUpper : z.1 ≤ I.2) (hLog : z.2 = 0) :
    z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
  exact ⟨hLower, hUpper, hLog⟩

theorem concreteClosedWindowZeroSet_lower
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    I.1 ≤ z.1 :=
  hz.1

theorem concreteClosedWindowZeroSet_upper
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    z.1 ≤ I.2 :=
  hz.2.1

theorem concreteClosedWindowZeroSet_logScale_eq_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    z.2 = 0 :=
  hz.2.2

theorem concreteClosedWindowZeroKernel_eq_raw_of_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    SourceSupportWindowData.closedWindowZeroKernel
        (concreteSupportWindowData I sourceTest) I
        concreteRawSupportKernel f z =
      concreteRawSupportKernel f z := by
  simp [SourceSupportWindowData.closedWindowZeroKernel, hz]

theorem concreteClosedWindowZeroKernel_eq_zero_of_not_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz : z ∉ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    SourceSupportWindowData.closedWindowZeroKernel
        (concreteSupportWindowData I sourceTest) I
        concreteRawSupportKernel f z = 0 := by
  simp [SourceSupportWindowData.closedWindowZeroKernel, hz]

theorem concreteSupportKernel_eq_raw_of_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f z =
      concreteRawSupportKernel f z := by
  simpa [concreteFixedWindowCoordinateRows,
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer,
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.supportKernel] using
      concreteClosedWindowZeroKernel_eq_raw_of_mem I sourceTest hz

theorem concreteSupportKernel_eq_concreteRawSupportKernel_of_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz : z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f z =
      concreteRawSupportKernel f z := by
  exact concreteSupportKernel_eq_raw_of_mem I sourceTest hz

theorem concreteSupportKernel_eq_zero_of_not_mem
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz : z ∉ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f z = 0 := by
  simpa [concreteFixedWindowCoordinateRows,
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer,
    SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.supportKernel] using
      concreteClosedWindowZeroKernel_eq_zero_of_not_mem I sourceTest hz

theorem concreteSupportKernel_ne_zero_iff_closedWindow_raw_ne_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (f : ConcreteTest) (z : ℝ × ℝ) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f z ≠ 0 ↔
      z ∈ SourceSupportWindowData.closedWindowZeroSet
          (concreteSupportWindowData I sourceTest) I ∧
        concreteRawSupportKernel f z ≠ 0 := by
  exact
    by
      simpa [concreteFixedWindowCoordinateRows,
        SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer] using
        (((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel)
            |>.supportKernel_ne_zero_iff f z)

theorem concreteMemClosedWindowZeroSet_of_supportKernel_ne_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz :
      ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f z ≠ 0) :
    z ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
  exact
    ((concreteFixedWindowCoordinateRows I sourceTest)
      |>.sourceSupportClosedWindowZeroKernelModel)
        |>.mem_closedWindowZeroSet_of_supportKernel_ne_zero hz

theorem concreteSupportFootprint_subset_closedWindowZeroSet
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    (f : ConcreteTest) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportFootprint f ⊆
      SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
  exact
    ((concreteFixedWindowCoordinateRows I sourceTest)
      |>.sourceSupportClosedWindowZeroKernelModel)
        |>.supportFootprint_subset_closedWindowZeroSet f

theorem concreteSupportFootprint_coordinateLower
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz :
      z ∈ ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportFootprint f) :
    I.1 ≤ z.1 := by
  exact
    concreteClosedWindowZeroSet_lower I sourceTest
      (concreteSupportFootprint_subset_closedWindowZeroSet I sourceTest f hz)

theorem concreteSupportFootprint_coordinateUpper
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz :
      z ∈ ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportFootprint f) :
    z.1 ≤ I.2 := by
  exact
    concreteClosedWindowZeroSet_upper I sourceTest
      (concreteSupportFootprint_subset_closedWindowZeroSet I sourceTest f hz)

theorem concreteSupportFootprint_logScale_eq_zero
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest)
    {f : ConcreteTest} {z : ℝ × ℝ}
    (hz :
      z ∈ ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportFootprint f) :
    z.2 = 0 := by
  exact
    concreteClosedWindowZeroSet_logScale_eq_zero I sourceTest
      (concreteSupportFootprint_subset_closedWindowZeroSet I sourceTest f hz)

theorem concreteSupportValue_eq_supportKernel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    (x : ConcreteSupportPoint) :
    (concreteSupportWindowData I sourceTest).supportValue f x =
      ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f x := by
  exact
    ((concreteFixedWindowCoordinateRows I sourceTest)
      |>.sourceSupportClosedWindowZeroKernelModel)
        |>.supportValue_eq_supportKernel f x

theorem concreteSupportValue_eq_kernel_raw_of_pointInWindow
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : pointInConcreteWindow I x) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f x =
      concreteRawSupportKernel f x := by
  have hz :
      x ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
    simpa [pointInConcreteWindow] using hx
  exact concreteSupportKernel_eq_raw_of_mem I sourceTest hz

theorem concreteSupportValue_eq_kernel_zero_of_not_pointInWindow
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : ¬pointInConcreteWindow I x) :
    ((concreteFixedWindowCoordinateRows I sourceTest)
        |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f x = 0 := by
  have hz :
      x ∉ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
    intro h
    exact hx (by simpa [pointInConcreteWindow] using h)
  exact concreteSupportKernel_eq_zero_of_not_mem I sourceTest hz

theorem concreteSupportValue_ne_zero_mem_closedWindowZeroSet
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : (concreteSupportWindowData I sourceTest).supportValue f x ≠ 0) :
    x ∈ SourceSupportWindowData.closedWindowZeroSet
        (concreteSupportWindowData I sourceTest) I := by
  have hKernel :
      ((concreteFixedWindowCoordinateRows I sourceTest)
          |>.sourceSupportClosedWindowZeroKernelModel).supportKernel f x ≠ 0 := by
    simpa [(concreteSupportValue_eq_supportKernel I sourceTest f x).symm] using hx
  exact concreteMemClosedWindowZeroSet_of_supportKernel_ne_zero I sourceTest hKernel

theorem concreteSupportValue_ne_zero_coordinateLower_via_kernel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : (concreteSupportWindowData I sourceTest).supportValue f x ≠ 0) :
    I.1 ≤ x.1 :=
  concreteClosedWindowZeroSet_lower I sourceTest
    (concreteSupportValue_ne_zero_mem_closedWindowZeroSet I sourceTest f hx)

theorem concreteSupportValue_ne_zero_coordinateUpper_via_kernel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : (concreteSupportWindowData I sourceTest).supportValue f x ≠ 0) :
    x.1 ≤ I.2 :=
  concreteClosedWindowZeroSet_upper I sourceTest
    (concreteSupportValue_ne_zero_mem_closedWindowZeroSet I sourceTest f hx)

theorem concreteSupportValue_ne_zero_logScale_eq_zero_via_kernel
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    {x : ConcreteSupportPoint}
    (hx : (concreteSupportWindowData I sourceTest).supportValue f x ≠ 0) :
    x.2 = 0 :=
  concreteClosedWindowZeroSet_logScale_eq_zero I sourceTest
    (concreteSupportValue_ne_zero_mem_closedWindowZeroSet I sourceTest f hx)

theorem concreteSourceSupportCarrier_subset_coordinateWindowCarrier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).supportCarrier sourceTest ⊆
      (concreteSupportWindowData I sourceTest).coordinateWindowCarrier I :=
  (concreteFixedWindowCoordinateRows I sourceTest)
    |>.supportCarrier_subset_coordinateWindowCarrier

theorem concreteSourceSupportCarrier_subset_windowCarrier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).supportCarrier sourceTest ⊆
      (concreteSupportWindowData I sourceTest).windowCarrier I :=
  (concreteFixedWindowCoordinateRows I sourceTest)
    |>.supportCarrier_subset_windowCarrier

theorem concreteFourierSupportCarrier_subset_coordinateWindowCarrier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).fourierSupportCarrier sourceTest ⊆
      (concreteSupportWindowData I sourceTest).coordinateWindowCarrier I :=
  (concreteFixedWindowCoordinateRows I sourceTest)
    |>.fourierSupportCarrier_subset_coordinateWindowCarrier

theorem concreteFourierSupportCarrier_subset_windowCarrier
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).fourierSupportCarrier sourceTest ⊆
      (concreteSupportWindowData I sourceTest).windowCarrier I :=
  (concreteFixedWindowCoordinateRows I sourceTest)
    |>.fourierSupportCarrier_subset_windowCarrier

theorem concreteSourceSupportInWindow
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).supportInWindow sourceTest I :=
  (concreteFixedWindowCoordinateRows I sourceTest).supportInWindow

theorem concreteFourierSupportInWindow
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).fourierSupportInWindow sourceTest I :=
  (concreteFixedWindowCoordinateRows I sourceTest).fourierSupportInWindow

theorem concreteConvolutionSupportTransported
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).convolutionSupportTransported
      sourceTest I :=
  (concreteFixedWindowCoordinateRows I sourceTest).convolutionSupportTransported

theorem concreteSourceSoninSpaceComparison
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).soninSpaceComparison I :=
  SourceSupportWindowData.soninSpaceComparison_of_subsets
    (concreteSourceSupportCarrier_subset_windowCarrier I sourceTest)
    (concreteFourierSupportCarrier_subset_windowCarrier I sourceTest)

noncomputable def concreteSemilocalRows
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    SourceSemilocalRows (concreteSupportWindowData I sourceTest) :=
  SourceSemilocalRows.ofFourierCoordinateModelData
    (concreteFixedWindowCoordinateRows I sourceTest)
    (concreteRealPlaceCarrierData I sourceTest)
    (fun V H => concreteRealScalarCoordinateScalingData I sourceTest V H)
    (fun V H => concreteRealFourierCoordinateGradingData I sourceTest V H)
    (fun V H => concreteRealSignedCoordinateComparisonData I sourceTest V H)

theorem concreteFixedWindowExhaustionCompatible
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    (concreteSupportWindowData I sourceTest).fixedWindowExhaustionCompatible I :=
  SourceSupportWindowData.fixedWindowExhaustionCompatible_of_fourier_coordinate_model_data
    (concreteFixedWindowCoordinateRows I sourceTest)
    (concreteRealPlaceCarrierData I sourceTest)
    (fun V H => concreteRealScalarCoordinateScalingData I sourceTest V H)
    (fun V H => concreteRealFourierCoordinateGradingData I sourceTest V H)
    (fun V H => concreteRealSignedCoordinateComparisonData I sourceTest V H)

end SourceConcreteBaseLayer

/-
Exact finite-prime source support over the shared test algebra.

The global/restricted index sets are still finite `Finset ℕ` objects to match
the route-facing `WeilFormSymbols` API.  This record owns only support/cutoff
exactness; evaluator-backed finite-prime term and pairing definitions live in
`SourceFinitePrimeData`.
-/
/-- Global finite-prime support carrier with source-evaluation witnesses. -/
def SourceFinitePrimeGlobalSupportCarrier
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) :=
  { carrier : Finset ℕ //
    ∀ F : A.Test, ∀ n : ℕ,
      n ∈ carrier →
        E.sourceFinitePrimeTerm n F ≠ 0 }

/-- Fixed-lambda finite-prime support carrier with source-evaluation witnesses. -/
def SourceFinitePrimeRestrictedSupportCarrier
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) (lambda : ℝ) :=
  { carrier : Finset ℕ //
    ∀ F : A.Test, ∀ n : ℕ,
      n ∈ carrier →
        E.sourceFinitePrimeTerm n F ≠ 0 ∧ 1 < n ∧ (n : ℝ) ≤ lambda ^ 2 }

structure SourceFinitePrimeExactSupportData
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) where
  globalPrimeIndexCarrier : SourceFinitePrimeGlobalSupportCarrier A E
  restrictedPrimeIndexCarrier :
    (lambda : ℝ) → SourceFinitePrimeRestrictedSupportCarrier A E lambda
  sourceVisibleGlobalIndex :
    ∀ F : A.Test, ∀ n : ℕ,
      E.sourceFinitePrimeTerm n F ≠ 0 → n ∈ globalPrimeIndexCarrier.1
  sourceVisibleRestrictedIndex :
    ∀ lambda : ℝ, ∀ F : A.Test, ∀ n : ℕ,
      E.sourceFinitePrimeTerm n F ≠ 0 → 1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ (restrictedPrimeIndexCarrier lambda).1

namespace SourceFinitePrimeExactSupportData

theorem concrete_sourceFinitePrimeTerm_zero
    (E : SourceEvaluationData SourceConcreteBaseLayer.concreteTestAlgebra)
    (n : ℕ) :
    E.sourceFinitePrimeTerm n (0 : TestFunction) = 0 := by
  simp [SourceEvaluationData.sourceFinitePrimeTerm,
    SourceEvaluationData.valueAt,
    SourceConcreteBaseLayer.concreteTestAlgebra,
    SourceConcreteBaseLayer.concreteLegacyTestEquiv]

theorem concrete_all_sourceFinitePrimeTerms_zero
    {E : SourceEvaluationData SourceConcreteBaseLayer.concreteTestAlgebra}
    (S :
      SourceFinitePrimeExactSupportData
        SourceConcreteBaseLayer.concreteTestAlgebra E)
    (F : TestFunction) (n : ℕ) :
    E.sourceFinitePrimeTerm n F = 0 := by
  by_contra hVisible
  have hmem : n ∈ S.globalPrimeIndexCarrier.1 :=
    S.sourceVisibleGlobalIndex F n hVisible
  have hzeroVisible :
      E.sourceFinitePrimeTerm n (0 : TestFunction) ≠ 0 :=
    S.globalPrimeIndexCarrier.2 (0 : TestFunction) n hmem
  exact hzeroVisible (concrete_sourceFinitePrimeTerm_zero E n)

def globalPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (S : SourceFinitePrimeExactSupportData A E) : Finset ℕ :=
  S.globalPrimeIndexCarrier.1

def restrictedPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (S : SourceFinitePrimeExactSupportData A E) : ℝ → Finset ℕ :=
  fun lambda => (S.restrictedPrimeIndexCarrier lambda).1

theorem globalIndexData
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (S : SourceFinitePrimeExactSupportData A E)
    (F : A.Test) (n : ℕ)
    (hn : n ∈ S.globalPrimeIndexSet) :
    E.sourceFinitePrimeTerm n F ≠ 0 :=
  S.globalPrimeIndexCarrier.2 F n hn

theorem restrictedIndexData
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (S : SourceFinitePrimeExactSupportData A E)
    (lambda : ℝ) (F : A.Test) (n : ℕ)
    (hn : n ∈ S.restrictedPrimeIndexSet lambda) :
    E.sourceFinitePrimeTerm n F ≠ 0 ∧ 1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  (S.restrictedPrimeIndexCarrier lambda).2 F n hn

theorem restrictedCoverage
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (S : SourceFinitePrimeExactSupportData A E)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (F : A.Test) (n : ℕ)
    (hVisible : E.sourceFinitePrimeTerm n F ≠ 0)
    (hn : 1 < n) (hle : (n : ℝ) ≤ lambda ^ 2) :
    n ∈ S.restrictedPrimeIndexSet lambda := by
  exact S.sourceVisibleRestrictedIndex lambda F n hVisible hn hle

end SourceFinitePrimeExactSupportData

/--
CCM25 finite-prime source arithmetic over the shared test algebra.

The evaluator-backed finite-prime term, prime-power pairing, and visibility
definitions are fixed here.  Exact support/cutoff data is supplied through the
separate `exactSupport` object so support rows do not live inside visible
arithmetic read-off records.
-/
structure SourceFinitePrimeData
    (A : SourceTestAlgebra) (E : SourceEvaluationData A) where
  exactSupport : SourceFinitePrimeExactSupportData A E

namespace SourceFinitePrimeData

def globalPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) : Finset ℕ :=
  P.exactSupport.globalPrimeIndexSet

def restrictedPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) : ℝ → Finset ℕ :=
  P.exactSupport.restrictedPrimeIndexSet

@[simp] theorem globalPrimeIndexSet_eq_exactSupport
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) :
    P.globalPrimeIndexSet = P.exactSupport.globalPrimeIndexSet :=
  rfl

@[simp] theorem restrictedPrimeIndexSet_eq_exactSupport
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) :
    P.restrictedPrimeIndexSet = P.exactSupport.restrictedPrimeIndexSet :=
  rfl

theorem globalExact
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) :
    ∀ F : A.Test, ∀ n : ℕ,
      n ∈ P.globalPrimeIndexSet ↔
        IsPrimePow n ∧ E.sourceFinitePrimeTerm n F ≠ 0 := by
  intro F n
  constructor
  · intro hn
    have hVisible := P.exactSupport.globalIndexData F n hn
    exact ⟨E.sourceFinitePrimeTerm_nonzero_primePower hVisible, hVisible⟩
  · intro hdata
    exact P.exactSupport.sourceVisibleGlobalIndex F n hdata.2

theorem restrictedExact
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) :
    ∀ lambda : ℝ, ∀ F : A.Test, ∀ n : ℕ,
      n ∈ P.restrictedPrimeIndexSet lambda ↔
        IsPrimePow n ∧ E.sourceFinitePrimeTerm n F ≠ 0 ∧
          1 < n ∧ (n : ℝ) ≤ lambda ^ 2 := by
  intro lambda F n
  constructor
  · intro hn
    have hdata := P.exactSupport.restrictedIndexData lambda F n hn
    exact
      ⟨E.sourceFinitePrimeTerm_nonzero_primePower hdata.1, hdata.1,
        hdata.2⟩
  · intro hdata
    exact
      P.exactSupport.sourceVisibleRestrictedIndex lambda F n
        hdata.2.1 hdata.2.2.1 hdata.2.2.2

def sourcePrimePowerIndex
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (_P : SourceFinitePrimeData A E) :
    ℕ → Prop :=
  fun n => IsPrimePow n

@[simp] theorem sourcePrimePowerIndex_iff
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) (n : ℕ) :
    P.sourcePrimePowerIndex n ↔ IsPrimePow n :=
  Iff.rfl

noncomputable def vonMangoldtWeight
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (_P : SourceFinitePrimeData A E) :
    ℕ → ℝ :=
  fun n => ArithmeticFunction.vonMangoldt n

def legacyGlobalPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    Finset ℕ :=
  P.globalPrimeIndexSet

def legacyRestrictedPrimeIndexSet
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    ℝ → Finset ℕ :=
  P.restrictedPrimeIndexSet

noncomputable def sourceAtomVisible
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (_P : SourceFinitePrimeData A E) :
    ℕ → A.Test → Prop :=
  fun n F => E.sourceFinitePrimeTerm n F ≠ 0

noncomputable def legacyFinitePrimeAtomVisible
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    ℕ → TestFunction → Prop :=
  fun n F => P.sourceAtomVisible n (A.legacy.decode F)

noncomputable def finitePrimeTerm
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (_P : SourceFinitePrimeData A E) :
    ℕ → A.Test → ℝ :=
  E.sourceFinitePrimeTerm

noncomputable def legacyFinitePrimeTerm
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    ℕ → TestFunction → ℝ :=
  fun n F => P.finitePrimeTerm n (A.legacy.decode F)

noncomputable def primePowerPairing
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (_P : SourceFinitePrimeData A E) :
    ℕ → A.Test → A.Test → ℝ :=
  E.sourcePrimePowerPairing

noncomputable def legacyPrimePowerPairing
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    ℕ → TestFunction → TestFunction → ℝ :=
  fun n f g =>
    P.primePowerPairing n (A.legacy.decode f) (A.legacy.decode g)

@[simp] theorem legacyGlobalPrimeIndexSet_eq
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) :
    P.legacyGlobalPrimeIndexSet = P.globalPrimeIndexSet :=
  rfl

@[simp] theorem legacyRestrictedPrimeIndexSet_apply
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) :
    P.legacyRestrictedPrimeIndexSet lambda =
      P.restrictedPrimeIndexSet lambda :=
  rfl

@[simp] theorem legacyFinitePrimeAtomVisible_apply
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (n : ℕ) (F : TestFunction) :
    P.legacyFinitePrimeAtomVisible n F =
      P.sourceAtomVisible n (A.legacy.decode F) :=
  rfl

@[simp] theorem legacyFinitePrimeTerm_apply
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (n : ℕ) (F : TestFunction) :
    P.legacyFinitePrimeTerm n F =
      P.finitePrimeTerm n (A.legacy.decode F) :=
  rfl

@[simp] theorem finitePrimeTerm_eq_evaluation
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) (n : ℕ) (F : A.Test) :
    P.finitePrimeTerm n F = E.sourceFinitePrimeTerm n F :=
  rfl

@[simp] theorem legacyPrimePowerPairing_apply
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (n : ℕ) (f g : TestFunction) :
    P.legacyPrimePowerPairing n f g =
      P.primePowerPairing n (A.legacy.decode f) (A.legacy.decode g) :=
  rfl

@[simp] theorem primePowerPairing_eq_evaluation
    {A : SourceTestAlgebra} {E : SourceEvaluationData A}
    (P : SourceFinitePrimeData A E) (n : ℕ) (f g : A.Test) :
    P.primePowerPairing n f g = E.sourcePrimePowerPairing n f g :=
  rfl

theorem vonMangoldtWeight_eq_arithmetic
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E) (n : ℕ) :
    P.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  rfl

theorem globalPrimeIndex_primePower
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (F : A.Test) {n : ℕ} (hn : n ∈ P.globalPrimeIndexSet) :
    IsPrimePow n :=
  ((P.globalExact F n).1 hn).1

theorem globalPrimeIndex_visible
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (F : A.Test) {n : ℕ} (hn : n ∈ P.globalPrimeIndexSet) :
    P.sourceAtomVisible n F :=
  ((P.globalExact F n).1 hn).2

theorem globalPrimeIndex_mem_of_primePower_visible
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (F : A.Test) {n : ℕ}
    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n F) :
    n ∈ P.globalPrimeIndexSet :=
  (P.globalExact F n).2 ⟨hPrime, hVisible⟩

theorem sourceAtomVisible_primePower_index
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (F : A.Test) {n : ℕ} (hVisible : P.sourceAtomVisible n F) :
    IsPrimePow n :=
  E.sourceFinitePrimeTerm_nonzero_primePower hVisible

theorem globalCoverage
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (F : A.Test) (n : ℕ) :
    P.sourceAtomVisible n F → n ∈ P.globalPrimeIndexSet := by
  intro hVisible
  exact
    P.globalPrimeIndex_mem_of_primePower_visible F
      (P.sourceAtomVisible_primePower_index F hVisible) hVisible

theorem restrictedPrimeIndex_primePower
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hn : n ∈ P.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  (((P.restrictedExact lambda F n).1 hn).1)

theorem restrictedPrimeIndex_visible
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hn : n ∈ P.restrictedPrimeIndexSet lambda) :
    P.sourceAtomVisible n F :=
  (((P.restrictedExact lambda F n).1 hn).2).1

theorem restrictedPrimeIndex_one_lt
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hn : n ∈ P.restrictedPrimeIndexSet lambda) :
    1 < n :=
  ((((P.restrictedExact lambda F n).1 hn).2).2).1

theorem restrictedPrimeIndex_le_lambda_sq
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hn : n ∈ P.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  ((((P.restrictedExact lambda F n).1 hn).2).2).2

theorem restrictedPrimeIndex_lambdaCut
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hn : n ∈ P.restrictedPrimeIndexSet lambda) :
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  ⟨P.restrictedPrimeIndex_one_lt lambda F hn,
    P.restrictedPrimeIndex_le_lambda_sq lambda F hn⟩

theorem restrictedPrimeIndex_mem_of_primePower_visible_cutoff
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (F : A.Test) {n : ℕ}
    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n F)
    (hOne : 1 < n) (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
    n ∈ P.restrictedPrimeIndexSet lambda :=
  (P.restrictedExact lambda F n).2
    ⟨hPrime, hVisible, hOne, hCutoff⟩

theorem restrictedCoverage
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (F : A.Test) (n : ℕ) :
    P.sourceAtomVisible n F → 1 < n → (n : ℝ) ≤ lambda ^ 2 →
      n ∈ P.restrictedPrimeIndexSet lambda := by
  intro hVisible
  exact P.exactSupport.restrictedCoverage lambda hlambda F n hVisible

theorem finitePrimeTerm_convolutionStar
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (f g : A.Test) (n : ℕ) :
    P.finitePrimeTerm n (A.convolutionStar f g) =
      P.vonMangoldtWeight n * P.primePowerPairing n f g :=
  rfl

theorem finitePrimeTerm_convolutionSquare
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (g : A.Test) (n : ℕ) :
    P.finitePrimeTerm n (A.convolutionSquare g) =
      P.vonMangoldtWeight n * P.primePowerPairing n g g := by
  rw [A.convolutionSquare_eq g]
  exact P.finitePrimeTerm_convolutionStar g g n

theorem legacyFinitePrimeTerm_convolutionStar
    {A : SourceTestAlgebra} {E : SourceEvaluationData A} (P : SourceFinitePrimeData A E)
    (f g : TestFunction) (n : ℕ) :
    P.legacyFinitePrimeTerm n (A.legacyConvolutionStar f g) =
      P.vonMangoldtWeight n * P.legacyPrimePowerPairing n f g := by
  simpa [legacyFinitePrimeTerm, legacyPrimePowerPairing,
    SourceTestAlgebra.legacy_decode_legacyConvolutionStar]
    using P.finitePrimeTerm_convolutionStar
      (A.legacy.decode f) (A.legacy.decode g) n

end SourceFinitePrimeData

/-- CCM25 global/restricted Weil-form formulas over the shared source algebra. -/
structure SourceWeilFormData (A : SourceTestAlgebra) where
  evaluation : SourceEvaluationData A
  finitePrime : SourceFinitePrimeData A evaluation
  archimedeanTerm : A.Test → ℝ

namespace SourceWeilFormData

noncomputable def psi
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    A.Test → ℝ :=
  fun F =>
    W.evaluation.poleFunctional F - W.archimedeanTerm F -
      ∑ n ∈ W.finitePrime.globalPrimeIndexSet,
        W.finitePrime.finitePrimeTerm n F

noncomputable def qw
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    A.Test → A.Test → ℝ :=
  fun f g => W.psi (A.convolutionStar f g)

noncomputable def qwLambda
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    ℝ → A.Test → A.Test → ℝ :=
  fun lambda f g =>
    W.archimedeanTerm (A.convolutionStar f g) +
      W.evaluation.poleFunctional (A.convolutionStar f g) -
        ∑ n ∈ W.finitePrime.restrictedPrimeIndexSet lambda,
          W.finitePrime.vonMangoldtWeight n *
            W.finitePrime.primePowerPairing n f g

noncomputable def toWeilFormSymbols
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols where
  qw := fun f g => W.qw (A.legacy.decode f) (A.legacy.decode g)
  qwLambda := fun lambda f g =>
    W.qwLambda lambda (A.legacy.decode f) (A.legacy.decode g)
  psi := fun F => W.psi (A.legacy.decode F)
  convolutionStar := A.legacyConvolutionStar
  globalPrimeIndexSet := W.finitePrime.globalPrimeIndexSet
  restrictedPrimeIndexSet := W.finitePrime.restrictedPrimeIndexSet
  finitePrimeTerm := W.finitePrime.legacyFinitePrimeTerm
  archimedeanTerm := fun F => W.archimedeanTerm (A.legacy.decode F)
  poleFunctional := fun F => W.evaluation.poleFunctional (A.legacy.decode F)
  polePairing := fun f => W.evaluation.polePairing (A.legacy.decode f)
  primePowerPairing := W.finitePrime.legacyPrimePowerPairing

@[simp] theorem toWeilFormSymbols_qw
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (f g : TestFunction) :
    W.toWeilFormSymbols.qw f g =
      W.qw (A.legacy.decode f) (A.legacy.decode g) :=
  rfl

@[simp] theorem toWeilFormSymbols_qwLambda
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (lambda : ℝ) (f g : TestFunction) :
    W.toWeilFormSymbols.qwLambda lambda f g =
      W.qwLambda lambda (A.legacy.decode f) (A.legacy.decode g) :=
  rfl

@[simp] theorem toWeilFormSymbols_psi
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) :
    W.toWeilFormSymbols.psi F = W.psi (A.legacy.decode F) :=
  rfl

@[simp] theorem toWeilFormSymbols_convolutionStar
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (f g : TestFunction) :
    W.toWeilFormSymbols.convolutionStar f g =
      A.legacyConvolutionStar f g :=
  rfl

@[simp] theorem toWeilFormSymbols_globalPrimeIndexSet
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    W.toWeilFormSymbols.globalPrimeIndexSet =
      W.finitePrime.globalPrimeIndexSet :=
  rfl

@[simp] theorem toWeilFormSymbols_restrictedPrimeIndexSet
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (lambda : ℝ) :
    W.toWeilFormSymbols.restrictedPrimeIndexSet lambda =
      W.finitePrime.restrictedPrimeIndexSet lambda :=
  rfl

@[simp] theorem toWeilFormSymbols_finitePrimeAtomVisible
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (n : ℕ) (F : TestFunction) :
    W.toWeilFormSymbols.finitePrimeAtomVisible n F =
      W.finitePrime.sourceAtomVisible n (A.legacy.decode F) :=
  rfl

@[simp] theorem toWeilFormSymbols_finitePrimeTerm
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (n : ℕ) (F : TestFunction) :
    W.toWeilFormSymbols.finitePrimeTerm n F =
      W.finitePrime.finitePrimeTerm n (A.legacy.decode F) :=
  rfl

@[simp] theorem toWeilFormSymbols_archimedeanTerm
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) :
    W.toWeilFormSymbols.archimedeanTerm F =
      W.archimedeanTerm (A.legacy.decode F) :=
  rfl

@[simp] theorem toWeilFormSymbols_poleFunctional
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) :
    W.toWeilFormSymbols.poleFunctional F =
      W.evaluation.poleFunctional (A.legacy.decode F) :=
  rfl

@[simp] theorem toWeilFormSymbols_polePairing
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (f : TestFunction) :
    W.toWeilFormSymbols.polePairing f =
      W.evaluation.polePairing (A.legacy.decode f) :=
  rfl

@[simp] theorem toWeilFormSymbols_primePowerPairing
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (n : ℕ) (f g : TestFunction) :
    W.toWeilFormSymbols.primePowerPairing n f g =
      W.finitePrime.primePowerPairing n
        (A.legacy.decode f) (A.legacy.decode g) :=
  rfl

@[simp] theorem toWeilFormSymbols_vonMangoldtWeight
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (n : ℕ) :
    W.toWeilFormSymbols.vonMangoldtWeight n =
      ArithmeticFunction.vonMangoldt n :=
  rfl

theorem toWeilFormSymbols_globalPrimeIndex_exact
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) (n : ℕ) :
    n ∈ W.toWeilFormSymbols.globalPrimeIndexSet ↔
      IsPrimePow n ∧ W.toWeilFormSymbols.finitePrimeAtomVisible n F := by
  exact W.finitePrime.globalExact (A.legacy.decode F) n

theorem toWeilFormSymbols_restrictedPrimeIndex_exact
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (lambda : ℝ) (F : TestFunction) (n : ℕ) :
    n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda ↔
      IsPrimePow n ∧ W.toWeilFormSymbols.finitePrimeAtomVisible n F ∧
        1 < n ∧ (n : ℝ) ≤ lambda ^ 2 := by
  exact W.finitePrime.restrictedExact lambda (A.legacy.decode F) n

theorem toWeilFormSymbols_finitePrimeAtomVisible_primePower
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) {n : ℕ}
    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F) :
    IsPrimePow n :=
  W.finitePrime.sourceAtomVisible_primePower_index
    (A.legacy.decode F) hVisible

theorem toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (F : TestFunction) {n : ℕ}
    (hPrime : IsPrimePow n)
    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F) :
    n ∈ W.toWeilFormSymbols.globalPrimeIndexSet :=
  (W.toWeilFormSymbols_globalPrimeIndex_exact F n).2
    ⟨hPrime, hVisible⟩

theorem toWeilFormSymbols_restrictedPrimeIndex_mem_of_primePower_visible_cutoff
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (lambda : ℝ) (F : TestFunction) {n : ℕ}
    (hPrime : IsPrimePow n)
    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F)
    (hOne : 1 < n) (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
    n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
  (W.toWeilFormSymbols_restrictedPrimeIndex_exact lambda F n).2
    ⟨hPrime, hVisible, hOne, hCutoff⟩

theorem toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (lambda : ℝ) (hlambda : 1 < lambda) (F : TestFunction) {n : ℕ}
    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F)
    (hOne : 1 < n) (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
    n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
  W.finitePrime.restrictedCoverage lambda hlambda
    (A.legacy.decode F) n hVisible hOne hCutoff

theorem finitePrimeTerm_convolutionStar
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (f g : A.Test) (n : ℕ) :
    W.finitePrime.finitePrimeTerm n (A.convolutionStar f g) =
      W.finitePrime.vonMangoldtWeight n *
        W.finitePrime.primePowerPairing n f g :=
  W.finitePrime.finitePrimeTerm_convolutionStar f g n

theorem finitePrimeTerm_convolutionSquare
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (g : A.Test) (n : ℕ) :
    W.finitePrime.finitePrimeTerm n (A.convolutionSquare g) =
      W.finitePrime.vonMangoldtWeight n *
        W.finitePrime.primePowerPairing n g g :=
  W.finitePrime.finitePrimeTerm_convolutionSquare g n

theorem toWeilFormSymbols_vonMangoldtWeight_eq_arithmetic
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (n : ℕ) :
    W.toWeilFormSymbols.vonMangoldtWeight n =
      ArithmeticFunction.vonMangoldt n :=
  W.toWeilFormSymbols_vonMangoldtWeight n

theorem toWeilFormSymbols_finitePrimeTerm_convolutionStar
    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
    (f g : TestFunction) (n : ℕ) :
    W.toWeilFormSymbols.finitePrimeTerm n
        (W.toWeilFormSymbols.convolutionStar f g) =
      W.toWeilFormSymbols.vonMangoldtWeight n *
        W.toWeilFormSymbols.primePowerPairing n f g := by
  simpa [toWeilFormSymbols, SourceFinitePrimeData.legacyFinitePrimeTerm,
    SourceFinitePrimeData.legacyPrimePowerPairing]
    using W.finitePrime.legacyFinitePrimeTerm_convolutionStar f g n

theorem qw_definition_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWDefinitionStatement W.toWeilFormSymbols := by
  intro f g
  simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    qw]

theorem psi_sign_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PsiSignStatement W.toWeilFormSymbols := by
  intro F
  simp [toWeilFormSymbols, SourceFinitePrimeData.legacyFinitePrimeTerm,
    psi]

theorem qw_lambda_formula_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWLambdaFormulaStatement W.toWeilFormSymbols := by
  intro lambda hlambda f
  simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    SourceFinitePrimeData.legacyPrimePowerPairing, qwLambda,
    WeilFormSymbols.vonMangoldtWeight,
    SourceFinitePrimeData.vonMangoldtWeight_eq_arithmetic,
    A.convolutionSquare_eq (A.legacy.decode f),
    W.evaluation.polePairing_eq_poleFunctional_convolutionSquare]

theorem finite_prime_term_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W.toWeilFormSymbols := by
  intro f g
  refine
    { globalPrimeIndexCoverage := ?_
      restrictedPrimeIndexCoverage := ?_
      finitePrimeTermNormalization := ?_ }
  · intro n hn
    exact W.finitePrime.globalCoverage
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
  · intro lambda hlambda n hn hOne hCutoff
    exact W.finitePrime.restrictedCoverage lambda hlambda
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
      hOne hCutoff
  · intro n
    simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
      SourceFinitePrimeData.legacyFinitePrimeTerm,
      SourceFinitePrimeData.legacyPrimePowerPairing]
      using W.finitePrime.finitePrimeTerm_convolutionStar
        (A.legacy.decode f) (A.legacy.decode g) n

theorem pole_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PoleNormalizationStatement W.toWeilFormSymbols := by
  intro f
  calc
    W.toWeilFormSymbols.polePairing f =
        W.evaluation.poleFunctional (A.convolutionSquare (A.legacy.decode f)) :=
      W.evaluation.polePairing_eq_poleFunctional_convolutionSquare
        (A.legacy.decode f)
    _ = W.toWeilFormSymbols.poleFunctional
        (W.toWeilFormSymbols.convolutionStar f f) := by
      simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
        A.convolutionSquare_eq (A.legacy.decode f)]

end SourceWeilFormData

/-- CC20 trace-scale source data over the shared test object. -/
structure SourceTraceScaleData (A : SourceTestAlgebra) where
  traceAmplitude : A.Test → ℝ
  traceClass : A.Test → Prop
  cyclicLegal : A.Test → Prop
  sourceNoDefectTrace : A.Test → ℝ

namespace SourceTraceScaleData

def supportSquareTrace
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    A.Test → ℝ :=
  fun g => T.traceAmplitude g ^ 2

def positiveTrace
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    A.Test → ℝ :=
  T.supportSquareTrace

def hilbertSchmidtGate
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    A.Test → Prop :=
  fun g => T.traceClass g ∧ T.cyclicLegal g

@[simp] theorem hilbertSchmidtGate_iff
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    T.hilbertSchmidtGate g ↔ T.traceClass g ∧ T.cyclicLegal g :=
  Iff.rfl

theorem traceClass_of_hilbertSchmidt
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    {g : A.Test} (hGate : T.hilbertSchmidtGate g) :
    T.traceClass g :=
  hGate.1

theorem cyclicLegal_of_hilbertSchmidt
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    {g : A.Test} (hGate : T.hilbertSchmidtGate g) :
    T.cyclicLegal g :=
  hGate.2

def toNormalizedLegalSquareTraceScaleSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols where
  Test := A.Test
  traceAmplitude := T.traceAmplitude
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal

def toArchimedeanTraceSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    ArchimedeanTraceSymbols where
  Test := A.Test
  supportSquareTrace := T.supportSquareTrace
  sourceNoDefectTrace := T.sourceNoDefectTrace
  positiveTrace := T.positiveTrace
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal
  hilbertSchmidtGate := T.hilbertSchmidtGate
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

@[simp] theorem toNormalizedLegalSquareTraceScaleSymbols_Test
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toNormalizedLegalSquareTraceScaleSymbols.Test = A.Test :=
  rfl

@[simp] theorem toNormalizedLegalSquareTraceScaleSymbols_traceAmplitude
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toNormalizedLegalSquareTraceScaleSymbols.traceAmplitude =
      T.traceAmplitude :=
  rfl

@[simp] theorem toNormalizedLegalSquareTraceScaleSymbols_traceClass
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toNormalizedLegalSquareTraceScaleSymbols.traceClass =
      T.traceClass :=
  rfl

@[simp] theorem toNormalizedLegalSquareTraceScaleSymbols_cyclicLegal
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toNormalizedLegalSquareTraceScaleSymbols.cyclicLegal =
      T.cyclicLegal :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_Test
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.Test = A.Test :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_supportSquareTrace
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.supportSquareTrace =
      T.supportSquareTrace :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_sourceNoDefectTrace
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.sourceNoDefectTrace =
      T.sourceNoDefectTrace :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_positiveTrace
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.positiveTrace =
      T.positiveTrace :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_traceClass
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.traceClass = T.traceClass :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_cyclicLegal
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.cyclicLegal = T.cyclicLegal :=
  rfl

@[simp] theorem toArchimedeanTraceSymbols_hilbertSchmidtGate
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    T.toArchimedeanTraceSymbols.hilbertSchmidtGate =
      T.hilbertSchmidtGate :=
  rfl

theorem supportSquareTrace_nonnegative
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    0 ≤ T.supportSquareTrace g := by
  dsimp [supportSquareTrace]
  exact sq_nonneg (T.traceAmplitude g)

theorem positiveTrace_nonnegative
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    0 ≤ T.positiveTrace g := by
  exact T.supportSquareTrace_nonnegative g

theorem positiveTrace_eq_supportSquare
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    T.positiveTrace g = T.supportSquareTrace g := by
  rfl

theorem positiveTrace_eq_amplitude_sq
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    T.positiveTrace g = T.traceAmplitude g ^ 2 := by
  rfl

theorem toArchimedeanTraceSymbols_supportSquareTrace_nonnegative
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    0 ≤ T.toArchimedeanTraceSymbols.supportSquareTrace g :=
  T.supportSquareTrace_nonnegative g

theorem toArchimedeanTraceSymbols_positiveTrace_nonnegative
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    0 ≤ T.toArchimedeanTraceSymbols.positiveTrace g :=
  T.positiveTrace_nonnegative g

theorem toArchimedeanTraceSymbols_positiveTrace_eq_amplitude_sq
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A)
    (g : A.Test) :
    T.toArchimedeanTraceSymbols.positiveTrace g =
      T.traceAmplitude g ^ 2 :=
  T.positiveTrace_eq_amplitude_sq g

theorem ordinary_trace_support_square_statement
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      T.toArchimedeanTraceSymbols := by
  intro g _hTrace _hCyclic
  rfl

theorem trace_class_template_statement
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      T.toArchimedeanTraceSymbols := by
  intro g hGate
  exact
    ⟨T.traceClass_of_hilbertSchmidt hGate,
      T.cyclicLegal_of_hilbertSchmidt hGate⟩

end SourceTraceScaleData

/-- The shared core object consumed by CCM24, CCM25, and CC20. -/
structure SourceAnalyticCore where
  testAlgebra : SourceTestAlgebra
  supportWindow : SourceSupportWindowData testAlgebra
  weilForm : SourceWeilFormData testAlgebra
  traceScale : SourceTraceScaleData testAlgebra

namespace SourceAnalyticCore

def evaluation (core : SourceAnalyticCore) :
    SourceEvaluationData core.testAlgebra :=
  core.weilForm.evaluation

noncomputable def toWeilFormSymbols (core : SourceAnalyticCore) : WeilFormSymbols :=
  core.weilForm.toWeilFormSymbols

def toSemilocalModelSymbols (core : SourceAnalyticCore) :
    SemilocalModelSymbols :=
  core.supportWindow.toSemilocalModelSymbols

def toArchimedeanTraceSymbols (core : SourceAnalyticCore) :
    ArchimedeanTraceSymbols :=
  core.traceScale.toArchimedeanTraceSymbols

def toNormalizedLegalSquareTraceScaleSymbols
    (core : SourceAnalyticCore) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  core.traceScale.toNormalizedLegalSquareTraceScaleSymbols

end SourceAnalyticCore

end AnalyticCore
end Source
end ConnesWeilRH
