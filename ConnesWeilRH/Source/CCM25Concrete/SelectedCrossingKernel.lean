/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare

/-!
# The two compact crossing kernels for one selected test

For a compactly supported log test `h` and a nonnegative crossing length `b`,
the source variable is restricted to `[0,b]` and the kernel variable to a
support-preserving compact interval.  The two kernels are the two crossing
orientations; their section pairing is the convolution-square integrand at
`b`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedCrossingKernel

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace
open ConnesWeilRH.Source.CC20Concrete

abbrev SourceInterval (b : ℝ) := Set.Icc (0 : ℝ) b

abbrev KernelInterval (a c b : ℝ) := Set.Icc (a - b) (c + b)

noncomputable instance sourceIntervalMeasureSpace (b : ℝ) :
    MeasureSpace (SourceInterval b) := Measure.Subtype.measureSpace

noncomputable instance kernelIntervalMeasureSpace (a c b : ℝ) :
    MeasureSpace (KernelInterval a c b) := Measure.Subtype.measureSpace

noncomputable instance sourceIntervalFiniteMeasure (b : ℝ) :
    IsFiniteMeasure (volume : Measure (SourceInterval b)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

noncomputable instance kernelIntervalFiniteMeasure (a c b : ℝ) :
    IsFiniteMeasure (volume : Measure (KernelInterval a c b)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

noncomputable def leftKernel
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ) :
    ContinuousMap ((SourceInterval b) × (KernelInterval a c b)) ℂ where
  toFun z := h (z.2.1 - z.1.1 + b)
  continuous_toFun := by
    exact hh.comp
      (((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst)).add_const b)

noncomputable def rightKernel
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ) :
    ContinuousMap ((SourceInterval b) × (KernelInterval a c b)) ℂ where
  toFun z := h (z.2.1 - z.1.1)
  continuous_toFun := by
    exact hh.comp
      ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))

theorem leftKernel_apply
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    (s : SourceInterval b) (t : KernelInterval a c b) :
    leftKernel h hh a c b (s, t) = h (t.1 - s.1 + b) := rfl

theorem rightKernel_apply
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    (s : SourceInterval b) (t : KernelInterval a c b) :
    rightKernel h hh a c b (s, t) = h (t.1 - s.1) := rfl

noncomputable def pairData
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.BasisHilbertSchmidtPairData (G :=
      Lp ℂ 2 (volume : Measure (SourceInterval b))) basis :=
  ContinuousKernelHilbertSchmidt.pairData
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (leftKernel h hh a c b) (rightKernel h hh a c b) basis

theorem pairData_trace_eq_restricted_crossing_integral
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (pairData h hh a c b basis).traceProduct =
      ∫ s, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel h hh a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel h hh a c b) s) := by
  exact ContinuousKernelHilbertSchmidt.pairData_trace_eq_kernel_inner
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (leftKernel h hh a c b) (rightKernel h hh a c b) basis
    (ContinuousKernelHilbertSchmidt.coefficient_inner_integrable
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel h hh a c b) (rightKernel h hh a c b) basis)
    (ContinuousKernelHilbertSchmidt.coefficient_inner_integral_norm_summable
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel h hh a c b) (rightKernel h hh a c b) basis)

end SelectedCrossingKernel
end CCM25Concrete
end Source
end ConnesWeilRH
