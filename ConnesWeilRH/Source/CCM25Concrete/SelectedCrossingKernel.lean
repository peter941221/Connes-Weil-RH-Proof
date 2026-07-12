/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
import ConnesWeilRH.Source.CCM25Concrete.SelectedSingleCrossing
import ConnesWeilRH.Source.CCM25Concrete.SelectedYoshidaBridge

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

noncomputable def reversePairData
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.BasisHilbertSchmidtPairData (G :=
      Lp ℂ 2 (volume : Measure (SourceInterval b))) basis :=
  ContinuousKernelHilbertSchmidt.pairData
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (rightKernel h hh a c b) (leftKernel h hh a c b) basis

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

theorem reversePairData_trace_eq_restricted_crossing_integral
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (reversePairData h hh a c b basis).traceProduct =
      ∫ s, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel h hh a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel h hh a c b) s) := by
  exact ContinuousKernelHilbertSchmidt.pairData_trace_eq_kernel_inner
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (rightKernel h hh a c b) (leftKernel h hh a c b) basis
    (ContinuousKernelHilbertSchmidt.coefficient_inner_integrable
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel h hh a c b) (leftKernel h hh a c b) basis)
    (ContinuousKernelHilbertSchmidt.coefficient_inner_integral_norm_summable
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel h hh a c b) (leftKernel h hh a c b) basis)

theorem section_pair_eq_interval_integral
    (h : ℝ → ℂ) (hh : Continuous h) (a c b : ℝ)
    (s : SourceInterval b) :
    inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel h hh a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel h hh a c b) s) =
      ∫ t in Set.Icc (a - b) (c + b),
        star (h (t - s.1)) * h (t - s.1 + b) := by
  change inner ℂ
    (ContinuousMap.toLp 2 (volume : Measure (KernelInterval a c b)) ℂ
      (ContinuousKernelHilbertSchmidt.kernelSection
        (rightKernel h hh a c b) s))
    (ContinuousMap.toLp 2 (volume : Measure (KernelInterval a c b)) ℂ
      (ContinuousKernelHilbertSchmidt.kernelSection
        (leftKernel h hh a c b) s)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : KernelInterval a c b,
    (ContinuousKernelHilbertSchmidt.kernelSection
      (leftKernel h hh a c b) s) x *
      star ((ContinuousKernelHilbertSchmidt.kernelSection
        (rightKernel h hh a c b) s) x)
      ∂Measure.comap Subtype.val volume) = _
  change (∫ x : Set.Icc (a - b) (c + b),
    h (x.1 - s.1 + b) * star (h (x.1 - s.1))
      ∂Measure.comap Subtype.val volume) = _
  calc
    (∫ x : Set.Icc (a - b) (c + b),
        h (x.1 - s.1 + b) * star (h (x.1 - s.1))
        ∂Measure.comap Subtype.val volume) =
        ∫ t in Set.Icc (a - b) (c + b),
          h (t - s.1 + b) * star (h (t - s.1)) :=
      integral_subtype_comap (μ := (volume : Measure ℝ))
        measurableSet_Icc
        (fun t : ℝ => h (t - s.1 + b) * star (h (t - s.1)))
    _ = ∫ t in Set.Icc (a - b) (c + b),
        star (h (t - s.1)) * h (t - s.1 + b) := by
      apply integral_congr_ae
      filter_upwards with t
      exact mul_comm _ _

theorem crossing_integrand_eq_zero_of_not_mem
    (h : ℝ → ℂ) (a c b : ℝ)
    (hsupp : Function.support h ⊆ Set.Icc a c)
    (hb : 0 ≤ b) (s : SourceInterval b)
    {t : ℝ} (ht : t ∉ Set.Icc (a - b) (c + b)) :
    star (h (t - s.1)) * h (t - s.1 + b) = 0 := by
  by_cases hleft : h (t - s.1) = 0
  · simp [hleft]
  by_cases hright : h (t - s.1 + b) = 0
  · simp [hright]
  have hleft_mem : t - s.1 ∈ Set.Icc a c := by
    apply hsupp
    simpa [Function.mem_support, hleft]
  have hright_mem : t - s.1 + b ∈ Set.Icc a c := by
    apply hsupp
    simpa [Function.mem_support, hright]
  have hs0 : 0 ≤ s.1 := s.2.1
  have hsb : s.1 ≤ b := s.2.2
  have ht_lower : a - b ≤ t := by linarith [hleft_mem.1]
  have ht_upper : t ≤ c + b := by linarith [hright_mem.2]
  exact False.elim (ht ⟨ht_lower, ht_upper⟩)

theorem crossing_integral_restrict_eq_full
    (h : ℝ → ℂ) (a c b : ℝ)
    (hsupp : Function.support h ⊆ Set.Icc a c)
    (hb : 0 ≤ b) (s : SourceInterval b) :
    (∫ t in Set.Icc (a - b) (c + b),
      star (h (t - s.1)) * h (t - s.1 + b)) =
      ∫ t : ℝ, star (h (t - s.1)) * h (t - s.1 + b) := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [Set.indicator_of_mem ht]
  · simp only [Set.indicator, ht, if_false]
    exact (crossing_integrand_eq_zero_of_not_mem h a c b hsupp hb s ht).symm

theorem full_crossing_integral_eq_convolution_integral
    (h : ℝ → ℂ) (b : ℝ) (s : SourceInterval b) :
    (∫ t : ℝ, star (h (t - s.1)) * h (t - s.1 + b)) =
      ∫ u : ℝ, star (h (-u)) * h (b - u) := by
  let f : ℝ → ℂ := fun u => star (h (-u)) * h (b - u)
  have htranslate := integral_sub_left_eq_self f (volume : Measure ℝ) s.1
  calc
    (∫ t : ℝ, star (h (t - s.1)) * h (t - s.1 + b)) =
        ∫ t : ℝ, f (s.1 - t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [f]
      congr 2 <;> ring
    _ = ∫ u : ℝ, star (h (-u)) * h (b - u) := by
      simpa only [f] using htranslate

theorem section_pair_eq_convolutionSquare
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b) (s : SourceInterval b) :
    inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel g.test g.test.continuous a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel g.test g.test.continuous a c b) s) =
      g.convolutionSquare.test b := by
  rw [section_pair_eq_interval_integral]
  rw [crossing_integral_restrict_eq_full g.test a c b hsupp hb s]
  rw [full_crossing_integral_eq_convolution_integral]
  exact (CompactLogConvolution.CompactLogTest.convolutionSquare_apply g b).symm

theorem reverse_section_pair_eq_convolutionSquare_neg
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b) (s : SourceInterval b) :
    inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel g.test g.test.continuous a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel g.test g.test.continuous a c b) s) =
      g.convolutionSquare.test (-b) := by
  rw [← inner_conj_symm]
  rw [section_pair_eq_convolutionSquare g a c b hsupp hb s]
  exact (g.convolutionSquare_neg b).symm

theorem pairData_trace_eq_mul_convolutionSquare
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (pairData g.test g.test.continuous a c b basis).traceProduct =
      (b : ℂ) * g.convolutionSquare.test b := by
  rw [pairData_trace_eq_restricted_crossing_integral]
  calc
    (∫ s, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel g.test g.test.continuous a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel g.test g.test.continuous a c b) s)) =
        ∫ _s : SourceInterval b, g.convolutionSquare.test b := by
      apply integral_congr_ae
      filter_upwards with s
      exact section_pair_eq_convolutionSquare g a c b hsupp hb s
    _ = (b : ℂ) * g.convolutionSquare.test b := by
      rw [integral_const]
      change ((((volume : Measure (SourceInterval b)) Set.univ).toReal : ℝ) : ℂ) *
        g.convolutionSquare.test b = _
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
      simp [hb, ENNReal.toReal_ofReal]

theorem reversePairData_trace_eq_mul_convolutionSquare_neg
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (reversePairData g.test g.test.continuous a c b basis).traceProduct =
      (b : ℂ) * g.convolutionSquare.test (-b) := by
  rw [reversePairData_trace_eq_restricted_crossing_integral]
  calc
    (∫ s, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (leftKernel g.test g.test.continuous a c b) s)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (KernelInterval a c b))
          (rightKernel g.test g.test.continuous a c b) s)) =
        ∫ _s : SourceInterval b, g.convolutionSquare.test (-b) := by
      apply integral_congr_ae
      filter_upwards with s
      exact reverse_section_pair_eq_convolutionSquare_neg g a c b hsupp hb s
    _ = (b : ℂ) * g.convolutionSquare.test (-b) := by
      rw [integral_const]
      change ((((volume : Measure (SourceInterval b)) Set.univ).toReal : ℝ) : ℂ) *
        g.convolutionSquare.test (-b) = _
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
      simp [hb, ENNReal.toReal_ofReal]

theorem pair_traces_add_eq_mul_symmetric_convolutionSquare
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (pairData g.test g.test.continuous a c b basis).traceProduct +
      PositiveTrace.ordinaryTraceAlong basis
        (reversePairData g.test g.test.continuous a c b basis).traceProduct =
      (b : ℂ) *
        (g.convolutionSquare.test b + g.convolutionSquare.test (-b)) := by
  rw [pairData_trace_eq_mul_convolutionSquare g a c b hsupp hb basis]
  rw [reversePairData_trace_eq_mul_convolutionSquare_neg
    g a c b hsupp hb basis]
  ring

theorem owner_pair_traces_add_eq_singleCrossingPairDiagonalIntegral
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c b : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    PositiveTrace.ordinaryTraceAlong basis
        (pairData owner.sourceTest.test owner.sourceTest.test.continuous
          a c b basis).traceProduct +
      PositiveTrace.ordinaryTraceAlong basis
        (reversePairData owner.sourceTest.test owner.sourceTest.test.continuous
          a c b basis).traceProduct =
      owner.singleCrossingPairDiagonalIntegral b := by
  rw [pair_traces_add_eq_mul_symmetric_convolutionSquare
    owner.sourceTest a c b hsupp hb basis]
  rw [owner.singleCrossingPairDiagonalIntegral_eq]
  rfl

theorem eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c
        ((m : ℝ) * Real.log (p : ℝ)))))) :
    (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
        (PositiveTrace.ordinaryTraceAlong basis
            (pairData owner.sourceTest.test owner.sourceTest.test.continuous
              a c ((m : ℝ) * Real.log (p : ℝ)) basis).traceProduct +
          PositiveTrace.ordinaryTraceAlong basis
            (reversePairData owner.sourceTest.test owner.sourceTest.test.continuous
              a c ((m : ℝ) * Real.log (p : ℝ)) basis).traceProduct) =
      owner.finitePrimeTerm (p ^ m) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hb : 0 ≤ (m : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hp_one)
  rw [owner_pair_traces_add_eq_singleCrossingPairDiagonalIntegral
    owner a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb basis]
  exact owner.eulerLogSingleCrossingAtom_eq_finitePrimeTerm_pow hp hm

noncomputable abbrev positiveIntervalSquareOwner
    (source : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest) :
    SelectedWeilSquare.SelectedWeilSquareOwner :=
  (SelectedYoshidaBridge.selectedWeilFormulaOfPositiveIntervalCompactTest
    source).square

theorem positiveInterval_eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
    (source : CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval
        (Real.log source.lower) (Real.log source.upper)
        ((m : ℝ) * Real.log (p : ℝ)))))) :
    (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
        (PositiveTrace.ordinaryTraceAlong basis
            (pairData (positiveIntervalSquareOwner source).sourceTest.test
              (positiveIntervalSquareOwner source).sourceTest.test.continuous
              (Real.log source.lower) (Real.log source.upper)
              ((m : ℝ) * Real.log (p : ℝ)) basis).traceProduct +
          PositiveTrace.ordinaryTraceAlong basis
            (reversePairData (positiveIntervalSquareOwner source).sourceTest.test
              (positiveIntervalSquareOwner source).sourceTest.test.continuous
              (Real.log source.lower) (Real.log source.upper)
              ((m : ℝ) * Real.log (p : ℝ)) basis).traceProduct) =
      (positiveIntervalSquareOwner source).finitePrimeTerm (p ^ m) := by
  apply eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
    (positiveIntervalSquareOwner source)
    (Real.log source.lower) (Real.log source.upper) hp hm
  simpa only [positiveIntervalSquareOwner] using
    SelectedYoshidaBridge.compactLogTestOfPositiveIntervalCompactTest_support_subset
      source

end SelectedCrossingKernel
end CCM25Concrete
end Source
end ConnesWeilRH
