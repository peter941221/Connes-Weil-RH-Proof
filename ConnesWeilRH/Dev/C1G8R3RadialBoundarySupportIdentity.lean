/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactConvolutionSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# Finite-window support identity for the selected radial root crossing

The selected root convolution maps the source Sonin carrier across a radial
boundary only through a compact output window. This file identifies that
crossing with the zero extension of the existing compact-kernel factor. It
does not yet make a trace-ideal estimate for the internal prolate-gap term.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactConvolutionSupport
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedCrossingKernel
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance radialBoundarySupportSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A radius for the actual compact support of the selected root test. -/
noncomputable def selectedRootSupportRadius
    (owner : SelectedWeilSquareOwner) : ℝ := by
  classical
  exact max
    (Classical.choose
      owner.sourceTest.compactSupport.isBounded.exists_norm_le) 0

theorem selectedRoot_sourceTest_support_subset
    (owner : SelectedWeilSquareOwner) :
    Function.support owner.sourceTest.test ⊆
      Set.Icc (-selectedRootSupportRadius owner)
        (selectedRootSupportRadius owner) := by
  classical
  let hbound :=
    Classical.choose_spec
      (owner.sourceTest.compactSupport.isBounded.exists_norm_le)
  intro x hx
  have hts : x ∈ tsupport owner.sourceTest.test := subset_tsupport _ hx
  have hnorm : ‖x‖ ≤
      Classical.choose
        owner.sourceTest.compactSupport.isBounded.exists_norm_le :=
    hbound x hts
  have habs : |x| ≤ selectedRootSupportRadius owner := by
    calc
      |x| ≤ Classical.choose
          owner.sourceTest.compactSupport.isBounded.exists_norm_le := by
            simpa only [Real.norm_eq_abs] using hnorm
      _ ≤ selectedRootSupportRadius owner := by
        simp only [selectedRootSupportRadius]
        exact le_max_left _ _
  exact abs_le.mp habs

theorem selectedRoot_involution_support_subset
    (owner : SelectedWeilSquareOwner) :
    Function.support owner.sourceTest.involution.test ⊆
      Set.Icc (-selectedRootSupportRadius owner)
        (selectedRootSupportRadius owner) := by
  intro x hx
  have hvalue : star (owner.sourceTest.test (-x)) ≠ 0 := by
    simpa only [CompactLogConvolution.CompactLogTest.involution_apply,
      Function.mem_support] using hx
  have hsource : owner.sourceTest.test (-x) ≠ 0 := by
    intro hz
    apply hvalue
    simp [hz]
  have hbound := selectedRoot_sourceTest_support_subset owner
    (by simpa only [Function.mem_support] using hsource)
  rcases hbound with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The compact kernel factor which contains the zero-scale root crossing. -/
noncomputable def selectedRootBoundaryWindowFactor
    (owner : SelectedWeilSquareOwner) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure
        (CompactOutputInterval (-selectedRootSupportRadius owner) 0)) :=
  compactOutputRootFactor owner.sourceTest
    (-selectedRootSupportRadius owner) (selectedRootSupportRadius owner)
    (-selectedRootSupportRadius owner) 0

/-- Extend the finite output factor to the whole logarithmic carrier and
restrict its input to the positive half-line. -/
noncomputable def selectedRootBoundaryWindowOperator
    (owner : SelectedWeilSquareOwner) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  kernelIntervalL2ZeroExtension (-selectedRootSupportRadius owner) 0 0 ∘L
    selectedRootBoundaryWindowFactor owner ∘L cc20PositiveHalfLineProjection

theorem selectedRoot_crossing_restrict_below_eq_zero
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    globalL2ToKernelInterval (-(n : ℝ))
        (-selectedRootSupportRadius owner) 0 ∘L
      rootConvolution owner ∘L cc20PositiveHalfLineProjection = 0 := by
  have hroot := selectedRoot_sourceTest_support_subset owner
  unfold rootConvolution
  change (globalL2ToKernelInterval (-(n : ℝ))
      (-selectedRootSupportRadius owner) 0 ∘L
      cc20GlobalLogConvolution owner.sourceTest.involution.test) ∘L
        cc20PositiveHalfLineProjection = 0
  rw [← compactOutputRootFactor_eq_globalConvolution
    owner.sourceTest (-selectedRootSupportRadius owner)
    (selectedRootSupportRadius owner) (-(n : ℝ))
    (-selectedRootSupportRadius owner) hroot]
  change compactOutputRootFactor owner.sourceTest
      (-selectedRootSupportRadius owner) (selectedRootSupportRadius owner)
      (-(n : ℝ)) (-selectedRootSupportRadius owner) ∘L
        cc20PositiveHalfLineProjection = 0
  apply compactOutputRootFactor_comp_positiveHalfLine_eq_zero
  norm_num

theorem selectedRoot_crossing_ae_zero_below_window
    (owner : SelectedWeilSquareOwner) (u : finiteSCarrier) :
    ∀ᵐ x : ℝ ∂volume,
      x < -selectedRootSupportRadius owner →
        (rootConvolution owner
          (cc20PositiveHalfLineProjection u) : ℝ → ℂ) x = 0 := by
  let output := rootConvolution owner (cc20PositiveHalfLineProjection u)
  have hcompact (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume,
        x ∈ Set.Icc (-(n : ℝ)) (-selectedRootSupportRadius owner) →
          (output : ℝ → ℂ) x = 0 := by
    have hop := selectedRoot_crossing_restrict_below_eq_zero owner n
    have happ := congrArg
      (fun T : finiteSCarrier →L[ℂ]
        Lp ℂ 2 (volume : Measure
          (KernelInterval (-(n : ℝ))
            (-selectedRootSupportRadius owner) 0)) => T u) hop
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, output] using
      ae_eq_zero_on_compactInterval_of_restriction_eq_zero output
        (-(n : ℝ)) (-selectedRootSupportRadius owner) happ
  have hall : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x ∈ Set.Icc (-(n : ℝ)) (-selectedRootSupportRadius owner) →
        (output : ℝ → ℂ) x = 0 :=
    ae_all_iff.mpr hcompact
  filter_upwards [hall] with x hx hxbelow
  obtain ⟨n, hn⟩ := exists_nat_ge (-x)
  exact hx n ⟨by linarith, by exact le_of_lt hxbelow⟩

theorem negativeCompactProjection_fixes_selectedRootCrossing
    (owner : SelectedWeilSquareOwner) :
    kernelIntervalProjection (-selectedRootSupportRadius owner) 0 0 ∘L
      cc20NegativeHalfLineProjection ∘L rootConvolution owner ∘L
          cc20PositiveHalfLineProjection =
    cc20NegativeHalfLineProjection ∘L rootConvolution owner ∘L
          cc20PositiveHalfLineProjection := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  let output := rootConvolution owner (cc20PositiveHalfLineProjection u)
  let crossing := cc20NegativeHalfLineProjection output
  have hprojection := kernelIntervalProjection_coeFn
    (-selectedRootSupportRadius owner) 0 0 crossing
  have hnegative := cc20NegativeHalfLineProjection_coeFn output
  have hbelow := selectedRoot_crossing_ae_zero_below_window owner u
  filter_upwards [hprojection, hnegative, hbelow] with x hp hn hb
  simp only [ContinuousLinearMap.comp_apply, output, crossing] at hp hn ⊢
  simp only [sub_zero, add_zero] at hp
  rw [hp]
  let outputSet := Set.Icc (-selectedRootSupportRadius owner) (0 : ℝ)
  by_cases hx : x ∈ outputSet
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hn]
    by_cases hxnegative : x ∈ Set.Iio (0 : ℝ)
    · rw [Set.indicator_of_mem hxnegative]
      have hxbelow : x < -selectedRootSupportRadius owner := by
        by_contra hxnot
        apply hx
        exact ⟨le_of_not_gt hxnot, le_of_lt hxnegative⟩
      exact (hb hxbelow).symm
    · rw [Set.indicator_of_notMem hxnegative]

/-- The selected root's positive-to-negative zero-boundary crossing is
exactly the zero extension of its finite-window compact-kernel factor. -/
theorem selectedRoot_zeroBoundaryCrossing_eq_finiteWindow
    (owner : SelectedWeilSquareOwner) :
    selectedRootBoundaryWindowOperator owner =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        cc20PositiveHalfLineProjection) ∘L rootConvolution owner ∘L
          cc20PositiveHalfLineProjection := by
  unfold selectedRootBoundaryWindowOperator
  unfold rootConvolution
  let outputProjection := kernelIntervalProjection
    (-selectedRootSupportRadius owner) 0 0
  let halfLine := cc20PositiveHalfLineProjection
  let outputExtension := kernelIntervalL2ZeroExtension
    (-selectedRootSupportRadius owner) 0 0
  let outputRestriction := globalL2ToKernelInterval
    (-selectedRootSupportRadius owner) 0 0
  have hprojectionHalfLine : outputProjection ∘L halfLine = 0 := by
    simpa only [outputProjection, zero_add, add_zero] using
      inputProjection_comp_positiveHalfLine_eq_zero
        (-selectedRootSupportRadius owner) 0 0 0 (by norm_num)
  have hprojectionNegative : outputProjection ∘L
      cc20NegativeHalfLineProjection =
      outputProjection := by
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u)
      hprojectionHalfLine
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hu
    change outputProjection (u - halfLine u) = outputProjection u
    rw [map_sub]
    rw [hu, sub_zero]
  have houtputProjection : outputProjection =
      outputExtension ∘L outputRestriction := by
    change kernelIntervalProjection
        (-selectedRootSupportRadius owner) 0 0 =
      kernelIntervalL2ZeroExtension
          (-selectedRootSupportRadius owner) 0 0 ∘L
        globalL2ToKernelInterval
          (-selectedRootSupportRadius owner) 0 0
    unfold kernelIntervalProjection
    have hadj :
        (kernelIntervalL2ZeroExtension
          (-selectedRootSupportRadius owner) 0 0).adjoint =
          globalL2ToKernelInterval
            (-selectedRootSupportRadius owner) 0 0 := by
      rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
        ContinuousLinearMap.adjoint_adjoint]
    rw [hadj]
  have hfinite := compactOutputRootFactor_eq_globalConvolution
    owner.sourceTest (-selectedRootSupportRadius owner)
      (selectedRootSupportRadius owner)
      (-selectedRootSupportRadius owner) 0
      (selectedRoot_sourceTest_support_subset owner)
  calc
    outputExtension ∘L
        selectedRootBoundaryWindowFactor owner ∘L halfLine =
      (outputExtension ∘L outputRestriction) ∘L
        cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L halfLine := by
          rw [selectedRootBoundaryWindowFactor, hfinite]
          apply ContinuousLinearMap.ext
          intro u
          rfl
    _ = outputProjection ∘L
        cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L halfLine := by
          rw [← houtputProjection]
    _ = outputProjection ∘L cc20NegativeHalfLineProjection ∘L
        cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L halfLine := by
          have h := congrArg
            (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
              T ∘L (cc20GlobalLogConvolution
                owner.sourceTest.involution.test ∘L halfLine))
            hprojectionNegative
          calc
            outputProjection ∘L
                cc20GlobalLogConvolution
                  owner.sourceTest.involution.test ∘L halfLine =
                outputProjection ∘L
                  (cc20GlobalLogConvolution
                    owner.sourceTest.involution.test ∘L halfLine) := by
                    apply ContinuousLinearMap.ext
                    intro u
                    rfl
            _ = (outputProjection ∘L cc20NegativeHalfLineProjection) ∘L
                  (cc20GlobalLogConvolution
                    owner.sourceTest.involution.test ∘L halfLine) := h.symm
            _ = outputProjection ∘L cc20NegativeHalfLineProjection ∘L
                  cc20GlobalLogConvolution
                    owner.sourceTest.involution.test ∘L halfLine := by
                    apply ContinuousLinearMap.ext
                    intro u
                    rfl
    _ = cc20NegativeHalfLineProjection ∘L
        cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L halfLine := by
          exact negativeCompactProjection_fixes_selectedRootCrossing owner

/-- At the actual CCM24 radial cutoff, the selected root's source-Sonin
leakage is the translate of the same finite-window half-line crossing. -/
theorem selectedRoot_radialSourceLeakage_eq_translatedFiniteWindow
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda) ∘L
        rootConvolution owner ∘L sourceInclusion lambda =
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
        selectedRootBoundaryWindowOperator owner ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
            sourceInclusion lambda := by
  let root := rootConvolution owner
  let inclusion := sourceInclusion lambda
  let radial := radialSupportProjection lambda
  let halfLine := cc20PositiveHalfLineProjection
  let plus :=
    (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
  let minus :=
    (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap
  let negative := ContinuousLinearMap.id ℂ finiteSCarrier - halfLine
  have hRadial := radialSupportProjection_eq_translation_conjugation lambda
  have hComplement :
      ContinuousLinearMap.id ℂ finiteSCarrier - radial =
        minus ∘L negative ∘L plus := by
    apply ContinuousLinearMap.ext
    intro u
    have hRadialU := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u) hRadial
    simp only [ContinuousLinearMap.comp_apply] at hRadialU
    change u - radial u = minus (plus u - halfLine (plus u))
    rw [map_sub]
    have hMinusPlus : minus (plus u) = u := by
      change cc20GlobalLogTranslation (-Real.log lambda)
        (cc20GlobalLogTranslation (Real.log lambda) u) = u
      simpa only [neg_neg] using
        cc20GlobalLogTranslation_neg_apply (-Real.log lambda) u
    rw [hMinusPlus, ← hRadialU]
  have hSourceProjection :
      sourceSoninProjection lambda ∘L inclusion = inclusion := by
    calc
      sourceSoninProjection lambda ∘L inclusion =
          (inclusion ∘L (inclusion)†) ∘L inclusion := by
        rw [← sourceInclusion_comp_adjoint]
      _ = inclusion ∘L ((inclusion)† ∘L inclusion) := by
        apply ContinuousLinearMap.ext
        intro u
        rfl
      _ = inclusion := by
        rw [sourceInclusion_adjoint_comp_self]
        simp only [ContinuousLinearMap.comp_id]
  have hRadialSource : radial ∘L inclusion = inclusion := by
    calc
      radial ∘L inclusion = radial ∘L
          (sourceSoninProjection lambda ∘L inclusion) := by
        rw [hSourceProjection]
      _ = (radial ∘L sourceSoninProjection lambda) ∘L inclusion := by
        apply ContinuousLinearMap.ext
        intro u
        rfl
      _ = sourceSoninProjection lambda ∘L inclusion := by
        rw [radialSupportProjection_comp_sourceSoninProjection]
      _ = inclusion := hSourceProjection
  have hHalfLineTranslation : halfLine ∘L plus = plus ∘L radial := by
    apply ContinuousLinearMap.ext
    intro u
    have hRadialU := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u) hRadial
    simp only [ContinuousLinearMap.comp_apply] at hRadialU
    change halfLine (plus u) = plus (radial u)
    rw [hRadialU]
    exact (cc20GlobalLogTranslation_neg_apply (Real.log lambda)
      (halfLine (plus u))).symm
  have hRootTranslation : root ∘L plus = plus ∘L root := by
    change cc20GlobalLogConvolution owner.sourceTest.involution.test ∘L plus =
      plus ∘L cc20GlobalLogConvolution owner.sourceTest.involution.test
    simpa only [neg_neg, plus] using
      cc20GlobalLogConvolution_comp_translation_neg_eq
        owner.sourceTest (-Real.log lambda)
  apply ContinuousLinearMap.ext
  intro u
  have hRadialAt := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => T u)
    hRadialSource
  simp only [ContinuousLinearMap.comp_apply, inclusion] at hRadialAt
  have hHalfAt := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T (inclusion u))
    hHalfLineTranslation
  simp only [ContinuousLinearMap.comp_apply] at hHalfAt
  have hRootAt := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T (inclusion u))
    hRootTranslation
  simp only [ContinuousLinearMap.comp_apply] at hRootAt
  have hHalfSource : halfLine (plus (inclusion u)) =
      plus (inclusion u) := by
    calc
      halfLine (plus (inclusion u)) =
          plus (radial (inclusion u)) := hHalfAt
      _ = plus (inclusion u) := congrArg plus hRadialAt
  change (ContinuousLinearMap.id ℂ finiteSCarrier - radial)
        (root (inclusion u)) =
      minus (selectedRootBoundaryWindowOperator owner (plus (inclusion u)))
  have hLeakAt := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (root (inclusion u))) hComplement
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    root] at hLeakAt
  calc
    (ContinuousLinearMap.id ℂ finiteSCarrier - radial)
        (root (inclusion u)) =
      minus (negative (plus (root (inclusion u)))) := hLeakAt
    _ = minus (negative (root (plus (inclusion u)))) := by
      rw [← hRootAt]
    _ = minus (negative
        (root (halfLine (plus (inclusion u))))) := by
      exact congrArg (fun z => minus (negative (root z)))
        hHalfSource.symm
    _ = minus (selectedRootBoundaryWindowOperator owner
        (plus (inclusion u))) := by
      have hwindow := congrArg
        (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
          T (plus (inclusion u)))
        (selectedRoot_zeroBoundaryCrossing_eq_finiteWindow owner)
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        root, halfLine, negative] at hwindow
      exact congrArg minus hwindow.symm

end Dev
end ConnesWeilRH
