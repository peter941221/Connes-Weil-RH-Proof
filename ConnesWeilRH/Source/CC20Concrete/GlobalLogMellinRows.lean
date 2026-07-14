/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
import ConnesWeilRH.Source.CC20Concrete.CompactBadSpace
import ConnesWeilRH.Source.CC20Concrete.ParameterizedHaarCompact
import ConnesWeilRH.Source.CC20YoshidaConvolution
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Mellin Riesz rows on the finite logarithmic window

For a source test supported in `(1 / lambda, lambda)`, its global Mellin
evaluation is represented by an actual `L2` inner product on the same finite
window that carries the CC20 regular operator.  The row is first constructed
on the compact log-window subtype, then transported to the restricted-log and
Haar carriers through the existing exact linear isometries.

This module identifies the genuine finite-node Mellin equations with row
orthogonality.  It does not claim that a chosen finite row span contains the
compact remainder's bad space; that containment remains a separate producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open CC20YoshidaNearZeros
open CompactBadSpace
open scoped ComplexConjugate FourierTransform InnerProduct InnerProductSpace

noncomputable local instance cc20LogWindowPointCompactSpace
    (lambda : ℝ) : CompactSpace (CC20LogWindowPoint lambda) := by
  unfold CC20LogWindowPoint cc20LogWindow
  infer_instance

/-- The source test restricted to the compact logarithmic window. -/
noncomputable def cc20LogMellinTestInputContinuous
    (lambda : ℝ) (g : normalizedCC20ConcreteTestAlgebra.Test) :
    ContinuousMap (CC20LogWindowPoint lambda) ℂ where
  toFun t := normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t.1)
  continuous_toFun := by
    exact (SchwartzMap.continuous
      (normalizedCC20ConcreteTestAlgebra.legacy.encode g)).comp
      (Real.continuous_exp.comp continuous_subtype_val)

/-- The Riesz row for Mellin evaluation at `s` in the logarithmic coordinate.
The conjugate is forced by Mathlib's convention that the first inner-product
argument is conjugate-linear. -/
noncomputable def cc20LogMellinRowContinuous
    (lambda : ℝ) (s : ℂ) : ContinuousMap (CC20LogWindowPoint lambda) ℂ where
  toFun t := star (Complex.exp (s * (t.1 : ℂ)))
  continuous_toFun := by
    fun_prop

noncomputable def cc20LogMellinRow
    (lambda : ℝ) (s : ℂ) :
    Lp ℂ 2 (cc20LogWindowBaseMeasure lambda) :=
  ContinuousMap.toLp 2 (cc20LogWindowBaseMeasure lambda) ℂ
    (cc20LogMellinRowContinuous lambda s)

noncomputable def cc20LogMellinTestInput
    (lambda : ℝ) (g : normalizedCC20ConcreteTestAlgebra.Test) :
    Lp ℂ 2 (cc20LogWindowBaseMeasure lambda) :=
  ContinuousMap.toLp 2 (cc20LogWindowBaseMeasure lambda) ℂ
    (cc20LogMellinTestInputContinuous lambda g)

/-- The subtype `L2` inner product is the expected finite log-window
integral. -/
theorem cc20LogMellinRow_inner_testInput_eq_logIntegral
    (lambda : ℝ) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    inner ℂ (cc20LogMellinRow lambda s)
        (cc20LogMellinTestInput lambda g) =
      ∫ t in cc20LogWindow lambda,
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) *
          Complex.exp (s * (t : ℂ)) := by
  change inner ℂ
      (ContinuousMap.toLp 2 (cc20LogWindowBaseMeasure lambda) ℂ
        (cc20LogMellinRowContinuous lambda s))
      (ContinuousMap.toLp 2 (cc20LogWindowBaseMeasure lambda) ℂ
        (cc20LogMellinTestInputContinuous lambda g)) = _
  rw [ContinuousMap.inner_toLp]
  unfold cc20LogWindowBaseMeasure
  unfold CC20LogWindowPoint cc20LogWindow
  change (∫ t : {t : ℝ // t ∈ Set.Icc (-Real.log lambda) (Real.log lambda)},
      normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp (t : ℝ)) *
        star (star (Complex.exp (s * (((t : ℝ) : ℂ)))))
        ∂Measure.comap Subtype.val volume) = _
  have hsub := integral_subtype_comap
    (s := Set.Icc (-Real.log lambda) (Real.log lambda))
    (μ := (volume : Measure ℝ)) measurableSet_Icc
    (fun t : ℝ =>
      normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) *
        star (star (Complex.exp (s * (t : ℂ)))))
  rw [hsub]
  simp

/-- A source test supported in the multiplicative window has its global
Mellin value represented by the finite-window row. -/
theorem cc20LogMellinRow_inner_testInput_eq_mellin
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20LogMellinRow lambda s)
        (cc20LogMellinTestInput lambda g) =
      mellin
        (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) s := by
  rw [cc20LogMellinRow_inner_testInput_eq_logIntegral]
  rw [show cc20LogWindow lambda =
      Set.Icc (-Real.log lambda) (Real.log lambda) by rfl]
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  let hlogTest :=
    CCM25Concrete.SelectedYoshidaBridge.compactLogTestOfWindow g
      (one_div_pos.mpr hlambda_pos) hlambda_pos hsupport
  have hwindow_zero :
      ∀ t : ℝ, t ∉ Set.Icc (-Real.log lambda) (Real.log lambda) →
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) *
            Complex.exp (s * (t : ℂ)) = 0 := by
    intro t ht
    by_cases hzero :
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) = 0
    · simp [hzero]
    · have hmem : Real.exp t ∈ Function.support
          (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) :=
        Function.mem_support.mpr hzero
      have hbounds := hsupport hmem
      have hleft : -Real.log lambda < t := by
        have hlog := (Real.log_lt_iff_lt_exp
          (one_div_pos.mpr hlambda_pos)).2 hbounds.1
        simpa [Real.log_inv] using hlog
      have hright : t < Real.log lambda :=
        (Real.lt_log_iff_exp_lt hlambda_pos).2 hbounds.2
      exact (ht ⟨le_of_lt hleft, le_of_lt hright⟩).elim
  calc
    (∫ t in Set.Icc (-Real.log lambda) (Real.log lambda),
        normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) *
          Complex.exp (s * (t : ℂ))) =
        ∫ t : ℝ,
          normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp t) *
            Complex.exp (s * (t : ℂ)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hwindow_zero
    _ = CC20YoshidaConvolution.CompactLogTest.laplaceAt hlogTest s := by
      unfold CC20YoshidaConvolution.CompactLogTest.laplaceAt
      simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
        hlogTest,
        CCM25Concrete.SelectedYoshidaBridge.compactLogTestOfWindow_apply]
      apply integral_congr_ae
      filter_upwards with t
      exact mul_comm _ _
    _ = mellin
        (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) s :=
      CC20YoshidaConvolution.CompactLogTest.laplaceAt_compactLogTestOfWindow_eq_mellin
        g (one_div_pos.mpr hlambda_pos) hlambda_pos hsupport s

theorem cc20LogMellinRow_inner_testInput_eq_fourier
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20LogMellinRow lambda s)
        (cc20LogMellinTestInput lambda g) =
      𝓕 (fun u : ℝ =>
        Real.exp (-s.re * u) •
          normalizedCC20ConcreteTestAlgebra.legacy.encode g (Real.exp (-u)))
        (s.im / (2 * Real.pi)) := by
  rw [cc20LogMellinRow_inner_testInput_eq_mellin
    lambda hlambda s g hsupport]
  exact mellin_eq_fourier _

theorem cc20LogMellinRow_inner_testInput_eq_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20LogMellinRow lambda s)
        (cc20LogMellinTestInput lambda g) =
      normalizedCC20TestSpace.mellinAt g s := by
  rw [cc20LogMellinRow_inner_testInput_eq_mellin
    lambda hlambda s g hsupport]
  rfl

/-- Consumer orientation: detector constraints use `inner input row`. -/
theorem cc20LogMellinTestInput_inner_row_eq_star_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20LogMellinTestInput lambda g)
        (cc20LogMellinRow lambda s) =
      star (normalizedCC20TestSpace.mellinAt g s) := by
  calc
    inner ℂ (cc20LogMellinTestInput lambda g)
        (cc20LogMellinRow lambda s) =
        star (inner ℂ (cc20LogMellinRow lambda s)
          (cc20LogMellinTestInput lambda g)) :=
      (inner_conj_symm (𝕜 := ℂ)
        (cc20LogMellinTestInput lambda g)
        (cc20LogMellinRow lambda s)).symm
    _ = star (normalizedCC20TestSpace.mellinAt g s) :=
      congrArg star
        (cc20LogMellinRow_inner_testInput_eq_mellinAt
          lambda hlambda s g hsupport)

theorem cc20LogMellinTestInput_inner_row_eq_zero_iff
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20LogMellinTestInput lambda g)
        (cc20LogMellinRow lambda s) = 0 ↔
      normalizedCC20TestSpace.mellinAt g s = 0 := by
  rw [cc20LogMellinTestInput_inner_row_eq_star_mellinAt
    lambda hlambda s g hsupport]
  simp

/-- The same row on the restricted logarithmic `L2` carrier used by the
compact regular endomorphism. -/
noncomputable def cc20RestrictedLogMellinRow
    (lambda : ℝ) (s : ℂ) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  (cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda).symm
    (cc20LogMellinRow lambda s)

noncomputable def cc20RestrictedLogMellinTestInput
    (lambda : ℝ) (g : normalizedCC20ConcreteTestAlgebra.Test) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  (cc20LogWindowSubtypeRestrictedL2IsometryEquiv lambda).symm
    (cc20LogMellinTestInput lambda g)

theorem cc20RestrictedLogMellinRow_inner_testInput_eq_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20RestrictedLogMellinRow lambda s)
        (cc20RestrictedLogMellinTestInput lambda g) =
      normalizedCC20TestSpace.mellinAt g s := by
  have htransport :
      inner ℂ (cc20RestrictedLogMellinRow lambda s)
          (cc20RestrictedLogMellinTestInput lambda g) =
        inner ℂ (cc20LogMellinRow lambda s)
          (cc20LogMellinTestInput lambda g) := by
    rw [cc20RestrictedLogMellinRow, cc20RestrictedLogMellinTestInput]
    simp
  rw [htransport]
  exact cc20LogMellinRow_inner_testInput_eq_mellinAt
    lambda hlambda s g hsupport

theorem cc20RestrictedLogMellinTestInput_inner_row_eq_star_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20RestrictedLogMellinTestInput lambda g)
        (cc20RestrictedLogMellinRow lambda s) =
      star (normalizedCC20TestSpace.mellinAt g s) := by
  calc
    inner ℂ (cc20RestrictedLogMellinTestInput lambda g)
        (cc20RestrictedLogMellinRow lambda s) =
        star (inner ℂ (cc20RestrictedLogMellinRow lambda s)
          (cc20RestrictedLogMellinTestInput lambda g)) :=
      (inner_conj_symm (𝕜 := ℂ)
        (cc20RestrictedLogMellinTestInput lambda g)
        (cc20RestrictedLogMellinRow lambda s)).symm
    _ = star (normalizedCC20TestSpace.mellinAt g s) :=
      congrArg star
        (cc20RestrictedLogMellinRow_inner_testInput_eq_mellinAt
          lambda hlambda s g hsupport)

theorem cc20RestrictedLogMellinTestInput_inner_row_eq_zero_iff
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20RestrictedLogMellinTestInput lambda g)
        (cc20RestrictedLogMellinRow lambda s) = 0 ↔
      normalizedCC20TestSpace.mellinAt g s = 0 := by
  rw [cc20RestrictedLogMellinTestInput_inner_row_eq_star_mellinAt
    lambda hlambda s g hsupport]
  simp

/-- The Mellin row on the exact Haar carrier, transported through the same
equivalence used to conjugate the regular operator. -/
noncomputable def cc20WindowHaarMellinRow
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
  (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm
    (cc20RestrictedLogMellinRow lambda s)

noncomputable def cc20WindowHaarMellinTestInput
    (lambda : ℝ) (hlambda : 1 < lambda)
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
  (cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda).symm
    (cc20RestrictedLogMellinTestInput lambda g)

theorem cc20WindowHaarMellinRow_inner_testInput_eq_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20WindowHaarMellinRow lambda hlambda s)
        (cc20WindowHaarMellinTestInput lambda hlambda g) =
      normalizedCC20TestSpace.mellinAt g s := by
  have htransport :
      inner ℂ (cc20WindowHaarMellinRow lambda hlambda s)
          (cc20WindowHaarMellinTestInput lambda hlambda g) =
        inner ℂ (cc20RestrictedLogMellinRow lambda s)
          (cc20RestrictedLogMellinTestInput lambda g) := by
    rw [cc20WindowHaarMellinRow, cc20WindowHaarMellinTestInput]
    simp
  rw [htransport]
  exact cc20RestrictedLogMellinRow_inner_testInput_eq_mellinAt
    lambda hlambda s g hsupport

theorem cc20WindowHaarMellinTestInput_inner_row_eq_star_mellinAt
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20WindowHaarMellinTestInput lambda hlambda g)
        (cc20WindowHaarMellinRow lambda hlambda s) =
      star (normalizedCC20TestSpace.mellinAt g s) := by
  calc
    inner ℂ (cc20WindowHaarMellinTestInput lambda hlambda g)
        (cc20WindowHaarMellinRow lambda hlambda s) =
        star (inner ℂ (cc20WindowHaarMellinRow lambda hlambda s)
          (cc20WindowHaarMellinTestInput lambda hlambda g)) :=
      (inner_conj_symm (𝕜 := ℂ)
        (cc20WindowHaarMellinTestInput lambda hlambda g)
        (cc20WindowHaarMellinRow lambda hlambda s)).symm
    _ = star (normalizedCC20TestSpace.mellinAt g s) :=
      congrArg star
        (cc20WindowHaarMellinRow_inner_testInput_eq_mellinAt
          lambda hlambda s g hsupport)

theorem cc20WindowHaarMellinTestInput_inner_row_eq_zero_iff
    (lambda : ℝ) (hlambda : 1 < lambda) (s : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    inner ℂ (cc20WindowHaarMellinTestInput lambda hlambda g)
        (cc20WindowHaarMellinRow lambda hlambda s) = 0 ↔
      normalizedCC20TestSpace.mellinAt g s = 0 := by
  rw [cc20WindowHaarMellinTestInput_inner_row_eq_star_mellinAt
    lambda hlambda s g hsupport]
  simp

/-- The actual finite-node Mellin rows on the restricted logarithmic carrier. -/
noncomputable def cc20RestrictedLogFiniteMellinRows
    (lambda : ℝ) (nodes : Finset ℂ) :
    FiniteMellinNode nodes →
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  fun z => cc20RestrictedLogMellinRow lambda z.1

/-- The same finite-node family on the Haar carrier. -/
noncomputable def cc20WindowHaarFiniteMellinRows
    (lambda : ℝ) (hlambda : 1 < lambda) (nodes : Finset ℂ) :
    FiniteMellinNode nodes →
      Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
  fun z => cc20WindowHaarMellinRow lambda hlambda z.1

theorem cc20RestrictedLogFiniteMellinRows_vanishing_iff
    (lambda : ℝ) (hlambda : 1 < lambda) (nodes : Finset ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    (∀ z : FiniteMellinNode nodes,
      inner ℂ (cc20RestrictedLogMellinTestInput lambda g)
        (cc20RestrictedLogFiniteMellinRows lambda nodes z) = 0) ↔
      ∀ z : FiniteMellinNode nodes,
        normalizedCC20TestSpace.mellinAt g z.1 = 0 := by
  constructor
  · intro h z
    exact (cc20RestrictedLogMellinTestInput_inner_row_eq_zero_iff
      lambda hlambda z.1 g hsupport).mp (h z)
  · intro h z
    exact (cc20RestrictedLogMellinTestInput_inner_row_eq_zero_iff
      lambda hlambda z.1 g hsupport).mpr (h z)

theorem cc20WindowHaarFiniteMellinRows_vanishing_iff
    (lambda : ℝ) (hlambda : 1 < lambda) (nodes : Finset ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test)
    (hsupport : Function.support
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
      Set.Ioo (1 / lambda) lambda) :
    (∀ z : FiniteMellinNode nodes,
      inner ℂ (cc20WindowHaarMellinTestInput lambda hlambda g)
        (cc20WindowHaarFiniteMellinRows lambda hlambda nodes z) = 0) ↔
      ∀ z : FiniteMellinNode nodes,
        normalizedCC20TestSpace.mellinAt g z.1 = 0 := by
  constructor
  · intro h z
    exact (cc20WindowHaarMellinTestInput_inner_row_eq_zero_iff
      lambda hlambda z.1 g hsupport).mp (h z)
  · intro h z
    exact (cc20WindowHaarMellinTestInput_inner_row_eq_zero_iff
      lambda hlambda z.1 g hsupport).mpr (h z)

/-- Distinct finite Mellin nodes give linearly independent Riesz rows.  The
proof uses the existing fixed-window Mellin interpolation theorem, so this is
an operator-space consequence of genuine source tests rather than a formal
relabeling of an abstract basis. -/
theorem linearIndependent_cc20RestrictedLogFiniteMellinRows
    (lambda : ℝ) (hlambda : 1 < lambda) (nodes : Finset ℂ) :
    LinearIndependent ℂ
      (cc20RestrictedLogFiniteMellinRows lambda nodes) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum z
  have hlambda_pos : 0 < lambda := lt_trans (by norm_num) hlambda
  have hinv_pos : 0 < 1 / lambda := one_div_pos.mpr hlambda_pos
  have hinv_one : 1 / lambda < 1 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hlambda
    simpa using h
  obtain ⟨g, _hcompact, hsupport, hvalues⟩ :=
    fixed_window_finite_mellin_surjective nodes
      hinv_pos hinv_one hlambda
      (fun w => if w = z then 1 else 0)
  let input := cc20RestrictedLogMellinTestInput lambda g
  have hsumInner := congrArg (fun v => inner ℂ input v) hsum
  change inner ℂ input
      (∑ i, coeff i • cc20RestrictedLogFiniteMellinRows lambda nodes i) =
    inner ℂ input 0 at hsumInner
  rw [inner_sum] at hsumInner
  simp only [inner_smul_right, inner_zero_right] at hsumInner
  have hread (w : FiniteMellinNode nodes) :
      inner ℂ input (cc20RestrictedLogFiniteMellinRows lambda nodes w) =
        star (normalizedCC20TestSpace.mellinAt g w.1) := by
    dsimp [input, cc20RestrictedLogFiniteMellinRows]
    exact cc20RestrictedLogMellinTestInput_inner_row_eq_star_mellinAt
      lambda hlambda w.1 g hsupport
  simp_rw [hread, hvalues] at hsumInner
  simpa using hsumInner

theorem linearIndependent_cc20WindowHaarFiniteMellinRows
    (lambda : ℝ) (hlambda : 1 < lambda) (nodes : Finset ℂ) :
    LinearIndependent ℂ
      (cc20WindowHaarFiniteMellinRows lambda hlambda nodes) := by
  let e := cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
  let f :
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →ₗ[ℂ]
        Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda) :=
    e.symm.toLinearEquiv.toLinearMap
  have hmap :=
    (linearIndependent_cc20RestrictedLogFiniteMellinRows
      lambda hlambda nodes).map' f
      (LinearMap.ker_eq_bot_of_injective e.symm.injective)
  simpa [cc20WindowHaarFiniteMellinRows,
    cc20WindowHaarMellinRow, cc20RestrictedLogFiniteMellinRows,
    Function.comp_def, e, f] using hmap

/-- A compact control space for the Haar remainder can be consumed by actual
finite Mellin rows once their span contains it.  The theorem deliberately
keeps that span-containment premise visible: fixed-window interpolation gives
independence of the rows, not containment of an arbitrary compact bad space. -/
theorem exists_finite_cc20WindowHaarMellinControlSpace
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ∃ controlSpace :
        Submodule ℂ (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)),
      FiniteDimensional ℂ controlSpace ∧
        controlSpace ≤ Submodule.span ℂ
          (Set.range
            (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ)) ∧
        ∀ (nodes : Finset ℂ),
          controlSpace ≤ Submodule.span ℂ
            (Set.range (cc20WindowHaarFiniteMellinRows lambda hlambda nodes)) →
          ∀ (g : normalizedCC20ConcreteTestAlgebra.Test),
            Function.support
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
              Set.Ioo (1 / lambda) lambda →
            (∀ z : FiniteMellinNode nodes,
              normalizedCC20TestSpace.mellinAt g z.1 = 0) →
            (inner ℂ
              (cc20WindowHaarMellinTestInput lambda hlambda g)
              (cc20WindowHaarComplexL2Operator lambda hlambda
                (cc20WindowHaarMellinTestInput lambda hlambda g) -
                (2 : ℂ) • cc20WindowHaarMellinTestInput lambda hlambda g)).re ≤ 0 := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
      (p := (2 : ENNReal)) (μ := cc20WindowHaarMeasure lambda hlambda)
      (by norm_num)
  obtain ⟨controlSpace, hfinite, hsource, hbound⟩ :=
    exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace_spanned_by_denseRange
      (cc20WindowHaarComplexL2Operator lambda hlambda)
      (isCompactOperator_cc20WindowHaarComplexL2Operator lambda hlambda)
      (ContinuousMap.toLp 2 (cc20WindowHaarMeasure lambda hlambda) ℂ)
      hdense
      (by norm_num : (0 : ℝ) < 2)
  refine ⟨controlSpace, hfinite, hsource, ?_⟩
  intro nodes hcoverage g hsupport hzeros
  let evaluationSpace : Submodule ℂ
      (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda)) :=
    Submodule.span ℂ
      (Set.range (cc20WindowHaarFiniteMellinRows lambda hlambda nodes))
  have hcontrolEval : controlSpace ≤ evaluationSpace := by
    simpa [evaluationSpace] using hcoverage
  apply hbound evaluationSpace hcontrolEval
  rw [Submodule.mem_orthogonal']
  intro y hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact (cc20WindowHaarMellinTestInput_inner_row_eq_zero_iff
      lambda hlambda z.1 g hsupport).mpr (hzeros z)
  · simp
  · intro y z hy hz hiy hiz
    rw [inner_add_right, hiy, hiz, add_zero]
  · intro a y hy hiy
    rw [inner_smul_right, hiy, mul_zero]

end CC20Concrete
end Source
end ConnesWeilRH
