/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Selected CCM25 Weil squares

This module keeps one compact log-coordinate test tied to its genuine
half-density convolution square and prime-power evaluations.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedWeilSquare

open CompactLogConvolution

/-- One selected test, its definitional convolution square, and a support bound. -/
structure SelectedWeilSquareOwner where
  sourceTest : CompactLogTest
  supportRadius : ℝ
  supportRadius_nonnegative : 0 ≤ supportRadius
  convolutionSquare_support :
    Function.support sourceTest.convolutionSquare.test ⊆
      Set.Icc (-supportRadius) supportRadius

namespace SelectedWeilSquareOwner

/-- Compact support supplies the radius required by the selected owner. -/
noncomputable def ofCompactLogTest
    (sourceTest : CompactLogTest) : SelectedWeilSquareOwner := by
  classical
  let hexists :=
    sourceTest.convolutionSquare.compactSupport.isBounded.exists_norm_le
  let R := Classical.choose hexists
  have hR := Classical.choose_spec hexists
  refine
    { sourceTest := sourceTest
      supportRadius := max R 0
      supportRadius_nonnegative := le_max_right R 0
      convolutionSquare_support := ?_ }
  intro x hx
  have hxtsupport : x ∈ tsupport sourceTest.convolutionSquare.test :=
    subset_tsupport _ hx
  have habs : |x| ≤ max R 0 := by
    simpa [Real.norm_eq_abs] using
      (hR x hxtsupport).trans (le_max_left R 0)
  exact abs_le.1 habs

/-- The square remains tied to `sourceTest`; no second square witness is stored. -/
noncomputable def convolutionSquare
    (owner : SelectedWeilSquareOwner) : CompactLogTest :=
  owner.sourceTest.convolutionSquare

@[simp] theorem convolutionSquare_apply
    (owner : SelectedWeilSquareOwner) (x : ℝ) :
    owner.convolutionSquare.test x =
      ∫ t : ℝ,
        star (owner.sourceTest.test (-t)) * owner.sourceTest.test (x - t) :=
  rfl

/-- The prime-power evaluation before taking its real scalar read-off. -/
noncomputable def primePowerValue
    (owner : SelectedWeilSquareOwner) (n : ℕ) : ℂ :=
  ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
    (owner.convolutionSquare.test (Real.log n) +
      owner.convolutionSquare.test (-Real.log n))

/-- The exact von Mangoldt weighted prime-power term. -/
noncomputable def finitePrimeTerm
    (owner : SelectedWeilSquareOwner) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * owner.primePowerValue n

/-- The route's real scalar is an explicit read-off from the complex term. -/
noncomputable def finitePrimeTermReal
    (owner : SelectedWeilSquareOwner) (n : ℕ) : ℝ :=
  (owner.finitePrimeTerm n).re

@[simp] theorem primePowerValue_eq
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    owner.primePowerValue n =
      ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        (owner.convolutionSquare.test (Real.log n) +
          owner.convolutionSquare.test (-Real.log n)) :=
  rfl

@[simp] theorem finitePrimeTerm_eq
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    owner.finitePrimeTerm n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * owner.primePowerValue n :=
  rfl

theorem convolutionSquare_neg
    (owner : SelectedWeilSquareOwner) (x : ℝ) :
    owner.convolutionSquare.test (-x) =
      star (owner.convolutionSquare.test x) :=
  owner.sourceTest.convolutionSquare_neg x

theorem convolutionSquare_zero_im
    (owner : SelectedWeilSquareOwner) :
    (owner.convolutionSquare.test 0).im = 0 :=
  owner.sourceTest.convolutionSquare_zero_im

theorem convolutionSquare_zero_re_nonnegative
    (owner : SelectedWeilSquareOwner) :
    0 ≤ (owner.convolutionSquare.test 0).re :=
  owner.sourceTest.convolutionSquare_zero_re_nonnegative

theorem convolutionSquare_add_neg_eq_two_re
    (owner : SelectedWeilSquareOwner) (x : ℝ) :
    owner.convolutionSquare.test x + owner.convolutionSquare.test (-x) =
      ((2 * (owner.convolutionSquare.test x).re : ℝ) : ℂ) :=
  owner.sourceTest.convolutionSquare_add_neg_eq_two_re x

theorem primePowerValue_im_eq_zero
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    (owner.primePowerValue n).im = 0 := by
  rw [primePowerValue, owner.convolutionSquare_add_neg_eq_two_re]
  simp

theorem finitePrimeTerm_im_eq_zero
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    (owner.finitePrimeTerm n).im = 0 := by
  rw [finitePrimeTerm, Complex.mul_im, owner.primePowerValue_im_eq_zero]
  simp

theorem finitePrimeTerm_eq_real
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    owner.finitePrimeTerm n = (owner.finitePrimeTermReal n : ℂ) := by
  apply Complex.ext
  · simp [finitePrimeTermReal]
  · simpa [finitePrimeTermReal] using owner.finitePrimeTerm_im_eq_zero n

theorem convolutionSquare_eq_zero_of_abs_gt
    (owner : SelectedWeilSquareOwner) (x : ℝ)
    (h : owner.supportRadius < |x|) :
    owner.convolutionSquare.test x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support owner.convolutionSquare.test := hne
  have hbounds := owner.convolutionSquare_support hmem
  have habs : |x| ≤ owner.supportRadius := abs_le.2 hbounds
  exact (not_lt_of_ge habs) h

theorem abs_log_le_supportRadius_of_finitePrimeTerm_ne_zero
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0) :
    |Real.log n| ≤ owner.supportRadius := by
  have hvalue : owner.primePowerValue n ≠ 0 := by
    intro hzero
    apply hterm
    rw [finitePrimeTerm, hzero, mul_zero]
  have hsum :
      owner.convolutionSquare.test (Real.log n) +
          owner.convolutionSquare.test (-Real.log n) ≠ 0 := by
    intro hzero
    apply hvalue
    rw [primePowerValue, hzero, mul_zero]
  have hpoint :
      owner.convolutionSquare.test (Real.log n) ≠ 0 ∨
        owner.convolutionSquare.test (-Real.log n) ≠ 0 := by
    by_cases hleft : owner.convolutionSquare.test (Real.log n) ≠ 0
    · exact Or.inl hleft
    by_cases hright : owner.convolutionSquare.test (-Real.log n) ≠ 0
    · exact Or.inr hright
    exfalso
    apply hsum
    rw [not_ne_iff.mp hleft, not_ne_iff.mp hright]
    simp
  rcases hpoint with hpoint | hpoint
  · exact abs_le.2 (owner.convolutionSquare_support hpoint)
  · have hbounds := owner.convolutionSquare_support hpoint
    simpa only [abs_neg] using (abs_le.2 hbounds)

/-- A computable natural bound containing every visible selected prime power. -/
noncomputable def globalIndexBound
    (owner : SelectedWeilSquareOwner) : ℕ :=
  Nat.ceil (Real.exp owner.supportRadius) + 1

theorem index_lt_globalIndexBound
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hprime : IsPrimePow n) (hterm : owner.finitePrimeTerm n ≠ 0) :
    n < owner.globalIndexBound := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt (IsPrimePow.one_lt hprime))
  have hlogle : Real.log n ≤ owner.supportRadius :=
    (le_abs_self (Real.log n)).trans
      (owner.abs_log_le_supportRadius_of_finitePrimeTerm_ne_zero hterm)
  have hnexp : (n : ℝ) ≤ Real.exp owner.supportRadius := by
    have h := Real.exp_le_exp.mpr hlogle
    simpa [Real.exp_log hnpos] using h
  have hexpceil :
      Real.exp owner.supportRadius ≤ (Nat.ceil (Real.exp owner.supportRadius) : ℝ) :=
    Nat.le_ceil (Real.exp owner.supportRadius)
  have hnceil : n ≤ Nat.ceil (Real.exp owner.supportRadius) := by
    exact_mod_cast hnexp.trans hexpceil
  exact Nat.lt_succ_iff.2 hnceil

end SelectedWeilSquareOwner

/-- Exact finite support for the selected square, not for every test at once. -/
structure SelectedFinitePrimeSupportData
    (owner : SelectedWeilSquareOwner) where
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  globalExact :
    ∀ n : ℕ,
      n ∈ globalPrimeIndexSet ↔
        IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0
  restrictedExact :
    ∀ lambda : ℝ, ∀ n : ℕ,
      n ∈ restrictedPrimeIndexSet lambda ↔
        IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0 ∧
          1 < n ∧ (n : ℝ) ≤ lambda ^ 2

namespace SelectedFinitePrimeSupportData

noncomputable def computedGlobalPrimeIndexSet
    (owner : SelectedWeilSquareOwner) : Finset ℕ :=
  (Finset.range owner.globalIndexBound).filter fun n =>
    IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0

noncomputable def computedRestrictedPrimeIndexSet
    (owner : SelectedWeilSquareOwner) (lambda : ℝ) : Finset ℕ :=
  (computedGlobalPrimeIndexSet owner).filter fun n =>
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2

/-- Compact support constructs both exact finite index sets. -/
noncomputable def ofOwner
    (owner : SelectedWeilSquareOwner) :
    SelectedFinitePrimeSupportData owner where
  globalPrimeIndexSet := computedGlobalPrimeIndexSet owner
  restrictedPrimeIndexSet := computedRestrictedPrimeIndexSet owner
  globalExact := by
    intro n
    simp only [computedGlobalPrimeIndexSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_hbound, hprime, hterm⟩
      exact ⟨hprime, hterm⟩
    · rintro ⟨hprime, hterm⟩
      exact ⟨owner.index_lt_globalIndexBound hprime hterm, hprime, hterm⟩
  restrictedExact := by
    intro lambda n
    simp only [computedRestrictedPrimeIndexSet, Finset.mem_filter]
    rw [show n ∈ computedGlobalPrimeIndexSet owner ↔
        IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0 by
      simp only [computedGlobalPrimeIndexSet, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_hbound, hprime, hterm⟩
        exact ⟨hprime, hterm⟩
      · rintro ⟨hprime, hterm⟩
        exact ⟨owner.index_lt_globalIndexBound hprime hterm, hprime, hterm⟩]
    tauto

end SelectedFinitePrimeSupportData

end SelectedWeilSquare
end CCM25Concrete
end Source
end ConnesWeilRH
