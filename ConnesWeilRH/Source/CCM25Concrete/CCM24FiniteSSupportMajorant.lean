/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRenewal

/-!
# Compact-support majorant for the two-sided Euler renewal

After the two lower factors are divided out, compact displacement support
still forces every prime with `log p > B` to take the zero forward/inverse
coordinate.  The remaining total variation therefore depends only on visible
places below the fixed support threshold.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSupportMajorant

open CC20Concrete
open CCM24FiniteSTwoSidedRenewal

theorem primeTwoSidedIndex_eq_zero_of_displacement_le_of_lt_log
    (B : ℝ) (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex)
    (hdisp : primeTwoSidedDisplacement p index ≤ B)
    (hlarge : B < Real.log p) :
    index = (false, 0) := by
  have hlog : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast p.property)
  have hexponent : forwardEulerExponent index.1 + index.2 = 0 := by
    by_contra hne
    have hone : 1 ≤ forwardEulerExponent index.1 + index.2 :=
      Nat.one_le_iff_ne_zero.mpr hne
    have hcast : (1 : ℝ) ≤
        (forwardEulerExponent index.1 + index.2 : ℕ) := by
      exact_mod_cast hone
    have hlogle : Real.log p ≤ primeTwoSidedDisplacement p index := by
      rw [primeTwoSidedDisplacement]
      nlinarith
    exact (not_lt_of_ge (hlogle.trans hdisp)) hlarge
  have hparts := Nat.add_eq_zero_iff.mp hexponent
  have hchoice : index.1 = false := by
    cases h : index.1 <;>
      simp [forwardEulerExponent, h] at hparts ⊢
  exact Prod.ext hchoice hparts.2

/-- Raw total-variation factor at one prime. -/
noncomputable def primeTwoSidedRawMass (p : CCM24VisiblePrime) : ℝ :=
  (1 + ccm24PrimeEulerCoefficient p) /
    (1 - ccm24PrimeEulerCoefficient p)

theorem primeTwoSidedRawWeight_hasSum
    (p : CCM24VisiblePrime) :
    HasSum (primeTwoSidedRawWeight p) (primeTwoSidedRawMass p) := by
  simpa [primeTwoSidedRawMass, tsum_primeTwoSidedRawWeight p] using
    (summable_primeTwoSidedRawWeight p).hasSum

theorem finiteEulerTwoSidedRawWeight_nonneg
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedRawWeight S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedRawWeight]
  | cons p S ih =>
      exact mul_nonneg (primeTwoSidedRawWeight_nonneg p index.1)
        (ih index.2)

/-- Exact raw total variation for a finite visible-prime list. -/
theorem finiteEulerTwoSidedRawWeight_hasSum
    (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerTwoSidedRawWeight S)
      ((S.map primeTwoSidedRawMass).prod) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedRawWeight]
  | cons p S ih =>
      have hp := primeTwoSidedRawWeight_hasSum p
      have hprod : Summable (fun index :
          PrimeTwoSidedRenewalIndex × FiniteEulerTwoSidedRenewalIndex S =>
            primeTwoSidedRawWeight p index.1 *
              finiteEulerTwoSidedRawWeight S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro index
            exact ih.summable.mul_left (primeTwoSidedRawWeight p index)
          · exact ((summable_primeTwoSidedRawWeight p).mul_right
                ((S.map primeTwoSidedRawMass).prod)).congr
              (fun index => by
                have h := ih.summable.tsum_mul_left
                  (primeTwoSidedRawWeight p index)
                rw [ih.tsum_eq] at h
                simpa using h.symm)
        · intro index
          exact mul_nonneg
            (primeTwoSidedRawWeight_nonneg p index.1)
            (finiteEulerTwoSidedRawWeight_nonneg S index.2)
      simpa [finiteEulerTwoSidedRawWeight] using hp.mul ih hprod

/-- One-prime support majorant: small primes retain their raw mass, while a
large prime retains only the zero coordinate. -/
noncomputable def primeTwoSidedSupportMajorant
    (B : ℝ) (p : CCM24VisiblePrime)
    (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  if Real.log p ≤ B then
    primeTwoSidedRawWeight p index
  else if index = (false, 0) then 1 else 0

noncomputable def primeTwoSidedSupportMass
    (B : ℝ) (p : CCM24VisiblePrime) : ℝ :=
  if Real.log p ≤ B then primeTwoSidedRawMass p else 1

theorem primeTwoSidedSupportMajorant_hasSum
    (B : ℝ) (p : CCM24VisiblePrime) :
    HasSum (primeTwoSidedSupportMajorant B p)
      (primeTwoSidedSupportMass B p) := by
  classical
  change HasSum
    (fun index : PrimeTwoSidedRenewalIndex =>
      if Real.log p ≤ B then primeTwoSidedRawWeight p index
      else if index = (false, 0) then 1 else 0)
    (if Real.log p ≤ B then primeTwoSidedRawMass p else 1)
  by_cases hsmall : Real.log p ≤ B
  · have hfun :
        (fun index : PrimeTwoSidedRenewalIndex =>
          if Real.log p ≤ B then primeTwoSidedRawWeight p index
          else if index = (false, 0) then 1 else 0) =
        primeTwoSidedRawWeight p := by
      funext index
      rw [if_pos hsmall]
    rw [hfun, if_pos hsmall]
    exact primeTwoSidedRawWeight_hasSum p
  · have hfun :
        (fun index : PrimeTwoSidedRenewalIndex =>
          if Real.log p ≤ B then primeTwoSidedRawWeight p index
          else if index = (false, 0) then 1 else 0) =
        (fun index => if index = (false, 0) then 1 else 0) := by
      funext index
      rw [if_neg hsmall]
    rw [hfun, if_neg hsmall]
    exact hasSum_ite_eq (false, 0) (1 : ℝ)

/-- Product support majorant on the complete two-sided index. -/
noncomputable def finiteEulerTwoSidedSupportMajorant :
    (B : ℝ) → (S : List CCM24VisiblePrime) →
      FiniteEulerTwoSidedRenewalIndex S → ℝ
  | _, [], _ => 1
  | B, p :: S, index =>
      primeTwoSidedSupportMajorant B p index.1 *
        finiteEulerTwoSidedSupportMajorant B S index.2

noncomputable def finiteEulerTwoSidedSupportMass
    (B : ℝ) (S : List CCM24VisiblePrime) : ℝ :=
  (S.map (primeTwoSidedSupportMass B)).prod

theorem finiteEulerTwoSidedSupportMajorant_nonneg
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedSupportMajorant B S index := by
  classical
  induction S with
  | nil => simp [finiteEulerTwoSidedSupportMajorant]
  | cons p S ih =>
      apply mul_nonneg
      · unfold primeTwoSidedSupportMajorant
        split_ifs
        · exact primeTwoSidedRawWeight_nonneg p index.1
        · exact zero_le_one
        · exact le_rfl
      · exact ih index.2

theorem finiteEulerTwoSidedSupportMajorant_hasSum
    (B : ℝ) (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerTwoSidedSupportMajorant B S)
      (finiteEulerTwoSidedSupportMass B S) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedSupportMajorant,
        finiteEulerTwoSidedSupportMass]
  | cons p S ih =>
      have hp := primeTwoSidedSupportMajorant_hasSum B p
      have hprod : Summable (fun index :
          PrimeTwoSidedRenewalIndex × FiniteEulerTwoSidedRenewalIndex S =>
            primeTwoSidedSupportMajorant B p index.1 *
              finiteEulerTwoSidedSupportMajorant B S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro index
            exact ih.summable.mul_left
              (primeTwoSidedSupportMajorant B p index)
          · exact (hp.summable.mul_right
                (finiteEulerTwoSidedSupportMass B S)).congr
              (fun index => by
                have h := ih.summable.tsum_mul_left
                  (primeTwoSidedSupportMajorant B p index)
                rw [ih.tsum_eq] at h
                simpa using h.symm)
        · intro index
          exact mul_nonneg
            (by
              unfold primeTwoSidedSupportMajorant
              split_ifs
              · exact primeTwoSidedRawWeight_nonneg p index.1
              · exact zero_le_one
              · exact le_rfl)
            (finiteEulerTwoSidedSupportMajorant_nonneg B S index.2)
      simpa [finiteEulerTwoSidedSupportMajorant,
        finiteEulerTwoSidedSupportMass] using hp.mul ih hprod

/-- On the compact displacement region, the raw coefficient equals the
support majorant exactly. -/
theorem finiteEulerTwoSidedRawWeight_eq_supportMajorant_of_displacement_le
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S)
    (hdisp : finiteEulerTwoSidedDisplacement S index ≤ B) :
    finiteEulerTwoSidedRawWeight S index =
      finiteEulerTwoSidedSupportMajorant B S index := by
  classical
  induction S with
  | nil => simp [finiteEulerTwoSidedRawWeight,
      finiteEulerTwoSidedSupportMajorant]
  | cons p S ih =>
      have hhead : primeTwoSidedDisplacement p index.1 ≤ B := by
        exact (le_add_of_nonneg_right
          (finiteEulerTwoSidedDisplacement_nonneg S index.2)).trans hdisp
      have htail : finiteEulerTwoSidedDisplacement S index.2 ≤ B := by
        exact (le_add_of_nonneg_left
          (primeTwoSidedDisplacement_nonneg p index.1)).trans hdisp
      have ihtail := ih index.2 htail
      by_cases hsmall : Real.log p ≤ B
      · simp [finiteEulerTwoSidedRawWeight,
          finiteEulerTwoSidedSupportMajorant,
          primeTwoSidedSupportMajorant, hsmall, ihtail]
      · have hzero :=
          primeTwoSidedIndex_eq_zero_of_displacement_le_of_lt_log
            B p index.1 hhead (lt_of_not_ge hsmall)
        simp [finiteEulerTwoSidedRawWeight,
          finiteEulerTwoSidedSupportMajorant,
          primeTwoSidedSupportMajorant, hsmall, hzero, ihtail,
          primeTwoSidedRawWeight, forwardEulerExponent]

/-- Raw coefficient restricted to the compact displacement window. -/
noncomputable def finiteEulerTwoSidedCompactRawWeight
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) : ℝ :=
  if finiteEulerTwoSidedDisplacement S index ≤ B then
    finiteEulerTwoSidedRawWeight S index else 0

/-- The compactly supported raw total variation is bounded by a product over
only the visible primes below the fixed support threshold. -/
theorem tsum_finiteEulerTwoSidedCompactRawWeight_le_supportMass
    (B : ℝ) (S : List CCM24VisiblePrime) :
    ∑' index : FiniteEulerTwoSidedRenewalIndex S,
        finiteEulerTwoSidedCompactRawWeight B S index ≤
      finiteEulerTwoSidedSupportMass B S := by
  classical
  have hmajorant := finiteEulerTwoSidedSupportMajorant_hasSum B S
  have hpoint : ∀ index : FiniteEulerTwoSidedRenewalIndex S,
      finiteEulerTwoSidedCompactRawWeight B S index ≤
        finiteEulerTwoSidedSupportMajorant B S index := by
    intro index
    unfold finiteEulerTwoSidedCompactRawWeight
    split_ifs with hdisp
    · exact le_of_eq
        (finiteEulerTwoSidedRawWeight_eq_supportMajorant_of_displacement_le
          B S index hdisp)
    · exact finiteEulerTwoSidedSupportMajorant_nonneg B S index
  have hcompact : Summable
      (finiteEulerTwoSidedCompactRawWeight B S) :=
    Summable.of_nonneg_of_le
      (fun index => by
        unfold finiteEulerTwoSidedCompactRawWeight
        split_ifs
        · exact finiteEulerTwoSidedRawWeight_nonneg S index
        · exact le_rfl)
      hpoint hmajorant.summable
  calc
    _ ≤ ∑' index : FiniteEulerTwoSidedRenewalIndex S,
        finiteEulerTwoSidedSupportMajorant B S index :=
      hcompact.tsum_le_tsum hpoint hmajorant.summable
    _ = finiteEulerTwoSidedSupportMass B S := hmajorant.tsum_eq

/-- A coarse universal bound for one raw prime factor.  The constant `7` is
chosen only for a clean proof from `p ≥ 2`; no prime-number estimate is used. -/
theorem primeTwoSidedRawMass_le_seven (p : CCM24VisiblePrime) :
    primeTwoSidedRawMass p ≤ 7 := by
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.succ_le_iff.mpr p.property)
  have hsquared : (4 / 3 : ℝ) ^ 2 < (p : ℝ) := by
    norm_num
    linarith
  have hsqrt : (4 / 3 : ℝ) < Real.sqrt p :=
    (Real.lt_sqrt (by norm_num)).2 hsquared
  have hsqrtpos : 0 < Real.sqrt p := by nlinarith
  have hcoefficient : ccm24PrimeEulerCoefficient p < 3 / 4 := by
    rw [ccm24PrimeEulerCoefficient]
    apply (div_lt_iff₀ hsqrtpos).2
    nlinarith
  unfold primeTwoSidedRawMass
  apply (div_le_iff₀ (sub_pos.mpr (ccm24PrimeEulerCoefficient_lt_one p))).2
  nlinarith

theorem finiteEulerTwoSidedSupportMass_eq_filtered_prod
    (B : ℝ) (S : List CCM24VisiblePrime) :
    finiteEulerTwoSidedSupportMass B S =
      (((S.filter fun p : CCM24VisiblePrime => Real.log (p : ℝ) ≤ B).map
        primeTwoSidedRawMass).prod) := by
  classical
  induction S with
  | nil => simp [finiteEulerTwoSidedSupportMass]
  | cons p S ih =>
      change primeTwoSidedSupportMass B p *
          finiteEulerTwoSidedSupportMass B S =
        (((List.filter
          (fun q : CCM24VisiblePrime => Real.log (q : ℝ) ≤ B)
          (p :: S)).map primeTwoSidedRawMass).prod)
      rw [ih]
      by_cases hsmall : Real.log p ≤ B
      · simp [primeTwoSidedSupportMass, hsmall]
      · simp [primeTwoSidedSupportMass, hsmall]

/-- A no-analytic-number-theory cardinality bound: a noduplicated list of
visible places with `log p ≤ B` has at most `ceil(exp B)+1` entries. -/
theorem length_filter_log_le
    (B : ℝ) (S : List CCM24VisiblePrime) (hS : S.Nodup) :
    (S.filter fun p : CCM24VisiblePrime => Real.log (p : ℝ) ≤ B).length ≤
      Nat.ceil (Real.exp B) + 1 := by
  classical
  let small := S.filter fun p : CCM24VisiblePrime => Real.log (p : ℝ) ≤ B
  let values : Finset ℕ :=
    small.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩
  have hsubset : values ⊆ Finset.range (Nat.ceil (Real.exp B) + 1) := by
    intro n hn
    rw [Finset.mem_map] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have hpmem : p ∈ small := by
      simpa [small] using hp
    have hlog : Real.log p ≤ B := by
      exact of_decide_eq_true (List.mem_filter.mp hpmem).2
    have hexp : (p : ℝ) ≤ Real.exp B := by
      calc
        (p : ℝ) = Real.exp (Real.log p) := by
          rw [Real.exp_log (by exact_mod_cast (Nat.zero_lt_of_lt p.property))]
        _ ≤ Real.exp B := Real.exp_le_exp.mpr hlog
    have hceil : p.1 ≤ Nat.ceil (Real.exp B) := by
      exact_mod_cast hexp.trans (Nat.le_ceil (Real.exp B))
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hceil)
  have hcard := Finset.card_le_card hsubset
  have hsmallNodup : small.Nodup := by
    exact hS.filter _
  have hcard' : small.length ≤ Nat.ceil (Real.exp B) + 1 := by
    calc
      small.length = small.toFinset.card :=
        (List.toFinset_card_of_nodup hsmallNodup).symm
      _ = values.card := by simp [values]
      _ ≤ Nat.ceil (Real.exp B) + 1 := by
        simpa using hcard
  simpa [small] using hcard'

/-- Explicit support-only bound, uniform in every noduplicated visible finite
set. -/
theorem finiteEulerTwoSidedSupportMass_le_universal
    (B : ℝ) (S : List CCM24VisiblePrime) (hS : S.Nodup) :
    finiteEulerTwoSidedSupportMass B S ≤
      (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) := by
  rw [finiteEulerTwoSidedSupportMass_eq_filtered_prod]
  calc
    _ ≤ (7 : ℝ) ^
        (S.filter fun p : CCM24VisiblePrime => Real.log (p : ℝ) ≤ B).length := by
      let small := S.filter fun p : CCM24VisiblePrime =>
        Real.log (p : ℝ) ≤ B
      change (small.map primeTwoSidedRawMass).prod ≤
        (7 : ℝ) ^ small.length
      induction small with
      | nil => simp
      | cons p small ih =>
          have htailnonneg : 0 ≤
              (small.map primeTwoSidedRawMass).prod := by
            apply List.prod_nonneg
            intro x hx
            rcases List.mem_map.mp hx with ⟨q, _hq, rfl⟩
            unfold primeTwoSidedRawMass
            exact div_nonneg
              (add_nonneg zero_le_one
                (ccm24PrimeEulerCoefficient_nonneg q))
              (sub_nonneg.mpr
                (le_of_lt (ccm24PrimeEulerCoefficient_lt_one q)))
          simp only [List.map_cons, List.prod_cons, List.length_cons]
          calc
            primeTwoSidedRawMass p *
                (small.map primeTwoSidedRawMass).prod ≤
              7 * (7 : ℝ) ^ small.length :=
                mul_le_mul (primeTwoSidedRawMass_le_seven p) ih
                  htailnonneg (by norm_num)
            _ = (7 : ℝ) ^ (small.length + 1) := by
              rw [pow_succ]
              ring
    _ ≤ (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) := by
      exact pow_le_pow_right₀ (by norm_num)
        (length_filter_log_le B S hS)

/-- The compact two-sided raw total variation now has a constant independent
of the visible finite set. -/
theorem tsum_finiteEulerTwoSidedCompactRawWeight_le_universal
    (B : ℝ) (S : List CCM24VisiblePrime) (hS : S.Nodup) :
    ∑' index : FiniteEulerTwoSidedRenewalIndex S,
        finiteEulerTwoSidedCompactRawWeight B S index ≤
      (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) :=
  (tsum_finiteEulerTwoSidedCompactRawWeight_le_supportMass B S).trans
    (finiteEulerTwoSidedSupportMass_le_universal B S hS)

/-- Specialization to the actual deduplicated visible-prime family. -/
theorem family_compactRawWeight_le_universal
    (B : ℝ) (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    ∑' index : FiniteEulerTwoSidedRenewalIndex family.visiblePrimes,
        finiteEulerTwoSidedCompactRawWeight B family.visiblePrimes index ≤
      (7 : ℝ) ^ (Nat.ceil (Real.exp B) + 1) :=
  tsum_finiteEulerTwoSidedCompactRawWeight_le_universal B
    family.visiblePrimes family.visiblePrimes_nodup

end CCM24FiniteSSupportMajorant
end CCM25Concrete
end Source
end ConnesWeilRH
