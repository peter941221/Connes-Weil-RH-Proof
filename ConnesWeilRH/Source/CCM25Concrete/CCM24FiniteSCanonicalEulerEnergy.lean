/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalFamily
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSWeightedTranslationBessel
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Canonical finite-S Euler square energy

The synchronized generator square ledger is summed only over the visible
prime set canonically selected by the same compact Weil square.  The resulting
energy is bounded by a quadratic polynomial in the logarithm of the selected
integer cutoff.  This is the diagonal Euler-energy input from Proof 416; it is
not an estimate for the completed Burnol boundary response.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalEulerEnergy

open scoped BigOperators

open SelectedWeilSquare
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM24FiniteSWeightedTranslationBessel

/-- The complete one-prime synchronized square-energy majorant. -/
noncomputable def visiblePrimeEulerSquareEnergyTerm
    (p : CCM24VisiblePrime) : ℝ :=
  Real.log p / ((p : ℝ) - 1)

/-- The deduplicated square-energy budget of a finite visible-prime set. -/
noncomputable def visiblePrimeEulerSquareEnergy
    (S : Finset CCM24VisiblePrime) : ℝ :=
  ∑ p ∈ S, visiblePrimeEulerSquareEnergyTerm p

/-- The square-energy budget selected by one compact Weil square. -/
noncomputable def canonicalEulerSquareEnergy
    (owner : SelectedWeilSquareOwner) : ℝ :=
  ((ofSelectedOwner owner).visiblePrimes.map
    visiblePrimeEulerSquareEnergyTerm).sum

theorem visiblePrimeEulerSquareEnergyTerm_nonneg
    (p : CCM24VisiblePrime) :
    0 ≤ visiblePrimeEulerSquareEnergyTerm p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  exact div_nonneg (Real.log_nonneg hp.le) (sub_nonneg.mpr hp.le)

theorem visiblePrimeEulerSquareEnergy_nonneg
    (S : Finset CCM24VisiblePrime) :
    0 ≤ visiblePrimeEulerSquareEnergy S := by
  exact Finset.sum_nonneg fun p _ => visiblePrimeEulerSquareEnergyTerm_nonneg p

theorem canonicalEulerSquareEnergy_nonneg
    (owner : SelectedWeilSquareOwner) :
    0 ≤ canonicalEulerSquareEnergy owner := by
  unfold canonicalEulerSquareEnergy
  generalize (ofSelectedOwner owner).visiblePrimes = items
  induction items with
  | nil => simp
  | cons p items ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (visiblePrimeEulerSquareEnergyTerm_nonneg p) ih

private theorem nodup_list_sum_eq_toFinset_sum
    {α : Type*} [DecidableEq α] (f : α → ℝ) :
    ∀ {items : List α}, items.Nodup →
      (items.map f).sum = ∑ item ∈ items.toFinset, f item
  | [], _ => by simp
  | item :: items, hnodup => by
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert]
      · simpa using nodup_list_sum_eq_toFinset_sum f hnodup.tail
      · simpa using hnodup.notMem

private theorem inverse_sub_one_le_two_mul_inverse
    (p : CCM24VisiblePrime) :
    (((p : ℝ) - 1)⁻¹) ≤ 2 * (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp
  field_simp [hp0.ne', hpm1.ne']
  nlinarith

private theorem visiblePrimeEulerSquareEnergyTerm_le
    (p : CCM24VisiblePrime) (N : ℕ) (hpN : p.1 ≤ N) :
    visiblePrimeEulerSquareEnergyTerm p ≤
      2 * Real.log (N : ℝ) * (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (Nat.zero_lt_of_lt (p.property.trans_le hpN))
  have hpNreal : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
  have hlog : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (zero_lt_one.trans hp) hpNreal
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.le.trans hpN)
  unfold visiblePrimeEulerSquareEnergyTerm
  rw [div_eq_mul_inv]
  calc
    Real.log (p : ℝ) * (((p : ℝ) - 1)⁻¹) ≤
        Real.log (N : ℝ) * (((p : ℝ) - 1)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hlog (by positivity)
    _ ≤ Real.log (N : ℝ) * (2 * (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (inverse_sub_one_le_two_mul_inverse p) hlogN
    _ = 2 * Real.log (N : ℝ) * (p : ℝ)⁻¹ := by ring

private theorem visiblePrimeInverseSum_le_harmonic
    (S : Finset CCM24VisiblePrime) (N : ℕ)
    (hcutoff : ∀ p ∈ S, p.1 ≤ N) :
    (∑ p ∈ S, (p : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
  let bases : Finset ℕ := S.image fun p => p.1
  have hbases : bases ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.zero_lt_of_lt p.property)),
      hcutoff p hpS⟩
  have hsumImage :
      (∑ p ∈ S, (p : ℝ)⁻¹) = ∑ n ∈ bases, (n : ℝ)⁻¹ := by
    unfold bases
    rw [Finset.sum_image Subtype.coe_injective.injOn]
  rw [hsumImage]
  calc
    (∑ n ∈ bases, (n : ℝ)⁻¹) ≤
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hbases
        (fun _ _ _ => by positivity)
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- A deduplicated visible-prime family below `N` has Euler square energy at
most a quadratic polynomial in `log N`. -/
theorem visiblePrimeEulerSquareEnergy_le_logCutoff
    (S : Finset CCM24VisiblePrime) (N : ℕ)
    (hcutoff : ∀ p ∈ S, p.1 ≤ N) :
    visiblePrimeEulerSquareEnergy S ≤
      2 * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  by_cases hS : S.Nonempty
  · obtain ⟨p0, hp0⟩ := hS
    have hN : (1 : ℕ) ≤ N := p0.property.le.trans (hcutoff p0 hp0)
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    calc
      visiblePrimeEulerSquareEnergy S ≤
          ∑ p ∈ S, 2 * Real.log (N : ℝ) * (p : ℝ)⁻¹ := by
        exact Finset.sum_le_sum fun p hp =>
          visiblePrimeEulerSquareEnergyTerm_le p N (hcutoff p hp)
      _ = 2 * Real.log (N : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * Real.log (N : ℝ) * (harmonic N : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (visiblePrimeInverseSum_le_harmonic S N hcutoff)
          (mul_nonneg (by positivity) hlogN)
      _ ≤ 2 * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N)
          (mul_nonneg (by positivity) hlogN)
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst S
    cases N with
    | zero => norm_num [visiblePrimeEulerSquareEnergy]
    | succ N =>
        have hlog : 0 ≤ Real.log ((Nat.succ N : ℕ) : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
        simp only [visiblePrimeEulerSquareEnergy, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg (by norm_num) hlog) (by linarith)

/-- The selected exact-support family has a family-free square-energy bound
depending only on the selected owner's global integer cutoff. -/
theorem canonicalEulerSquareEnergy_le_logGlobalIndexBound
    (owner : SelectedWeilSquareOwner) :
    canonicalEulerSquareEnergy owner ≤
      2 * Real.log (owner.globalIndexBound : ℝ) *
        (1 + Real.log (owner.globalIndexBound : ℝ)) := by
  rw [canonicalEulerSquareEnergy,
    nodup_list_sum_eq_toFinset_sum visiblePrimeEulerSquareEnergyTerm
      (ofSelectedOwner owner).visiblePrimes_nodup]
  apply visiblePrimeEulerSquareEnergy_le_logCutoff
  intro p hp
  have hpList : p ∈ (ofSelectedOwner owner).visiblePrimes := by
    simpa using hp
  exact Nat.le_of_lt
    (visiblePrime_lt_globalIndexBound_ofSelectedOwner owner hpList)

/-- The logarithm of the selected integer cutoff differs from the source
support radius by at most the fixed constant `log 3`. -/
theorem log_globalIndexBound_le_supportRadius_add_log_three
    (owner : SelectedWeilSquareOwner) :
    Real.log (owner.globalIndexBound : ℝ) ≤
      owner.supportRadius + Real.log 3 := by
  have hexpOne : (1 : ℝ) ≤ Real.exp owner.supportRadius :=
    Real.one_le_exp owner.supportRadius_nonnegative
  have hceil :
      (Nat.ceil (Real.exp owner.supportRadius) : ℝ) <
        Real.exp owner.supportRadius + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos owner.supportRadius).le
  have hbound :
      (owner.globalIndexBound : ℝ) <
        3 * Real.exp owner.supportRadius := by
    rw [SelectedWeilSquareOwner.globalIndexBound, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpositive : (0 : ℝ) < owner.globalIndexBound := by
    exact_mod_cast Nat.succ_pos (Nat.ceil (Real.exp owner.supportRadius))
  calc
    Real.log (owner.globalIndexBound : ℝ) ≤
        Real.log (3 * Real.exp owner.supportRadius) :=
      Real.log_le_log hpositive hbound.le
    _ = owner.supportRadius + Real.log 3 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (Real.exp_ne_zero owner.supportRadius), Real.log_exp]
      ring

/-- The canonical synchronized Euler square budget has polynomial cost in
the compact source support radius. -/
theorem canonicalEulerSquareEnergy_le_supportRadiusPolynomial
    (owner : SelectedWeilSquareOwner) :
    canonicalEulerSquareEnergy owner ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  have hbase := canonicalEulerSquareEnergy_le_logGlobalIndexBound owner
  have hlog := log_globalIndexBound_le_supportRadius_add_log_three owner
  have hcutoffNonneg :
      0 ≤ Real.log (owner.globalIndexBound : ℝ) := by
    apply Real.log_nonneg
    rw [SelectedWeilSquareOwner.globalIndexBound]
    exact_mod_cast Nat.succ_le_succ
      (Nat.zero_le (Nat.ceil (Real.exp owner.supportRadius)))
  have hsupportNonneg :
      0 ≤ owner.supportRadius + Real.log 3 := by
    exact add_nonneg owner.supportRadius_nonnegative
      (Real.log_nonneg (by norm_num))
  calc
    canonicalEulerSquareEnergy owner ≤
        2 * Real.log (owner.globalIndexBound : ℝ) *
          (1 + Real.log (owner.globalIndexBound : ℝ)) := hbase
    _ ≤ 2 * (owner.supportRadius + Real.log 3) *
          (1 + Real.log (owner.globalIndexBound : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (by norm_num))
        (by linarith)
    _ ≤ 2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3) := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (by norm_num) hsupportNonneg)

/-! ## The actual synchronized mode budget -/

/-- The integrated square budget of the genuine synchronized prime-power
mode family attached to one selected Weil square.  This is the analytic mode
ledger, while `canonicalEulerSquareEnergy` is its geometric majorant. -/
noncomputable def canonicalSynchronizedEulerModeEnergy
    (owner : SelectedWeilSquareOwner) : ℝ :=
  ((ofSelectedOwner owner).visiblePrimes.map (fun p =>
    ∑' n : ℕ,
      ∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n)).sum

/-- The actual synchronized mode budget is bounded by the canonical Euler
square energy for the same selected owner. -/
theorem canonicalSynchronizedEulerModeEnergy_le_canonicalEulerSquareEnergy
    (owner : SelectedWeilSquareOwner) :
    canonicalSynchronizedEulerModeEnergy owner ≤
      canonicalEulerSquareEnergy owner := by
  simpa [canonicalSynchronizedEulerModeEnergy, canonicalEulerSquareEnergy,
    visiblePrimeEulerSquareEnergyTerm] using
    (sum_tsum_integral_parameterizedPrimeEulerModeBoundaryEnergy_le
      (ofSelectedOwner owner).visiblePrimes)

/-- The genuine synchronized mode budget therefore has the same support-only
polynomial bound as its canonical majorant. -/
theorem canonicalSynchronizedEulerModeEnergy_le_supportRadiusPolynomial
    (owner : SelectedWeilSquareOwner) :
    canonicalSynchronizedEulerModeEnergy owner ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  calc
    canonicalSynchronizedEulerModeEnergy owner ≤
        canonicalEulerSquareEnergy owner :=
      canonicalSynchronizedEulerModeEnergy_le_canonicalEulerSquareEnergy owner
    _ ≤ 2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3) :=
      canonicalEulerSquareEnergy_le_supportRadiusPolynomial owner

end CCM24FiniteSCanonicalEulerEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
