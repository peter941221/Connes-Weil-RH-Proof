/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCausalCoframe

/-!
# Two-sided finite Euler renewal law

The forward normalized Euler polynomial contributes a Boolean choice at each
visible prime, while the normalized inverse contributes a geometric count.
The combined displacement is always causal.  Its absolute normalized mass is
`prod_p (1-p⁻¹)`, hence at most one.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTwoSidedRenewal

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalMarkov

/-- The exponent contributed by one forward Euler choice. -/
def forwardEulerExponent (choice : Bool) : ℕ :=
  if choice then 1 else 0

/-- One forward/inverse coordinate at a visible prime. -/
abbrev PrimeTwoSidedRenewalIndex := Bool × ℕ

/-- Absolute coefficient before the two lower factors are inserted. -/
noncomputable def primeTwoSidedRawWeight
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  ccm24PrimeEulerCoefficient p ^
    (forwardEulerExponent index.1 + index.2)

/-- Absolute coefficient after both lower factors are inserted. -/
noncomputable def primeTwoSidedNormalizedWeight
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  (1 - ccm24PrimeEulerCoefficient p) ^ 2 *
    primeTwoSidedRawWeight p index

/-- Causal displacement of one forward/inverse coordinate. -/
noncomputable def primeTwoSidedDisplacement
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  ((forwardEulerExponent index.1 + index.2 : ℕ) : ℝ) * Real.log p

theorem primeTwoSidedRawWeight_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedRawWeight p index :=
  pow_nonneg (ccm24PrimeEulerCoefficient_nonneg p) _

theorem primeTwoSidedNormalizedWeight_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedNormalizedWeight p index := by
  exact mul_nonneg (sq_nonneg _) (primeTwoSidedRawWeight_nonneg p index)

theorem primeTwoSidedDisplacement_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedDisplacement p index := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast p.property.le))

theorem summable_primeTwoSidedRawWeight (p : CCM24VisiblePrime) :
    Summable (primeTwoSidedRawWeight p) := by
  rw [summable_prod_of_nonneg]
  · constructor
    · intro choice
      unfold primeTwoSidedRawWeight
      simp only [pow_add]
      exact (summable_geometric_of_norm_lt_one
        (show ‖ccm24PrimeEulerCoefficient p‖ < 1 by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
          exact ccm24PrimeEulerCoefficient_lt_one p)).mul_left _
    · exact (hasSum_fintype _).summable
  · intro index
    exact primeTwoSidedRawWeight_nonneg p index

/-- The raw total variation at one prime is `(1+a_p)/(1-a_p)`. -/
theorem tsum_primeTwoSidedRawWeight (p : CCM24VisiblePrime) :
    ∑' index : PrimeTwoSidedRenewalIndex,
      primeTwoSidedRawWeight p index =
        (1 + ccm24PrimeEulerCoefficient p) /
          (1 - ccm24PrimeEulerCoefficient p) := by
  have hsum := summable_primeTwoSidedRawWeight p
  rw [Summable.tsum_prod hsum]
  simp only [primeTwoSidedRawWeight, pow_add]
  simp_rw [(summable_geometric_of_norm_lt_one
    (show ‖ccm24PrimeEulerCoefficient p‖ < 1 by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
      exact ccm24PrimeEulerCoefficient_lt_one p)).tsum_mul_left]
  rw [tsum_geometric_of_lt_one (ccm24PrimeEulerCoefficient_nonneg p)
    (ccm24PrimeEulerCoefficient_lt_one p)]
  simp [forwardEulerExponent]
  field_simp [ne_of_gt (primeEulerLowerFactor_pos p)]
  ring

theorem summable_primeTwoSidedNormalizedWeight
    (p : CCM24VisiblePrime) :
    Summable (primeTwoSidedNormalizedWeight p) := by
  exact (summable_primeTwoSidedRawWeight p).mul_left
    ((1 - ccm24PrimeEulerCoefficient p) ^ 2)

/-- The normalized total variation at one prime is `1-a_p²`. -/
theorem tsum_primeTwoSidedNormalizedWeight (p : CCM24VisiblePrime) :
    ∑' index : PrimeTwoSidedRenewalIndex,
      primeTwoSidedNormalizedWeight p index =
        1 - ccm24PrimeEulerCoefficient p ^ 2 := by
  simp only [primeTwoSidedNormalizedWeight]
  rw [(summable_primeTwoSidedRawWeight p).tsum_mul_left,
    tsum_primeTwoSidedRawWeight]
  field_simp [ne_of_gt (primeEulerLowerFactor_pos p)]
  ring

/-- The raw coefficient at a prime equals the exponentially decaying
displacement kernel `exp (-(1/2)·disp)`, pointwise on every index.  This is the
universal ``weight = exp(-D/2)'' law: it holds for every visible prime with the
same `-1/2` slope because `a_p = 1/sqrt(p) = exp (-(1/2) log p)`. -/
theorem primeTwoSidedRawWeight_eq_exp_negHalfDisplacement
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    primeTwoSidedRawWeight p index =
      Real.exp (-(primeTwoSidedDisplacement p index) / 2) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  have h0p : (0 : ℝ) ≤ p := by positivity
  have hlogs : Real.log (Real.sqrt p) = Real.log p / 2 :=
    Real.log_sqrt (x := p) h0p
  have hsqrt_exp : Real.sqrt p = Real.exp (Real.log p / 2) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < Real.sqrt p)]
    rw [hlogs]
  have hcoeff : ccm24PrimeEulerCoefficient p = Real.exp (-(Real.log p / 2)) := by
    rw [ccm24PrimeEulerCoefficient]
    -- 1/sqrt p = exp(-log p / 2) = 1 / exp(log p / 2)
    rw [Real.exp_neg]
    rw [one_div]
    rw [hsqrt_exp]
  let n : ℕ := if index.1 then index.2 + 1 else index.2
  have hn : (forwardEulerExponent index.1 + index.2 : ℕ) = n := by
    dsimp [n, forwardEulerExponent]
    split_ifs <;> omega
  unfold primeTwoSidedRawWeight primeTwoSidedDisplacement
  rw [hn]
  change ccm24PrimeEulerCoefficient p ^ n =
      Real.exp (-((n : ℝ) * Real.log p) / 2)
  rw [hcoeff]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- One two-sided coordinate for every visible-prime occurrence. -/
abbrev FiniteEulerTwoSidedRenewalIndex : List CCM24VisiblePrime → Type
  | [] => PUnit
  | _ :: S => PrimeTwoSidedRenewalIndex ×
      FiniteEulerTwoSidedRenewalIndex S

noncomputable def finiteEulerTwoSidedRawWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeTwoSidedRawWeight p index.1 *
        finiteEulerTwoSidedRawWeight S index.2

noncomputable def finiteEulerTwoSidedNormalizedWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeTwoSidedNormalizedWeight p index.1 *
        finiteEulerTwoSidedNormalizedWeight S index.2

noncomputable def finiteEulerTwoSidedDisplacement :
    (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 0
  | p :: S, index =>
      primeTwoSidedDisplacement p index.1 +
        finiteEulerTwoSidedDisplacement S index.2

/-- Universal exponential law for the joint two-sided raw weight: for any finite
visible-prime list, the raw weight at an index is exactly
`exp (-(1/2)·(joint displacement))`.  This is the multi-prime analogue of
`primeTwoSidedRawWeight_eq_exp_negHalfDisplacement`, and it is uniform in the
family: the `-1/2` slope does not depend on which primes occur. -/
theorem finiteEulerTwoSidedRawWeight_eq_exp_negHalfDisplacement
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    finiteEulerTwoSidedRawWeight S index =
      Real.exp (-(finiteEulerTwoSidedDisplacement S index) / 2) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedRawWeight, finiteEulerTwoSidedDisplacement]
  | cons p S ih =>
      simp only [finiteEulerTwoSidedRawWeight, finiteEulerTwoSidedDisplacement]
      rw [primeTwoSidedRawWeight_eq_exp_negHalfDisplacement p index.1]
      rw [ih index.2]
      -- exp(-a/2)·exp(-b/2) = exp(-(a+b)/2), from exp_add reversed
      rw [← Real.exp_add]
      congr 1
      ring

theorem finiteEulerTwoSidedNormalizedWeight_nonneg
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedNormalizedWeight S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedNormalizedWeight]
  | cons p S ih =>
      exact mul_nonneg (primeTwoSidedNormalizedWeight_nonneg p index.1)
        (ih index.2)

theorem finiteEulerTwoSidedDisplacement_nonneg
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedDisplacement S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedDisplacement]
  | cons p S ih =>
      exact add_nonneg (primeTwoSidedDisplacement_nonneg p index.1)
        (ih index.2)

/-- Exact total variation of the normalized two-sided law. -/
theorem finiteEulerTwoSidedNormalizedWeight_hasSum
    (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerTwoSidedNormalizedWeight S)
      ((S.map fun p => 1 - ccm24PrimeEulerCoefficient p ^ 2).prod) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedNormalizedWeight]
  | cons p S ih =>
      have hp : HasSum (primeTwoSidedNormalizedWeight p)
          (1 - ccm24PrimeEulerCoefficient p ^ 2) := by
        simpa [tsum_primeTwoSidedNormalizedWeight p] using
          (summable_primeTwoSidedNormalizedWeight p).hasSum
      have hprod : Summable (fun index :
          PrimeTwoSidedRenewalIndex × FiniteEulerTwoSidedRenewalIndex S =>
            primeTwoSidedNormalizedWeight p index.1 *
              finiteEulerTwoSidedNormalizedWeight S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro index
            exact ih.summable.mul_left
              (primeTwoSidedNormalizedWeight p index)
          · exact ((summable_primeTwoSidedNormalizedWeight p).mul_right
                ((S.map fun q =>
                  1 - ccm24PrimeEulerCoefficient q ^ 2).prod)).congr
              (fun index => by
                have h := ih.summable.tsum_mul_left
                  (primeTwoSidedNormalizedWeight p index)
                rw [ih.tsum_eq] at h
                simpa using h.symm)
        · intro index
          exact mul_nonneg
            (primeTwoSidedNormalizedWeight_nonneg p index.1)
            (finiteEulerTwoSidedNormalizedWeight_nonneg S index.2)
      simpa [finiteEulerTwoSidedNormalizedWeight] using hp.mul ih hprod

theorem summable_finiteEulerTwoSidedNormalizedWeight
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerTwoSidedNormalizedWeight S) :=
  (finiteEulerTwoSidedNormalizedWeight_hasSum S).summable

/-- The complete normalized two-sided total variation is at most one. -/
theorem tsum_finiteEulerTwoSidedNormalizedWeight_le_one
    (S : List CCM24VisiblePrime) :
    ∑' index : FiniteEulerTwoSidedRenewalIndex S,
      finiteEulerTwoSidedNormalizedWeight S index ≤ 1 := by
  rw [(finiteEulerTwoSidedNormalizedWeight_hasSum S).tsum_eq]
  induction S with
  | nil => simp
  | cons p S ih =>
      simp only [List.map_cons, List.prod_cons]
      have hp : 0 ≤ 1 - ccm24PrimeEulerCoefficient p ^ 2 := by
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient p),
          ccm24PrimeEulerCoefficient_nonneg p,
          ccm24PrimeEulerCoefficient_lt_one p]
      have hple : 1 - ccm24PrimeEulerCoefficient p ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient p)]
      have hprodnonneg : 0 ≤
          (S.map fun q => 1 - ccm24PrimeEulerCoefficient q ^ 2).prod := by
        apply List.prod_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨q, _hq, rfl⟩
        nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient q),
          ccm24PrimeEulerCoefficient_nonneg q,
          ccm24PrimeEulerCoefficient_lt_one q]
      calc
        _ ≤ 1 * (S.map fun q =>
              1 - ccm24PrimeEulerCoefficient q ^ 2).prod := by
          exact mul_le_mul_of_nonneg_right hple hprodnonneg
        _ ≤ 1 := by simpa using ih

/-- Half-power base at a prime: `ρ_p = exp (-(log p)/4) < 1`. -/
noncomputable def ccm24QuarterEulerCoefficient (p : CCM24VisiblePrime) : ℝ :=
  Real.exp (-Real.log p / 4)

theorem ccm24QuarterEulerCoefficient_nonneg
    (p : CCM24VisiblePrime) : 0 ≤ ccm24QuarterEulerCoefficient p :=
  Real.exp_nonneg _

theorem ccm24QuarterEulerCoefficient_pos
    (p : CCM24VisiblePrime) : 0 < ccm24QuarterEulerCoefficient p :=
  Real.exp_pos _

theorem ccm24QuarterEulerCoefficient_lt_one
    (p : CCM24VisiblePrime) : ccm24QuarterEulerCoefficient p < 1 := by
  rw [ccm24QuarterEulerCoefficient]
  exact Real.exp_lt_one_iff.mpr (by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.property
    have hlogp : 0 < Real.log p := Real.log_pos hp
    nlinarith)

/-- One half-power (raw) coordinate value at a visible prime: `ρ_p^(f+c)`. -/
noncomputable def primeTwoSidedQuarterWeight
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) : ℝ :=
  ccm24QuarterEulerCoefficient p ^ (forwardEulerExponent index.1 + index.2)

theorem primeTwoSidedQuarterWeight_nonneg
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    0 ≤ primeTwoSidedQuarterWeight p index :=
  pow_nonneg (ccm24QuarterEulerCoefficient_nonneg p) _

theorem summable_primeTwoSidedQuarterWeight (p : CCM24VisiblePrime) :
    Summable (primeTwoSidedQuarterWeight p) := by
  rw [summable_prod_of_nonneg]
  · constructor
    · intro choice
      unfold primeTwoSidedQuarterWeight
      simp only [pow_add]
      exact (summable_geometric_of_norm_lt_one
        (show ‖ccm24QuarterEulerCoefficient p‖ < 1 by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (ccm24QuarterEulerCoefficient_nonneg p)]
          exact ccm24QuarterEulerCoefficient_lt_one p)).mul_left _
    · exact (hasSum_fintype _).summable
  · intro index
    exact primeTwoSidedQuarterWeight_nonneg p index

/-- Per-prime half-power mass: `∑_n ρ_p^n·(2 branches) = (1+ρ_p)/(1-ρ_p)`. -/
noncomputable def primeTwoSidedQuarterMass (p : CCM24VisiblePrime) : ℝ :=
  (1 + ccm24QuarterEulerCoefficient p) /
    (1 - ccm24QuarterEulerCoefficient p)

theorem tsum_primeTwoSidedQuarterWeight (p : CCM24VisiblePrime) :
    ∑' index : PrimeTwoSidedRenewalIndex,
      primeTwoSidedQuarterWeight p index =
        primeTwoSidedQuarterMass p := by
  have hsum := summable_primeTwoSidedQuarterWeight p
  rw [Summable.tsum_prod hsum]
  simp only [primeTwoSidedQuarterWeight, pow_add]
  simp_rw [(summable_geometric_of_norm_lt_one
    (show ‖ccm24QuarterEulerCoefficient p‖ < 1 by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ccm24QuarterEulerCoefficient_nonneg p)]
      exact ccm24QuarterEulerCoefficient_lt_one p)).tsum_mul_left]
  rw [tsum_geometric_of_lt_one (ccm24QuarterEulerCoefficient_nonneg p)
    (ccm24QuarterEulerCoefficient_lt_one p)]
  simp [forwardEulerExponent, primeTwoSidedQuarterMass]
  field_simp [ne_of_gt (by
    linarith [ccm24QuarterEulerCoefficient_lt_one p] :
      1 - ccm24QuarterEulerCoefficient p > 0)]
  ring

theorem primeTwoSidedQuarterWeight_hasSum (p : CCM24VisiblePrime) :
    HasSum (primeTwoSidedQuarterWeight p) (primeTwoSidedQuarterMass p) := by
  simpa [tsum_primeTwoSidedQuarterWeight p] using
    (summable_primeTwoSidedQuarterWeight p).hasSum

/-- Per-prime quarter indent: `ρ_p^(f+c) = exp (-disp/4)`, definitional because
`ρ_p = exp (-(log p)/4)` and `disp = (f+c)·log p`. -/
theorem primeTwoSidedQuarterWeight_eq_exp_negFourthDisplacement
    (p : CCM24VisiblePrime) (index : PrimeTwoSidedRenewalIndex) :
    primeTwoSidedQuarterWeight p index =
      Real.exp (-(primeTwoSidedDisplacement p index) / 4) := by
  let n : ℕ := if index.1 then index.2 + 1 else index.2
  have hn : (forwardEulerExponent index.1 + index.2 : ℕ) = n := by
    dsimp [n, forwardEulerExponent]
    split_ifs <;> omega
  unfold primeTwoSidedQuarterWeight primeTwoSidedDisplacement
  rw [hn, ccm24QuarterEulerCoefficient]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- One two-sided half-power weight = product of per-prime quarter weights. -/
noncomputable def finiteEulerTwoSidedQuarterWeight
    : (S : List CCM24VisiblePrime) → FiniteEulerTwoSidedRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeTwoSidedQuarterWeight p index.1 *
        finiteEulerTwoSidedQuarterWeight S index.2

theorem finiteEulerTwoSidedQuarterWeight_nonneg
    (S : List CCM24VisiblePrime) (index : FiniteEulerTwoSidedRenewalIndex S) :
    0 ≤ finiteEulerTwoSidedQuarterWeight S index := by
  induction S with
  | nil => simp [finiteEulerTwoSidedQuarterWeight]
  | cons p S ih =>
      exact mul_nonneg (primeTwoSidedQuarterWeight_nonneg p index.1)
        (ih index.2)

/-- Joint half-power identity: `qweight = exp (-(1/4)·disp)`. -/
theorem finiteEulerTwoSidedQuarterWeight_eq_exp_negFourthDisplacement
    (S : List CCM24VisiblePrime) (index : FiniteEulerTwoSidedRenewalIndex S) :
    finiteEulerTwoSidedQuarterWeight S index =
      Real.exp (-(finiteEulerTwoSidedDisplacement S index) / 4) := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedQuarterWeight, finiteEulerTwoSidedDisplacement]
  | cons p S ih =>
      simp only [finiteEulerTwoSidedQuarterWeight, finiteEulerTwoSidedDisplacement]
      rw [primeTwoSidedQuarterWeight_eq_exp_negFourthDisplacement p index.1]
      rw [ih index.2]
      rw [← Real.exp_add]
      congr 1
      ring

/-- The half-power weight product is summable, and its exact total variation is
the finite product of the per-prime half-power masses. -/
theorem finiteEulerTwoSidedQuarterWeight_hasSum
    (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerTwoSidedQuarterWeight S)
      (S.map primeTwoSidedQuarterMass).prod := by
  induction S with
  | nil =>
      simp [finiteEulerTwoSidedQuarterWeight]
  | cons p S ih =>
      have hp : HasSum (primeTwoSidedQuarterWeight p)
          (primeTwoSidedQuarterMass p) :=
        primeTwoSidedQuarterWeight_hasSum p
      have hprod : Summable (fun index :
          PrimeTwoSidedRenewalIndex × FiniteEulerTwoSidedRenewalIndex S =>
            primeTwoSidedQuarterWeight p index.1 *
              finiteEulerTwoSidedQuarterWeight S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro index
            exact ih.summable.mul_left (primeTwoSidedQuarterWeight p index)
          · exact ((summable_primeTwoSidedQuarterWeight p).mul_right
                ((S.map primeTwoSidedQuarterMass).prod)).congr
              (fun index => by
                have h := ih.summable.tsum_mul_left
                  (primeTwoSidedQuarterWeight p index)
                rw [ih.tsum_eq] at h
                simpa using h.symm)
        · intro index
          exact mul_nonneg
            (primeTwoSidedQuarterWeight_nonneg p index.1)
            (finiteEulerTwoSidedQuarterWeight_nonneg S index.2)
      simpa [finiteEulerTwoSidedQuarterWeight] using hp.mul ih hprod

/-- The half-power summand at one prime is summable, so the full half-power
product is too. -/
theorem summable_finiteEulerTwoSidedQuarterWeight
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerTwoSidedQuarterWeight S) :=
  (finiteEulerTwoSidedQuarterWeight_hasSum S).summable

/-- Exponential tail-decay of the joint two-sided raw weight: the tail over
`{D > B}` is at most `exp(-B/4) · ∏_p (1+ρ_p)/(1-ρ_p)` with the universal
`ρ_p = exp(-(log p)/4) < 1`.  This uses the identities `w = exp(-D/2)` and
`qweight = exp(-D/4)` pointwise, and the pointwise comparison
`[D>B]·exp(-D/2) ≤ exp(-B/4)·exp(-D/4)`. -/
theorem finiteEulerTwoSidedRawWeight_tail_decay
    (S : List CCM24VisiblePrime) (B : Real) :
    (∑' index : FiniteEulerTwoSidedRenewalIndex S,
        if B < finiteEulerTwoSidedDisplacement S index then
          finiteEulerTwoSidedRawWeight S index else 0) ≤
      Real.exp (-B / 4) * (S.map primeTwoSidedQuarterMass).prod := by
  classical
  -- pointwise: on the tail, w = exp(-D/2) ≤ exp(-B/4)·exp(-D/4).
  have hpoint : ∀ index : FiniteEulerTwoSidedRenewalIndex S,
      (if B < finiteEulerTwoSidedDisplacement S index then
          finiteEulerTwoSidedRawWeight S index else 0) ≤
        Real.exp (-B / 4) * finiteEulerTwoSidedQuarterWeight S index := by
    intro index
    split_ifs with hB
    · rw [finiteEulerTwoSidedRawWeight_eq_exp_negHalfDisplacement S index]
      rw [finiteEulerTwoSidedQuarterWeight_eq_exp_negFourthDisplacement S index]
      rw [← Real.exp_add]
      have hle : -(finiteEulerTwoSidedDisplacement S index) / 2 ≤
          -B / 4 + -finiteEulerTwoSidedDisplacement S index / 4 := by
        nlinarith [hB]
      exact Real.exp_le_exp.mpr hle
    · exact mul_nonneg (Real.exp_nonneg (-B / 4))
        (finiteEulerTwoSidedQuarterWeight_nonneg S index)
  -- the tail summand is nonneg.
  have hnonneg : ∀ index : FiniteEulerTwoSidedRenewalIndex S,
      0 ≤ if B < finiteEulerTwoSidedDisplacement S index then
        finiteEulerTwoSidedRawWeight S index else 0 := by
    intro index
    split_ifs with hB
    · rw [finiteEulerTwoSidedRawWeight_eq_exp_negHalfDisplacement S index]
      exact Real.exp_nonneg _
    · simp
  -- sum: LHS tsum ≤ exp(-B/4) · RHS tsum (both summable).
  have hLsum : Summable (fun index : FiniteEulerTwoSidedRenewalIndex S =>
      if B < finiteEulerTwoSidedDisplacement S index then
        finiteEulerTwoSidedRawWeight S index else 0) :=
    Summable.of_nonneg_of_le hnonneg hpoint
      (Summable.mul_left (Real.exp (-B / 4))
        (summable_finiteEulerTwoSidedQuarterWeight S))
  have hconst : (∑' index : FiniteEulerTwoSidedRenewalIndex S,
        Real.exp (-B / 4) * finiteEulerTwoSidedQuarterWeight S index) =
      Real.exp (-B / 4) * (S.map primeTwoSidedQuarterMass).prod := by
    rw [Summable.tsum_mul_left (Real.exp (-B / 4))
      (summable_finiteEulerTwoSidedQuarterWeight S)]
    rw [(finiteEulerTwoSidedQuarterWeight_hasSum S).tsum_eq]
  calc
    (∑' index : FiniteEulerTwoSidedRenewalIndex S,
        if B < finiteEulerTwoSidedDisplacement S index then
          finiteEulerTwoSidedRawWeight S index else 0) ≤
      ∑' index : FiniteEulerTwoSidedRenewalIndex S,
        Real.exp (-B / 4) * finiteEulerTwoSidedQuarterWeight S index :=
      hLsum.tsum_le_tsum hpoint
        (Summable.mul_left (Real.exp (-B / 4))
          (summable_finiteEulerTwoSidedQuarterWeight S))
    _ = Real.exp (-B / 4) * (S.map primeTwoSidedQuarterMass).prod := hconst

end CCM24FiniteSTwoSidedRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
