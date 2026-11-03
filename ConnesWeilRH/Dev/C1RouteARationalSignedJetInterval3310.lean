import ConnesWeilRH.Dev.C1RouteARationalTightCell3298
import ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
Record 3310 starts the formal bridge from the 3306 signed jet to rational
cell bounds. The bump exponential is enclosed by the already audited 3298
ladder; only the polynomial and denominator factors are new exact rational
arithmetic.
-/

def ratBumpNumerator3310 : ℕ → ℚ → ℚ
  | 0, _ => 1
  | 1, u => -60 * u
  | 2, u => -60 + 3480 * u ^ 2 + 180 * u ^ 4
  | 3, u => 10080 * u - 193680 * u ^ 3 - 31680 * u ^ 5 - 720 * u ^ 7
  | 4, u => 10080 - 1085040 * u ^ 2 + 10189440 * u ^ 4 +
      3575520 * u ^ 6 + 266400 * u ^ 8 + 3600 * u ^ 10
  | 5, u => -2613600 * u + 92678400 * u ^ 3 -
      493207200 * u ^ 5 - 320371200 * u ^ 7 - 51703200 * u ^ 9 -
      2361600 * u ^ 11 - 21600 * u ^ 13
  | 6, u => -2613600 + 387806400 * u ^ 2 -
      6679584000 * u ^ 4 + 20842228800 * u ^ 6 +
      24232824000 * u ^ 8 + 7137633600 * u ^ 10 +
      714873600 * u ^ 12 + 22680000 * u ^ 14 + 151200 * u ^ 16
  | _, _ => 0

theorem ratBumpNumerator_cast3310 (order : ℕ) (u : ℚ) (horder : order ≤ 6) :
    (ratBumpNumerator3310 order u : ℝ) = bumpNumerator2350 order (u : ℝ) := by
  interval_cases order <;>
    simp [ratBumpNumerator3310, bumpNumerator2350, Rat.cast_add,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_pow]
  <;> push_cast
  <;> ring

def ratBumpJetInterval3310 (order : ℕ) (radius position : ℚ) : RatInterval3276 :=
  if |position| < radius then
    let u := position / radius
    let deficit := 1 - u ^ 2
    let factor := deficit⁻¹ ^ (2 * order) * ratBumpNumerator3310 order u /
      radius ^ order
    RatInterval3276.mul
      (ratTailBumpInterval3298 (ratBumpT3286 radius |position|))
      {lo := factor, hi := factor}
  else
    {lo := 0, hi := 0}

theorem ratBumpJetInterval_mem3310
    {order : ℕ} (horder : order ≤ 6)
    {radius position : ℚ} (hradius : 0 < (radius : ℝ)) :
    (ratBumpJetInterval3310 order radius position).Mem
      (iteratedDeriv order (widthBump (radius : ℝ)) (position : ℝ)) := by
  by_cases hactive : |position| < radius
  · have hactiveR : |(position : ℝ)| < (radius : ℝ) := by
      have hcast : ((|position| : ℚ) : ℝ) < (radius : ℝ) := by
        exact_mod_cast hactive
      simpa [Rat.cast_abs] using hcast
    have hposQ : 0 ≤ |position| := abs_nonneg _
    have hpos : (0 : ℝ) ≤ ((|position| : ℚ) : ℝ) := by
      exact_mod_cast hposQ
    have hinside : ((|position| : ℚ) : ℝ) < (radius : ℝ) := by
      exact_mod_cast hactive
    have ht : (ratBumpT3286 radius |position| : ℝ) =
        30 - 30 / (1 - (((|position| : ℚ) : ℝ) / (radius : ℝ)) ^ 2) := by
      norm_num [ratBumpT3286, Rat.cast_sub, Rat.cast_div, Rat.cast_pow]
    have ht0 := ratBumpT_nonpos3287 (radius := (radius : ℝ))
      (position := ((|position| : ℚ) : ℝ)) hradius hpos hinside
    have ht0' : (ratBumpT3286 radius |position| : ℝ) ≤ 0 := by
      simpa [ht] using ht0
    have hwidth := ratTailBumpInterval_mem3298
      (radius := radius) (position := |position|)
      (t := ratBumpT3286 radius |position|) hradius hpos hinside ht ht0'
    let factorQ : ℚ :=
      (1 - (position / radius) ^ 2)⁻¹ ^ (2 * order) *
        ratBumpNumerator3310 order (position / radius) / radius ^ order
    have hfactorMem :
        ({lo := factorQ, hi := factorQ} : RatInterval3276).Mem
          (factorQ : ℝ) := by
        unfold RatInterval3276.Mem RatInterval3276.toReal
          RealInterval2429.Mem
        dsimp
        constructor <;> rfl
    have hmul := RatInterval3276.mem_mul hwidth hfactorMem
    have hderiv := widthBump_iteratedDeriv_global2350 order horder hradius
      (position := (position : ℝ))
    rw [hderiv, if_pos hactiveR]
    have hscaledEq :
        Real.exp (-30 / (1 - ((position : ℝ) / (radius : ℝ)) ^ 2)) *
            (1 - ((position : ℝ) / (radius : ℝ)) ^ 2)⁻¹ ^ (2 * order) *
              bumpNumerator2350 order ((position : ℝ) / (radius : ℝ)) /
                (radius : ℝ) ^ order =
          widthBump (radius : ℝ) ((|position| : ℚ) : ℝ) * (factorQ : ℝ) := by
      have hinsideAbs : |(((|position| : ℚ) : ℝ))| < (radius : ℝ) := by
        simpa [abs_of_nonneg hpos] using hinside
      rw [widthBump, if_pos hinsideAbs]
      dsimp [factorQ]
      push_cast
      rw [ratBumpNumerator_cast3310 order (position / radius) horder]
      norm_num [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
        Rat.cast_abs]
      rw [div_pow, div_pow, sq_abs]
      ring
    unfold ratBumpJetInterval3310
    rw [if_pos hactive]
    change (RatInterval3276.mul _ _).Mem _
    change (RatInterval3276.mul _
      ({lo := factorQ, hi := factorQ} : RatInterval3276)).Mem _
    unfold scaledBumpJet2350 bumpJet2350 bumpDeficit2350
    rw [hscaledEq]
    exact hmul
  · have hactiveR : ¬ |(position : ℝ)| < (radius : ℝ) := by
      intro h
      apply hactive
      exact_mod_cast h
    have hderiv := widthBump_iteratedDeriv_global2350 order horder hradius
      (position := (position : ℝ))
    rw [hderiv, if_neg hactiveR]
    unfold ratBumpJetInterval3310
    rw [if_neg hactive]
    norm_num [RatInterval3276.Mem, RatInterval3276.toReal,
      RealInterval2429.Mem]

end ConnesWeilRH.Dev
