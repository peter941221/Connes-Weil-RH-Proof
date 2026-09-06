import ConnesWeilRH.Dev.C1ConcreteClassMomentGroundingB

namespace ConnesWeilRH.Source.C1ConcreteClassMomentCertificate

def probeQ : ℕ := 35 ^ 19 * Nat.factorial 19

theorem cast_probe (i : ℕ) (hi : i < 20) :
    (if i < 20 then ((-(2 / 35 : ℚ)) ^ i) / (i.factorial : ℚ) else 0) *
        (probeQ : ℚ) =
      (((-2 : ℤ) ^ i * (35 : ℤ) ^ (19 - i) *
        ((Nat.factorial 19 / i.factorial : ℕ) : ℤ) : ℤ) : ℚ) := by
  rw [if_pos hi]
  have hdvd : i.factorial ∣ Nat.factorial 19 :=
    Nat.factorial_dvd_factorial (by omega)
  have hdiv : ((Nat.factorial 19 / i.factorial : ℕ) : ℚ) =
      (Nat.factorial 19 : ℚ) / (i.factorial : ℚ) :=
    Nat.cast_div hdvd (by positivity)
  have hpow : (35 : ℚ) ^ i * (35 : ℚ) ^ (19 - i) = (35 : ℚ) ^ 19 := by
    rw [← pow_add]
    congr 1
    omega
  unfold probeQ
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast]
  rw [show (-(2 / 35 : ℚ)) = (-2 : ℚ) / 35 by norm_num, div_pow]
  rw [hdiv]
  field_simp [Nat.cast_pos.mpr i.factorial_pos]
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  calc
    (-2 : ℚ) ^ i * 26447672832002022437587219218750000000000000000 =
        (-2 : ℚ) ^ i * ((35 : ℚ) ^ 19 * (Nat.factorial 19 : ℚ)) := by norm_num
    _ = (-2 : ℚ) ^ i * ((35 : ℚ) ^ i * 35 ^ (19 - i)) *
        (Nat.factorial 19 : ℚ) := by rw [hpow]; ring
    _ = _ := by ring

end ConnesWeilRH.Source.C1ConcreteClassMomentCertificate
