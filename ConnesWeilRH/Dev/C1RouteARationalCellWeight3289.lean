import ConnesWeilRH.Dev.C1RouteARationalTaylor3283

namespace ConnesWeilRH.Dev

def ratCellWeightArgument3289 (index : ℕ) : ℚ :=
  -(record2680CenterRat3279 index) / 120

def ratCellWeightInterval3289 (index : ℕ) : RatInterval3276 :=
  RatInterval3276.powNat
    (ratTaylorInterval3283 (ratCellWeightArgument3289 index)) 60

theorem ratCellWeightArgument_mem_unit3289
    {index : ℕ} (hindex : index < 40960) :
    |(ratCellWeightArgument3289 index : ℝ)| ≤ 1 := by
  have hindex0 : (0 : ℝ) ≤ index := by positivity
  have hindexR : (index : ℝ) < 40960 := by exact_mod_cast hindex
  have htwo : (2 : ℝ) * (index : ℝ) + 1 < 81921 := by
    nlinarith
  rw [abs_le]
  constructor
  · dsimp [ratCellWeightArgument3289, record2680CenterRat3279]
    norm_num [Rat.cast_sub, Rat.cast_add, Rat.cast_neg, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, div_eq_mul_inv] at *
    nlinarith [htwo]
  · dsimp [ratCellWeightArgument3289, record2680CenterRat3279]
    norm_num [Rat.cast_sub, Rat.cast_add, Rat.cast_neg, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, div_eq_mul_inv] at *
    nlinarith [hindex0, htwo]

theorem ratCellWeightInterval_mem3289
    {index : ℕ} (hindex : index < 40960) :
    (ratCellWeightInterval3289 index).Mem
      (Real.exp (-(1 / 2 : ℝ) * record2680Center3212 index)) := by
  have hx := ratCellWeightArgument_mem_unit3289 hindex
  have hbase := ratTaylorInterval_mem3283 hx
  have hpow := RatInterval3276.mem_powNat hbase 60
  have harg : (60 : ℝ) * (ratCellWeightArgument3289 index : ℝ) =
      -(1 / 2 : ℝ) * record2680Center3212 index := by
    norm_num [ratCellWeightArgument3289, Rat.cast_neg, Rat.cast_div]
    rw [record2680CenterRat_cast3279]
    ring
  rw [← harg]
  change (ratCellWeightInterval3289 index).Mem
    (Real.exp (((60 : ℕ) : ℝ) * (ratCellWeightArgument3289 index : ℝ)))
  simpa only [ratCellWeightInterval3289, Real.exp_nat_mul] using hpow

end ConnesWeilRH.Dev
