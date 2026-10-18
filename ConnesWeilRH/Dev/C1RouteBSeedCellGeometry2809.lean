import ConnesWeilRH.Dev.C1RouteBSeedJetComplexRect2808

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable def routeBSeedCell2809 (i : ℕ) : RealInterval2429 :=
  { lo := (8192 + 2047 * i : ℝ) / 33554432
    hi := (8192 + 2047 * (i + 1) : ℝ) / 33554432 }

theorem routeBSeedCell2809_mem_unit (i : ℕ) (hi : i < 8192) :
    0 < (routeBSeedCell2809 i).lo ∧
      (routeBSeedCell2809 i).hi < 1 := by
  constructor
  · norm_num [routeBSeedCell2809]
    positivity
  · norm_num [routeBSeedCell2809]
    have hi' : i ≤ 8191 := by omega
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 33554432)).2
    exact_mod_cast (show 8192 + 2047 * (i + 1) < 33554432 by omega)

theorem routeBSeedCell2809_adjacent (i : ℕ) :
    (routeBSeedCell2809 i).hi = (routeBSeedCell2809 (i + 1)).lo := by
  simp [routeBSeedCell2809]

theorem routeBSeedCell2809_first :
    (routeBSeedCell2809 0).lo = (1 : ℝ) / 4096 := by
  norm_num [routeBSeedCell2809]

theorem routeBSeedCell2809_last :
    (routeBSeedCell2809 8191).hi = (1 : ℝ) / 2 := by
  norm_num [routeBSeedCell2809]

theorem routeBSeedCell2809_d4_mem (i : ℕ) (hi : i < 8192)
    {x : ℝ} (hx : (routeBSeedCell2809 i).Mem x) :
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 4).Mem
      ((iteratedDeriv 4 Real.smoothTransition x : ℝ) : ℂ) := by
  exact seedJetComplexRect_mem2808 _ 4
    (routeBSeedCell2809_mem_unit i hi).1
    (routeBSeedCell2809_mem_unit i hi).2 hx

theorem routeBSeedCell2809_d7_mem (i : ℕ) (hi : i < 8192)
    {x : ℝ} (hx : (routeBSeedCell2809 i).Mem x) :
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 7).Mem
      ((iteratedDeriv 7 Real.smoothTransition x : ℝ) : ℂ) := by
  exact seedJetComplexRect_mem2808 _ 7
    (routeBSeedCell2809_mem_unit i hi).1
    (routeBSeedCell2809_mem_unit i hi).2 hx

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
