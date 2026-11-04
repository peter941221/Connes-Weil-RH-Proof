import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3345
import ConnesWeilRH.Dev.C1RouteARationalBumpSelector3335

namespace ConnesWeilRH.Dev

theorem ratBaseInterval3284_order3346 :
    ratBaseInterval3284.lo ≤ ratBaseInterval3284.hi := by
  have h := ratBaseInterval_mem3284
  have hreal : (ratBaseInterval3284.lo : ℝ) ≤
      (ratBaseInterval3284.hi : ℝ) := le_trans h.1 h.2
  exact_mod_cast hreal

theorem ratBaseInterval3284_powNat_hi_eq_pow3346 (n : ℕ) :
    (RatInterval3276.powNat ratBaseInterval3284 n).hi =
      ratBaseInterval3284.hi ^ n := by
  exact ratInterval_powNat_hi_eq_pow_of_nonneg3345
    ratBaseInterval3284 ratBaseInterval3284_lo_nonneg3344
    ratBaseInterval3284_hi_nonneg3344 ratBaseInterval3284_order3346 n

theorem signed_bump_tail_selector3335_cell0_family4_hi3346 :
    (ratTailBumpInterval3298
        (ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0|)).hi =
      ratBaseInterval3284.hi ^ 188 := by
  rw [signed_bump_tail_selector3335_cell0_family4]
  exact ratBaseInterval3284_powNat_hi_eq_pow3346 188

end ConnesWeilRH.Dev
