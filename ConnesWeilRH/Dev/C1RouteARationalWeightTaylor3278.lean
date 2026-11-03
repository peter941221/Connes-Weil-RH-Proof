import ConnesWeilRH.Dev.C1RouteARationalCellCertificates3277
import ConnesWeilRH.Dev.C1RouteACellContainment2676

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace RatInterval3276

def powNat (a : RatInterval3276) : ℕ → RatInterval3276
  | 0 => { lo := 1, hi := 1 }
  | n + 1 => mul (powNat a n) a

theorem mem_powNat {x : ℝ} {a : RatInterval3276}
    (ha : a.Mem x) : ∀ n, (powNat a n).Mem (x ^ n)
  | 0 => by
      change (powNat a 0).toReal.Mem (x ^ 0)
      norm_num [powNat, toReal, RealInterval2429.Mem]
  | n + 1 => by
      rw [pow_succ]
      exact mem_mul (mem_powNat ha n) ha

end RatInterval3276

theorem ratTaylorExp60_mem3278
    {x : ℝ} {n : ℕ} (hn : 0 < n) (hx : |x| ≤ 1)
    {S E : ℝ} (hS : ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ) = S)
    (hE : |x| ^ n * (n.succ / (n.factorial * n)) = E)
    {a : RatInterval3276}
    (hlo : (a.lo : ℝ) ≤ S - E)
    (hhi : S + E ≤ (a.hi : ℝ))
    (hpos : 0 ≤ a.lo) :
    (RatInterval3276.powNat a 60).Mem (Real.exp ((60 : ℕ) * x)) := by
  have hpin := expTwoSided2676 hn hx hS hE
  have ha : a.Mem (Real.exp x) := by
    change (a.lo : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (a.hi : ℝ)
    constructor <;> linarith [hpin.1, hpin.2]
  have hpow := RatInterval3276.mem_powNat ha 60
  simpa only [Real.exp_nat_mul] using hpow

end ConnesWeilRH.Dev
