import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218
import ConnesWeilRH.Dev.C1RouteACellContainment2676

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem complexRectPowSq_staged_step3251
    {inner outer : ComplexRect2427} {z : ℂ}
    (hinner : inner.Mem z)
    (houter : outer.reLo ≤ inner.reLo)
    (houter' : inner.reHi ≤ outer.reHi)
    (houter_im : outer.imLo ≤ inner.imLo)
    (houter_im' : inner.imHi ≤ outer.imHi) :
    outer.Mem z := by
  exact rectSubset2676 houter houter' houter_im houter_im' hinner

theorem complexRectPowSq_staged_mem3251
    {boxes : ℕ → ComplexRect2427} {z : ℂ} {n : ℕ}
    (hbase : (boxes 0).Mem z)
    (hstep : ∀ (k : ℕ) (w : ℂ),
      (boxes k).Mem w → (boxes (k + 1)).Mem (w * w)) :
    (boxes n).Mem (z ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hnext := hstep n (z ^ (2 ^ n)) ih
      have hpow : z ^ (2 ^ (n + 1)) = (z ^ (2 ^ n)) * (z ^ (2 ^ n)) := by
        rw [show 2 ^ (n + 1) = (2 ^ n) * 2 by ring, pow_mul]
        simp [pow_two]
      simpa [hpow] using hnext

theorem complexRectPowSq_staged_mem_of_bound3251
    {boxes : ℕ → ComplexRect2427} {z : ℂ} {n : ℕ}
    (hbase : (boxes 0).Mem z)
    (hstep : ∀ k : ℕ, k < n → ∀ w : ℂ,
      (boxes k).Mem w → (boxes (k + 1)).Mem (w * w)) :
    (boxes n).Mem (z ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      have hprev := ih (fun k hk w hw =>
        hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)) w hw)
      have hnext := hstep n (Nat.lt_succ_self n) (z ^ (2 ^ n)) hprev
      have hpow : z ^ (2 ^ (n + 1)) = (z ^ (2 ^ n)) * (z ^ (2 ^ n)) := by
        rw [show 2 ^ (n + 1) = (2 ^ n) * 2 by ring, pow_mul]
        simp [pow_two]
      simpa [hpow] using hnext

theorem complexRectPowSq_staged_step_of_subset3251
    {inner outer : ComplexRect2427} {z : ℂ}
    (hz : inner.Mem z)
    (hsubset : outer.reLo ≤ inner.reLo ∧
      inner.reHi ≤ outer.reHi ∧
      outer.imLo ≤ inner.imLo ∧
      inner.imHi ≤ outer.imHi) :
    outer.Mem z := by
  exact complexRectPowSq_staged_step3251 hz hsubset.1 hsubset.2.1
    hsubset.2.2.1 hsubset.2.2.2

end ConnesWeilRH.Dev
