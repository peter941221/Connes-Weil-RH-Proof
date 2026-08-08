import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import ConnesWeilRH.Dev.ArctanCert

--
-- Brick 2b (S-series elementary sandwich), in-repo, no external dependency.
--
-- arch-phase arg Gamma(1+i/2) = -gamma/2 - atan(1/2) + S, with S := tsum a,
-- a n = 1/(2(n+1)) - atan(1/(2(n+2))).  Split a = p + u:
--   p telescopes to 1/2 (hasSum_p),  u >= 0, and u n <= (1/8)*c n where
--   c n = 1/((n+1)(n+2)(n+3)) telescopes to 1/4, so tsum u <= 1/32.
-- Conclude the sandwich:  1/2 <= S <= 1/2 + 1/32  (S_ge_half, S_le_half_plus).
-- axiom-clean: only mathlib foundations [propext, Classical.choice, Quot.sound].
--




































open Filter

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace SSandwich

noncomputable section


def a (n : Nat) : Real := (1 : ℝ)/(2*(n+1)) - Real.arctan (1/(2*(n+2)))

def p (n : Nat) : Real := (1 : ℝ)/(2*(n+1)) - (1 : ℝ)/(2*(n+2))

def u (n : Nat) : Real := (1 : ℝ)/(2*(n+2)) - Real.arctan (1/(2*(n+2)))

lemma a_eq_p_add_u (n : Nat) : a n = p n + u n := by
  unfold a p u; ring

lemma atan_le_self (x : Real) (hx : 0 ≤ x) : Real.arctan x ≤ x :=
  (ArctanCert.arctan_le_self x hx)

lemma lower_le_atan (x : Real) (hx : 0 ≤ x) : x/(1 + x^2) ≤ Real.arctan x :=
  (ArctanCert.lower_le_arctan x hx)


lemma sub_cube_le_frac (x : Real) (hx : 0 ≤ x) : x - x ^ 3 ≤ x / (1 + x ^ 2) := by
  have hden : 0 < (1 : ℝ) + x ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  have hx5 : (0 : ℝ) ≤ x ^ 5 := pow_nonneg hx 5
  ring_nf
  nlinarith


lemma atan_ge_sub_cube (x : Real) (hx : 0 ≤ x) : x - x ^ 3 ≤ Real.arctan x := by
  exact le_trans (sub_cube_le_frac x hx) (lower_le_atan x hx)


lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  unfold u
  have h : Real.arctan (1 / (2 * (n + 2))) ≤ (1 : ℝ) / (2 * (n + 2)) :=
    atan_le_self (1 / (2 * (n + 2))) (by positivity)
  linarith


lemma p_nonneg (n : ℕ) : 0 ≤ p n := by
  unfold p
  have h : (1 : ℝ)/(2*((n:ℝ)+1)) - 1/(2*((n:ℝ)+2)) =
      1 / ((2:ℝ) * ((n:ℝ)+1) * ((n:ℝ)+2)) := by
    field_simp [show (2:ℝ)*((n:ℝ)+1) ≠ 0 by positivity, show (2:ℝ)*((n:ℝ)+2) ≠ 0 by positivity]
    ring
  rw [h]
  positivity


lemma sum_range_p (N : ℕ) : Finset.sum (Finset.range N) p = (1 : ℝ)/2 - 1/(2*((N:ℝ)+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      unfold p
      field_simp [Finset.sum_range_succ]
      push_cast
      ring


lemma u_le_cube (n : ℕ) : u n ≤ (1 : ℝ) / (8 * ((n : ℝ) + 2) ^ 3) := by
  let x : ℝ := 1 / (2 * (n + 2))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hga := atan_ge_sub_cube x hx0
  have hu : u n = x - Real.arctan x := by
    unfold u x
    rfl
  have hb : x - Real.arctan x ≤ x ^ 3 := by
    have : x - Real.arctan x ≤ x - (x - x ^ 3) := by linarith
    linarith
  have hc : x ^ 3 = (1 : ℝ) / (8 * ((n : ℝ) + 2) ^ 3) := by
    dsimp [x]
    field_simp
    ring_nf
  rw [hu]
  simpa [hc] using hb




lemma tendsto_halfN_zero : Tendsto (fun N : Nat => (1 : Real)/(2*((N:Real)+1))) atTop (nhds (0:Real)) := by
  have hbase : Tendsto (fun N : Nat => (2 * ((N : Real) + 1))⁻¹) atTop (nhds (0 : Real)) := by
    have h := tendsto_mul_add_inv_atTop_nhds_zero (2 : ℝ) (2 : ℝ) (by norm_num)
    have hcomp : Tendsto (fun N : Nat => (2 * (N : Real) + 2)⁻¹) atTop (nhds (0 : ℝ)) :=
      h.comp tendsto_natCast_atTop_atTop
    exact hcomp.congr' (by
      filter_upwards with N
      congr 1
      ring
    )
  simpa [one_div] using hbase


theorem hasSum_p : HasSum p (1/2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg p_nonneg (1/2)]
  have hfun : (fun N : Nat => (Finset.sum (Finset.range N) p)) =
      fun N : Nat => (1 : Real)/2 - (1 : Real)/(2*((N:Real)+1)) := by
    funext N
    rw [sum_range_p]
  rw [hfun]
  simpa using (tendsto_const_nhds.sub tendsto_halfN_zero)




def S : Real := tsum a


def c (n : Nat) : Real :=
  (1 : Real) / (((n : Real) + 1) * ((n : Real) + 2) * ((n : Real) + 3))

lemma c_nonneg (n : Nat) : 0 <= c n := by
  dsimp [c]
  positivity


def d (n : Nat) : Real :=
  1 / (((n : Real) + 1) * ((n : Real) + 2)) -
    1 / (((n : Real) + 2) * ((n : Real) + 3))

lemma c_eq_half_d (n : Nat) : c n = (1 / 2 : Real) * d n := by
  dsimp [c, d]
  field_simp
  ring


lemma sum_range_d (N : Nat) :
    (Finset.sum (Finset.range N) d) =
      (1 / 2 : Real) - 1 / (((N : Real) + 1) * ((N : Real) + 2)) := by
  induction N with
  | zero => norm_num [d]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      dsimp [d]
      norm_cast
      field_simp
      ring


lemma sum_range_c (N : Nat) :
    (Finset.sum (Finset.range N) c) =
      (1 / 2 : Real) * (1 / 2 - 1 / (((N : Real) + 1) * ((N : Real) + 2))) := by
  calc
    (Finset.sum (Finset.range N) c)
        = (Finset.sum (Finset.range N) (fun n : Nat => (1 / 2 : Real) * d n)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact c_eq_half_d n
    _ = (1 / 2 : Real) * (Finset.sum (Finset.range N) d) := by
          rw [Finset.mul_sum]
    _ = (1 / 2 : Real) * (1/2 - 1 / (((N : Real) + 1) * ((N : Real) + 2))) := by
          rw [sum_range_d]


lemma one_cube_le_prod (n : Nat) :
    (1 : Real) / ((n : Real) + 2) ^ 3 <=
      1 / (((n : Real) + 1) * ((n : Real) + 2) * ((n : Real) + 3)) := by
  apply one_div_le_one_div_of_le
  · show (0 : Real) < ((n : Real) + 1) * ((n : Real) + 2) * ((n : Real) + 3)
    positivity
  · have h : (((n : Real) + 1) * ((n : Real) + 2) * ((n : Real) + 3)) =
            ((n : Real) + 2) ^ 3 - ((n : Real) + 2) := by ring
    rw [h]
    have hnn : (0 : Real) <= (n : Real) + 2 := by positivity
    linarith


lemma u_le_eighth_c (n : Nat) : u n <= (1 / 8 : Real) * c n := by
  have hu : u n <= 1 / (8 * ((n : Real) + 2) ^ 3) := u_le_cube n
  have hsplit : 1 / (8 * ((n : Real) + 2) ^ 3) = (1 / 8 : Real) * (1 / ((n : Real) + 2) ^ 3) := by
    field_simp
  calc
    u n <= 1 / (8 * ((n : Real) + 2) ^ 3) := hu
    _ = (1 / 8 : Real) * (1 / ((n : Real) + 2) ^ 3) := hsplit
    _ <= (1 / 8 : Real) * (1 / (((n : Real) + 1) * ((n : Real) + 2) * ((n : Real) + 3))) := by
      exact mul_le_mul_of_nonneg_left (one_cube_le_prod n) (by norm_num)
    _ = (1 / 8 : Real) * c n := by rfl


lemma sum_range_c_le (n : Nat) : (Finset.sum (Finset.range n) c) <= (1 / 4 : Real) := by
  rw [sum_range_c]
  have hpos : (0 : Real) <= 1 / (((n : Real) + 1) * ((n : Real) + 2)) := by positivity
  have hdiff : (1 / 2 : Real) - 1 / (((n : Real) + 1) * ((n : Real) + 2)) <= (1 / 2 : Real) := by
    linarith
  have hmul : (1 / 2 : Real) * (1 / 2 - 1 / (((n : Real) + 1) * ((n : Real) + 2))) <=
      (1 / 2 : Real) * (1 / 2) := mul_le_mul_of_nonneg_left hdiff (by norm_num)
  exact hmul.trans (by norm_num)


theorem u_range_le_32 (n : Nat) :
    (Finset.sum (Finset.range n) u) <= (1 / 32 : Real) := by
  calc
    (Finset.sum (Finset.range n) u)
        <= (Finset.sum (Finset.range n) (fun k : Nat => (1 / 8 : Real) * c k)) := by
          exact Finset.sum_le_sum (fun k hk => u_le_eighth_c k)
    _ = (1 / 8 : Real) * (Finset.sum (Finset.range n) c) := by
          rw [Finset.mul_sum]
    _ <= (1 / 32 : Real) := by
          have hmul : (1 / 8 : Real) * (Finset.sum (Finset.range n) c) <=
              (1 / 8 : Real) * (1 / 4) := mul_le_mul_of_nonneg_left (sum_range_c_le n) (by norm_num)
          exact hmul.trans (by norm_num)


lemma u_summable : Summable u := by
  exact summable_of_sum_range_le u_nonneg u_range_le_32


theorem tsum_u_le_32 : (tsum u) <= (1 / 32 : Real) := by
  exact Real.tsum_le_of_sum_range_le u_nonneg u_range_le_32


lemma p_summable : Summable p := hasSum_p.summable


lemma a_summable : Summable a := by
  have h : Summable (fun n : Nat => p n + u n) := p_summable.add u_summable
  have heq : (fun n : Nat => p n + u n) = a := by
    funext n
    exact (a_eq_p_add_u n).symm
  rw [← heq]
  exact h


theorem S_eq : S = (1 / 2 : Real) + (tsum u) := by
  dsimp [S]
  have hs : HasSum a ((1/2 : Real) + (tsum u)) := by
    have h := hasSum_p.add u_summable.hasSum
    convert h using 1
    funext n
    exact a_eq_p_add_u n
  exact hs.tsum_eq


theorem S_ge_half : (1 / 2 : Real) <= S := by
  rw [S_eq]
  have hnn : (0 : Real) <= tsum u := tsum_nonneg u_nonneg
  linarith


theorem S_le_half_plus : S <= (1 / 2 : Real) + (1 / 32) := by
  rw [S_eq]
  have ht : tsum u <= (1 / 32 : Real) := tsum_u_le_32
  linarith

-- Bridge brick (docs/903): tie the Euler-Weierstrass imaginary series S2
-- to the closed S-series via a telescoping atan sum.  With
--   a n  = 1/(2(n+1)) - atan(1/(2(n+2)))            (Lean S := tsum a)
--   S2 n = 1/(2(n+1)) - atan(1/(2(n+1)))            (Euler-Weierstrass arg gamma term)
--   b n  = atan(1/(2(n+1))) - atan(1/(2(n+2)))
-- we have a = S2 + b pointwise, and b telescopes to tsum b = atan(1/2).
-- Hence tsum a = tsum S2 + atan(1/2)  (docs/903 identity (2)).
-- Axiom-clean: mathlib foundations only.

def S2 (n : Nat) : Real :=
  (1 : Real)/(2*(n+1)) - Real.arctan (1/(2*(n+1)))

def b (n : Nat) : Real :=
  Real.arctan (1/(2*(n+1))) - Real.arctan (1/(2*(n+2)))

lemma a_eq_S2_add_b (n : Nat) : a n = S2 n + b n := by
  unfold a S2 b
  ring

lemma sum_range_b (N : Nat) :
    (Finset.sum (Finset.range N) b) = Real.arctan (1/2) - Real.arctan (1/(2*((N:Real)+1))) := by
  induction N with
  | zero => norm_num [b]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      unfold b
      push_cast
      ring_nf

lemma b_nonneg (n : Nat) : 0 <= b n := by
  unfold b
  have h2 : Real.arctan (1/(2*((n:Real)+2))) <= Real.arctan (1/(2*((n:Real)+1))) := by
    rw [Real.arctan_le_arctan_iff]
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  linarith

lemma tendsto_b_tail :
    Tendsto (fun N : Nat => Real.arctan (1/(2*((N:Real)+1)))) atTop (nhds (0:Real)) := by
  have hc := (Real.continuous_arctan.tendsto 0).comp tendsto_halfN_zero
  simpa [Real.arctan_zero] using hc

theorem hasSum_b : HasSum b (Real.arctan (1/2)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg b_nonneg (Real.arctan (1/2))]
  have hfun : (fun N : Nat => (Finset.sum (Finset.range N) b)) =
      fun N : Nat => (Real.arctan (1/2) - Real.arctan (1/(2*((N:Real)+1)))) := by
    funext N
    rw [sum_range_b]
  rw [hfun]
  simpa using (tendsto_const_nhds.sub tendsto_b_tail)

lemma b_summable : Summable b := hasSum_b.summable

lemma S2_summable : Summable S2 := by
  have h : (fun n : Nat => S2 n) = fun n : Nat => a n - b n := by
    funext n
    unfold a S2 b
    ring
  simp [h, a_summable.sub b_summable]

theorem S_eq_S2_add_atan_half : S = (tsum S2) + Real.arctan (1/2) := by
  dsimp [S]
  have hsplit : (tsum a) = (tsum (fun n : Nat => S2 n + b n)) := by
    congr 1
    funext n
    exact (a_eq_S2_add_b n)
  calc
    (tsum a) = (tsum (fun n : Nat => S2 n + b n)) := hsplit
    _ = (tsum S2) + (tsum b) := by rw [S2_summable.tsum_add b_summable]
    _ = (tsum S2) + Real.arctan (1/2) := by rw [hasSum_b.tsum_eq]

end

end SSandwich
end Dev
end Source
end ConnesWeilRH
