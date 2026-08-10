import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
/-!
# RealWeierstrassProd: real Weierstrass partial-product skeleton (docs/944)

First divide-and-conquer brick for the in-repo Gamma product developable
(docs/940, lane (a)).  We isolate the REAL Weierstrass factors
    webfac s n = (1 + s/(n+1)) * exp(-s/(n+1))   (0 <= s)
and prove the rudimentary structural facts needed for product convergence
(eventually this limit is 1/Real.Gamma s; NOT proven here):
  1. 0 < webfac s n <= 1;
  2. the partial products P_N = prod_{n<N} webfac s n are positive and <= 1;
  3. P_N is monotone non-increasing, hence (by monotone convergence) has a leaf.
No claim that the limit equals 1/Gamma; that is the next analytic match.
Axiom-clean off mathlib foundations. RH NOT claimed.
-/


namespace ConnesWeilRH
namespace Dev
namespace RealWeierstrassProd

/-- The per-factor scale x = s/(n+1) (nonnegative for 0 <= s). -/
noncomputable def factorScale (s : Real) (n : Nat) : Real := s / (n + 1 : Real)

/-- The s-th Weierstrass factor w(n) = (1 + x) * exp(-x), x = s/(n+1). -/
noncomputable def webfac (s : Real) (n : Nat) : Real :=
  (1 + factorScale s n) * Real.exp (-factorScale s n)

/-- The finite partial Weierstrass product over n = 0..N-1. -/
noncomputable def partialP (s : Real) (N : Nat) : Real :=
  Finset.prod (Finset.range N) (fun n : Nat => webfac s n)

/-- The per-factor scale is nonnegative for 0 <= s. -/
lemma factorScale_nonneg {s : Real} (hs : 0 <= s) (n : Nat) :
    0 <= factorScale s n := by
  dsimp [factorScale]
  positivity

/-- The real Weierstrass factor is strictly positive and at most 1. -/
theorem webfac_bounds (hs : 0 <= s) (n : Nat) :
    0 < webfac s n ∧ webfac s n <= 1 := by
  let x := factorScale s n
  have hx : 0 <= x := factorScale_nonneg hs n
  constructor
  · dsimp [webfac]
    have hpos1 : 0 < (1 + x : Real) := by linarith
    have hposE : 0 < Real.exp (-x) := Real.exp_pos _
    exact mul_pos hpos1 hposE
  · dsimp [webfac]
    have hle1 : (1 + x : Real) <= Real.exp x := by
      simpa [add_comm] using Real.add_one_le_exp x
    have hE : 0 <= Real.exp (-x) := (Real.exp_pos _).le
    calc
      (1 + x) * Real.exp (-x) <= Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hle1 hE
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num

/-- The finite partial product is strictly positive: all Weierstrass factors > 0. -/
theorem partialP_pos (hs : 0 <= s) (N : Nat) :
    0 < partialP s N := by
  dsimp [partialP]
  exact Finset.prod_pos (fun n _ => (webfac_bounds hs n).1)

/-- The finite partial product is at most 1: each factor <= 1 (finitely many). -/
theorem partialP_le_one (hs : 0 <= s) (N : Nat) :
    partialP s N <= 1 := by
  dsimp [partialP]
  exact Finset.prod_le_one
    (fun n _ => (webfac_bounds hs n).1.le)
    (fun n _ => (webfac_bounds hs n).2)

/-- The partial products form a non-increasing sequence. -/
theorem partialP_mono (hs : 0 <= s) (N : Nat) :
    partialP s (N + 1) <= partialP s N := by
  dsimp [partialP]
  rw [Finset.prod_range_succ]
  simpa [mul_one] using mul_le_mul_of_nonneg_left (webfac_bounds hs N).2 (partialP_pos hs N).le
end RealWeierstrassProd
end Dev
end ConnesWeilRH
