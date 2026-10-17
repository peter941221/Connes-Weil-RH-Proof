import ConnesWeilRH.Dev.C1SeedJetSemantics2731
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

/-! Interval jet propagation for the actual transition function.
Exact real interval operations are reused; no floating-point endpoints
or unverified derivative values are asserted here.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable section

def sumJetIntervals2734 (r : ℕ → RealInterval2429) (n : ℕ) : RealInterval2429 :=
  { lo := ∑ j ∈ Finset.range n, (r j).lo
    hi := ∑ j ∈ Finset.range n, (r j).hi }

theorem mem_sumJetIntervals2734 (r : ℕ → RealInterval2429) (v : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, (r j).Mem (v j)) :
    (sumJetIntervals2734 r n).Mem (∑ j ∈ Finset.range n, v j) := by
  constructor
  · exact Finset.sum_le_sum fun j hj => (h j (Finset.mem_range.mp hj)).1
  · exact Finset.sum_le_sum fun j hj => (h j (Finset.mem_range.mp hj)).2

def productJetInterval2734 (X Y : ℕ → RealInterval2429) (n : ℕ) : RealInterval2429 :=
  sumJetIntervals2734 (fun j =>
    ((RealInterval2429.point (n.choose j)).mul (X j)).mul (Y (n - j))) (n + 1)

def reciprocalJetInterval2734 (X : ℕ → RealInterval2429) : ℕ → RealInterval2429
  | 0 => (X 0).invPositive
  | n + 1 =>
    ((RealInterval2429.point 0).sub
      (sumJetIntervals2734 (fun j =>
        ((RealInterval2429.point ((n + 1).choose (j + 1))).mul (X (j + 1))).mul
          (reciprocalJetInterval2734 X (n - j))) (n + 1))).mul (X 0).invPositive
termination_by n => n
decreasing_by omega

def exponentialJetInterval2734 (X : ℕ → RealInterval2429)
    (e0 : RealInterval2429) : ℕ → RealInterval2429
  | 0 => e0
  | n + 1 =>
    sumJetIntervals2734 (fun j =>
      ((RealInterval2429.point (n.choose j)).mul (X (j + 1))).mul
        (exponentialJetInterval2734 X e0 (n - j))) (n + 1)
termination_by n => n
decreasing_by omega

theorem iteratedDeriv_reciprocal_general2734 (f : ℝ → ℝ) (n : ℕ) {x : ℝ}
    (hf : ContDiffAt ℝ (n + 1) f x) (hfx : f x ≠ 0) :
    iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x =
      -(∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
        iteratedDeriv (j + 1) f x *
        iteratedDeriv (n - j) (fun y => (f y)⁻¹) x) / f x := by
  have hne : ∀ᶠ y in nhds x, f y ≠ 0 :=
    hf.continuousAt.eventually (eventually_ne_nhds hfx)
  have hid : (fun y => f y * (f y)⁻¹) =ᶠ[nhds x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hne] with y hy
    exact mul_inv_cancel₀ hy
  have hp := iteratedDeriv_fun_mul (n := n + 1) hf (hf.inv hfx)
  rw [hid.iteratedDeriv_eq (n + 1), iteratedDeriv_const, if_neg (by omega)] at hp
  rw [Finset.sum_range_succ'] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul,
    Nat.sub_zero, Nat.add_sub_add_right] at hp
  apply (eq_div_iff hfx).2
  linarith

theorem reciprocalJetInterval_mem2734 (X : ℕ → RealInterval2429)
    (f : ℝ → ℝ) (N : ℕ) {x : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hlo : 0 < (X 0).lo)
    (hX : ∀ j ≤ N, (X j).Mem (iteratedDeriv j f x)) :
    ∀ n ≤ N, (reciprocalJetInterval2734 X n).Mem
      (iteratedDeriv n (fun y => (f y)⁻¹) x) := by
  have hX0 : (X 0).Mem (f x) := by simpa only [iteratedDeriv_zero] using hX 0 (by omega)
  have hfx : f x ≠ 0 := (lt_of_lt_of_le hlo hX0.1).ne'
  have hinv := RealInterval2429.mem_invPositive hlo hX0
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [reciprocalJetInterval2734, iteratedDeriv_zero] using hinv
    | succ m =>
      rw [reciprocalJetInterval2734,
        iteratedDeriv_reciprocal_general2734 f m (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfx]
      have hs := mem_sumJetIntervals2734
        (fun j => ((RealInterval2429.point ((m + 1).choose (j + 1))).mul
          (X (j + 1))).mul (reciprocalJetInterval2734 X (m - j)))
        (fun j => ((m + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) f x *
          iteratedDeriv (m - j) (fun y => (f y)⁻¹) x) (m + 1) (by
          intro j hj
          exact RealInterval2429.mem_mul
            (RealInterval2429.mem_mul (RealInterval2429.point_mem _) (hX (j + 1) (by omega)))
            (ih (m - j) (by omega) (by omega)))
      have hneg := RealInterval2429.mem_sub (RealInterval2429.point_mem 0) hs
      simpa only [zero_sub, div_eq_mul_inv] using RealInterval2429.mem_mul hneg hinv

theorem exponentialJetInterval_mem2734 (X : ℕ → RealInterval2429)
    (e0 : RealInterval2429) (N : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (he0 : e0.Mem (transitionExp2731 x))
    (hX : ∀ j ≤ N, (X j).Mem (iteratedDeriv j transitionPhase2731 x)) :
    ∀ n ≤ N, (exponentialJetInterval2734 X e0 n).Mem
      (iteratedDeriv n transitionExp2731 x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [exponentialJetInterval2734, iteratedDeriv_zero] using he0
    | succ m =>
      rw [exponentialJetInterval2734, iteratedDeriv_transitionExp2731 m hx0 hx1]
      apply mem_sumJetIntervals2734
      intro j hj
      exact RealInterval2429.mem_mul
        (RealInterval2429.mem_mul (RealInterval2429.point_mem _) (hX (j + 1) (by omega)))
        (ih (m - j) (by omega) (by omega))

theorem productJetInterval_mem2734 (X Y : ℕ → RealInterval2429)
    (n : ℕ) (a b : ℕ → ℝ)
    (hX : ∀ j ≤ n, (X j).Mem (a j)) (hY : ∀ j ≤ n, (Y j).Mem (b j)) :
    (productJetInterval2734 X Y n).Mem
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a j * b (n - j)) := by
  apply mem_sumJetIntervals2734
  intro j hj
  exact RealInterval2429.mem_mul
    (RealInterval2429.mem_mul (RealInterval2429.point_mem _) (hX j (by omega)))
    (hY (n - j) (by omega))

def coordinateJetInterval2734 (B : RealInterval2429) (n : ℕ) : RealInterval2429 :=
  if n = 0 then B else RealInterval2429.point (if n = 1 then 1 else 0)

def reflectedCoordinateJetInterval2734 (B : RealInterval2429) (n : ℕ) : RealInterval2429 :=
  if n = 0 then (RealInterval2429.point 1).sub B
  else RealInterval2429.point (if n = 1 then -1 else 0)

def phaseJetInterval2734 (B : RealInterval2429) (n : ℕ) : RealInterval2429 :=
  (reciprocalJetInterval2734 (reflectedCoordinateJetInterval2734 B) n).sub
    (reciprocalJetInterval2734 (coordinateJetInterval2734 B) n)

def seedExpJetInterval2734 (B : RealInterval2429) : ℕ → RealInterval2429 :=
  exponentialJetInterval2734 (phaseJetInterval2734 B) ((phaseJetInterval2734 B 0).exp)

def seedDenominatorJetInterval2734 (B : RealInterval2429) (n : ℕ) : RealInterval2429 :=
  (RealInterval2429.point (if n = 0 then 1 else 0)).add (seedExpJetInterval2734 B n)

def seedTransitionJetInterval2734 (B : RealInterval2429) (n : ℕ) : RealInterval2429 :=
  productJetInterval2734 (seedExpJetInterval2734 B)
    (reciprocalJetInterval2734 (seedDenominatorJetInterval2734 B)) n

theorem coordinateJetInterval_mem2734 (B : RealInterval2429) (n : ℕ) {x : ℝ}
    (hx : B.Mem x) :
    (coordinateJetInterval2734 B n).Mem (iteratedDeriv n (fun y : ℝ => y) x) := by
  by_cases hn : n = 0
  · subst n
    simpa only [coordinateJetInterval2734, if_pos rfl, iteratedDeriv_zero] using hx
  · simp [coordinateJetInterval2734, hn, iteratedDeriv_fun_id,
      RealInterval2429.point, RealInterval2429.Mem]

theorem reflectedCoordinateJetInterval_mem2734 (B : RealInterval2429) (n : ℕ) {x : ℝ}
    (hx : B.Mem x) :
    (reflectedCoordinateJetInterval2734 B n).Mem
      (iteratedDeriv n (fun y : ℝ => 1 - y) x) := by
  by_cases hn : n = 0
  · subst n
    simpa only [reflectedCoordinateJetInterval2734, if_pos rfl, iteratedDeriv_zero] using
      RealInterval2429.mem_sub (RealInterval2429.point_mem 1) hx
  · rw [iteratedDeriv_const_sub (Nat.pos_of_ne_zero hn) 1, iteratedDeriv_neg]
    by_cases hn1 : n = 1 <;>
      simp [reflectedCoordinateJetInterval2734, hn, hn1, iteratedDeriv_fun_id,
        RealInterval2429.point, RealInterval2429.Mem]

theorem phaseJetInterval_mem2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (phaseJetInterval2734 B n).Mem (iteratedDeriv n transitionPhase2731 x) := by
  have hx0 : 0 < x := hlo.trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt hhi
  have hUlo : 0 < (coordinateJetInterval2734 B 0).lo := hlo
  have hVlo : 0 < (reflectedCoordinateJetInterval2734 B 0).lo := by
    change 0 < 1 - B.hi
    linarith
  have hU := reciprocalJetInterval_mem2734 (coordinateJetInterval2734 B)
    (fun y : ℝ => y) n contDiffAt_id hUlo
    (fun j _ => coordinateJetInterval_mem2734 B j hx) n le_rfl
  have hV := reciprocalJetInterval_mem2734 (reflectedCoordinateJetInterval2734 B)
    (fun y : ℝ => 1 - y) n (contDiffAt_const.sub contDiffAt_id) hVlo
    (fun j _ => reflectedCoordinateJetInterval_mem2734 B j hx) n le_rfl
  have hu : ContDiffAt ℝ n (fun y : ℝ => y⁻¹) x := contDiffAt_id.inv hx0.ne'
  have hv : ContDiffAt ℝ n (fun y : ℝ => (1 - y)⁻¹) x :=
    (contDiffAt_const.sub contDiffAt_id).inv (ne_of_gt (sub_pos.mpr hx1))
  have hF : transitionPhase2731 = (fun y : ℝ => (1 - y)⁻¹ - y⁻¹) := by
    funext y
    unfold transitionPhase2731
    ring
  rw [hF, iteratedDeriv_fun_sub hv hu]
  exact RealInterval2429.mem_sub hV hU

theorem seedExpJetInterval_mem2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (seedExpJetInterval2734 B n).Mem (iteratedDeriv n transitionExp2731 x) := by
  have hF0 := phaseJetInterval_mem2734 B 0 hlo hhi hx
  simp only [iteratedDeriv_zero] at hF0
  exact exponentialJetInterval_mem2734 (phaseJetInterval2734 B)
    ((phaseJetInterval2734 B 0).exp) n (hlo.trans_le hx.1) (hx.2.trans_lt hhi)
    (RealInterval2429.mem_exp hF0)
    (fun j _ => phaseJetInterval_mem2734 B j hlo hhi hx) n le_rfl

theorem seedDenominatorJetInterval_mem2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (seedDenominatorJetInterval2734 B n).Mem
      (iteratedDeriv n (fun y => 1 + transitionExp2731 y) x) := by
  have h := RealInterval2429.mem_add (RealInterval2429.point_mem (if n = 0 then 1 else 0))
    (seedExpJetInterval_mem2734 B n hlo hhi hx)
  by_cases hn : n = 0
  · subst n
    simpa only [iteratedDeriv_zero, ite_true] using h
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn) 1]
    simpa only [seedDenominatorJetInterval2734, if_neg hn, zero_add] using h

theorem seedReciprocalJetInterval_mem2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (reciprocalJetInterval2734 (seedDenominatorJetInterval2734 B) n).Mem
      (iteratedDeriv n transitionReciprocal2731 x) := by
  have hdenlo : 0 < (seedDenominatorJetInterval2734 B 0).lo := by
    simp only [seedDenominatorJetInterval2734, seedExpJetInterval2734,
      exponentialJetInterval2734, RealInterval2429.add, RealInterval2429.point,
      RealInterval2429.exp]
    positivity
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => 1 + transitionExp2731 y) x :=
    contDiffAt_const.add (contDiffAt_transitionExp2731 ⊤ (hlo.trans_le hx.1) (hx.2.trans_lt hhi))
  exact reciprocalJetInterval_mem2734 (seedDenominatorJetInterval2734 B)
    (fun y => 1 + transitionExp2731 y) n hf hdenlo
    (fun j _ => seedDenominatorJetInterval_mem2734 B j hlo hhi hx) n le_rfl

theorem seedTransitionJetInterval_mem2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (seedTransitionJetInterval2734 B n).Mem (iteratedDeriv n Real.smoothTransition x) := by
  rw [iteratedDeriv_smoothTransition_product2731 n (hlo.trans_le hx.1) (hx.2.trans_lt hhi)]
  exact productJetInterval_mem2734 (seedExpJetInterval2734 B)
    (reciprocalJetInterval2734 (seedDenominatorJetInterval2734 B)) n
    (fun j => iteratedDeriv j transitionExp2731 x)
    (fun j => iteratedDeriv j transitionReciprocal2731 x)
    (fun j _ => seedExpJetInterval_mem2734 B j hlo hhi hx)
    (fun j _ => seedReciprocalJetInterval_mem2734 B j hlo hhi hx)

theorem norm_iteratedDeriv_le_seedCellJet2734 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    ‖iteratedDeriv n Real.smoothTransition x‖ ≤
      (seedTransitionJetInterval2734 B n).endpointAbsMax := by
  rw [Real.norm_eq_abs]
  exact RealInterval2429.abs_le_endpointAbsMax (seedTransitionJetInterval_mem2734 B n hlo hhi hx)

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
