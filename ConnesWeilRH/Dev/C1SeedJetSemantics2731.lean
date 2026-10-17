import ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Interior identities for the derivative jet used in record 2730.
These identities do not certify the numerical integration or endpoint bounds.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

def transitionPhase2731 (x : ℝ) : ℝ := -x⁻¹ + (1 - x)⁻¹
def transitionExp2731 (x : ℝ) : ℝ := Real.exp (transitionPhase2731 x)
def transitionReciprocal2731 (x : ℝ) : ℝ := (1 + transitionExp2731 x)⁻¹

theorem contDiffAt_transitionPhase2731 (n : ℕ∞) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ContDiffAt ℝ n transitionPhase2731 x := by
  have hi : ContDiffAt ℝ n (fun y : ℝ => y⁻¹) x :=
    contDiffAt_id.inv (ne_of_gt hx0)
  have hj : ContDiffAt ℝ n (fun y : ℝ => (1 - y)⁻¹) x :=
    (contDiffAt_const.sub contDiffAt_id).inv (ne_of_gt (sub_pos.mpr hx1))
  exact hi.neg.add hj

theorem contDiffAt_transitionExp2731 (n : ℕ∞) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ContDiffAt ℝ n transitionExp2731 x :=
  (contDiffAt_transitionPhase2731 n hx0 hx1).exp

theorem contDiffAt_transitionReciprocal2731 (n : ℕ∞) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ContDiffAt ℝ n transitionReciprocal2731 x := by
  exact (contDiffAt_const.add (contDiffAt_transitionExp2731 n hx0 hx1)).inv
    (ne_of_gt (by
      have hpos : 0 < transitionExp2731 x := Real.exp_pos _
      linarith))

theorem smoothTransition_eq_exp_mul_reciprocal2731 {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.smoothTransition x = transitionExp2731 x * transitionReciprocal2731 x := by
  have ha : Real.exp (-x⁻¹) ≠ 0 := Real.exp_ne_zero _
  have hb : Real.exp (-(1 - x)⁻¹) ≠ 0 := Real.exp_ne_zero _
  have hab : Real.exp (-x⁻¹) + Real.exp (-(1 - x)⁻¹) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have he : transitionExp2731 x =
      Real.exp (-x⁻¹) / Real.exp (-(1 - x)⁻¹) := by
    unfold transitionExp2731 transitionPhase2731
    rw [show -x⁻¹ + (1 - x)⁻¹ = -x⁻¹ - (-(1 - x)⁻¹) by ring, Real.exp_sub]
  have hden : 1 + transitionExp2731 x ≠ 0 :=
    ne_of_gt (by
      have hpos : 0 < transitionExp2731 x := Real.exp_pos _
      linarith)
  unfold Real.smoothTransition transitionReciprocal2731
  simp only [expNegInvGlue, if_neg (not_le.mpr hx0),
    if_neg (not_le.mpr (sub_pos.mpr hx1))]
  rw [he]
  field_simp
  ring

theorem iteratedDeriv_smoothTransition_product2731 (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv n Real.smoothTransition x =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv j transitionExp2731 x *
        iteratedDeriv (n - j) transitionReciprocal2731 x := by
  have hlocal : Real.smoothTransition =ᶠ[nhds x]
      (fun y => transitionExp2731 y * transitionReciprocal2731 y) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact smoothTransition_eq_exp_mul_reciprocal2731 hy.1 hy.2
  rw [hlocal.iteratedDeriv_eq n]
  exact iteratedDeriv_fun_mul (contDiffAt_transitionExp2731 n hx0 hx1)
    (contDiffAt_transitionReciprocal2731 n hx0 hx1)

theorem deriv_transitionExp2731 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    deriv transitionExp2731 x =
      deriv transitionPhase2731 x * transitionExp2731 x := by
  have h := ((contDiffAt_transitionPhase2731 1 hx0 hx1).differentiableAt
    (by norm_num)).hasDerivAt.exp
  simpa only [transitionExp2731, mul_comm] using h.deriv

theorem iteratedDeriv_transitionExp2731 (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv (n + 1) transitionExp2731 x =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv (j + 1) transitionPhase2731 x *
        iteratedDeriv (n - j) transitionExp2731 x := by
  have hlocal : deriv transitionExp2731 =ᶠ[nhds x]
      (fun y => deriv transitionPhase2731 y * transitionExp2731 y) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact deriv_transitionExp2731 hy.1 hy.2
  have hFd : ContDiffAt ℝ n (deriv transitionPhase2731) x :=
    (contDiffAt_transitionPhase2731 (n + 1) hx0 hx1).derivWithin (by simp)
  rw [iteratedDeriv_succ', hlocal.iteratedDeriv_eq n]
  simpa only [← iteratedDeriv_succ'] using
    iteratedDeriv_fun_mul hFd (contDiffAt_transitionExp2731 n hx0 hx1)

theorem iteratedDeriv_reciprocal_product2731 (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      iteratedDeriv j (fun y => 1 + transitionExp2731 y) x *
      iteratedDeriv (n - j) transitionReciprocal2731 x) = 0 := by
  have hid : (fun y => (1 + transitionExp2731 y) * transitionReciprocal2731 y) =
      (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    exact mul_inv_cancel₀ (ne_of_gt (by
      have hpos : 0 < transitionExp2731 y := Real.exp_pos _
      linarith))
  have hp := iteratedDeriv_fun_mul (f := fun y : ℝ => 1 + transitionExp2731 y)
    (contDiffAt_const.add (contDiffAt_transitionExp2731 n hx0 hx1))
    (contDiffAt_transitionReciprocal2731 n hx0 hx1)
  rw [hid, iteratedDeriv_const, if_neg (ne_of_gt hn)] at hp
  exact hp.symm

theorem iteratedDeriv_transitionReciprocal2731 (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv (n + 1) transitionReciprocal2731 x =
      -(∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
        iteratedDeriv (j + 1) transitionExp2731 x *
        iteratedDeriv (n - j) transitionReciprocal2731 x) /
        (1 + transitionExp2731 x) := by
  have hs := iteratedDeriv_reciprocal_product2731 (n + 1) (by omega) hx0 hx1
  rw [Finset.sum_range_succ'] at hs
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul,
    Nat.sub_zero, Nat.add_sub_add_right, Nat.succ_eq_add_one,
    iteratedDeriv_const_add (Nat.succ_pos _)] at hs
  have hden : 1 + transitionExp2731 x ≠ 0 := by
    have hpos : 0 < transitionExp2731 x := Real.exp_pos _
    linarith
  apply (eq_div_iff hden).2
  linarith

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
