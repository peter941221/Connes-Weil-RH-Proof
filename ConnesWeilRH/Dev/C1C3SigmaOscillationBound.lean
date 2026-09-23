/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3SigmaKernel

/-!
# C3' sigma oscillation bound

The reciprocal-series representation of `c3Sigma` gives a quantitative
same-tail modulus of continuity.  If both heights stay at least `R` away from
zero on the imaginary scale, then the sigma difference is at most
`2 * |xi - eta| / R`.  This is the analytic derivative-scale input for the
carrier-square remainder; it does not by itself bound that remainder or the
prime budget.
-/

namespace ConnesWeilRH
namespace Dev

open Complex
open Filter
open scoped Topology
open scoped BigOperators

noncomputable def c3SigmaVerticalPoint (xi : Real) (n : Nat) : Complex :=
  (((n : Real) + 1 / 4 : Real) : Complex) -
    ((xi / 2 : Real) : Complex) * Complex.I

noncomputable def c3SigmaOscillationTerm
    (xi eta : Real) (n : Nat) : Complex :=
  (c3SigmaVerticalPoint xi n)⁻¹ - (c3SigmaVerticalPoint eta n)⁻¹

private noncomputable def c3SigmaAnchorDifferenceTerm
    (xi : Real) (n : Nat) : Complex :=
  (((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) +
        (((1 / 4 : Real) : Complex) - (xi : Complex) * Complex.I / 2))⁻¹) -
    (((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹)

private theorem summable_c3SigmaAnchorDifferenceTerm (xi : Real) :
    Summable (fun n : Nat => c3SigmaAnchorDifferenceTerm xi n) := by
  let z : Complex :=
    ((1 / 4 : Real) : Complex) - (xi : Complex) * Complex.I / 2
  have hz : 0 < z.re := by simp [z, Complex.mul_re]
  have hz0 : 0 < (((1 / 4 : Real) : Complex).re) := by norm_num
  have hxi :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz
  have hzero :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hz0
  refine (hxi.sub hzero).congr ?_
  intro n
  simp only [c3SigmaAnchorDifferenceTerm, z]

private theorem summable_c3SigmaOscillationTerm (xi eta : Real) :
    Summable (fun n : Nat => c3SigmaOscillationTerm xi eta n) := by
  let zxi : Complex :=
    ((1 / 4 : Real) : Complex) - (xi : Complex) * Complex.I / 2
  let zeta : Complex :=
    ((1 / 4 : Real) : Complex) - (eta : Complex) * Complex.I / 2
  have hzxi : 0 < zxi.re := by simp [zxi, Complex.mul_re]
  have hzeta : 0 < zeta.re := by simp [zeta, Complex.mul_re]
  have hxi :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzxi
  have heta :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries hzeta
  refine (heta.sub hxi).congr ?_
  intro n
  simp only [c3SigmaOscillationTerm, c3SigmaVerticalPoint, zxi, zeta]
  push_cast
  ring

/-- Difference form of the sigma reciprocal series: the anchor terms cancel,
leaving only the same-owner vertical reciprocal difference. -/
theorem c3Sigma_sub_eq_re_tsum_oscillation
    (xi eta : Real) :
    c3Sigma xi - c3Sigma eta =
      (∑' n : Nat, c3SigmaOscillationTerm xi eta n).re := by
  have hxi := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries xi
  have heta := c3Sigma_sub_zero_eq_neg_re_reciprocalDifferenceSeries eta
  have hdxi := summable_c3SigmaAnchorDifferenceTerm xi
  have hdeta := summable_c3SigmaAnchorDifferenceTerm eta
  have hosc := summable_c3SigmaOscillationTerm xi eta
  have hsub :
      (∑' n : Nat,
        (c3SigmaAnchorDifferenceTerm eta n -
          c3SigmaAnchorDifferenceTerm xi n)) =
        (∑' n : Nat, c3SigmaAnchorDifferenceTerm eta n) -
          (∑' n : Nat, c3SigmaAnchorDifferenceTerm xi n) :=
    hdeta.tsum_sub hdxi
  have hxiTerm (n : Nat) :
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) +
            (((1 / 4 : Real) : Complex) -
              (xi : Complex) * Complex.I / 2))⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹) =
        c3SigmaAnchorDifferenceTerm xi n := by
    simp [c3SigmaAnchorDifferenceTerm]
  have hetaTerm (n : Nat) :
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) +
            (((1 / 4 : Real) : Complex) -
              (eta : Complex) * Complex.I / 2))⁻¹) -
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + ((1 / 4 : Real) : Complex))⁻¹) =
        c3SigmaAnchorDifferenceTerm eta n := by
    simp [c3SigmaAnchorDifferenceTerm]
  calc
    c3Sigma xi - c3Sigma eta =
        (c3Sigma xi - c3Sigma 0) - (c3Sigma eta - c3Sigma 0) := by ring
    _ = -((∑' n : Nat, c3SigmaAnchorDifferenceTerm xi n).re) +
        (∑' n : Nat, c3SigmaAnchorDifferenceTerm eta n).re := by
          rw [hxi, heta]
          rw [tsum_congr hxiTerm, tsum_congr hetaTerm]
          ring
    _ = ((∑' n : Nat, c3SigmaAnchorDifferenceTerm eta n) -
          (∑' n : Nat, c3SigmaAnchorDifferenceTerm xi n)).re := by
          rw [Complex.sub_re]
          ring
    _ = ((∑' n : Nat,
          (c3SigmaAnchorDifferenceTerm eta n -
            c3SigmaAnchorDifferenceTerm xi n)).re) := by
          rw [← hsub]
    _ = (∑' n : Nat, c3SigmaOscillationTerm xi eta n).re := by
          have hdiff (n : Nat) :
              c3SigmaAnchorDifferenceTerm eta n -
                  c3SigmaAnchorDifferenceTerm xi n =
                c3SigmaOscillationTerm xi eta n := by
            simp only [c3SigmaAnchorDifferenceTerm, c3SigmaOscillationTerm,
              c3SigmaVerticalPoint]
            push_cast
            ring
          calc
            ((∑' n : Nat,
                (c3SigmaAnchorDifferenceTerm eta n -
                  c3SigmaAnchorDifferenceTerm xi n)).re) =
                (∑' n : Nat, c3SigmaOscillationTerm xi eta n).re := by
                  congr 1
                  apply tsum_congr
                  exact hdiff

private theorem hasSum_c3Sigma_telescope {c : Real} (hc : 1 ≤ c) :
    HasSum (fun n : Nat =>
      ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹) c⁻¹ := by
  have hnonneg : ∀ n : Nat,
      0 ≤ ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹ := by
    intro n
    have h1 : 0 < (n : Real) + c := by positivity
    have h2 : 0 < (n : Real) + c + 1 := by positivity
    have heq : ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹ =
        1 / (((n : Real) + c) * ((n : Real) + c + 1)) := by
      field_simp
      ring
    rw [heq]
    positivity
  have hpartial : ∀ N : Nat,
      Finset.sum (Finset.range N) (fun n : Nat =>
        ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹) =
          c⁻¹ - ((N : Real) + c)⁻¹ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have hinv : Tendsto (fun N : Nat => ((N : Real) + c)⁻¹) atTop
      (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat =>
        ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹))
      atTop (nhds c⁻¹) := by
    have heq : (fun N : Nat =>
        Finset.sum (Finset.range N) (fun n : Nat =>
          ((n : Real) + c)⁻¹ - ((n : Real) + c + 1)⁻¹)) =
        fun N : Nat => c⁻¹ - ((N : Real) + c)⁻¹ := by
      funext N
      exact hpartial N
    rw [heq]
    simpa using (tendsto_const_nhds.sub hinv)
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg c⁻¹).mpr hlim

private theorem c3Sigma_quadraticMajorant_le_telescope {R : Real}
    (hR : 1 ≤ R) (n : Nat) :
    (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹ ≤
      4 * (((n : Real) + (R + 1 / 4))⁻¹ -
        ((n : Real) + (R + 1 / 4) + 1)⁻¹) := by
  let x : Real := (n : Real) + 1 / 4 + R
  have hx : 1 ≤ x := by
    have hn : (0 : Real) ≤ (n : Real) := by positivity
    dsimp [x]
    nlinarith [hn, hR]
  have hq : 0 < ((n : Real) + 1 / 4) ^ 2 + R ^ 2 := by positivity
  have hxpos : 0 < x := by linarith
  have hquad : x ^ 2 / 2 ≤ ((n : Real) + 1 / 4) ^ 2 + R ^ 2 := by
    dsimp [x]
    nlinarith [sq_nonneg ((n : Real) + 1 / 4 - R)]
  have hinv : (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹ ≤
      (x ^ 2 / 2)⁻¹ := (inv_le_inv₀ hq (by positivity)).2 hquad
  have hrewrite : (x ^ 2 / 2)⁻¹ = 2 * x⁻¹ ^ 2 := by
    field_simp <;> ring
  have htelescoping : 2 * x⁻¹ ^ 2 ≤
      4 * (x⁻¹ - (x + 1)⁻¹) := by
    have hxplus : 0 < x + 1 := by linarith
    field_simp <;> nlinarith [hx]
  calc
    (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹ ≤ (x ^ 2 / 2)⁻¹ := hinv
    _ = 2 * x⁻¹ ^ 2 := hrewrite
    _ ≤ 4 * (x⁻¹ - (x + 1)⁻¹) := htelescoping
    _ = 4 * (((n : Real) + (R + 1 / 4))⁻¹ -
          ((n : Real) + (R + 1 / 4) + 1)⁻¹) := by
          congr 1
          simp [x, add_assoc, add_comm, add_left_comm]

private theorem summable_c3Sigma_quadraticMajorant {R : Real}
    (hR : 1 ≤ R) :
    Summable (fun n : Nat =>
      (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹) := by
  let c : Real := R + 1 / 4
  have htel := hasSum_c3Sigma_telescope (c := c) (by dsimp [c]; linarith)
  have hupper := htel.summable.mul_left 4
  apply hupper.of_nonneg_of_le (fun _ => by positivity)
  intro n
  simpa [c] using c3Sigma_quadraticMajorant_le_telescope hR n

private theorem tsum_c3Sigma_quadraticMajorant_le {R : Real}
    (hR : 1 ≤ R) :
    (∑' n : Nat, (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹) ≤ 4 / R := by
  let c : Real := R + 1 / 4
  have htel := hasSum_c3Sigma_telescope (c := c) (by dsimp [c]; linarith)
  have hmajorant := summable_c3Sigma_quadraticMajorant hR
  have hupper := htel.summable.mul_left 4
  calc
    (∑' n : Nat, (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹) ≤
        ∑' n : Nat, 4 * (((n : Real) + c)⁻¹ -
          ((n : Real) + c + 1)⁻¹) := by
            apply hmajorant.tsum_le_tsum
              (fun n => by simpa [c] using
                c3Sigma_quadraticMajorant_le_telescope hR n)
              hupper
    _ = 4 * c⁻¹ := by rw [tsum_mul_left, htel.tsum_eq]
    _ ≤ 4 / R := by
      have hRpos : 0 < R := by linarith
      have hc : R ≤ c := by dsimp [c]; linarith
      have hcpos : 0 < c := by linarith
      have hinv : c⁻¹ ≤ R⁻¹ := (inv_le_inv₀ hcpos hRpos).2 hc
      simpa [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : Real) ≤ 4))

private theorem norm_c3SigmaOscillationTerm_le
    {R xi eta : Real} (hR : 1 ≤ R)
    (hxi : R ≤ |xi| / 2) (heta : R ≤ |eta| / 2) (n : Nat) :
    ‖c3SigmaOscillationTerm xi eta n‖ ≤
      (|xi - eta| / 2) * (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹ := by
  let A : Complex := c3SigmaVerticalPoint xi n
  let B : Complex := c3SigmaVerticalPoint eta n
  let q : Real := ((n : Real) + 1 / 4) ^ 2 + R ^ 2
  have hR0 : 0 ≤ R := by linarith
  have hxiAbs : R ≤ |xi / 2| := by simpa [abs_div] using hxi
  have hetaAbs : R ≤ |eta / 2| := by simpa [abs_div] using heta
  have hxiSq : R ^ 2 ≤ (xi / 2) ^ 2 := by
    have h := (sq_le_sq₀ hR0 (abs_nonneg (xi / 2))).2 hxiAbs
    simpa [sq_abs] using h
  have hetaSq : R ^ 2 ≤ (eta / 2) ^ 2 := by
    have h := (sq_le_sq₀ hR0 (abs_nonneg (eta / 2))).2 hetaAbs
    simpa [sq_abs] using h
  have hnormSq (v : Real) :
      ‖c3SigmaVerticalPoint v n‖ ^ 2 =
        ((n : Real) + 1 / 4) ^ 2 + (v / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [c3SigmaVerticalPoint, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hAq : q ≤ ‖A‖ ^ 2 := by
    dsimp [q, A]
    rw [hnormSq]
    nlinarith [hxiSq]
  have hBq : q ≤ ‖B‖ ^ 2 := by
    dsimp [q, B]
    rw [hnormSq]
    nlinarith [hetaSq]
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hApos : 0 < ‖A‖ := by nlinarith [hAq, norm_nonneg A]
  have hBpos : 0 < ‖B‖ := by nlinarith [hBq, norm_nonneg B]
  have hAne : A ≠ 0 := norm_pos_iff.mp hApos
  have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
  have hprodSq : q ^ 2 ≤ (‖A‖ * ‖B‖) ^ 2 := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 :=
        mul_le_mul hAq hBq (le_of_lt hqpos) (sq_nonneg _)
      _ = (‖A‖ * ‖B‖) ^ 2 := by ring
  have hprod : q ≤ ‖A‖ * ‖B‖ := by
    have hnonneg : 0 ≤ ‖A‖ * ‖B‖ := by positivity
    nlinarith [hprodSq]
  have hprodpos : 0 < ‖A‖ * ‖B‖ := by linarith
  have hfield : A⁻¹ - B⁻¹ = (B - A) / (A * B) := by
    field_simp [hAne, hBne] <;> ring
  have hdiff : B - A = (((xi - eta) / 2 : Real) : Complex) * Complex.I := by
    dsimp [A, B, c3SigmaVerticalPoint]
    push_cast
    ring
  have hnum : ‖B - A‖ = |xi - eta| / 2 := by
    calc
      ‖B - A‖ = ‖(((xi - eta) / 2 : Real) : Complex)‖ := by
        rw [hdiff, norm_mul]
        simp
      _ = |xi - eta| / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_pos (by norm_num : (0 : Real) < 2)]
  have hinv : (‖A‖ * ‖B‖)⁻¹ ≤ q⁻¹ :=
    (inv_le_inv₀ hprodpos hqpos).2 hprod
  change ‖A⁻¹ - B⁻¹‖ ≤ (|xi - eta| / 2) * q⁻¹
  rw [hfield, norm_div, norm_mul, hnum]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)

/-- On a common high-frequency tail, `c3Sigma` has the explicit
`O(1/R)` oscillation bound needed for the carrier-shift remainder. -/
theorem abs_c3Sigma_sub_le_of_height_lower
    {R xi eta : Real} (hR : 1 ≤ R)
    (hxi : R ≤ |xi| / 2) (heta : R ≤ |eta| / 2) :
    |c3Sigma xi - c3Sigma eta| ≤ 2 * |xi - eta| / R := by
  have hosc := summable_c3SigmaOscillationTerm xi eta
  have hmajorant := summable_c3Sigma_quadraticMajorant hR
  have hupper := hmajorant.mul_left (|xi - eta| / 2)
  rw [c3Sigma_sub_eq_re_tsum_oscillation]
  calc
    |(∑' n : Nat, c3SigmaOscillationTerm xi eta n).re| ≤
        ‖∑' n : Nat, c3SigmaOscillationTerm xi eta n‖ :=
          Complex.abs_re_le_norm _
    _ ≤ ∑' n : Nat, ‖c3SigmaOscillationTerm xi eta n‖ :=
          norm_tsum_le_tsum_norm hosc.norm
    _ ≤ ∑' n : Nat,
          (|xi - eta| / 2) * (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹ :=
          hosc.norm.tsum_le_tsum
            (fun n => norm_c3SigmaOscillationTerm_le hR hxi heta n) hupper
    _ = (|xi - eta| / 2) *
          (∑' n : Nat, (((n : Real) + 1 / 4) ^ 2 + R ^ 2)⁻¹) := by
          rw [tsum_mul_left]
    _ ≤ (|xi - eta| / 2) * (4 / R) :=
          mul_le_mul_of_nonneg_left
            (tsum_c3Sigma_quadraticMajorant_le hR) (by positivity)
    _ = 2 * |xi - eta| / R := by ring

end Dev
end ConnesWeilRH
