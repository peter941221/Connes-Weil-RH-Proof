/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C3' carrier transport: the prime-cell phase law

Record 1800. The pinned head of the orbit-sum geometry (record 1799) carries
the carrier `exp(-iγx)`. Same-carrier pair profiles transport the carrier
exactly, which turns the measured phase law of record 1799 (quasiperiodic
prime cells) into a theorem:

* `carrierPair_transport`: `(Uᵧ)* ⋆ (Vᵧ) = carrierExp γ x · (u* ⋆ v)`;
* `convolutionSquare_carrier_apply`: the square-channel special case;
* `square_pair_sum_carrier`: `F(y) + F(-y) = 2 · Re[carrierExp γ y · G(y)]`,
  the exact per-cell phase form of the Weil pair sum;
* `finitePrimeTerm_carrierSquare`: the finite prime term of the carrier
  square reads `Λ(n) · 2/√n · Re[carrierExp γ (log n) · G(log n)]`.

These reduce the C3' two-span signed estimate to an envelope-level
inequality: the phase structure is exact algebra, not a family artifact.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3CarrierTransport

open MeasureTheory
open scoped ComplexConjugate
open scoped ContDiff
open ConnesWeilRH.Source.C1SameOwnerWeil
open ConnesWeilRH.Source.CC20YoshidaConvolution
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-- The carrier phase in the canonical single-cast form:
`carrierExp γ x = e^{-iγx}`. -/
noncomputable def carrierExp (γ x : Real) : Complex :=
  Complex.exp (Complex.ofReal (-γ * x) * Complex.I)

theorem conj_carrierExp (γ x : Real) :
    conj (carrierExp γ x) = carrierExp γ (-x) := by
  unfold carrierExp
  rw [← Complex.exp_conj, map_mul (starRingEnd Complex),
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  have h1 : (-γ * x) = -(γ * x) := by ring
  rw [h1, Complex.ofReal_neg]
  ring

/-- Carrier modulation of a compact log test by `e^{-iγx}`. -/
noncomputable def carrierModulate (γ : Real) (f : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => carrierExp γ x * f.test x
  have hcompact : HasCompactSupport raw := f.compactSupport.mul_left
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    have harg : ContDiff ℝ ∞ (fun x : ℝ => Complex.ofReal (-γ * x)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    have hcarrier : ContDiff ℝ ∞
        (fun x : ℝ => Complex.ofReal (-γ * x) * Complex.I) :=
      harg.mul contDiff_const
    exact hcarrier.cexp.mul (f.test.smooth ⊤)
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem carrierModulate_apply (γ : Real) (f : CompactLogTest) (x : ℝ) :
    (carrierModulate γ f).test x = carrierExp γ x * f.test x :=
  rfl

/-- **Carrier transport (C3' Lemma 1)**: a same-carrier pair test transports
the carrier unchanged — the phase structure of record 1799 is exact
algebra. -/
theorem carrierPair_transport (γ : Real) (u v : CompactLogTest) (x : ℝ) :
    ((carrierModulate γ u).involution.convolution
        (carrierModulate γ v)).test x
      = carrierExp γ x * ((u.involution.convolution v).test x) := by
  have hsplit : ∀ t : ℝ, carrierExp γ (x - t)
      = carrierExp γ x * carrierExp γ (-t) := by
    intro t
    dsimp only [carrierExp]
    rw [← Complex.exp_add]
    congr 1
    rw [← add_mul]
    congr 1
    rw [← Complex.ofReal_add]
    ring
  have hcancel : ∀ t : ℝ, carrierExp γ t * carrierExp γ (-t) = 1 := by
    intro t
    dsimp only [carrierExp]
    rw [← Complex.exp_add, ← add_mul]
    simp
  have hpt : ∀ t : ℝ,
      star (carrierExp γ (-t) * u.test (-t)) *
        (carrierExp γ (x - t) * v.test (x - t))
      = carrierExp γ x * (star (u.test (-t)) * v.test (x - t)) := by
    intro t
    simp only [Complex.star_def]
    rw [map_mul (starRingEnd Complex), conj_carrierExp, neg_neg, hsplit]
    linear_combination hcancel t * (carrierExp γ x
      * conj (u.test (-t)) * v.test (x - t))
  simp only [CompactLogTest.involution_apply, CompactLogTest.convolution_apply,
    carrierModulate_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]

/-- The square channel of a carrier-modulated test carries the same
carrier. -/
theorem convolutionSquare_carrier_apply (γ : Real) (u : CompactLogTest) (x : ℝ) :
    (carrierModulate γ u).convolutionSquare.test x
      = carrierExp γ x * u.convolutionSquare.test x :=
  carrierPair_transport γ u u x

/-- **Per-cell phase form (C3' Lemma 2)**: the Weil pair sum of the carrier
square collapses to one real phase readout, `2 · Re[e^{-iγy} · G(y)]`, with
`G = u* ⋆ u` the envelope square. -/
theorem square_pair_sum_carrier (γ : Real) (u : CompactLogTest) (y : ℝ) :
    (carrierModulate γ u).convolutionSquare.test y
      + (carrierModulate γ u).convolutionSquare.test (-y)
      = (2 : ℂ) *
          (carrierExp γ y * u.convolutionSquare.test y).re := by
  rw [convolutionSquare_carrier_apply, convolutionSquare_carrier_apply,
    CompactLogTest.convolutionSquare_neg, Complex.star_def]
  have hneg : carrierExp γ (-y) = conj (carrierExp γ y) :=
    (conj_carrierExp γ y).symm
  rw [hneg, ← map_mul (starRingEnd Complex)]
  simpa using Complex.add_conj (carrierExp γ y * u.convolutionSquare.test y)

/-- **Prime-cell phase law (C3' Lemma 3)**: the finite prime term of the
carrier square is the envelope cell dressed by the carrier phase
`e^{-iγ log n}`. This is the exact form of the quasiperiodic prime balance
measured in record 1799 (law W2). -/
theorem finitePrimeTerm_carrierSquare (γ : Real) (u : CompactLogTest) (n : ℕ) :
    finitePrimeTerm ((carrierModulate γ u).convolutionSquare) n
      = (ArithmeticFunction.vonMangoldt n : Real) * (2 / Real.sqrt (n : Real)) *
          (carrierExp γ (Real.log n) * u.convolutionSquare.test
            (Real.log n)).re := by
  rw [finitePrimeTerm, finitePrimeTermComplex, square_pair_sum_carrier]
  have hreal : (((ArithmeticFunction.vonMangoldt n : Real) : Complex) *
      (((1 / Real.sqrt (n : Real) : Real) : Complex) *
        ((2 : ℂ) * (carrierExp γ (Real.log n) *
          u.convolutionSquare.test (Real.log n)).re))).re
      = (ArithmeticFunction.vonMangoldt n : Real)
          * (1 / Real.sqrt (n : Real))
          * (2 * (carrierExp γ (Real.log n) *
            u.convolutionSquare.test (Real.log n)).re) := by
    rw [Complex.mul_re, Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
    ring
  rw [hreal]
  ring

end C1C3CarrierTransport
end Dev
end ConnesWeilRH
