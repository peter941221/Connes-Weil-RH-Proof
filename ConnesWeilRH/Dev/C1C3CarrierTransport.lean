/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2SpanProfileMatrix

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
open ConnesWeilRH.Source.C1P2BilateralProfile
open ConnesWeilRH.Source.C1GateMatrixRepresentation
open ConnesWeilRH.Source.C1LocalConfigurationDomination
open ConnesWeilRH.Source.C1OrbitWindowSemiLocalGate
open ConnesWeilRH.Source.C1SameOwnerWeil
open ConnesWeilRH.Source.CC20YoshidaConvolution
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open Matrix

/-- The carrier phase in the canonical single-cast form:
`carrierExp γ x = e^{-iγx}`. -/
noncomputable def carrierExp (γ x : Real) : Complex :=
  Complex.exp (Complex.ofReal (-γ * x) * Complex.I)

theorem carrierExp_mul_re (γ x : Real) (z : Complex) :
    (carrierExp γ x * z).re =
      Real.cos (γ * x) * z.re + Real.sin (γ * x) * z.im := by
  unfold carrierExp
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  have harg : -γ * x = -(γ * x) := by ring
  rw [harg, Real.cos_neg, Real.sin_neg]
  ring

theorem carrierExp_ne_zero (γ x : Real) :
    carrierExp γ x ≠ 0 := by
  unfold carrierExp
  exact Complex.exp_ne_zero _

theorem carrierExp_norm (γ x : Real) :
    ‖carrierExp γ x‖ = 1 := by
  unfold carrierExp
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

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

theorem carrierModulate_support_eq (γ : Real) (f : CompactLogTest) :
    Function.support (carrierModulate γ f).test = Function.support f.test := by
  ext x
  rw [Function.mem_support, Function.mem_support, carrierModulate_apply]
  constructor
  · intro h hx
    apply h
    simp [hx]
  · intro h
    exact mul_ne_zero (carrierExp_ne_zero γ x) h

theorem carrierModulate_norm_apply (γ : Real) (f : CompactLogTest) (x : Real) :
    ‖(carrierModulate γ f).test x‖ = ‖f.test x‖ := by
  rw [carrierModulate_apply, norm_mul, carrierExp_norm, one_mul]

theorem carrierExp_zero (γ : Real) :
    carrierExp γ 0 = 1 := by
  unfold carrierExp
  simp

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

theorem convolutionSquare_carrier_norm_apply
    (γ : Real) (u : CompactLogTest) (x : Real) :
    ‖(carrierModulate γ u).convolutionSquare.test x‖ =
      ‖u.convolutionSquare.test x‖ := by
  rw [convolutionSquare_carrier_apply, norm_mul, carrierExp_norm, one_mul]

theorem convolutionSquare_carrier_zero_eq
    (γ : Real) (u : CompactLogTest) :
    (carrierModulate γ u).convolutionSquare.test 0 =
      u.convolutionSquare.test 0 := by
  rw [convolutionSquare_carrier_apply, carrierExp_zero, one_mul]

theorem convolutionSquare_carrier_zero_eq_integral_normSq
    (γ : Real) (u : CompactLogTest) :
    (carrierModulate γ u).convolutionSquare.test 0 =
      ∫ t : Real, Complex.normSq (u.test t) := by
  rw [convolutionSquare_carrier_zero_eq]
  exact u.convolutionSquare_zero_eq_integral_normSq

theorem convolutionSquare_carrier_zero_re_nonnegative
    (γ : Real) (u : CompactLogTest) :
    0 ≤ ((carrierModulate γ u).convolutionSquare.test 0).re := by
  rw [convolutionSquare_carrier_zero_eq]
  exact u.convolutionSquare_zero_re_nonnegative

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

theorem archimedeanNumerator_carrierSquare
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanNumerator (carrierModulate γ u).convolutionSquare y =
      Complex.ofReal (Real.exp (y / 2)) *
          ((2 * (carrierExp γ y * u.convolutionSquare.test y).re : Real) : Complex) -
        2 * u.convolutionSquare.test 0 := by
  unfold archimedeanNumerator
  rw [square_pair_sum_carrier, convolutionSquare_carrier_zero_eq]
  simp only [Complex.ofRealCLM_apply]
  norm_num

theorem archimedeanNumerator_carrierSquare_phase_split
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanNumerator (carrierModulate γ u).convolutionSquare y =
      Complex.ofReal (Real.exp (y / 2)) *
          ((2 * (Real.cos (γ * y) * (u.convolutionSquare.test y).re +
              Real.sin (γ * y) * (u.convolutionSquare.test y).im) : Real) : Complex) -
        2 * u.convolutionSquare.test 0 := by
  rw [archimedeanNumerator_carrierSquare, carrierExp_mul_re]

noncomputable def carrierSquareArchimedeanNumeratorPhase
    (γ : Real) (u : CompactLogTest) (y : Real) : Complex :=
  Complex.ofReal (Real.exp (y / 2)) *
      ((2 * (Real.cos (γ * y) * (u.convolutionSquare.test y).re +
          Real.sin (γ * y) * (u.convolutionSquare.test y).im) : Real) : Complex) -
    2 * u.convolutionSquare.test 0

theorem archimedeanNumerator_carrierSquare_eq_phaseNumerator
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanNumerator (carrierModulate γ u).convolutionSquare y =
      carrierSquareArchimedeanNumeratorPhase γ u y := by
  exact archimedeanNumerator_carrierSquare_phase_split γ u y

theorem archimedeanNumerator_carrierPair
    (γ : Real) (u v : CompactLogTest) (y : Real) :
    archimedeanNumerator
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) y =
      Complex.ofReal (Real.exp (y / 2)) *
          (carrierExp γ y * (u.involution.convolution v).test y +
            carrierExp γ (-y) * (u.involution.convolution v).test (-y)) -
        2 * (u.involution.convolution v).test 0 := by
  unfold archimedeanNumerator
  have hy := carrierPair_transport γ u v y
  have hny := carrierPair_transport γ u v (-y)
  have h0 := carrierPair_transport γ u v 0
  rw [hy, hny, h0, carrierExp_zero]
  simp only [Complex.ofRealCLM_apply, one_mul]

noncomputable def carrierPairArchimedeanNumeratorPhase
    (γ : Real) (u v : CompactLogTest) (y : Real) : Complex :=
  Complex.ofReal (Real.exp (y / 2)) *
      ((carrierExp γ y * (u.involution.convolution v).test y) +
        (carrierExp γ (-y) * (u.involution.convolution v).test (-y))) -
    2 * (u.involution.convolution v).test 0

theorem archimedeanNumerator_carrierPair_eq_phaseNumerator
    (γ : Real) (u v : CompactLogTest) (y : Real) :
    archimedeanNumerator
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) y =
      carrierPairArchimedeanNumeratorPhase γ u v y := by
  exact archimedeanNumerator_carrierPair γ u v y

theorem archimedeanIntegrand_carrierPair
    (γ : Real) (u v : CompactLogTest) (y : Real) :
    archimedeanIntegrand
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) y =
      (Complex.ofReal (Real.exp (y / 2)) *
          (carrierExp γ y * (u.involution.convolution v).test y +
            carrierExp γ (-y) * (u.involution.convolution v).test (-y)) -
        2 * (u.involution.convolution v).test 0) /
        (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex) := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_carrierPair]

theorem archimedeanTerm_carrierPair
    (γ : Real) (u v : CompactLogTest) :
    archimedeanTerm
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          (u.involution.convolution v).test 0 +
        ∫ y in Set.Ioi (0 : Real),
          (Complex.ofReal (Real.exp (y / 2)) *
              (carrierExp γ y * (u.involution.convolution v).test y +
                carrierExp γ (-y) * (u.involution.convolution v).test (-y)) -
            2 * (u.involution.convolution v).test 0) /
            (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)).re := by
  unfold archimedeanTerm
  rw [carrierPair_transport γ u v 0, carrierExp_zero]
  simp only [one_mul]
  rw [show (fun y => archimedeanIntegrand
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) y) =
      (fun y =>
        (Complex.ofReal (Real.exp (y / 2)) *
            (carrierExp γ y * (u.involution.convolution v).test y +
              carrierExp γ (-y) * (u.involution.convolution v).test (-y)) -
          2 * (u.involution.convolution v).test 0) /
          (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)) by
    funext y
    exact archimedeanIntegrand_carrierPair γ u v y]

theorem archimedeanIntegrand_carrierSquare
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanIntegrand (carrierModulate γ u).convolutionSquare y =
      (Complex.ofReal (Real.exp (y / 2)) *
          ((2 * (carrierExp γ y * u.convolutionSquare.test y).re : Real) : Complex) -
        2 * u.convolutionSquare.test 0) /
        (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex) := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_carrierSquare]

theorem archimedeanIntegrand_carrierSquare_phase_split
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanIntegrand (carrierModulate γ u).convolutionSquare y =
      (Complex.ofReal (Real.exp (y / 2)) *
          ((2 * (Real.cos (γ * y) * (u.convolutionSquare.test y).re +
              Real.sin (γ * y) * (u.convolutionSquare.test y).im) : Real) : Complex) -
        2 * u.convolutionSquare.test 0) /
        (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex) := by
  rw [archimedeanIntegrand_carrierSquare, carrierExp_mul_re]

noncomputable def carrierSquareArchimedeanIntegrandPhase
    (γ : Real) (u : CompactLogTest) (y : Real) : Complex :=
  carrierSquareArchimedeanNumeratorPhase γ u y /
    (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)

theorem archimedeanIntegrand_carrierSquare_eq_phaseIntegrand
    (γ : Real) (u : CompactLogTest) (y : Real) :
    archimedeanIntegrand (carrierModulate γ u).convolutionSquare y =
      carrierSquareArchimedeanIntegrandPhase γ u y := by
  simpa [carrierSquareArchimedeanIntegrandPhase,
    carrierSquareArchimedeanNumeratorPhase] using
    archimedeanIntegrand_carrierSquare_phase_split γ u y

noncomputable def carrierPairArchimedeanIntegrandPhase
    (γ : Real) (u v : CompactLogTest) (y : Real) : Complex :=
  carrierPairArchimedeanNumeratorPhase γ u v y /
    (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)

theorem archimedeanIntegrand_carrierPair_eq_phaseIntegrand
    (γ : Real) (u v : CompactLogTest) (y : Real) :
    archimedeanIntegrand
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) y =
      carrierPairArchimedeanIntegrandPhase γ u v y := by
  simpa [carrierPairArchimedeanIntegrandPhase,
    carrierPairArchimedeanNumeratorPhase] using
    archimedeanIntegrand_carrierPair γ u v y

noncomputable def carrierSquareArchimedeanTermPhase
    (γ : Real) (u : CompactLogTest) : Real :=
  (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
      u.convolutionSquare.test 0 +
    ∫ y in Set.Ioi (0 : Real), carrierSquareArchimedeanIntegrandPhase γ u y).re

theorem archimedeanTerm_carrierSquare_eq_phaseTerm
    (γ : Real) (u : CompactLogTest) :
    archimedeanTerm (carrierModulate γ u).convolutionSquare =
      carrierSquareArchimedeanTermPhase γ u := by
  unfold archimedeanTerm carrierSquareArchimedeanTermPhase
  rw [convolutionSquare_carrier_zero_eq]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact archimedeanIntegrand_carrierSquare_eq_phaseIntegrand γ u y

noncomputable def carrierPairArchimedeanTermPhase
    (γ : Real) (u v : CompactLogTest) : Real :=
  (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
      (u.involution.convolution v).test 0 +
    ∫ y in Set.Ioi (0 : Real), carrierPairArchimedeanIntegrandPhase γ u v y).re

theorem archimedeanTerm_carrierPair_eq_phaseTerm
    (γ : Real) (u v : CompactLogTest) :
    archimedeanTerm
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      carrierPairArchimedeanTermPhase γ u v := by
  unfold archimedeanTerm carrierPairArchimedeanTermPhase
  rw [carrierPair_transport γ u v 0, carrierExp_zero]
  simp only [one_mul]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact archimedeanIntegrand_carrierPair_eq_phaseIntegrand γ u v y

theorem archimedeanTerm_carrierSquare
    (γ : Real) (u : CompactLogTest) :
    archimedeanTerm (carrierModulate γ u).convolutionSquare =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          u.convolutionSquare.test 0 +
        ∫ y in Set.Ioi (0 : Real),
          (Complex.ofReal (Real.exp (y / 2)) *
              ((2 * (carrierExp γ y * u.convolutionSquare.test y).re : Real) : Complex) -
            2 * u.convolutionSquare.test 0) /
            (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)).re := by
  unfold archimedeanTerm
  rw [convolutionSquare_carrier_zero_eq]
  rw [show (fun y => archimedeanIntegrand (carrierModulate γ u).convolutionSquare y) =
      (fun y =>
        (Complex.ofReal (Real.exp (y / 2)) *
            ((2 * (carrierExp γ y * u.convolutionSquare.test y).re : Real) : Complex) -
          2 * u.convolutionSquare.test 0) /
          (ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanDenominator y : Complex)) by
    funext y
    exact archimedeanIntegrand_carrierSquare γ u y]

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

theorem finitePrimeSum_carrierSquare (γ : Real) (u : CompactLogTest) :
    finitePrimeSum ((carrierModulate γ u).convolutionSquare) =
      ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
        (ArithmeticFunction.vonMangoldt n : Real) *
          (2 / Real.sqrt (n : Real)) *
          (carrierExp γ (Real.log n) * u.convolutionSquare.test
            (Real.log n)).re := by
  unfold finitePrimeSum
  apply Finset.sum_congr rfl
  intro n hn
  exact finitePrimeTerm_carrierSquare γ u n

theorem finitePrimeSum_carrierSquare_phase_split
    (γ : Real) (u : CompactLogTest) :
    finitePrimeSum ((carrierModulate γ u).convolutionSquare) =
      ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
        (ArithmeticFunction.vonMangoldt n : Real) *
          (2 / Real.sqrt (n : Real)) *
          (Real.cos (γ * Real.log n) *
              (u.convolutionSquare.test (Real.log n)).re +
            Real.sin (γ * Real.log n) *
              (u.convolutionSquare.test (Real.log n)).im) := by
  rw [finitePrimeSum_carrierSquare]
  apply Finset.sum_congr rfl
  intro n hn
  rw [carrierExp_mul_re]

noncomputable def carrierSquarePhaseTerm
    (γ : Real) (u : CompactLogTest) (n : ℕ) : Real :=
  (ArithmeticFunction.vonMangoldt n : Real) *
    (2 / Real.sqrt (n : Real)) *
      (Real.cos (γ * Real.log n) *
          (u.convolutionSquare.test (Real.log n)).re +
        Real.sin (γ * Real.log n) *
          (u.convolutionSquare.test (Real.log n)).im)

theorem finitePrimeTerm_carrierSquare_eq_phaseTerm
    (γ : Real) (u : CompactLogTest) (n : ℕ) :
    finitePrimeTerm ((carrierModulate γ u).convolutionSquare) n =
      carrierSquarePhaseTerm γ u n := by
  unfold carrierSquarePhaseTerm
  rw [finitePrimeTerm_carrierSquare, carrierExp_mul_re]

theorem finitePrimeSum_carrierSquare_eq_phaseTerm_sum
    (γ : Real) (u : CompactLogTest) :
    finitePrimeSum ((carrierModulate γ u).convolutionSquare) =
      ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
        carrierSquarePhaseTerm γ u n := by
  unfold finitePrimeSum
  apply Finset.sum_congr rfl
  intro n hn
  exact finitePrimeTerm_carrierSquare_eq_phaseTerm γ u n

theorem finitePrimeSum_carrierSquare_phase_signed_balance
    (γ : Real) (u : CompactLogTest) :
    finitePrimeSum ((carrierModulate γ u).convolutionSquare) =
      (∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          max 0 (carrierSquarePhaseTerm γ u n)) -
        ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          max 0 (-carrierSquarePhaseTerm γ u n) := by
  unfold finitePrimeSum
  calc
    (∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
        finitePrimeTerm ((carrierModulate γ u).convolutionSquare) n) =
      ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
        (max 0 (finitePrimeTerm
            ((carrierModulate γ u).convolutionSquare) n) -
          max 0 (-finitePrimeTerm
            ((carrierModulate γ u).convolutionSquare) n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : 0 ≤ finitePrimeTerm
          ((carrierModulate γ u).convolutionSquare) n
      · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
        ring
      · have hn' : finitePrimeTerm
            ((carrierModulate γ u).convolutionSquare) n ≤ 0 := le_of_not_ge h
        rw [max_eq_left hn', max_eq_right (neg_nonneg.mpr hn')]
        ring
    _ = (∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          max 0 (carrierSquarePhaseTerm γ u n)) -
        ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          max 0 (-carrierSquarePhaseTerm γ u n) := by
      rw [Finset.sum_sub_distrib]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro n hn
        rw [finitePrimeTerm_carrierSquare_eq_phaseTerm]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [finitePrimeTerm_carrierSquare_eq_phaseTerm]

theorem p2AggregateValue_carrierSquare_phase_split
    (γ : Real) (u : CompactLogTest) :
    p2AggregateValue (carrierModulate γ u) =
      archimedeanTerm (carrierModulate γ u).convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (2 / Real.sqrt (n : Real)) *
            (Real.cos (γ * Real.log n) *
                (u.convolutionSquare.test (Real.log n)).re +
              Real.sin (γ * Real.log n) *
                (u.convolutionSquare.test (Real.log n)).im) := by
  rw [p2AggregateValue_eq_archimedean_plus_finiteProfile,
    ← finitePrimeSum_eq_bilateralProfile_weighted_sum,
    finitePrimeSum_carrierSquare_phase_split]

theorem orbitWindowSemiLocalGate_carrierSquare_phase_split
    (γ : Real) (u : CompactLogTest) :
    orbitWindowSemiLocalGate (carrierModulate γ u) ↔
      archimedeanTerm (carrierModulate γ u).convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (2 / Real.sqrt (n : Real)) *
            (Real.cos (γ * Real.log n) *
                (u.convolutionSquare.test (Real.log n)).re +
              Real.sin (γ * Real.log n) *
                (u.convolutionSquare.test (Real.log n)).im) ≤ 0 := by
  unfold orbitWindowSemiLocalGate
  rw [finitePrimeSum_carrierSquare_phase_split]

/-! The cross-channel readback keeps both physical cells explicit.  Unlike the
square case, no Hermitian reduction to a single real part is available for one
directed pair, so this is the correct same-owner interface for the AB/BA
signed estimate. -/
theorem finitePrimeTermComplex_carrierPair
    (γ : Real) (u v : CompactLogTest) (n : ℕ) :
    finitePrimeTermComplex
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) n =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        (((1 / Real.sqrt (n : Real) : Real) : Complex) *
          (carrierExp γ (Real.log n) *
              (u.involution.convolution v).test (Real.log n) +
            carrierExp γ (-(Real.log n)) *
              (u.involution.convolution v).test (-(Real.log n)))) := by
  unfold finitePrimeTermComplex
  rw [carrierPair_transport, carrierPair_transport]

theorem finitePrimeTerm_carrierPair_phase_split
    (γ : Real) (u v : CompactLogTest) (n : ℕ) :
    finitePrimeTerm
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) n =
      (ArithmeticFunction.vonMangoldt n : Real) *
        (1 / Real.sqrt (n : Real)) *
        (Real.cos (γ * Real.log n) *
            (u.involution.convolution v).test (Real.log n)).re +
      (ArithmeticFunction.vonMangoldt n : Real) *
        (1 / Real.sqrt (n : Real)) *
        (Real.sin (γ * Real.log n) *
            (u.involution.convolution v).test (Real.log n)).im +
      (ArithmeticFunction.vonMangoldt n : Real) *
        (1 / Real.sqrt (n : Real)) *
        (Real.cos (γ * (-(Real.log n))) *
            (u.involution.convolution v).test (-(Real.log n))).re +
      (ArithmeticFunction.vonMangoldt n : Real) *
        (1 / Real.sqrt (n : Real)) *
        (Real.sin (γ * (-(Real.log n))) *
            (u.involution.convolution v).test (-(Real.log n))).im := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_carrierPair]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.add_re]
  rw [carrierExp_mul_re, carrierExp_mul_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

noncomputable def carrierPairPhaseTerm
    (γ : Real) (u v : CompactLogTest) (n : ℕ) : Real :=
  (ArithmeticFunction.vonMangoldt n : Real) *
    (1 / Real.sqrt (n : Real)) *
      ((Real.cos (γ * Real.log n) *
          (u.involution.convolution v).test (Real.log n)).re +
        (Real.sin (γ * Real.log n) *
          (u.involution.convolution v).test (Real.log n)).im +
        (Real.cos (γ * (-(Real.log n))) *
          (u.involution.convolution v).test (-(Real.log n))).re +
        (Real.sin (γ * (-(Real.log n))) *
          (u.involution.convolution v).test (-(Real.log n))).im)

theorem finitePrimeTerm_carrierPair_eq_phaseTerm
    (γ : Real) (u v : CompactLogTest) (n : ℕ) :
    finitePrimeTerm
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) n = carrierPairPhaseTerm γ u v n := by
  unfold carrierPairPhaseTerm
  convert finitePrimeTerm_carrierPair_phase_split γ u v n using 1 <;> ring

theorem finitePrimeSum_carrierPair_eq_phaseTerm_sum
    (γ : Real) (u v : CompactLogTest) :
    finitePrimeSum
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
        carrierPairPhaseTerm γ u v n := by
  unfold finitePrimeSum
  apply Finset.sum_congr rfl
  intro n hn
  exact finitePrimeTerm_carrierPair_eq_phaseTerm γ u v n

theorem ICgate_carrierPair_phase_split
    (γ : Real) (u v : CompactLogTest) :
    ICgate
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      archimedeanTerm
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) +
        ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (1 / Real.sqrt (n : Real)) *
              ((Real.cos (γ * Real.log n) *
                  (u.involution.convolution v).test (Real.log n)).re +
                (Real.sin (γ * Real.log n) *
                  (u.involution.convolution v).test (Real.log n)).im +
                (Real.cos (γ * (-(Real.log n))) *
                  (u.involution.convolution v).test (-(Real.log n))).re +
                (Real.sin (γ * (-(Real.log n))) *
                  (u.involution.convolution v).test (-(Real.log n))).im) := by
  unfold ICgate finitePrimeSum
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  convert finitePrimeTerm_carrierPair_phase_split γ u v n using 1 <;> ring

theorem finitePrimeSum_carrierPair_phase_split
    (γ : Real) (u v : CompactLogTest) :
    finitePrimeSum
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (1 / Real.sqrt (n : Real)) *
              ((Real.cos (γ * Real.log n) *
                  (u.involution.convolution v).test (Real.log n)).re +
                (Real.sin (γ * Real.log n) *
                  (u.involution.convolution v).test (Real.log n)).im +
                (Real.cos (γ * (-(Real.log n))) *
                  (u.involution.convolution v).test (-(Real.log n))).re +
                (Real.sin (γ * (-(Real.log n))) *
                  (u.involution.convolution v).test (-(Real.log n))).im) := by
  have h := ICgate_carrierPair_phase_split γ u v
  unfold ICgate at h
  linarith

theorem finitePrimeSum_carrierPair_eq_positive_sub_negative
    (γ : Real) (u v : CompactLogTest) :
    finitePrimeSum
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      (∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          max 0 (finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n)) -
      ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          max 0 (-finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n) := by
  unfold finitePrimeSum
  calc
    (∑ n ∈ globalPrimeIndexSet
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)),
        finitePrimeTerm
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) n) =
      ∑ n ∈ globalPrimeIndexSet
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)),
        (max 0 (finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n) -
          max 0 (-finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : 0 ≤ finitePrimeTerm
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) n
      · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
        ring
      · have hn' : finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n ≤ 0 := le_of_not_ge h
        rw [max_eq_left hn', max_eq_right (neg_nonneg.mpr hn')]
        ring
    _ = (∑ n ∈ globalPrimeIndexSet
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)),
          max 0 (finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n)) -
        ∑ n ∈ globalPrimeIndexSet
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)),
          max 0 (-finitePrimeTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) n) := by
      rw [Finset.sum_sub_distrib]

theorem finitePrimeSum_carrierPair_phase_signed_balance
    (γ : Real) (u v : CompactLogTest) :
    finitePrimeSum
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) =
      (∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          max 0 (carrierPairPhaseTerm γ u v n)) -
      ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)),
          max 0 (-carrierPairPhaseTerm γ u v n) := by
  rw [finitePrimeSum_carrierPair_eq_positive_sub_negative]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro n hn
    rw [← finitePrimeTerm_carrierPair_eq_phaseTerm]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [← finitePrimeTerm_carrierPair_eq_phaseTerm]

theorem twoSpan_gate_qform_expand_carrier
    (γ : Real) (u v : CompactLogTest) (lam : Real) :
    (![1, -lam] : Fin 2 → Real) ⬝ᵥ
        (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
          (![1, -lam] : Fin 2 → Real)) =
      ICgate (carrierModulate γ u).convolutionSquare +
        lam ^ 2 * ICgate (carrierModulate γ v).convolutionSquare -
        2 * lam * ICgate
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) := by
  exact Source.C1P2SpanProfileMatrix.twoSpan_gate_qform_expand_symmetric
    (carrierModulate γ u) (carrierModulate γ v) lam

theorem carrier_twoSpan_gate_qform_at_optimal_lambda
    (γ : Real) (u v : CompactLogTest)
    (hB : 0 < ICgate (carrierModulate γ v).convolutionSquare) :
    (![1, -(
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) /
          ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real) ⬝ᵥ
        (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
          (![1, -(
              ICgate
                  ((carrierModulate γ u).involution.convolution
                    (carrierModulate γ v)) /
                ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real)) =
      (ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare -
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) /
        ICgate (carrierModulate γ v).convolutionSquare := by
  rw [twoSpan_gate_qform_expand_carrier]
  field_simp [ne_of_gt hB]
  ring

theorem carrier_twoSpan_determinant_split
    (γ : Real) (u v : CompactLogTest) :
    ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare -
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2 =
      (archimedeanTerm (carrierModulate γ u).convolutionSquare *
          archimedeanTerm (carrierModulate γ v).convolutionSquare -
        archimedeanTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) +
      (archimedeanTerm (carrierModulate γ u).convolutionSquare *
          finitePrimeSum (carrierModulate γ v).convolutionSquare +
        archimedeanTerm (carrierModulate γ v).convolutionSquare *
          finitePrimeSum (carrierModulate γ u).convolutionSquare -
        2 * archimedeanTerm
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) *
          finitePrimeSum
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v))) +
      (finitePrimeSum (carrierModulate γ u).convolutionSquare *
          finitePrimeSum (carrierModulate γ v).convolutionSquare -
        finitePrimeSum
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) := by
  unfold ICgate
  ring

noncomputable def carrierSquarePrimePhaseSum
    (γ : Real) (u : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
    carrierSquarePhaseTerm γ u n

noncomputable def carrierPairPrimePhaseSum
    (γ : Real) (u v : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet
      ((carrierModulate γ u).involution.convolution
        (carrierModulate γ v)),
    carrierPairPhaseTerm γ u v n

noncomputable def carrierSquarePrimeCredit
    (γ : Real) (u : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
    max 0 (carrierSquarePhaseTerm γ u n)

noncomputable def carrierSquarePrimeDeficit
    (γ : Real) (u : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare),
    max 0 (-carrierSquarePhaseTerm γ u n)

noncomputable def carrierPairPrimeCredit
    (γ : Real) (u v : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet
      ((carrierModulate γ u).involution.convolution
        (carrierModulate γ v)),
    max 0 (carrierPairPhaseTerm γ u v n)

noncomputable def carrierPairPrimeDeficit
    (γ : Real) (u v : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet
      ((carrierModulate γ u).involution.convolution
        (carrierModulate γ v)),
    max 0 (-carrierPairPhaseTerm γ u v n)

theorem carrierSquarePrimePhaseSum_eq_credit_sub_deficit
    (γ : Real) (u : CompactLogTest) :
    carrierSquarePrimePhaseSum γ u =
      carrierSquarePrimeCredit γ u - carrierSquarePrimeDeficit γ u := by
  calc
    carrierSquarePrimePhaseSum γ u =
        finitePrimeSum ((carrierModulate γ u).convolutionSquare) := by
      symm
      exact finitePrimeSum_carrierSquare_eq_phaseTerm_sum γ u
    _ = carrierSquarePrimeCredit γ u - carrierSquarePrimeDeficit γ u := by
      exact finitePrimeSum_carrierSquare_phase_signed_balance γ u

theorem carrierPairPrimePhaseSum_eq_credit_sub_deficit
    (γ : Real) (u v : CompactLogTest) :
    carrierPairPrimePhaseSum γ u v =
      carrierPairPrimeCredit γ u v - carrierPairPrimeDeficit γ u v := by
  calc
    carrierPairPrimePhaseSum γ u v =
        finitePrimeSum
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) := by
      symm
      exact finitePrimeSum_carrierPair_eq_phaseTerm_sum γ u v
    _ = carrierPairPrimeCredit γ u v - carrierPairPrimeDeficit γ u v := by
      exact finitePrimeSum_carrierPair_phase_signed_balance γ u v

noncomputable def carrierArchimedeanDeterminantPhase
    (γ : Real) (u v : CompactLogTest) : Real :=
  carrierSquareArchimedeanTermPhase γ u *
      carrierSquareArchimedeanTermPhase γ v -
    (carrierPairArchimedeanTermPhase γ u v) ^ 2

noncomputable def carrierMixedDeterminantPhase
    (γ : Real) (u v : CompactLogTest) : Real :=
  carrierSquareArchimedeanTermPhase γ u * carrierSquarePrimePhaseSum γ v +
    carrierSquareArchimedeanTermPhase γ v * carrierSquarePrimePhaseSum γ u -
    2 * carrierPairArchimedeanTermPhase γ u v *
      carrierPairPrimePhaseSum γ u v

noncomputable def carrierPrimeDeterminantPhase
    (γ : Real) (u v : CompactLogTest) : Real :=
  carrierSquarePrimePhaseSum γ u * carrierSquarePrimePhaseSum γ v -
  (carrierPairPrimePhaseSum γ u v) ^ 2

theorem carrierPrimeDeterminantPhase_signed_expansion
    (γ : Real) (u v : CompactLogTest) :
    carrierPrimeDeterminantPhase γ u v =
      (carrierSquarePrimeCredit γ u - carrierSquarePrimeDeficit γ u) *
          (carrierSquarePrimeCredit γ v - carrierSquarePrimeDeficit γ v) -
        (carrierPairPrimeCredit γ u v - carrierPairPrimeDeficit γ u v) ^ 2 := by
  unfold carrierPrimeDeterminantPhase
  rw [carrierSquarePrimePhaseSum_eq_credit_sub_deficit,
    carrierSquarePrimePhaseSum_eq_credit_sub_deficit,
    carrierPairPrimePhaseSum_eq_credit_sub_deficit]

theorem carrier_twoSpan_determinant_split_phase
    (γ : Real) (u v : CompactLogTest) :
    ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare -
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2 =
      carrierArchimedeanDeterminantPhase γ u v +
        carrierMixedDeterminantPhase γ u v +
        carrierPrimeDeterminantPhase γ u v := by
  rw [carrier_twoSpan_determinant_split]
  rw [archimedeanTerm_carrierSquare_eq_phaseTerm γ u,
    archimedeanTerm_carrierSquare_eq_phaseTerm γ v,
    archimedeanTerm_carrierPair_eq_phaseTerm γ u v,
    finitePrimeSum_carrierSquare_eq_phaseTerm_sum γ u,
    finitePrimeSum_carrierSquare_eq_phaseTerm_sum γ v,
    finitePrimeSum_carrierPair_eq_phaseTerm_sum γ u v]
  unfold carrierArchimedeanDeterminantPhase carrierMixedDeterminantPhase
    carrierPrimeDeterminantPhase carrierSquarePrimePhaseSum
    carrierPairPrimePhaseSum
  ring

theorem carrier_twoSpan_signed_budget_iff_optimal_nonpos
    (γ : Real) (u v : CompactLogTest)
    (hB : 0 < ICgate (carrierModulate γ v).convolutionSquare) :
    ((![1, -(
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) /
          ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real) ⬝ᵥ
        (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
          (![1, -(
              ICgate
                  ((carrierModulate γ u).involution.convolution
                    (carrierModulate γ v)) /
                ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real)) ≤ 0) ↔
      ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2 := by
  rw [carrier_twoSpan_gate_qform_at_optimal_lambda γ u v hB]
  rw [div_nonpos_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim ((not_lt_of_ge h.2) hB)
    · exact sub_nonpos.mp h.1
  · intro h
    exact Or.inr ⟨sub_nonpos.mpr h, le_of_lt hB⟩

theorem carrier_twoSpan_phase_budget_iff_optimal_nonpos
    (γ : Real) (u v : CompactLogTest)
    (hB : 0 < ICgate (carrierModulate γ v).convolutionSquare) :
    ((![1, -(
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) /
          ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real) ⬝ᵥ
        (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
          (![1, -(
              ICgate
                  ((carrierModulate γ u).involution.convolution
                    (carrierModulate γ v)) /
                ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real)) ≤ 0) ↔
      carrierArchimedeanDeterminantPhase γ u v +
      carrierMixedDeterminantPhase γ u v +
        carrierPrimeDeterminantPhase γ u v ≤ 0 := by
  rw [carrier_twoSpan_signed_budget_iff_optimal_nonpos γ u v hB]
  constructor
  · intro h
    have h' := sub_nonpos.mpr h
    rwa [carrier_twoSpan_determinant_split_phase] at h'
  · intro h
    apply sub_nonpos.mp
    rw [carrier_twoSpan_determinant_split_phase]
    exact h

theorem orbitWindowSemiLocalGate_carrier_twoSpan_of_optimal_determinant
    (γ : Real) (u v : CompactLogTest) (B : Real)
    (hAu : Function.support (carrierModulate γ u).test ⊆ Set.Ioo (-B) B)
    (hBv : Function.support (carrierModulate γ v).test ⊆ Set.Ioo (-B) B)
    (hBB : 0 < ICgate (carrierModulate γ v).convolutionSquare)
    (hdet :
      ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) :
    orbitWindowSemiLocalGate
        (spanObj ![carrierModulate γ u, carrierModulate γ v]
          ![(1 : Real), -(
            ICgate
                ((carrierModulate γ u).involution.convolution
                  (carrierModulate γ v)) /
              ICgate (carrierModulate γ v).convolutionSquare)]) := by
  have hq :
      (![1, -(
          ICgate
              ((carrierModulate γ u).involution.convolution
                (carrierModulate γ v)) /
            ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, -(
                ICgate
                    ((carrierModulate γ u).involution.convolution
                      (carrierModulate γ v)) /
                  ICgate (carrierModulate γ v).convolutionSquare)] : Fin 2 → Real)) ≤ 0 :=
    (carrier_twoSpan_signed_budget_iff_optimal_nonpos γ u v hBB).mpr hdet
  apply
    (Source.C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
      ![carrierModulate γ u, carrierModulate γ v]
      ![(1 : Real), -(
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) /
          ICgate (carrierModulate γ v).convolutionSquare)]
      (B := B) ?_).mpr hq
  intro i
  fin_cases i
  · exact hAu
  · exact hBv

theorem exists_carrier_twoSpan_gate_qform_nonpos_iff_discriminant
    (γ : Real) (u v : CompactLogTest)
    (hC : 0 < ICgate (carrierModulate γ v).convolutionSquare) :
    (∃ lam : Real,
      (![1, -lam] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, -lam] : Fin 2 → Real)) ≤ 0) ↔
      ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2 := by
  exact Source.C1P2SpanProfileMatrix.exists_twoSpan_gate_qform_nonpos_iff_symmetric_discriminant
    (carrierModulate γ u) (carrierModulate γ v) hC

theorem exists_carrier_twoSpan_gate_qform_nonpos_of_discriminant
    (γ : Real) (u v : CompactLogTest)
    (hC : 0 < ICgate (carrierModulate γ v).convolutionSquare)
    (hdisc :
      ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) :
    ∃ lam : Real,
      (![1, -lam] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, -lam] : Fin 2 → Real)) ≤ 0 :=
  (exists_carrier_twoSpan_gate_qform_nonpos_iff_discriminant γ u v hC).mpr hdisc

theorem exists_carrier_twoSpan_gate_of_discriminant
    (γ : Real) (u v : CompactLogTest) (B : Real)
    (hAu : Function.support (carrierModulate γ u).test ⊆ Set.Ioo (-B) B)
    (hBv : Function.support (carrierModulate γ v).test ⊆ Set.Ioo (-B) B)
    (hC : 0 < ICgate (carrierModulate γ v).convolutionSquare)
    (hdisc :
      ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2) :
    ∃ lam : Real,
      orbitWindowSemiLocalGate
        (spanObj ![carrierModulate γ u, carrierModulate γ v]
          ![(1 : Real), -lam]) := by
  obtain ⟨lam, hq⟩ :=
    exists_carrier_twoSpan_gate_qform_nonpos_of_discriminant
      γ u v hC hdisc
  refine ⟨lam, ?_⟩
  apply
    (Source.C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
      ![carrierModulate γ u, carrierModulate γ v]
      ![(1 : Real), -lam] (B := B) ?_).mpr hq
  intro i
  fin_cases i
  · exact hAu
  · exact hBv

theorem carrierPair_gate_polarization
    (γ : Real) (u v : CompactLogTest) (B : Real)
    (hAu : Function.support (carrierModulate γ u).test ⊆ Set.Ioo (-B) B)
    (hBv : Function.support (carrierModulate γ v).test ⊆ Set.Ioo (-B) B) :
    4 * ICgate
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) =
      ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), 1]).convolutionSquare -
        ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), -1]).convolutionSquare := by
  let A := carrierModulate γ u
  let C := carrierModulate γ v
  have hw : ∀ i, Function.support (![A, C] i).test ⊆ Set.Ioo (-B) B := by
    intro i
    fin_cases i
    · exact hAu
    · exact hBv
  have hplus :=
    Source.C1ArchimedeanIntegrabilityGeneric.gate_qform_span_free
      ![A, C] ![(1 : Real), 1] hw
  have hminus :=
    Source.C1ArchimedeanIntegrabilityGeneric.gate_qform_span_free
      ![A, C] ![(1 : Real), -1] hw
  have hplusQ :=
    Source.C1P2SpanProfileMatrix.twoSpan_gate_qform_expand_symmetric A C (-1)
  have hminusQ :=
    Source.C1P2SpanProfileMatrix.twoSpan_gate_qform_expand_symmetric A C 1
  dsimp [A, C] at hplus hminus hplusQ hminusQ ⊢
  have hplusQ' :
      (![1, 1] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, 1] : Fin 2 → Real)) =
        ICgate (carrierModulate γ u).convolutionSquare +
          ICgate (carrierModulate γ v).convolutionSquare +
          2 * ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) := by
    simpa using hplusQ
  have hminusQ' :
      (![1, -1] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, -1] : Fin 2 → Real)) =
        ICgate (carrierModulate γ u).convolutionSquare +
          ICgate (carrierModulate γ v).convolutionSquare -
          2 * ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) := by
    simpa using hminusQ
  calc
    4 * ICgate
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v)) =
        (ICgate (carrierModulate γ u).convolutionSquare +
          ICgate (carrierModulate γ v).convolutionSquare +
          2 * ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v))) -
        (ICgate (carrierModulate γ u).convolutionSquare +
          ICgate (carrierModulate γ v).convolutionSquare -
          2 * ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v))) := by ring
    _ = ((![1, 1] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, 1] : Fin 2 → Real))) -
        ((![1, -1] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![carrierModulate γ u, carrierModulate γ v] *ᵥ
            (![1, -1] : Fin 2 → Real))) := by
      rw [hplusQ', hminusQ']
    _ = ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), 1]).convolutionSquare -
        ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), -1]).convolutionSquare := by
      rw [← hplus, ← hminus]

theorem carrier_discriminant_iff_polarized_span_gates
    (γ : Real) (u v : CompactLogTest) (B : Real)
    (hAu : Function.support (carrierModulate γ u).test ⊆ Set.Ioo (-B) B)
    (hBv : Function.support (carrierModulate γ v).test ⊆ Set.Ioo (-B) B) :
    ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare ≤
        ICgate
            ((carrierModulate γ u).involution.convolution
              (carrierModulate γ v)) ^ 2 ↔
      16 * (ICgate (carrierModulate γ u).convolutionSquare *
          ICgate (carrierModulate γ v).convolutionSquare) ≤
        (ICgate
            (spanObj ![carrierModulate γ u, carrierModulate γ v]
              ![(1 : Real), 1]).convolutionSquare -
          ICgate
            (spanObj ![carrierModulate γ u, carrierModulate γ v]
              ![(1 : Real), -1]).convolutionSquare) ^ 2 := by
  have hpol := carrierPair_gate_polarization γ u v B hAu hBv
  have hsquare :
      (ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), 1]).convolutionSquare -
        ICgate
          (spanObj ![carrierModulate γ u, carrierModulate γ v]
            ![(1 : Real), -1]).convolutionSquare) ^ 2 =
        (4 * ICgate
          ((carrierModulate γ u).involution.convolution
            (carrierModulate γ v))) ^ 2 := by
    rw [← hpol]
  rw [hsquare]
  constructor <;> intro h <;> nlinarith

theorem carrier_spanObj_eq_modulated_envelope
    (γ : Real) (u v : CompactLogTest) (s : Real) :
    spanObj ![carrierModulate γ u, carrierModulate γ v]
        ![(1 : Real), s] =
      carrierModulate γ (spanObj ![u, v] ![(1 : Real), s]) := by
  apply CompactLogTest.ext
  ext x
  simp [spanObj_apply, carrierModulate_apply, Fin.sum_univ_two]
  ring

theorem p2AggregateValue_carrierSpan_phase_split
    (γ : Real) (u v : CompactLogTest) (s : Real) :
    p2AggregateValue
        (spanObj ![carrierModulate γ u, carrierModulate γ v] ![(1 : Real), s]) =
      archimedeanTerm
          (carrierModulate γ (spanObj ![u, v] ![(1 : Real), s])).convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ (spanObj ![u, v] ![(1 : Real), s])).convolutionSquare),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (2 / Real.sqrt (n : Real)) *
            (Real.cos (γ * Real.log n) *
                ((spanObj ![u, v] ![(1 : Real), s]).convolutionSquare.test
                  (Real.log n)).re +
              Real.sin (γ * Real.log n) *
                ((spanObj ![u, v] ![(1 : Real), s]).convolutionSquare.test
                  (Real.log n)).im) := by
  rw [carrier_spanObj_eq_modulated_envelope]
  exact p2AggregateValue_carrierSquare_phase_split γ
    (spanObj ![u, v] ![(1 : Real), s])

theorem orbitWindowSemiLocalGate_carrierSpan_phase_split
    (γ : Real) (u v : CompactLogTest) (s : Real) :
    orbitWindowSemiLocalGate
        (spanObj ![carrierModulate γ u, carrierModulate γ v] ![(1 : Real), s]) ↔
      archimedeanTerm
          (carrierModulate γ (spanObj ![u, v] ![(1 : Real), s])).convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet
            ((carrierModulate γ (spanObj ![u, v] ![(1 : Real), s])).convolutionSquare),
          (ArithmeticFunction.vonMangoldt n : Real) *
            (2 / Real.sqrt (n : Real)) *
            (Real.cos (γ * Real.log n) *
                ((spanObj ![u, v] ![(1 : Real), s]).convolutionSquare.test
                  (Real.log n)).re +
              Real.sin (γ * Real.log n) *
                ((spanObj ![u, v] ![(1 : Real), s]).convolutionSquare.test
                  (Real.log n)).im) ≤ 0 := by
  rw [carrier_spanObj_eq_modulated_envelope]
  exact orbitWindowSemiLocalGate_carrierSquare_phase_split γ
    (spanObj ![u, v] ![(1 : Real), s])

/-! The two directed carrier cross channels have the same real prime readout.
This is the scalar form needed before estimating the single AB channel in the
two-span signed budget. -/
theorem finitePrimeTerm_carrierPair_swap
    (γ : Real) (u v : CompactLogTest) (n : ℕ) :
    finitePrimeTerm
        ((carrierModulate γ u).involution.convolution
          (carrierModulate γ v)) n =
      finitePrimeTerm
        ((carrierModulate γ v).involution.convolution
          (carrierModulate γ u)) n := by
  unfold finitePrimeTerm
  have h :=
    Source.C1P2SpanProfileMatrix.finitePrimeTermComplex_pairTest_swap
      (carrierModulate γ u) (carrierModulate γ v) n
  rw [h]
  simp [Complex.star_def]

/-- The remaining C3' producer input, with its carrier and visible owner
bound together so an estimate cannot mix different phase channels. -/
structure CarrierTwoSpanDeterminantCertificate
    (γ : Real) (u v : CompactLogTest) (B : Real) where
  support_u : Function.support (carrierModulate γ u).test ⊆ Set.Ioo (-B) B
  support_v : Function.support (carrierModulate γ v).test ⊆ Set.Ioo (-B) B
  pivot_pos : 0 < ICgate (carrierModulate γ v).convolutionSquare
  phase_budget :
    carrierArchimedeanDeterminantPhase γ u v +
      carrierMixedDeterminantPhase γ u v +
        carrierPrimeDeterminantPhase γ u v ≤ 0

theorem CarrierTwoSpanDeterminantCertificate.gate
    {γ : Real} {u v : CompactLogTest} {B : Real}
    (certificate : CarrierTwoSpanDeterminantCertificate γ u v B) :
    orbitWindowSemiLocalGate
        (spanObj ![carrierModulate γ u, carrierModulate γ v]
          ![(1 : Real), -(
            ICgate
                ((carrierModulate γ u).involution.convolution
                  (carrierModulate γ v)) /
              ICgate (carrierModulate γ v).convolutionSquare)]) := by
  apply orbitWindowSemiLocalGate_carrier_twoSpan_of_optimal_determinant
    γ u v B certificate.support_u certificate.support_v certificate.pivot_pos
  apply (carrier_twoSpan_signed_budget_iff_optimal_nonpos γ u v
    certificate.pivot_pos).mp
  exact (carrier_twoSpan_phase_budget_iff_optimal_nonpos γ u v
    certificate.pivot_pos).mpr certificate.phase_budget

end C1C3CarrierTransport
end Dev
end ConnesWeilRH
