/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1T2Assembly
import ConnesWeilRH.Dev.C1OrbitWindowExitComposition

/-!
# P2-α: finite visible-prime control for a defect

This leaf proves the first non-circular estimate needed by the detector-
specific semi-local route.  It bounds the absolute value of the finite
visible-prime part of a defect by a finite sum of per-prime term bounds.  The
per-term bounds remain an analytic producer obligation; no gate sign,
`qw >= 0`, or Stage-B defect budget is assumed here.

Consumer: the healthy `CompactLog`, B5-shaped orbit-detector chain through
`C1T2Assembly`.  RH is not claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2DefectControl

open C1SameOwnerWeil
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1T2Assembly
open CC20YoshidaNearZeros
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1OrbitWindowExitComposition
open CCM25Concrete.CompactLogConvolution
open MeasureTheory
open scoped BigOperators

/-! ## Per-index norm envelope -/

/-- The pointwise norm envelope for one finite-prime term.  It is deliberately
defined from the same-owner term, so later analytic estimates only need to
bound the two defect values appearing at `± log n`. -/
noncomputable def primeTermNormEnvelope
    (F : CompactLogTest) (n : Nat) : Real :=
  ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
    ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
      (‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖)

/-! The complex norm coefficient can be read back as a real coefficient. -/

/-- The envelope's coefficient is exactly the real von Mangoldt weight times
the reciprocal square-root weight.  This is a readback identity, not an
estimate; it lets a producer work with real arithmetic on the finite cutoff. -/
theorem primeTermNormEnvelope_eq_realCoefficient_mul
    (F : CompactLogTest) (n : Nat) :
    primeTermNormEnvelope F n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖) := by
  simp only [primeTermNormEnvelope, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hs : 0 ≤ (1 / Real.sqrt (n : Real)) := by positivity
  rw [abs_of_nonneg hs]

/-- A real coefficient upper bound turns the envelope into the scalar `2*A`
budget.  The coefficient bound is intentionally supplied by the producer,
so this adapter does not hide any prime-growth or cutoff argument. -/
theorem primeTermNormEnvelope_le_of_realCoefficientBound
    (F : CompactLogTest) (n : Nat) (A K : Real)
    (hA : 0 ≤ A)
    (hF : ∀ x : Real, ‖F.test x‖ ≤ A)
    (hcoef : ArithmeticFunction.vonMangoldt n *
      (1 / Real.sqrt (n : Real)) ≤ K) :
    primeTermNormEnvelope F n ≤ K * (2 * A) := by
  rw [primeTermNormEnvelope_eq_realCoefficient_mul]
  have hsum : ‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖ ≤ 2 * A := by
    linarith [hF (Real.log n), hF (-Real.log n)]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hs : 0 ≤ (1 / Real.sqrt (n : Real)) := by positivity
  have hcoef0 : 0 ≤ ArithmeticFunction.vonMangoldt n *
      (1 / Real.sqrt (n : Real)) := mul_nonneg hΛ hs
  calc
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖) ≤
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (2 * A) := mul_le_mul_of_nonneg_left hsum hcoef0
    _ ≤ K * (2 * A) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- The standard von Mangoldt estimate gives a concrete coefficient bound on
every positive index: `Λ(n)/√n ≤ log n`. -/
theorem vonMangoldt_sqrtWeight_le_log_of_one_le
    (n : Nat) (hn : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) ≤
      Real.log (n : Real) := by
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hnreal : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hsqrt : (1 : Real) ≤ Real.sqrt (n : Real) :=
    (Real.one_le_sqrt).2 hnreal
  have hinv : 1 / Real.sqrt (n : Real) ≤ (1 : Real) := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hsqrt)
  calc
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) ≤
        ArithmeticFunction.vonMangoldt n * 1 :=
      mul_le_mul_of_nonneg_left hinv hΛ
    _ = ArithmeticFunction.vonMangoldt n := by ring
    _ ≤ Real.log (n : Real) := ArithmeticFunction.vonMangoldt_le_log

/-- The same coefficient bound in the exact complex-norm spelling used by the
explicit finite-range sum, including the harmless zero index. -/
theorem primeCoefficientNorm_le_log_of_nat (n : Nat) :
    ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ ≤
      Real.log (n : Real) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have h := vonMangoldt_sqrtWeight_le_log_of_one_le (n + 1) (by omega)
      have hs : 0 ≤ (1 / Real.sqrt ((n + 1 : Nat) : Real)) := by positivity
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg hs] using h

/-- On any finite index set, the complex-norm coefficient sum is bounded by
the corresponding real logarithmic sum once the common test factor is
nonnegative. -/
theorem finitePrimeCoefficientSum_le_logSum
    (s : Finset Nat) (A : Real) (hA : 0 ≤ A) :
    (∑ n ∈ s,
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * A)) ≤
      ∑ n ∈ s, Real.log (n : Real) * (2 * A) := by
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_right (primeCoefficientNorm_le_log_of_nat n)
    (mul_nonneg (by norm_num) hA)

/-- A logarithmic coefficient bound is enough to invoke the real-coefficient
adapter.  This is the finite-prime producer shape used with a cutoff. -/
theorem primeTermNormEnvelope_le_of_logBound
    (F : CompactLogTest) (n : Nat) (A K : Real)
    (hn : 1 ≤ n) (hA : 0 ≤ A)
    (hF : ∀ x : Real, ‖F.test x‖ ≤ A)
    (hlog : Real.log (n : Real) ≤ K) :
    primeTermNormEnvelope F n ≤ K * (2 * A) := by
  apply primeTermNormEnvelope_le_of_realCoefficientBound F n A K hA hF
  exact (vonMangoldt_sqrtWeight_le_log_of_one_le n hn).trans hlog

/-- Every real prime-term readout is bounded by its explicit complex norm
envelope.  No sign of the von Mangoldt coefficient is used. -/
theorem abs_finitePrimeTerm_le_primeTermNormEnvelope
    (F : CompactLogTest) (n : Nat) :
    |finitePrimeTerm F n| ≤ primeTermNormEnvelope F n := by
  unfold finitePrimeTerm primeTermNormEnvelope finitePrimeTermComplex
  calc
    |((ArithmeticFunction.vonMangoldt n : Complex) *
        (((1 / Real.sqrt (n : Real) : Real) : Complex) *
          (F.test (Real.log n) + F.test (-Real.log n)))).re| ≤
        ‖(ArithmeticFunction.vonMangoldt n : Complex) *
          (((1 / Real.sqrt (n : Real) : Real) : Complex) *
            (F.test (Real.log n) + F.test (-Real.log n)))‖ :=
      Complex.abs_re_le_norm _
    _ = ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
          ‖F.test (Real.log n) + F.test (-Real.log n)‖ := by
      rw [norm_mul, norm_mul]
      ring
    _ ≤ primeTermNormEnvelope F n := by
      unfold primeTermNormEnvelope
      gcongr
      exact norm_add_le _ _

/-- A uniform pointwise test bound turns the exact envelope into the simpler
`2 A` estimate used by a concrete correction producer. -/
theorem primeTermNormEnvelope_le_of_uniformTestBound
    (F : CompactLogTest) (n : Nat) (A : Real)
    (hA : 0 ≤ A)
    (hF : ∀ x : Real, ‖F.test x‖ ≤ A) :
    primeTermNormEnvelope F n ≤
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * A) := by
  unfold primeTermNormEnvelope
  have hsum : ‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖ ≤ A + A :=
    add_le_add (hF _) (hF _)
  have hcoef : 0 ≤
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ := by
    positivity
  calc
    ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
          (‖F.test (Real.log n)‖ + ‖F.test (-Real.log n)‖) ≤
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (A + A) := by
      exact mul_le_mul_of_nonneg_left hsum hcoef
    _ = ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * A) := by
      congr 2
      ring

/-! ## Archimedean integral channel -/

/-- Bound the archimedean functional by the zero-point value and the
integral of the norm of its direct density.  This is the analytic interface
that a concrete defect producer must discharge; no sign is used. -/
theorem abs_archimedeanTerm_le_of_zeroAndIntegralBounds
    (F : CompactLogTest) (A I : Real)
    (hzero : ‖F.test 0‖ ≤ A)
    (hintegral :
      (∫ y in Set.Ioi (0 : Real), ‖archimedeanIntegrand F y‖) ≤ I) :
    |archimedeanTerm F| ≤
      |Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| * A + I := by
  have hInt :
      ‖∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y‖ ≤ I := by
    calc
      ‖∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y‖ ≤
          ∫ y in Set.Ioi (0 : Real), ‖archimedeanIntegrand F y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ I := hintegral
  unfold archimedeanTerm
  calc
    |((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0) +
        ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re| ≤
        ‖(((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0) +
        ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0‖ +
        ‖∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y‖ :=
      norm_add_le _ _
    _ = |Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| * ‖F.test 0‖ +
        ‖∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| * A + I := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hzero (abs_nonneg _)) hInt

/-- A one-window defect inherits a pointwise norm bound from its two square
ingredients.  This is the first concrete bridge from bounds on the detector
and certified window to the `A` parameter used by the prime envelope. -/
theorem defect_test_norm_le_of_uniformBounds
    (g W : CompactLogTest) (G H : Real)
    (hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G)
    (hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H) :
    ∀ x : Real, ‖(ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)).test x‖ ≤ G + H := by
  intro x
  rw [ICdefect_test]
  simp only [Finset.sum_singleton]
  simpa using
    ((norm_sub_le (g.convolutionSquare.test x) (W.convolutionSquare.test x)).trans
      (add_le_add (hg x) (hW x)))

/-- The same norm control for the full finite Stage-B window family. -/
theorem defect_test_norm_le_of_uniformFamilyBounds
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hH : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i) :
    ∀ x : Real, ‖(ICdefect g s w lam).test x‖ ≤
      G + ∑ i ∈ s, |lam i| * H i := by
  intro x
  rw [ICdefect_test]
  have hsum :
      ‖∑ i ∈ s, (lam i : ℂ) • (w i).test x‖ ≤
        ∑ i ∈ s, ‖(lam i : ℂ) • (w i).test x‖ := by
    exact norm_sum_le _ _
  calc
    ‖g.test x - ∑ i ∈ s, (lam i : ℂ) • (w i).test x‖ ≤
        ‖g.test x‖ + ‖∑ i ∈ s, (lam i : ℂ) • (w i).test x‖ :=
      norm_sub_le _ _
    _ ≤ G + ∑ i ∈ s, ‖(lam i : ℂ) • (w i).test x‖ := by
      linarith [hg x, hsum]
    _ ≤ G + ∑ i ∈ s, |lam i| * H i := by
      have hsum2 :
          (∑ i ∈ s, ‖(lam i : ℂ) • (w i).test x‖) ≤
            ∑ i ∈ s, |lam i| * H i := by
        exact Finset.sum_le_sum fun i hi => by
          rw [norm_smul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hH i hi x) (abs_nonneg (lam i))
      exact add_le_add (le_refl G) hsum2

/-- Every compact-log test has a canonical uniform pointwise bound given by
its zero-order Schwartz seminorm. -/
theorem compactLogTest_norm_le_zeroSeminorm (F : CompactLogTest) :
    ∀ x : Real, ‖F.test x‖ ≤ SchwartzMap.seminorm ℂ 0 0 F.test := by
  intro x
  exact SchwartzMap.norm_le_seminorm ℂ F.test x

/-! ## Canonical archimedean budget -/

/-- The direct norm budget for the archimedean density, attached to the same
`CompactLogTest` owner as the gate.  A concrete producer may later bound this
quantity analytically, but the Stage-B interface no longer needs a separately
named integral expression. -/
noncomputable def archimedeanIntegralNorm (F : CompactLogTest) : Real :=
  ∫ y in Set.Ioi (0 : Real), ‖archimedeanIntegrand F y‖

/-- The canonical archimedean integral budget is nonnegative. -/
theorem archimedeanIntegralNorm_nonneg (F : CompactLogTest) :
    0 ≤ archimedeanIntegralNorm F := by
  unfold archimedeanIntegralNorm
  exact MeasureTheory.integral_nonneg fun y => norm_nonneg _

/-- A concrete integrable pointwise majorant produces the canonical
archimedean integral budget.  The producer only has to verify the bound on
positive `y`; restriction to `Ioi 0` supplies the almost-everywhere premise. -/
theorem archimedeanIntegralNorm_le_of_pointwiseEnvelope
    (F : CompactLogTest) (E : Real → Real)
    (hE : IntegrableOn E (Set.Ioi (0 : Real)))
    (hpoint : ∀ y : Real, 0 < y →
      ‖archimedeanIntegrand F y‖ ≤ E y) :
    archimedeanIntegralNorm F ≤ ∫ y in Set.Ioi (0 : Real), E y := by
  have hF : IntegrableOn (fun y : Real => ‖archimedeanIntegrand F y‖)
      (Set.Ioi (0 : Real)) :=
    (C1ArchimedeanIntegrabilityGeneric.integrableOn_archimedeanIntegrand F).norm
  have hpoint' : ∀ᵐ y : Real ∂(volume.restrict (Set.Ioi (0 : Real))),
      ‖archimedeanIntegrand F y‖ ≤ E y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hpoint y hy
  unfold archimedeanIntegralNorm
  exact MeasureTheory.integral_mono_ae hF hE hpoint'

/-- Canonical specialization of the archimedean norm channel: the point value
is controlled by the owner's zero-order Schwartz seminorm and the density is
stored in `archimedeanIntegralNorm` on that same owner. -/
theorem abs_archimedeanTerm_le_of_zeroSeminorm_and_integralNorm
    (F : CompactLogTest) :
    |archimedeanTerm F| ≤
      |Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
          SchwartzMap.seminorm ℂ 0 0 F.test +
        archimedeanIntegralNorm F := by
  apply abs_archimedeanTerm_le_of_zeroAndIntegralBounds F
    (SchwartzMap.seminorm ℂ 0 0 F.test) (archimedeanIntegralNorm F)
  · exact compactLogTest_norm_le_zeroSeminorm F 0
  · rfl

/-- An explicit support interval gives an explicit finite cutoff for every
visible prime-power index.  This avoids the noncanonical `supportRadius`
choice when a detector construction already exports its support endpoints. -/
theorem index_lt_of_support_subset_Icc
    (F : CompactLogTest) (a b : Real)
    (hsupport : Function.support F.test ⊆ Set.Icc a b)
    {n : Nat} (hprime : IsPrimePow n)
    (hterm : finitePrimeTermComplex F n ≠ 0) :
    n < Nat.ceil (Real.exp (max |a| |b|)) + 1 := by
  have hsum : F.test (Real.log n) + F.test (-Real.log n) ≠ 0 := by
    intro hzero
    apply hterm
    simp [finitePrimeTermComplex, hzero]
  have hpoint : F.test (Real.log n) ≠ 0 ∨ F.test (-Real.log n) ≠ 0 := by
    by_cases hleft : F.test (Real.log n) ≠ 0
    · exact Or.inl hleft
    by_cases hright : F.test (-Real.log n) ≠ 0
    · exact Or.inr hright
    exfalso
    apply hsum
    rw [not_ne_iff.mp hleft, not_ne_iff.mp hright]
    simp
  have hlogabs : |Real.log n| ≤ max |a| |b| := by
    rcases hpoint with hleft | hright
    · have hab := hsupport (Function.mem_support.mpr hleft)
      rcases le_total 0 (Real.log n) with hnonneg | hnonpos
      · rw [abs_of_nonneg hnonneg]
        exact (hab.2.trans (le_abs_self b)).trans (le_max_right _ _)
      · rw [abs_of_nonpos hnonpos]
        have hneg : -Real.log n ≤ -a := by linarith [hab.1]
        exact (hneg.trans (neg_le_abs a)).trans (le_max_left _ _)
    · have hab := hsupport (Function.mem_support.mpr hright)
      have hneglogabs : |-Real.log n| ≤ max |a| |b| := by
        rcases le_total 0 (-Real.log n) with hnonneg | hnonpos
        · rw [abs_of_nonneg hnonneg]
          exact (hab.2.trans (le_abs_self b)).trans (le_max_right _ _)
        · rw [abs_of_nonpos hnonpos]
          have hneg : -(-Real.log n) ≤ -a := by linarith [hab.1]
          exact (hneg.trans (neg_le_abs a)).trans (le_max_left _ _)
      simpa only [abs_neg] using hneglogabs
  have hnpos : (0 : Real) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt (IsPrimePow.one_lt hprime))
  have hlogle : Real.log n ≤ max |a| |b| :=
    (le_abs_self (Real.log n)).trans hlogabs
  have hnexp : (n : Real) ≤ Real.exp (max |a| |b|) := by
    have h := Real.exp_le_exp.mpr hlogle
    simpa [Real.exp_log hnpos] using h
  have hexpceil : Real.exp (max |a| |b|) ≤
      (Nat.ceil (Real.exp (max |a| |b|)) : Real) :=
    Nat.le_ceil (Real.exp (max |a| |b|))
  have hnceil : n ≤ Nat.ceil (Real.exp (max |a| |b|)) := by
    exact_mod_cast hnexp.trans hexpceil
  exact Nat.lt_succ_iff.mpr hnceil

/-- The exact visible-prime set is contained in the support-derived finite
range, so a detector's exported support endpoints determine its arithmetic
cutoff without changing the owner. -/
theorem globalPrimeIndexSet_subset_range_of_support_subset_Icc
    (F : CompactLogTest) (a b : Real)
    (hsupport : Function.support F.test ⊆ Set.Icc a b) :
    globalPrimeIndexSet F ⊆
      Finset.range (Nat.ceil (Real.exp (max |a| |b|)) + 1) := by
  intro n hn
  have hmem := (mem_globalPrimeIndexSet_iff F n).mp hn
  exact Finset.mem_range.mpr
    (index_lt_of_support_subset_Icc F a b hsupport hmem.1 hmem.2)

/-- A support interval for a source test gives a concrete cutoff for the
visible prime powers of its convolution square. -/
theorem convolutionSquare_globalPrimeIndexSet_subset_range_of_support_subset_Icc
    (g : CompactLogTest) (a b : Real)
    (hsupport : Function.support g.test ⊆ Set.Icc a b) :
    globalPrimeIndexSet g.convolutionSquare ⊆
      Finset.range
        (Nat.ceil (Real.exp (max |(-(2 * max |a| |b|))| |(2 * max |a| |b|)|)) + 1) := by
  let R : Real := max |a| |b|
  have hsymm : Function.support g.test ⊆ Set.Icc (-R) R := by
    intro x hx
    have hab := hsupport hx
    constructor
    · exact (neg_le_neg (le_max_left |a| |b|)).trans
        ((neg_abs_le a).trans hab.1)
    · exact hab.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))
  have hsq : Function.support g.convolutionSquare.test ⊆ Set.Icc (-(2 * R)) (2 * R) :=
    CompactLogTest.convolutionSquare_support_subset_two_mul g
      (by simpa [R] using hsymm)
  simpa [R] using
    globalPrimeIndexSet_subset_range_of_support_subset_Icc
      g.convolutionSquare (-(2 * R)) (2 * R) hsq

/-- A common open support interval for a finite Stage-B family gives an
explicit arithmetic cutoff for the resulting defect. -/
theorem defect_globalPrimeIndexSet_subset_range_of_common_Ioo_support
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real) (B : Real)
    (hg : Function.support g.test ⊆ Set.Ioo (-B) B)
    (hw : ∀ i ∈ s, Function.support (w i).test ⊆ Set.Ioo (-B) B) :
    globalPrimeIndexSet (ICdefect g s w lam) ⊆
      Finset.range (Nat.ceil (Real.exp (max |(-B)| |B|)) + 1) := by
  have hDoo : Function.support (ICdefect g s w lam).test ⊆ Set.Ioo (-B) B :=
    support_ICdefect_subset hg hw
  exact globalPrimeIndexSet_subset_range_of_support_subset_Icc
    (ICdefect g s w lam) (-B) B (hDoo.trans Set.Ioo_subset_Icc_self)

/-! ## Finite visible-prime triangle bound -/

/-- The finite visible-prime contribution is bounded by any supplied
per-index absolute term bounds.  The index set is the owner's exact finite
visible set, so no density or infinite-prime interchange is hidden here. -/
theorem abs_finitePrimeSum_le_of_termBounds
    (F : CompactLogTest) (B : Nat → Real)
    (hB : ∀ n ∈ globalPrimeIndexSet F,
      |finitePrimeTerm F n| ≤ B n) :
    |finitePrimeSum F| ≤ ∑ n ∈ globalPrimeIndexSet F, B n := by
  unfold finitePrimeSum
  calc
    |∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n| ≤
        ∑ n ∈ globalPrimeIndexSet F, |finitePrimeTerm F n| := by
      exact Finset.abs_sum_le_sum_abs
        (s := globalPrimeIndexSet F)
        (f := fun n => finitePrimeTerm F n)
    _ ≤ ∑ n ∈ globalPrimeIndexSet F, B n := by
      exact Finset.sum_le_sum fun n hn => hB n hn

/-! ## Explicit finite-range prime budget -/

/-- Under a common support interval, the family defect's finite-prime budget
can be enlarged from its exact visible set to the explicit support-derived
`Finset.range`.  All summands are norm envelopes and hence nonnegative. -/
theorem abs_finitePrimeSum_defect_le_of_uniformFamilyBounds_and_commonSupport
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real) (Bsupport : Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i)
    (hgsupp : Function.support g.test ⊆ Set.Ioo (-Bsupport) Bsupport)
    (hwsupp : ∀ i ∈ s,
      Function.support (w i).test ⊆ Set.Ioo (-Bsupport) Bsupport) :
    |finitePrimeSum (ICdefect g s w lam)| ≤
      ∑ n ∈ Finset.range (Nat.ceil (Real.exp (max |(-Bsupport)| |Bsupport|)) + 1),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (G + ∑ i ∈ s, |lam i| * H i)) := by
  let D : CompactLogTest := ICdefect g s w lam
  let A : Real := G + ∑ i ∈ s, |lam i| * H i
  let Bterm : Nat → Real := fun n =>
    ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
      ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * A)
  have hsumH : 0 ≤ ∑ i ∈ s, |lam i| * H i := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (abs_nonneg _) (hH i hi)
  have hA : 0 ≤ A := add_nonneg hG hsumH
  have hD : ∀ x : Real, ‖D.test x‖ ≤ A := by
    intro x
    exact defect_test_norm_le_of_uniformFamilyBounds g s w lam G H hg hw x
  have hterm : ∀ n ∈ globalPrimeIndexSet D, |finitePrimeTerm D n| ≤ Bterm n := by
    intro n hn
    exact (abs_finitePrimeTerm_le_primeTermNormEnvelope D n).trans
      (primeTermNormEnvelope_le_of_uniformTestBound D n A hA hD)
  have hexact : |finitePrimeSum D| ≤
      ∑ n ∈ globalPrimeIndexSet D, Bterm n :=
    abs_finitePrimeSum_le_of_termBounds D Bterm hterm
  have hcut := defect_globalPrimeIndexSet_subset_range_of_common_Ioo_support
    g s w lam Bsupport hgsupp hwsupp
  have hrange :
      (∑ n ∈ globalPrimeIndexSet D, Bterm n) ≤
        ∑ n ∈ Finset.range (Nat.ceil (Real.exp (max |(-Bsupport)| |Bsupport|)) + 1),
          Bterm n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hcut
    intro n hn hnot
    dsimp [Bterm]
    positivity
  have htotal := hexact.trans hrange
  simpa [D, A, Bterm] using htotal

/-- The same explicit-cutoff bound after replacing every complex coefficient by
the real logarithmic coefficient.  This is the arithmetic-facing producer
interface for a common-support defect. -/
theorem abs_finitePrimeSum_defect_le_of_uniformFamilyBounds_and_logRange
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real) (Bsupport : Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i)
    (hgsupp : Function.support g.test ⊆ Set.Ioo (-Bsupport) Bsupport)
    (hwsupp : ∀ i ∈ s,
      Function.support (w i).test ⊆ Set.Ioo (-Bsupport) Bsupport) :
    |finitePrimeSum (ICdefect g s w lam)| ≤
      ∑ n ∈ Finset.range (Nat.ceil (Real.exp (max |(-Bsupport)| |Bsupport|)) + 1),
        Real.log (n : Real) *
          (2 * (G + ∑ i ∈ s, |lam i| * H i)) := by
  have hsumH : 0 ≤ ∑ i ∈ s, |lam i| * H i := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (abs_nonneg _) (hH i hi)
  have hA : 0 ≤ G + ∑ i ∈ s, |lam i| * H i :=
    add_nonneg hG hsumH
  have hbase := abs_finitePrimeSum_defect_le_of_uniformFamilyBounds_and_commonSupport
    g s w lam G H Bsupport hG hH hg hw hgsupp hwsupp
  have hlog := finitePrimeCoefficientSum_le_logSum
    (Finset.range (Nat.ceil (Real.exp (max |(-Bsupport)| |Bsupport|)) + 1))
    (G + ∑ i ∈ s, |lam i| * H i) hA
  exact hbase.trans (by simpa using hlog)

/-- The same bound specialized to the one-window P2 defect.  This is the
prime-side half of the future `|gate(defect)|` estimate; the archimedean half
must be supplied separately. -/
theorem abs_finitePrimeSum_defect_le_of_termBounds
    (g W : CompactLogTest) (B : Nat → Real)
    (hB : ∀ n ∈ globalPrimeIndexSet
        (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)),
      |finitePrimeTerm
        (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)) n| ≤ B n) :
    |finitePrimeSum
        (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1))| ≤
      ∑ n ∈ globalPrimeIndexSet
        (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)), B n := by
  exact abs_finitePrimeSum_le_of_termBounds _ B hB

/-- Combine the square bounds with the exact visible-prime envelope.  This is
the finite-prime producer interface in the variables used by Stage B. -/
theorem abs_finitePrimeSum_defect_le_of_uniformSquareBounds
    (g W : CompactLogTest) (G H : Real)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G)
    (hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H) :
    |finitePrimeSum (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))| ≤
      ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1)),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * (G + H)) := by
  let D : CompactLogTest := ICdefect g.convolutionSquare {()}
    (fun _ => W.convolutionSquare) (fun _ => 1)
  have hD : ∀ x : Real, ‖D.test x‖ ≤ G + H := by
    intro x
    exact defect_test_norm_le_of_uniformBounds g W G H hg hW x
  have hGH : 0 ≤ G + H := add_nonneg hG hH
  have hbound : |finitePrimeSum D| ≤
      ∑ n ∈ globalPrimeIndexSet D,
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * (G + H)) := by
    apply abs_finitePrimeSum_le_of_termBounds D
    intro n hn
    exact (abs_finitePrimeTerm_le_primeTermNormEnvelope D n).trans
      (primeTermNormEnvelope_le_of_uniformTestBound D n (G + H) hGH hD)
  simpa [D] using hbound

/-- Canonical specialization of the finite-prime bound using the zero-order
Schwartz seminorms of the detector and window squares. -/
theorem abs_finitePrimeSum_defect_le_of_zeroSeminorms
    (g W : CompactLogTest) :
    |finitePrimeSum (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))| ≤
      ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1)),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (SchwartzMap.seminorm ℂ 0 0 g.convolutionSquare.test +
              SchwartzMap.seminorm ℂ 0 0 W.convolutionSquare.test)) := by
  let G : Real := SchwartzMap.seminorm ℂ 0 0 g.convolutionSquare.test
  let H : Real := SchwartzMap.seminorm ℂ 0 0 W.convolutionSquare.test
  have hG : 0 ≤ G := by
    positivity
  have hH : 0 ≤ H := by
    positivity
  have hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G := by
    intro x
    exact compactLogTest_norm_le_zeroSeminorm g.convolutionSquare x
  have hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H := by
    intro x
    exact compactLogTest_norm_le_zeroSeminorm W.convolutionSquare x
  simpa [G, H] using
    abs_finitePrimeSum_defect_le_of_uniformSquareBounds g W G H hG hH hg hW

/-- Assemble the two P2-alpha channels once an independent archimedean bound
is supplied.  This is only a triangle-inequality consumer: the hypothesis
`harch` is an analytic input and is not a reformulation of the gate sign. -/
theorem abs_ICgate_le_of_archimedeanBound_and_termBounds
    (F : CompactLogTest) (A : Real) (B : Nat → Real)
    (harch : |archimedeanTerm F| ≤ A)
    (hBnonneg : ∀ n ∈ globalPrimeIndexSet F, 0 ≤ B n)
    (hB : ∀ n ∈ globalPrimeIndexSet F,
      |finitePrimeTerm F n| ≤ B n) :
    |ICgate F| ≤ A + ∑ n ∈ globalPrimeIndexSet F, B n := by
  have hprime := abs_finitePrimeSum_le_of_termBounds F B hB
  have hsum : 0 ≤ ∑ n ∈ globalPrimeIndexSet F, B n :=
    Finset.sum_nonneg fun n hn => hBnonneg n hn
  unfold ICgate
  calc
    |archimedeanTerm F + finitePrimeSum F| ≤
        |archimedeanTerm F| + |finitePrimeSum F| := abs_add_le _ _
    _ ≤ A + ∑ n ∈ globalPrimeIndexSet F, B n := by linarith

/-- Feed the finite-family norm bridge into the full gate estimate.  The only
analytic premise left here is the independent archimedean bound `harch`. -/
theorem abs_ICgate_defect_le_of_uniformFamilyBounds_and_arch
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real) (Aarch : Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (harch : |archimedeanTerm (ICdefect g s w lam)| ≤ Aarch)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i) :
    |ICgate (ICdefect g s w lam)| ≤
      Aarch + ∑ n ∈ globalPrimeIndexSet (ICdefect g s w lam),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (G + ∑ i ∈ s, |lam i| * H i)) := by
  let D : CompactLogTest := ICdefect g s w lam
  let A : Real := G + ∑ i ∈ s, |lam i| * H i
  have hsumH : 0 ≤ ∑ i ∈ s, |lam i| * H i := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (abs_nonneg _) (hH i hi)
  have hA : 0 ≤ A := by
    exact add_nonneg hG hsumH
  have hD : ∀ x : Real, ‖D.test x‖ ≤ A := by
    intro x
    exact defect_test_norm_le_of_uniformFamilyBounds g s w lam G H hg hw x
  let B : Nat → Real := fun n =>
    ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
      ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * A)
  have hBnonneg : ∀ n ∈ globalPrimeIndexSet D, 0 ≤ B n := by
    intro n hn
    dsimp [B]
    positivity
  have hB : ∀ n ∈ globalPrimeIndexSet D, |finitePrimeTerm D n| ≤ B n := by
    intro n hn
    exact (abs_finitePrimeTerm_le_primeTermNormEnvelope D n).trans
      (primeTermNormEnvelope_le_of_uniformTestBound D n A hA hD)
  have hgate := abs_ICgate_le_of_archimedeanBound_and_termBounds
    D Aarch B harch hBnonneg hB
  simpa [D, A, B] using hgate

/-- The direct Stage-B admission form: once the explicit analytic budget is at
most `epsilon`, the required defect gate inequality follows immediately. -/
theorem ICgate_defect_le_of_uniformFamilyBounds_and_arch_budget
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real) (Aarch epsilon : Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (harch : |archimedeanTerm (ICdefect g s w lam)| ≤ Aarch)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i)
    (hbudget : Aarch + ∑ n ∈ globalPrimeIndexSet (ICdefect g s w lam),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (G + ∑ i ∈ s, |lam i| * H i)) ≤ epsilon) :
    ICgate (ICdefect g s w lam) ≤ epsilon := by
  have hbound := abs_ICgate_defect_le_of_uniformFamilyBounds_and_arch
    g s w lam G H Aarch hG hH harch hg hw
  exact (le_abs_self _).trans (hbound.trans hbudget)

/-- Full same-owner Stage-B estimate with the archimedean channel supplied by
the canonical integral norm and the defect's zero-order Schwartz seminorm. -/
theorem abs_ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i) :
    |ICgate (ICdefect g s w lam)| ≤
      (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
          SchwartzMap.seminorm ℂ 0 0 (ICdefect g s w lam).test +
        archimedeanIntegralNorm (ICdefect g s w lam)) +
      ∑ n ∈ globalPrimeIndexSet (ICdefect g s w lam),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (G + ∑ i ∈ s, |lam i| * H i)) := by
  let D : CompactLogTest := ICdefect g s w lam
  let Aarch : Real :=
    |Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
        SchwartzMap.seminorm ℂ 0 0 D.test + archimedeanIntegralNorm D
  have harch : |archimedeanTerm D| ≤ Aarch := by
    dsimp [Aarch]
    exact abs_archimedeanTerm_le_of_zeroSeminorm_and_integralNorm D
  have hgate := abs_ICgate_defect_le_of_uniformFamilyBounds_and_arch
    g s w lam G H Aarch hG hH harch hg hw
  simpa [D, Aarch] using hgate

/-- Direct Stage-B admission form using only the canonical same-owner
archimedean norm and the explicit finite visible-prime budget. -/
theorem ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm_budget
    (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → Real)
    (G : Real) (H : ι → Real) (epsilon : Real)
    (hG : 0 ≤ G) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hg : ∀ x : Real, ‖g.test x‖ ≤ G)
    (hw : ∀ i ∈ s, ∀ x : Real, ‖(w i).test x‖ ≤ H i)
    (hbudget :
      (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
          SchwartzMap.seminorm ℂ 0 0 (ICdefect g s w lam).test +
        archimedeanIntegralNorm (ICdefect g s w lam)) +
      ∑ n ∈ globalPrimeIndexSet (ICdefect g s w lam),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
            (2 * (G + ∑ i ∈ s, |lam i| * H i)) ≤ epsilon) :
    ICgate (ICdefect g s w lam) ≤ epsilon := by
  have hbound := abs_ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm
    g s w lam G H hG hH hg hw
  exact (le_abs_self _).trans (hbound.trans hbudget)

/-- A canonical same-owner defect budget supplies the one-window Stage-B
contraction required by the route assembly.  The certified-window sign and
the scalar margin budget remain separate hypotheses. -/
noncomputable def stageBContraction_of_uniformSquareBounds_and_integralNorm_budget
    (g W : CompactLogTest) (G H mu epsilon b a : Real)
    (hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b)
    (hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a)
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G)
    (hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H)
    (hbudget :
      (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
          SchwartzMap.seminorm ℂ 0 0
            (ICdefect g.convolutionSquare {()}
              (fun _ => W.convolutionSquare) (fun _ => 1)).test +
        archimedeanIntegralNorm (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1))) +
      ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * (G + H)) ≤
      epsilon)
    (hmargin : epsilon ≤ mu) :
    ICStageBContraction g := by
  have hdec := ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm_budget
    (g.convolutionSquare) {()} (fun _ => W.convolutionSquare) (fun _ => 1)
    G (fun _ => H) epsilon hG
    (by
      intro i hi
      simpa using hH)
    hg
    (by
      intro i hi x
      simpa using hW x)
    (by simpa using hbudget)
  exact stageBContraction_of_certifiedWindow g W hgsupp hWsupp hcert hdec hmargin

/-- Direct orbit-window gate consumer for a one-window canonical P2 budget. -/
theorem orbitGate_of_uniformSquareBounds_and_integralNorm_budget
    (g W : CompactLogTest) (G H mu epsilon b a : Real)
    (hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b)
    (hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a)
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G)
    (hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H)
    (hbudget :
      (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
          SchwartzMap.seminorm ℂ 0 0
            (ICdefect g.convolutionSquare {()}
              (fun _ => W.convolutionSquare) (fun _ => 1)).test +
        archimedeanIntegralNorm (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1))) +
      ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)),
        ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
          ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * (G + H)) ≤
      epsilon)
    (hmargin : epsilon ≤ mu) :
    orbitWindowSemiLocalGate g := by
  exact orbitWindowSemiLocalGate_of_contraction g
    (stageBContraction_of_uniformSquareBounds_and_integralNorm_budget
      g W G H mu epsilon b a hgsupp hWsupp hcert hG hH hg hW hbudget hmargin)
    (by
      simpa [stageBContraction_of_uniformSquareBounds_and_integralNorm_budget,
        stageBContraction_of_certifiedWindow]
        using hmargin)

/-! ## Minimal same-detector P2 producer contract -/

/-- All analytic data needed by the one-window P2 consumer, packed with the
same detector owner.  This is a data contract for a future producer: its
budget field is an explicit inequality and carries no gate or `qw` conclusion.
-/
structure P2OneWindowBudgetWitness (g : CompactLogTest) where
  W : CompactLogTest
  G : Real
  H : Real
  mu : Real
  epsilon : Real
  b : Real
  a : Real
  hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b
  hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a
  hcert : ICgate W.convolutionSquare ≤ -mu
  hG : 0 ≤ G
  hH : 0 ≤ H
  hg : ∀ x : Real, ‖g.convolutionSquare.test x‖ ≤ G
  hW : ∀ x : Real, ‖W.convolutionSquare.test x‖ ≤ H
  hbudget :
    (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
        SchwartzMap.seminorm ℂ 0 0
          (ICdefect g.convolutionSquare {()}
            (fun _ => W.convolutionSquare) (fun _ => 1)).test +
      archimedeanIntegralNorm (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1))) +
    ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1)),
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ * (2 * (G + H)) ≤
    epsilon
  hmargin : epsilon ≤ mu

/-- A packed P2 witness produces the route's orbit-window gate for its owner. -/
theorem orbitGate_of_p2OneWindowBudgetWitness
    (g : CompactLogTest) (p : P2OneWindowBudgetWitness g) :
    orbitWindowSemiLocalGate g := by
  exact orbitGate_of_uniformSquareBounds_and_integralNorm_budget
    g p.W p.G p.H p.mu p.epsilon p.b p.a p.hgsupp p.hWsupp p.hcert
    p.hG p.hH p.hg p.hW p.hbudget p.hmargin

/-- Same-detector exit contract: if every right-oriented off-line zero admits
one healthy detector carrying a packed P2 witness, the existing contradiction
consumer yields `SourceRH`.  The theorem deliberately leaves witness
construction as the sole analytic producer obligation. -/
theorem sourceRH_of_healthyDetector_p2OneWindowBudgetWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (P2OneWindowBudgetWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  exact ⟨g, hdata,
    qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate hdata
      (orbitGate_of_p2OneWindowBudgetWitness g hp2)⟩

/-- Canonical producer contract: the pointwise constants `G` and `H` are
chosen as the zero-order Schwartz seminorms of the two square owners, so the
producer supplies only the genuine scalar budget and window certificate. -/
structure P2CanonicalOneWindowBudgetWitness (g : CompactLogTest) where
  W : CompactLogTest
  mu : Real
  epsilon : Real
  b : Real
  a : Real
  hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b
  hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a
  hcert : ICgate W.convolutionSquare ≤ -mu
  hbudget :
    (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
        SchwartzMap.seminorm ℂ 0 0
          (ICdefect g.convolutionSquare {()}
            (fun _ => W.convolutionSquare) (fun _ => 1)).test +
      archimedeanIntegralNorm (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1))) +
    ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1)),
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : Real) : Real) : Complex)‖ *
          (2 * (SchwartzMap.seminorm ℂ 0 0 g.convolutionSquare.test +
            SchwartzMap.seminorm ℂ 0 0 W.convolutionSquare.test)) ≤
      epsilon
  hmargin : epsilon ≤ mu

/-- Expand a canonical budget witness into the full pointwise P2 witness. -/
noncomputable def P2CanonicalOneWindowBudgetWitness.toP2OneWindowBudgetWitness
    (g : CompactLogTest) (p : P2CanonicalOneWindowBudgetWitness g) :
    P2OneWindowBudgetWitness g :=
  { W := p.W
    G := SchwartzMap.seminorm ℂ 0 0 g.convolutionSquare.test
    H := SchwartzMap.seminorm ℂ 0 0 p.W.convolutionSquare.test
    mu := p.mu
    epsilon := p.epsilon
    b := p.b
    a := p.a
    hgsupp := p.hgsupp
    hWsupp := p.hWsupp
    hcert := p.hcert
    hG := by positivity
    hH := by positivity
    hg := compactLogTest_norm_le_zeroSeminorm g.convolutionSquare
    hW := compactLogTest_norm_le_zeroSeminorm p.W.convolutionSquare
    hbudget := by simpa using p.hbudget
    hmargin := p.hmargin }

/-- A canonical one-window budget witness directly supplies the orbit gate. -/
theorem orbitGate_of_p2CanonicalOneWindowBudgetWitness
    (g : CompactLogTest) (p : P2CanonicalOneWindowBudgetWitness g) :
    orbitWindowSemiLocalGate g := by
  exact orbitGate_of_p2OneWindowBudgetWitness g
    (P2CanonicalOneWindowBudgetWitness.toP2OneWindowBudgetWitness g p)

/-- Same-detector exit using the canonical scalar P2 producer contract. -/
theorem sourceRH_of_healthyDetector_p2CanonicalOneWindowBudgetWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (P2CanonicalOneWindowBudgetWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  exact ⟨g, hdata,
    qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate hdata
      (orbitGate_of_p2CanonicalOneWindowBudgetWitness g hp2)⟩

/-- A pinned canonical producer contract keeps the detector, its orbit support,
and the finite visible-prime cutoff on one explicit owner.  The support and
cutoff fields are retained as audit data; the scalar budget and certified
window remain the only analytic sign inputs consumed below. -/
theorem sourceRH_of_pinnedOrbitDetector_p2CanonicalOneWindowBudgetWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest, ∃ n : Nat,
          HealthyYoshidaDetectorData rho.1 g ∧
          Function.support g.test ⊆
            Set.Ioo (-((n + 2 : ℕ) : Real)) (((n + 2 : ℕ) : Real)) ∧
          (∀ q ∈ C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare,
            (q : Real) < Real.exp (2 * ((n + 2 : ℕ) : Real))) ∧
          Nonempty (P2CanonicalOneWindowBudgetWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, _n, hdata, _hsupport, _hvisible, ⟨hp2⟩⟩ :=
    hproducer rho hright
  exact ⟨g, hdata,
    qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate hdata
      (orbitGate_of_p2CanonicalOneWindowBudgetWitness g hp2)⟩

end C1P2DefectControl
end Source
end ConnesWeilRH
