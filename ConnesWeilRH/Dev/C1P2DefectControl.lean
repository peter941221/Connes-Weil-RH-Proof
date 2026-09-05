/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1T2Assembly

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
open CCM25Concrete.CompactLogConvolution
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

/-- Every compact-log test has a canonical uniform pointwise bound given by
its zero-order Schwartz seminorm. -/
theorem compactLogTest_norm_le_zeroSeminorm (F : CompactLogTest) :
    ∀ x : Real, ‖F.test x‖ ≤ SchwartzMap.seminorm ℂ 0 0 F.test := by
  intro x
  exact SchwartzMap.norm_le_seminorm ℂ F.test x

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

end C1P2DefectControl
end Source
end ConnesWeilRH
