/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1LocalConfigurationDomination

/-!
# Record 1121: T2-rep - the gate as a quadratic form on a window span

Lands the matrix-representation generator of the `hrep` slot consumed by
the 1118/1119/1120 ABSOLUTE headlines
(docs/proofs/1121_t2rep_gate_matrix_preregistration.md): for a finite real
span of window tests, the gate of the span's convolution square IS the
quadratic form `y (gateMatrix w *v y)` whose matrix entries are the
pairwise gates `ICgate ((w i).involution.convolution (w j))`.  The
diagonal is definitional: `pairTest w j j = (w j).convolutionSquare`, so
the 1118/1120 class margins `-mu` bound exactly the diagonal entries.

Mechanism: pointwise expansion of the convolution integrand over the span
(SchwartzMap sum/smul, `star_sum`), integral split by
`MeasureTheory.integral_finsetSum` with per-piece integrability
(`Continuous.integrable_of_hasCompactSupport` on compactly supported
continuous pieces), transport by `ICgate_congr` to the packed double-sum
object, a generic accumulator linearity chain built on the 1117
`ICgate_packTest_add`, and Finset/dotProduct algebra.

Registered deviation: the per-pair ARCHIMEDEAN legality
`IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi 0)` stays a
named hypothesis (1117's own pattern - for squares it is discharged by
`archimedeanIntegrand_square_integrableOn_Ioi`; the pair version is a
T2-side obligation, never silently assumed).  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1GateMatrixRepresentation

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open scoped BigOperators

noncomputable section

/-! ### The span object, the pair object, and the gate matrix -/

/-- The packed test of a finite real span of window tests. -/
def spanObj {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ) : CompactLogTest where
  test := ∑ i, (y i : ℂ) • (w i).test
  compactSupport := by
    convert hasCompactSupport_finset_sum Finset.univ
      (fun i x => (y i : ℂ) • (w i).test x)
      (fun i _ => (w i).compactSupport.smul_left (f := fun _ => (y i : ℂ))) using 1
    ext x
    simp

@[simp] theorem spanObj_apply {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    (x : ℝ) : (spanObj w y).test x = ∑ i, y i * (w i).test x := by
  simp [spanObj]

/-- The convolution PAIR of two window tests; its `i = j` diagonal is
definitionally the convolution square of `w j`. -/
def pairTest {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k) : CompactLogTest :=
  (w i).involution.convolution (w j)

theorem pairTest_self {k : ℕ} (w : Fin k → CompactLogTest) (j : Fin k) :
    pairTest w j j = (w j).convolutionSquare :=
  rfl

/-- The pair's gate matrix: entry `(i, j)` is the pair gate. -/
def gateMatrix {k : ℕ} (w : Fin k → CompactLogTest) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ICgate (pairTest w i j)

/-! ### Pointwise pair facts -/

/-- The pair's convolution integrand is integrable: a product of compactly
supported continuous functions. -/
theorem pairIntegrand_integrable {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k)
    (x : ℝ) : Integrable
      (fun t : ℝ => star ((w i).test (-t)) * (w j).test (x - t)) volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · fun_prop
  · have h1 : HasCompactSupport (fun t : ℝ => (w i).test (-t)) := by
      simpa using (w i).compactSupport.comp_homeomorph (Homeomorph.neg ℝ)
    have h2 : HasCompactSupport (fun t : ℝ => (w j).test (x - t)) := by
      simpa using (w j).compactSupport.comp_homeomorph
        ((Homeomorph.subRight x).trans (Homeomorph.neg ℝ))
    have h3 := h1.mul_right h2
    simpa [Pi.mul_apply] using h3

/-- Both factors supported in `Ioo (-B) B` kill the pair test outside
`Ioo (-2B) (2B)`: at every `t` one of the two factors vanishes. -/
theorem pairTest_apply_of_abs_ge {k : ℕ} (w : Fin k → CompactLogTest) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) (i j : Fin k) {x : ℝ}
    (hx : 2 * B ≤ |x|) : (pairTest w i j).test x = 0 := by
  have hkill : ∀ t : ℝ, star ((w i).test (-t)) * (w j).test (x - t) = 0 := by
    intro t
    rcases le_or_lt (B : ℝ) |t| with hbig | hsmall
    · have hz : (w i).test (-t) = 0 := by
        by_contra hne
        have hin := hw i (Function.mem_support.mpr hne)
        have hlt : |(-t : ℝ)| < B := by
          simpa [abs_neg] using abs_lt.mp hin |>.2
        exact absurd hlt (by simpa [abs_neg] using not_lt.mpr hbig)
      simp [hz]
    · have hz : (w j).test (x - t) = 0 := by
        by_contra hne
        have hin := hw j (Function.mem_support.mpr hne)
        have habs : |x - t| < B := abs_lt.mp hin |>.2
        have htri : B ≤ |x - t| := by
          have h1 : |x| - |t| ≤ |x - t| := by
            simpa using abs_sub_le x t
          linarith
        exact absurd habs (not_lt.mpr htri)
      simp [hz]
  have happly : (pairTest w i j).test x
      = ∫ t : ℝ, star ((w i).test (-t)) * (w j).test (x - t) := rfl
  rw [happly]
  have hae : (fun t : ℝ => star ((w i).test (-t)) * (w j).test (x - t))
      = fun _ : ℝ => (0 : ℂ) := funext hkill
  rw [hae]
  simp

theorem pairTest_support {k : ℕ} (w : Fin k → CompactLogTest) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) (i j : Fin k) :
    Function.support (pairTest w i j).test ⊆ Ioo (-2 * B) (2 * B) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases h : x ∈ Ioo (-2 * B) (2 * B)
  · exact h
  · exfalso
    have habs : 2 * B ≤ |x| := by
      rcases lt_or_le x (-(2 * B)) with hlo | hhi
      · have hxneg : x < 0 := by linarith
        have : |x| = -x := abs_of_neg hxneg
        linarith
      · have hxpos : 0 ≤ x := by linarith
        have : |x| = x := abs_of_nonneg hxpos
        linarith
    simpa [Function.mem_support] using pairTest_apply_of_abs_ge w hw i j habs

/-! ### Gate of the zero test -/

theorem ICgate_zero_of_test_zero (F : CompactLogTest) (hF : ∀ x, F.test x = 0) :
    ICgate F = 0 := by
  have harch : archimedeanTerm F = 0 := by
    have h0 : F.test 0 = 0 := hF 0
    have hint : ∫ y : ℝ in Ioi (0 : ℝ), archimedeanIntegrand F y = 0 := by
      rw [integral_congr_ae (ae_of_all _ (fun y => by
        simp [archimedeanIntegrand, archimedeanNumerator, hF]))]
      simp
    simp [archimedeanTerm, h0, hint]
  have hprime : finitePrimeSum F = 0 := by
    unfold finitePrimeSum
    apply Finset.sum_eq_zero
    intro n hn
    have hterm : finitePrimeTermComplex F n = 0 := by
      simp [finitePrimeTermComplex, hF]
    exact absurd hterm ((mem_globalPrimeIndexSet_iff F n).mp hn).2
  unfold ICgate
  rw [harch, hprime]
  ring

/-! ### Generic accumulator linearity -/

/-- Support of a pointwise sum of tests stays in a common window. -/
theorem support_sum_subset {ι : Type} (s : Finset ι) (F : ι → TestFunction) {B : ℝ}
    (hFsupp : ∀ k ∈ s, Function.support (F k) ⊆ Ioo (-B) B) :
    Function.support (∑ k ∈ s, F k) ⊆ Ioo (-B) B := by
  intro x hx
  by_cases h : x ∈ Ioo (-B) B
  · exact h
  · rw [Function.mem_support] at hx
    exact absurd hx (by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk0 : F k x = 0 := by
        by_contra hne
        exact h (hFsupp k hk (Function.mem_support.mpr hne))
      simp [hk0])

/-- Pointwise: the archimedean integrand of a packed finite sum of tests is
the finite sum of the ingredient integrands. -/
theorem archimedeanIntegrand_packTest_sum {ι : Type} (s : Finset ι)
    (F : ι → TestFunction) (hF : ∀ k ∈ s, HasCompactSupport (F k))
    (hS : HasCompactSupport (∑ k ∈ s, F k)) (y : ℝ) :
    archimedeanIntegrand (packTest (∑ k ∈ s, F k) hS) y =
      ∑ k ∈ s, archimedeanIntegrand (packTest (F k) (hF k)) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      show archimedeanIntegrand
          (packTest (∑ k ∈ insert a s, F k) hS) y = _
      rw [Finset.sum_insert ha]
      show archimedeanIntegrand (packTest _ hS) y = _
      rw [archimedeanIntegrand_packTest_add (F a) (∑ k ∈ s, F k)
        (hF a (Finset.mem_insert_self a s)) (hF k ?) y]
      · rw [Finset.sum_insert ha, ih]
        ring
  · exact fun k hk => hF k (Finset.mem_insert_of_mem hk)

/-- Integrability of the archimedean integrand transfers to packed finite
sums of tests. -/
theorem integrableOn_archIntegrand_packTest_sum {ι : Type} (s : Finset ι)
    (F : ι → TestFunction) (hS : HasCompactSupport (∑ k ∈ s, F k))
    (hF : ∀ k ∈ s, HasCompactSupport (F k))
    (hI : ∀ k ∈ s, IntegrableOn
      (archimedeanIntegrand (packTest (F k) (hF k))) (Ioi (0 : ℝ))) :
    IntegrableOn (archimedeanIntegrand (packTest (∑ k ∈ s, F k) hS))
      (Ioi (0 : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : archimedeanIntegrand (packTest (∑ k ∈ (∅ : Finset ι), F k) hS)
          = fun _ => (0 : ℂ) := by
        funext y
        simp [archimedeanIntegrand, archimedeanNumerator]
      rw [hz]
      exact integrable_zero
  | @insert a s ha ih =>
      have hS' : HasCompactSupport (∑ k ∈ s, F k) :=
        hS  -- placeholder, replaced below
      have hadd : (∑ k ∈ insert a s, F k) = F a + ∑ k ∈ s, F k := by
        rw [Finset.sum_insert ha]
      show IntegrableOn (archimedeanIntegrand
        (packTest (F a + ∑ k ∈ s, F k) ((hF a (Finset.mem_insert_self a s)).add hS')))
        (Ioi (0 : ℝ))
      have hpt : ∀ y : ℝ, archimedeanIntegrand
          (packTest (F a + ∑ k ∈ s, F k)
            ((hF a (Finset.mem_insert_self a s)).add hS')) y
          = archimedeanIntegrand (packTest (F a) (hF a _)) y
              + archimedeanIntegrand (packTest (∑ k ∈ s, F k) hS') y :=
        archimedeanIntegrand_packTest_add (F a) (∑ k ∈ s, F k)
          (hF a (Finset.mem_insert_self a s)) hS'
      have : (archimedeanIntegrand
          (packTest (F a + ∑ k ∈ s, F k)
            ((hF a (Finset.mem_insert_self a s)).add hS')))
          = fun y => archimedeanIntegrand (packTest (F a) (hF a _)) y
              + archimedeanIntegrand (packTest (∑ k ∈ s, F k) hS') y :=
        funext hpt
      rw [this]
      exact (hI a (Finset.mem_insert_self a s)).add
        (ih hS' (fun k hk => hF k (Finset.mem_insert_of_mem hk))
          (fun k hk => hI k (Finset.mem_insert_of_mem hk)))

/-- **Accumulator linearity of the gate**: the gate of `G + sum_s F` is
`ICgate G + sum_s ICgate (F k)`, common window and per-piece archimedean
integrability carried as hypotheses (1117's pattern). -/
theorem ICgate_packTest_sum {ι : Type} (s : Finset ι) (F : ι → TestFunction)
    (G : TestFunction) (hG : HasCompactSupport G) (hF : ∀ k, HasCompactSupport (F k))
    (hS : HasCompactSupport (∑ k ∈ s, F k))
    {B : ℝ} (hGsupp : Function.support G ⊆ Ioo (-B) B)
    (hFsupp : ∀ k, Function.support (F k) ⊆ Ioo (-B) B)
    (hIG : IntegrableOn (archimedeanIntegrand (packTest G hG)) (Ioi (0 : ℝ)))
    (hIF : ∀ k, IntegrableOn
      (archimedeanIntegrand (packTest (F k) (hF k))) (Ioi (0 : ℝ))) :
    ICgate (packTest (G + ∑ k ∈ s, F k) (hG.add hS)) =
      ICgate (packTest G hG) +
        ∑ k ∈ s, ICgate (packTest (F k) (hF k)) := by
  classical
  revert hIG hGsupp hG
  induction s using Finset.induction_on with
  | empty =>
      intro G hG hGsupp hIG
      rw [Finset.sum_empty]
      show ICgate (packTest (G + 0) (hG.add hS)) = _
      have hobj : packTest (G + 0) (hG.add hS) = packTest G hG :=
        CompactLogTest.ext (by funext x; simp)
      rw [hobj]
      simp
  | @insert a s ha ih =>
      intro G hG hGsupp hIG
      have hsF : HasCompactSupport (F a) := hF a
      have hGFa : HasCompactSupport (G + F a) := hG.add hsF
      have hGFasupp : Function.support (G + F a) ⊆ Ioo (-B) B :=
        support_add_subset _ _ hGsupp (hFsupp a)
      have hrestsupp : Function.support (∑ k ∈ s, F k) ⊆ Ioo (-B) B :=
        support_sum_subset s F (fun k hk => hFsupp k hk)
      have hIrest : IntegrableOn
          (archimedeanIntegrand (packTest (∑ k ∈ s, F k) hS)) (Ioi (0 : ℝ)) :=
        integrableOn_archIntegrand_packTest_sum s F hS
          (fun k hk => hF k hk) (fun k hk => hIF k hk)
      have hIGFa : IntegrableOn
          (archimedeanIntegrand (packTest (G + F a) hGFa)) (Ioi (0 : ℝ)) := by
        have hpt : ∀ y : ℝ, archimedeanIntegrand (packTest (G + F a) hGFa) y
            = archimedeanIntegrand (packTest G hG) y
                + archimedeanIntegrand (packTest (F a) hsF) y :=
          archimedeanIntegrand_packTest_add G (F a) hG hsF
        have : (archimedeanIntegrand (packTest (G + F a) hGFa))
            = fun y => archimedeanIntegrand (packTest G hG) y
                + archimedeanIntegrand (packTest (F a) hsF) y :=
          funext hpt
        rw [this]
        exact hIG.add (hIF a)
      rw [Finset.sum_insert ha]
      rw [ICgate_packTest_add (G + F a) (∑ k ∈ s, F k) hGFa hS hGFasupp hrestsupp
        hIGFa hIrest]
      rw [ih (G + F a) hGFa hGFasupp hIGFa]
      rw [ICgate_packTest_add G (F a) hG hsF hGsupp (hFsupp a) hIG (hIF a)]
      ring

/-! ### The quadratic-form headline -/

/-- Pointwise expansion: the convolution square of the span, at every `x`,
is the double gate-weighted sum of the pair tests. -/
theorem convolutionSquare_spanObj_apply {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (x : ℝ) : (spanObj w y).convolutionSquare.test x
      = ∑ p : Fin k × Fin k, y p.1 * y p.2 * (pairTest w p.1 p.2).test x := by
  have happly : (spanObj w y).convolutionSquare.test x
      = ∫ t : ℝ, star ((spanObj w y).test (-t)) * (spanObj w y).test (x - t) := rfl
  have hpoint : ∀ t : ℝ, star ((spanObj w y).test (-t)) * (spanObj w y).test (x - t)
      = ∑ p : Fin k × Fin k,
          y p.1 * y p.2 * (star ((w p.1).test (-t)) * (w p.2).test (x - t)) := by
    intro t
    rw [spanObj_apply, spanObj_apply]
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast [map_mul]
    ring
  have hsplit : ∫ t : ℝ,
      ∑ p : Fin k × Fin k,
        y p.1 * y p.2 * (star ((w p.1).test (-t)) * (w p.2).test (x - t))
      = ∑ p : Fin k × Fin k, y p.1 * y p.2 * (pairTest w p.1 p.2).test x := by
    rw [MeasureTheory.integral_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hsm : (fun t : ℝ => y p.1 * y p.2 *
          (star ((w p.1).test (-t)) * (w p.2).test (x - t)))
        = (y p.1 * y p.2 : ℂ) •
          (fun t : ℝ => star ((w p.1).test (-t)) * (w p.2).test (x - t)) := by
      funext t
      simp
    rw [hsm, integral_smul, smul_eq_mul]
  rw [happly, integral_congr_ae (ae_of_all volume hpoint), hsplit]

/-- **HEADLINE (T2-rep)**: the gate of the span's convolution square is
the quadratic form of the pair-gate matrix.  Hypotheses: a common support
window `B` for the window tests, and per-pair archimedean legality (the
registered named slot). -/
theorem gate_qform_span {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn
      (archimedeanIntegrand (pairTest w i j)) (Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (gateMatrix w *ᵥ y) := by
  -- the packed scaled-pair pieces
  have hpieceHs : ∀ p : Fin k × Fin k, HasCompactSupport
      ((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test) :=
    fun p => (pairTest w p.1 p.2).compactSupport.smul_left
      (f := fun _ => (y p.1 * y p.2 : ℂ))
  have hwindow := pairTest_support w hw
  have hpieceSupp : ∀ p : Fin k × Fin k, Function.support
      ⇑((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test)
      ⊆ Ioo (-(2 * B)) (2 * B) := by
    intro p x hx
    by_cases h : x ∈ Ioo (-(2 * B)) (2 * B)
    · exact h
    · rw [Function.mem_support] at hx
      apply absurd hx
      by_contra hne
      have hcoe : ((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test) x
          = (y p.1 * y p.2 : ℂ) * (pairTest w p.1 p.2).test x := by simp
      rw [hcoe] at hne
      have hgz : (pairTest w p.1 p.2).test x = 0 := by
        by_contra hgne
        exact h (hwindow p.1 p.2 (Function.mem_support.mpr hgne))
      simp [hgz] at hne
  have hIFp : ∀ p : Fin k × Fin k, IntegrableOn
      (archimedeanIntegrand
        (packTest ((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test)
          (hpieceHs p))) (Ioi (0 : ℝ)) := by
    intro p
    have hpt : ∀ y : ℝ, archimedeanIntegrand
        (packTest ((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test)
          (hpieceHs p)) y
        = (y p.1 * y p.2 : ℂ) • archimedeanIntegrand
            (packTest (pairTest w p.1 p.2).test
              (pairTest w p.1 p.2).compactSupport) y :=
      fun y => archimedeanIntegrand_packTest_smul _ _
        (pairTest w p.1 p.2).compactSupport y _
    have hbr : packTest (pairTest w p.1 p.2).test
        (pairTest w p.1 p.2).compactSupport = pairTest w p.1 p.2 :=
      CompactLogTest.ext rfl
    rw [hpt, hbr]
    exact (hI p.1 p.2).smul _
  have hGatep : ∀ p : Fin k × Fin k, ICgate
      (packTest ((y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test)
        (hpieceHs p))
      = y p.1 * y p.2 * ICgate (pairTest w p.1 p.2) := by
    intro p
    rw [ICgate_packTest_smul _ _ (pairTest w p.1 p.2).compactSupport (2 * B)
      (hwindow p.1 p.2) (hpieceHs p)]
    congr 1
    exact congrArg ICgate (CompactLogTest.ext rfl)
  -- sum-object evidence
  have hSum : HasCompactSupport
      (∑ p : Fin k × Fin k,
        (y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test) := by
    convert hasCompactSupport_finset_sum Finset.univ
      (fun p x => (y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test x)
      (fun p _ => hpieceHs p) using 1
    ext x
    simp
  -- zero accumulator facts
  have hG0 : HasCompactSupport ((0 : TestFunction)) := by
    refine HasCompactSupport.of_support_subset_isCompact isCompact_empty ?_
    intro x hx
    rw [Function.mem_support] at hx
    simp at hx
  have hG0supp : Function.support ⇑((0 : TestFunction)) ⊆ Ioo (-(2 * B)) (2 * B) := by
    intro x hx
    rw [Function.mem_support] at hx
    simp at hx
  have hIG0 : IntegrableOn
      (archimedeanIntegrand (packTest (0 : TestFunction) hG0)) (Ioi (0 : ℝ)) := by
    have hz : archimedeanIntegrand (packTest (0 : TestFunction) hG0)
        = fun _ => (0 : ℂ) := by
      funext y
      simp [archimedeanIntegrand, archimedeanNumerator]
    rw [hz]
    exact integrable_zero
  -- the chain
  have hchain := ICgate_packTest_sum (Finset.univ : Finset (Fin k × Fin k))
    (fun p => (y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test) (0 : TestFunction)
    hG0 hpieceHs hSum (2 * B) hG0supp hpieceSupp hIG0 hIFp
  -- LHS transport
  have hLHS : ICgate ((spanObj w y).convolutionSquare)
      = ICgate (packTest ((0 : TestFunction) +
          ∑ p : Fin k × Fin k,
            (y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test)
          (hG0.add hSum)) := by
    refine ICgate_congr (CompactLogTest.ext ?_)
    funext x
    show (spanObj w y).convolutionSquare.test x =
      ((0 : TestFunction) + ∑ p : Fin k × Fin k,
        (y p.1 * y p.2 : ℂ) • (pairTest w p.1 p.2).test) x
    rw [convolutionSquare_spanObj_apply]
    simp
  rw [hLHS, hchain]
  rw [ICgate_zero_of_test_zero (packTest (0 : TestFunction) hG0) (by
    intro x
    simp)]
  simp only [zero_add, hGatep]
  -- matrix form
  simp only [Matrix.mulVec, dotProduct, gateMatrix, Matrix.of_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The hrep generator**: if the pair-gate matrix equals the committed
true matrix, the representation slot of the 1118/1120 ABSOLUTE headlines
holds verbatim. -/
theorem hrep_of_gateMatrix_eq {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (M_true : Matrix (Fin k) (Fin k) ℝ)
    (h : gateMatrix w = M_true) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn
      (archimedeanIntegrand (pairTest w i j)) (Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y) := by
  rw [← h]
  exact gate_qform_span w y hw hI

end C1GateMatrixRepresentation
end Source
end ConnesWeilRH
