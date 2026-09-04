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
open Matrix
open scoped BigOperators

noncomputable section


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

def pairTest {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k) : CompactLogTest :=
  (w i).involution.convolution (w j)

/-- The diagonal pair is definitionally the convolution square. -/
theorem pairTest_self {k : ℕ} (w : Fin k → CompactLogTest) (j : Fin k) :
    pairTest w j j = (w j).convolutionSquare := rfl

theorem pairIntegrand_integrable {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k)
    (x : ℝ) : Integrable
      (fun t : ℝ => star ((w i).test (-t)) * (w j).test (x - t)) volume := by
  have hex : MeasureTheory.ConvolutionExistsAt (w i).involution.test (w j).test x
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
    exact HasCompactSupport.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℂ) (w i).involution.compactSupport
      (w i).involution.test.integrable.locallyIntegrable
      ((w j).test.smooth ⊤).continuous x
  simpa only [CompactLogTest.involution_apply] using hex

theorem pairTest_apply_of_abs_ge {k : ℕ} (w : Fin k → CompactLogTest) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) (i j : Fin k) {x : ℝ}
    (hx : 2 * B ≤ |x|) : (pairTest w i j).test x = 0 := by
  have hkill : ∀ t : ℝ, star ((w i).test (-t)) * (w j).test (x - t) = 0 := by
    intro t
    by_cases hbig : B ≤ |t|
    · have hz : (w i).test (-t) = 0 := by
        by_contra hne
        have hin := hw i (Function.mem_support.mpr hne)
        have hlt : |(-t : ℝ)| < B := abs_lt.mpr hin
        exact (not_lt_of_ge (by simpa [abs_neg] using hbig)) hlt
      simp [hz]
    · have hsmall : |t| < B := lt_of_not_ge hbig
      have hz : (w j).test (x - t) = 0 := by
        by_contra hne
        have hin := hw j (Function.mem_support.mpr hne)
        have hlt : |x - t| < B := abs_lt.mpr hin
        have hle : B ≤ |x - t| := by
          have htriangle : |x| ≤ |x - t| + |t| := by
            simpa [add_comm] using (abs_sub_le x (x - t) 0)
          calc
            B ≤ |x| - |t| := by linarith
            _ ≤ |x - t| := by linarith
        exact (not_lt_of_ge hle) hlt
      simp [hz]
  rw [pairTest, CompactLogTest.convolution_apply]
  simp only [CompactLogTest.involution_apply]
  rw [show (fun t : ℝ => star ((w i).test (-t)) * (w j).test (x - t)) = 0 from funext hkill]
  simp

theorem pairTest_support {k : ℕ} (w : Fin k → CompactLogTest) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) (i j : Fin k) :
    Function.support (pairTest w i j).test ⊆ Ioo (-(2 * B)) (2 * B) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hmem
  have habs : 2 * B ≤ |x| := le_of_not_gt fun hlt => hmem (abs_lt.mp hlt)
  exact hx (pairTest_apply_of_abs_ge w hw i j habs)

def packedSum {ι : Type} (s : Finset ι) (F : ι → TestFunction)
    (hF : ∀ i, HasCompactSupport (F i)) : CompactLogTest where
  test := ∑ i ∈ s, F i
  compactSupport := by
    convert hasCompactSupport_finset_sum s (fun i x => F i x) (fun i _ => hF i) using 1
    ext x
    simp

@[simp] theorem packedSum_apply {ι : Type} (s : Finset ι) (F : ι → TestFunction)
    (hF : ∀ i, HasCompactSupport (F i)) (x : ℝ) :
    (packedSum s F hF).test x = ∑ i ∈ s, F i x := by
  simp [packedSum]

theorem packedSum_support {ι : Type} (s : Finset ι) (F : ι → TestFunction)
    (hF : ∀ i, HasCompactSupport (F i)) {B : ℝ}
    (hFsupp : ∀ i, Function.support (F i) ⊆ Ioo (-B) B) :
    Function.support (packedSum s F hF).test ⊆ Ioo (-B) B := by
  intro x hx
  by_contra hout
  rw [Function.mem_support] at hx
  apply hx
  rw [packedSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  by_contra hne
  exact hout (hFsupp i (Function.mem_support.mpr hne))

theorem archimedeanIntegrand_packedSum {ι : Type} (s : Finset ι)
    (F : ι → TestFunction) (hF : ∀ i, HasCompactSupport (F i)) (y : ℝ) :
    archimedeanIntegrand (packedSum s F hF) y =
      ∑ i ∈ s, archimedeanIntegrand (packTest (F i) (hF i)) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [packedSum, archimedeanIntegrand, archimedeanNumerator]
  | @insert a s ha ih =>
      have hS : HasCompactSupport ⇑(∑ i ∈ s, F i) := by
        convert hasCompactSupport_finset_sum s (fun i x => F i x)
          (fun i _ => hF i) using 1
        ext x
        simp
      have hobj : packedSum (insert a s) F hF =
          packTest (F a + ∑ i ∈ s, F i) ((hF a).add hS) := by
        apply CompactLogTest.ext
        ext x
        simp [packedSum, Finset.sum_insert, ha]
      have hrest : packTest (∑ i ∈ s, F i) hS = packedSum s F hF := by
        apply CompactLogTest.ext
        ext x
        simp [packedSum]
      rw [hobj, archimedeanIntegrand_packTest_add (F a) (∑ i ∈ s, F i)
        (hF a) hS y, hrest, ih]
      simp [Finset.sum_insert, ha]

theorem integrableOn_archimedeanIntegrand_packedSum {ι : Type} (s : Finset ι)
    (F : ι → TestFunction) (hF : ∀ i, HasCompactSupport (F i))
    (hI : ∀ i, IntegrableOn (archimedeanIntegrand (packTest (F i) (hF i)))
      (Ioi (0 : ℝ))) :
    IntegrableOn (archimedeanIntegrand (packedSum s F hF)) (Ioi (0 : ℝ)) := by
  have hpoint : archimedeanIntegrand (packedSum s F hF) =
      fun y => ∑ i ∈ s, archimedeanIntegrand (packTest (F i) (hF i)) y := by
    funext y
    exact archimedeanIntegrand_packedSum s F hF y
  rw [hpoint]
  refine ICintegrable_sum s (fun i y => archimedeanIntegrand
    (packTest (F i) (hF i)) y) ?_
  intro i hi
  exact hI i

theorem ICgate_zero_of_test_zero (F : CompactLogTest) (hF : ∀ x, F.test x = 0) :
    ICgate F = 0 := by
  have harch : archimedeanTerm F = 0 := by
    simp [archimedeanTerm, archimedeanIntegrand, archimedeanNumerator, hF]
  have hprime : finitePrimeSum F = 0 := by
    unfold finitePrimeSum
    apply Finset.sum_eq_zero
    intro n hn
    simp [finitePrimeTerm, finitePrimeTermComplex, hF]
  unfold ICgate
  rw [harch, hprime]
  ring

theorem ICgate_packedSum {ι : Type} (s : Finset ι) (F : ι → TestFunction)
    (hF : ∀ i, HasCompactSupport (F i)) {B : ℝ}
    (hFsupp : ∀ i, Function.support (F i) ⊆ Ioo (-B) B)
    (hI : ∀ i, IntegrableOn (archimedeanIntegrand (packTest (F i) (hF i)))
      (Ioi (0 : ℝ))) :
    ICgate (packedSum s F hF) = ∑ i ∈ s, ICgate (packTest (F i) (hF i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      apply ICgate_zero_of_test_zero
      intro x
      simp [packedSum]
  | @insert a s ha ih =>
      have hS : HasCompactSupport ⇑(∑ i ∈ s, F i) := by
        convert hasCompactSupport_finset_sum s (fun i x => F i x)
          (fun i _ => hF i) using 1
        ext x
        simp
      have hobj : packedSum (insert a s) F hF =
          packTest (F a + ∑ i ∈ s, F i) ((hF a).add hS) := by
        apply CompactLogTest.ext
        ext x
        simp [packedSum, Finset.sum_insert, ha]
      have hrest : packTest (∑ i ∈ s, F i) hS = packedSum s F hF := by
        apply CompactLogTest.ext
        ext x
        simp [packedSum]
      have hSuppS : Function.support ⇑(∑ i ∈ s, F i) ⊆ Ioo (-B) B := by
        intro x hx
        by_contra hout
        rw [Function.mem_support] at hx
        apply hx
        simp only [SchwartzMap.sum_apply]
        refine Finset.sum_eq_zero fun i hi => ?_
        by_contra hne
        exact hout (hFsupp i (Function.mem_support.mpr hne))
      have hIS : IntegrableOn (archimedeanIntegrand (packTest (∑ i ∈ s, F i) hS))
          (Ioi (0 : ℝ)) := by
        rw [hrest]
        exact integrableOn_archimedeanIntegrand_packedSum s F hF hI
      rw [hobj, ICgate_packTest_add (F a) (∑ i ∈ s, F i) (hF a) hS
        (hFsupp a) hSuppS (hI a) hIS, hrest, ih]
      simp [Finset.sum_insert, ha]

theorem convolutionSquare_spanObj_apply {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (x : ℝ) : (spanObj w y).convolutionSquare.test x =
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
        ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
        (pairTest w i j).test x := by
  rw [CompactLogTest.convolutionSquare_apply]
  have hpoint : ∀ t : ℝ,
      star ((spanObj w y).test (-t)) * (spanObj w y).test (x - t) =
        ∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t)) := by
    intro t
    rw [spanObj_apply, spanObj_apply]
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [Finset.sum_mul]
    change (Finset.univ.sum fun i : Fin k =>
        star ((w i).test (-t)) * (y i : ℂ) *
          (Finset.univ.sum fun j : Fin k =>
            (y j : ℂ) * (w j).test (x - t))) =
      Finset.univ.sum fun i : Fin k =>
        Finset.univ.sum fun j : Fin k => ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t))
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast [map_mul]
    ring
  calc
    (∫ t : ℝ, star ((spanObj w y).test (-t)) * (spanObj w y).test (x - t)) =
        ∫ t : ℝ, ∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t)) :=
      integral_congr_ae (ae_of_all volume hpoint)
    _ = ∑ i ∈ (Finset.univ : Finset (Fin k)), ∫ t : ℝ,
        ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t)) := by
      refine MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin k))
        (f := fun i t => ∑ j ∈ (Finset.univ : Finset (Fin k)),
          ((y i * y j : ℝ) : ℂ) *
            (star ((w i).test (-t)) * (w j).test (x - t))) ?_
      intro i hi
      refine ICintegrable_sum (Finset.univ : Finset (Fin k))
        (fun j t => ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t))) ?_
      intro j hj
      exact (pairIntegrand_integrable w i j x).const_mul' _
    _ = ∑ i ∈ (Finset.univ : Finset (Fin k)),
        ∑ j ∈ (Finset.univ : Finset (Fin k)), ∫ t : ℝ, ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin k))
        (f := fun j t => ((y i * y j : ℝ) : ℂ) *
          (star ((w i).test (-t)) * (w j).test (x - t))) ?_
      intro j hj
      exact (pairIntegrand_integrable w i j x).const_mul' _
    _ = ∑ i ∈ (Finset.univ : Finset (Fin k)),
        ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
          (pairTest w i j).test x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_const_mul]
      congr 1

def pairPiece {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    (p : Fin k × Fin k) : TestFunction :=
  ((y p.1 * y p.2 : ℝ) : ℂ) • (pairTest w p.1 p.2).test

theorem gate_sum_span {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) =
      ∑ p : Fin k × Fin k, y p.1 * y p.2 * ICgate (pairTest w p.1 p.2) := by
  have hPc : ∀ p : Fin k × Fin k, HasCompactSupport (pairPiece w y p) := by
    intro p
    simpa [pairPiece] using (pairTest w p.1 p.2).compactSupport.smul_left
      (f := fun _ => ((y p.1 * y p.2 : ℝ) : ℂ))
  have hPs : ∀ p : Fin k × Fin k,
      Function.support (pairPiece w y p) ⊆ Ioo (-(2 * B)) (2 * B) := by
    intro p x hx
    by_contra hout
    rw [Function.mem_support] at hx
    have hz : (pairTest w p.1 p.2).test x = 0 := by
      by_contra hne
      exact hout (pairTest_support w hw p.1 p.2 (Function.mem_support.mpr hne))
    apply hx
    simp [pairPiece, hz]
  have hPI : ∀ p : Fin k × Fin k, IntegrableOn
      (archimedeanIntegrand (packTest (pairPiece w y p) (hPc p))) (Ioi (0 : ℝ)) := by
    intro p
    have hsm : ∀ z : ℝ, archimedeanIntegrand
        (packTest (pairPiece w y p) (hPc p)) z =
        ((y p.1 * y p.2 : ℝ) : ℂ) • archimedeanIntegrand (pairTest w p.1 p.2) z := by
      intro z
      change archimedeanIntegrand (packTest
        (((y p.1 * y p.2 : ℝ) : ℂ) • (pairTest w p.1 p.2).test) (hPc p)) z = _
      rw [archimedeanIntegrand_packTest_smul (y p.1 * y p.2 : ℝ)
        (pairTest w p.1 p.2).test (pairTest w p.1 p.2).compactSupport z (hPc p)]
      congr 1
    have hfun : archimedeanIntegrand (packTest (pairPiece w y p) (hPc p)) =
        fun z => ((y p.1 * y p.2 : ℝ) : ℂ) •
          archimedeanIntegrand (pairTest w p.1 p.2) z := funext hsm
    rw [hfun]
    simpa only [Pi.smul_apply] using
      (hI p.1 p.2).smul ((y p.1 * y p.2 : ℝ) : ℂ)
  have hobj : (spanObj w y).convolutionSquare =
      packedSum (Finset.univ : Finset (Fin k × Fin k)) (pairPiece w y) hPc := by
    apply CompactLogTest.ext
    ext x
    rw [convolutionSquare_spanObj_apply]
    have hsum : (∑ p : Fin k × Fin k, ((y p.1 * y p.2 : ℝ) : ℂ) *
        (pairTest w p.1 p.2).test x) =
        ∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)), ((y i * y j : ℝ) : ℂ) *
            (pairTest w i j).test x := by
      simpa using (Fintype.sum_prod_type fun p : Fin k × Fin k =>
        ((y p.1 * y p.2 : ℝ) : ℂ) * (pairTest w p.1 p.2).test x)
    rw [← hsum]
    simp [packedSum_apply, pairPiece]
  have hgate : ∀ p : Fin k × Fin k,
      ICgate (packTest (pairPiece w y p) (hPc p)) =
        y p.1 * y p.2 * ICgate (pairTest w p.1 p.2) := by
    intro p
    change ICgate (packTest (((y p.1 * y p.2 : ℝ) : ℂ) •
      (pairTest w p.1 p.2).test) (hPc p)) = _
    rw [ICgate_packTest_smul (y p.1 * y p.2 : ℝ) (pairTest w p.1 p.2).test
      (pairTest w p.1 p.2).compactSupport (pairTest_support w hw p.1 p.2) (hPc p)]
    congr 1
  rw [hobj, ICgate_packedSum (Finset.univ : Finset (Fin k × Fin k))
    (pairPiece w y) hPc hPs hPI]
  simp_rw [hgate]

def gateMatrix {k : ℕ} (w : Fin k → CompactLogTest) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ICgate (pairTest w i j)

theorem pair_gate_sum_eq_qform {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) :
    (∑ p : Fin k × Fin k, y p.1 * y p.2 * ICgate (pairTest w p.1 p.2)) =
      y ⬝ᵥ (gateMatrix w *ᵥ y) := by
  rw [Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, gateMatrix, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gate_qform_span {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (gateMatrix w *ᵥ y) := by
  rw [gate_sum_span w y hw hI, pair_gate_sum_eq_qform]

theorem hrep_of_gateMatrix_eq {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (M_true : Matrix (Fin k) (Fin k) ℝ)
    (hM : gateMatrix w = M_true) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Ioi (0 : ℝ))) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y) := by
  rw [gate_qform_span w y hw hI, hM]

end
end C1GateMatrixRepresentation
end Source
end ConnesWeilRH
