import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGeneric

/-!
# Finite-span readback of the selected prime profile

The signed-budget observable is evaluated on a convolution square, not on
the root test itself.  This leaf expands one actual prime-log profile term of
a finite root span into the pair-basis quadratic form.  It is an exact
same-owner algebraic interface; it proves no sign or RH statement.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2SpanProfileMatrix

open C1GateMatrixRepresentation
open C1G8R0OrbitGeometry
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2SignedBudget
open C1SameOwnerWeil
open C1ArchimedeanIntegrabilityGeneric
open C1LocalConfigurationDomination
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open Matrix
open MeasureTheory
open scoped BigOperators

noncomputable section

theorem signedProfileTerm_spanObj_eq_pair_profile_quadratic
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ) (n : ℕ) :
    signedProfileTerm (spanObj w y) n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)),
            ((y i * y j : ℝ) : ℂ) *
              bilateralProfile (pairTest w i j) (Real.log n)).re := by
  unfold signedProfileTerm bilateralProfile
  rw [convolutionSquare_spanObj_apply, convolutionSquare_spanObj_apply]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]

theorem signedProfileTerm_twoSpan_eq_four_pair_profiles
    (A B : CompactLogTest) (lam : ℝ) (n : ℕ) :
    signedProfileTerm (spanObj ![A, B] ![(1 : ℝ), -lam]) n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile (pairTest ![A, B] 0 0) (Real.log n)).re -
      lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile (pairTest ![A, B] 0 1) (Real.log n)).re) -
      lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile (pairTest ![A, B] 1 0) (Real.log n)).re) +
      lam ^ 2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile (pairTest ![A, B] 1 1) (Real.log n)).re) := by
  rw [signedProfileTerm_spanObj_eq_pair_profile_quadratic]
  simp [Fin.sum_univ_two]
  ring

theorem bilateralProfile_pairTest_swap_re
    (f g : CompactLogTest) (y : ℝ) :
    (bilateralProfile (f.involution.convolution g) y).re =
      (bilateralProfile (g.involution.convolution f) y).re := by
  have hswap (x : ℝ) :
      (g.involution.convolution f).test x =
        star ((f.involution.convolution g).test (-x)) := by
    rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
    simp only [CompactLogTest.involution_apply]
    simp only [Complex.star_def]
    rw [← integral_conj]
    let reflected : ℝ → ℂ := fun t =>
      star (g.test (-t)) * f.test (x - t)
    calc
      (∫ t : ℝ, star (g.test (-t)) * f.test (x - t)) =
          ∫ t : ℝ, reflected t := rfl
      _ = ∫ t : ℝ, reflected (t + x) := by
        symm
        exact integral_add_right_eq_self reflected x
      _ = ∫ t : ℝ,
          star (star (f.test (-t)) * g.test (-x - t)) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [reflected, star_mul, star_star]
        congr 1 <;> ring
  unfold bilateralProfile
  rw [hswap y, hswap (-y)]
  simp [Complex.star_def, add_comm]

theorem archimedeanTerm_pairTest_swap
    (f g : CompactLogTest) :
    archimedeanTerm (f.involution.convolution g) =
      archimedeanTerm (g.involution.convolution f) := by
  have hswap (x : ℝ) :
      (g.involution.convolution f).test x =
        star ((f.involution.convolution g).test (-x)) := by
    rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
    simp only [CompactLogTest.involution_apply, Complex.star_def]
    rw [← integral_conj]
    let reflected : ℝ → ℂ := fun t =>
      star (g.test (-t)) * f.test (x - t)
    calc
      (∫ t : ℝ, star (g.test (-t)) * f.test (x - t)) =
          ∫ t : ℝ, reflected t := rfl
      _ = ∫ t : ℝ, reflected (t + x) := by
        symm
        exact integral_add_right_eq_self reflected x
      _ = ∫ t : ℝ,
          star (star (f.test (-t)) * g.test (-x - t)) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [reflected, star_mul, star_star]
        congr 1 <;> ring
  have hnum (y : ℝ) :
      archimedeanNumerator (g.involution.convolution f) y =
        star (archimedeanNumerator (f.involution.convolution g) y) := by
    unfold archimedeanNumerator
    rw [hswap y, hswap (-y), hswap 0]
    have hexp : star (Complex.exp ((y : ℂ) / 2)) =
        Complex.exp ((y : ℂ) / 2) := by
      apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im]
    simp [Complex.star_def, hexp, add_comm]
  have hint (y : ℝ) :
      archimedeanIntegrand (g.involution.convolution f) y =
        star (archimedeanIntegrand (f.involution.convolution g) y) := by
    unfold archimedeanIntegrand
    rw [hnum]
    simp [Complex.star_def]
  unfold archimedeanTerm
  have hI :
      (∫ y in Set.Ioi (0 : ℝ),
          archimedeanIntegrand (g.involution.convolution f) y) =
        star (∫ y in Set.Ioi (0 : ℝ),
          archimedeanIntegrand (f.involution.convolution g) y) := by
    simp only [Complex.star_def]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with y
    exact hint y
  rw [hI, hswap 0]
  simp [Complex.star_def]

theorem finitePrimeTermComplex_pairTest_swap
    (f g : CompactLogTest) (n : ℕ) :
    finitePrimeTermComplex (g.involution.convolution f) n =
      star (finitePrimeTermComplex (f.involution.convolution g) n) := by
  have hswap (x : ℝ) :
      (g.involution.convolution f).test x =
        star ((f.involution.convolution g).test (-x)) := by
    rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
    simp only [CompactLogTest.involution_apply, Complex.star_def]
    rw [← integral_conj]
    let reflected : ℝ → ℂ := fun t =>
      star (g.test (-t)) * f.test (x - t)
    calc
      (∫ t : ℝ, star (g.test (-t)) * f.test (x - t)) =
          ∫ t : ℝ, reflected t := rfl
      _ = ∫ t : ℝ, reflected (t + x) := by
        symm
        exact integral_add_right_eq_self reflected x
      _ = ∫ t : ℝ,
          star (star (f.test (-t)) * g.test (-x - t)) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [reflected, star_mul, star_star]
        congr 1 <;> ring
  unfold finitePrimeTermComplex
  rw [hswap (Real.log n), hswap (-Real.log n)]
  simp [Complex.star_def, add_comm]

theorem globalPrimeIndexSet_pairTest_swap
    (f g : CompactLogTest) :
    globalPrimeIndexSet (g.involution.convolution f) =
      globalPrimeIndexSet (f.involution.convolution g) := by
  apply Finset.ext
  intro n
  rw [mem_globalPrimeIndexSet_iff, mem_globalPrimeIndexSet_iff]
  rw [finitePrimeTermComplex_pairTest_swap]
  simp

theorem finitePrimeSum_pairTest_swap
    (f g : CompactLogTest) :
    finitePrimeSum (g.involution.convolution f) =
      finitePrimeSum (f.involution.convolution g) := by
  unfold finitePrimeSum
  rw [globalPrimeIndexSet_pairTest_swap]
  apply Finset.sum_congr rfl
  intro n hn
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_pairTest_swap]
  simp

theorem ICgate_pairTest_swap
    (f g : CompactLogTest) :
    ICgate (f.involution.convolution g) =
      ICgate (g.involution.convolution f) := by
  unfold ICgate
  rw [archimedeanTerm_pairTest_swap,
    finitePrimeSum_pairTest_swap]

theorem orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Set.Ioi (0 : ℝ))) :
    orbitWindowSemiLocalGate (spanObj w y) ↔
      y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0 := by
  have hgate :
      orbitWindowSemiLocalGate (spanObj w y) ↔
        p2AggregateValue (spanObj w y) ≤ 0 := by
    unfold orbitWindowSemiLocalGate p2AggregateValue
    rw [← finitePrimeSum_eq_bilateralProfile_weighted_sum]
  rw [hgate, p2AggregateValue_spanObj_eq_gate_qform w y hw hI]

theorem orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B) :
    orbitWindowSemiLocalGate (spanObj w y) ↔
      y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0 := by
  exact orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos w y hw
    (fun i j => pairTest_legality w i j)

theorem sourceRH_of_right_orbitGeometry_spanGateCertificate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ (k : ℕ) (w : Fin k → CompactLogTest) (y : Fin k → ℝ) (B : ℝ),
              g = spanObj w y ∧
              (∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B) ∧
              y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_signedBudget
  intro rho hright
  obtain ⟨g, geometry, k, w, y, B, howner, hw, hq⟩ := hproducer rho hright
  have hspanGate : orbitWindowSemiLocalGate (spanObj w y) :=
    (orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
      w y hw).mpr hq
  have hgate : orbitWindowSemiLocalGate g := by
    rw [howner]
    exact hspanGate
  have hbudget := (orbitWindowSemiLocalGate_iff_signedBudget geometry).mp hgate
  refine ⟨g, geometry, ?_⟩
  simpa [orbitVisiblePrimeRange] using hbudget

theorem oneWindowICdefect_eq_twoSpan
    (g W : CompactLogTest) (lam : ℝ) :
    ICdefect g ({()} : Finset Unit) (fun _ => W) (fun _ => lam) =
      spanObj ![g, W] ![(1 : ℝ), -lam] := by
  apply CompactLogTest.ext
  ext x
  simp [ICdefect_test, spanObj]
  ring

theorem oneWindowICdefect_gate_iff_twoSpan_qform_nonpos
    (g W : CompactLogTest) (lam B : ℝ)
    (hg : Function.support g.test ⊆ Set.Ioo (-B) B)
    (hW : Function.support W.test ⊆ Set.Ioo (-B) B) :
    orbitWindowSemiLocalGate
        (ICdefect g ({()} : Finset Unit) (fun _ => W) (fun _ => lam)) ↔
      (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![g, W] *ᵥ (![1, -lam] : Fin 2 → ℝ)) ≤ 0 := by
  rw [oneWindowICdefect_eq_twoSpan]
  apply orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
  intro i
  fin_cases i
  · simpa using hg
  · simpa using hW

theorem twoSpan_gate_qform_expand
    (A B : CompactLogTest) (lam : ℝ) :
    (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![A, B] *ᵥ (![1, -lam] : Fin 2 → ℝ)) =
      ICgate A.convolutionSquare + lam ^ 2 * ICgate B.convolutionSquare -
        lam * (ICgate (A.involution.convolution B) +
          ICgate (B.involution.convolution A)) := by
  change
    (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![A, B] *ᵥ (![1, -lam] : Fin 2 → ℝ)) =
      ICgate (A.involution.convolution A) + lam ^ 2 *
          ICgate (B.involution.convolution B) -
        lam * (ICgate (A.involution.convolution B) +
          ICgate (B.involution.convolution A))
  simp [gateMatrix, Matrix.mulVec, dotProduct, pairTest]
  ring

theorem exists_quadratic_nonpos_iff_discriminant
    (a b c : ℝ) (hc : 0 < c) :
      (∃ lam : ℝ, a + c * lam ^ 2 - 2 * b * lam ≤ 0) ↔
        a * c ≤ b ^ 2 := by
    constructor
    · rintro ⟨lam, hlam⟩
      have hmul : c * (a + c * lam ^ 2 - 2 * b * lam) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hlam
      have hsquare : 0 ≤ (c * lam - b) ^ 2 := sq_nonneg (c * lam - b)
      nlinarith
    · intro hab
      have hcne : c ≠ 0 := ne_of_gt hc
      refine ⟨b / c, ?_⟩
      have hidentity :
          a + c * (b / c) ^ 2 - 2 * b * (b / c) = (a * c - b ^ 2) / c := by
        field_simp [hcne]
        ring
      rw [hidentity]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hab) (le_of_lt hc)

theorem exists_twoSpan_gate_qform_nonpos_of_discriminant
    (A B : CompactLogTest)
    (hC : 0 < ICgate B.convolutionSquare)
    (hdisc :
      ICgate A.convolutionSquare * ICgate B.convolutionSquare ≤
        ((ICgate (A.involution.convolution B) +
            ICgate (B.involution.convolution A)) / 2) ^ 2) :
    ∃ lam : ℝ,
      (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![A, B] *ᵥ (![1, -lam] : Fin 2 → ℝ)) ≤ 0 := by
  have hq :=
    (exists_quadratic_nonpos_iff_discriminant
      (ICgate A.convolutionSquare)
      ((ICgate (A.involution.convolution B) +
        ICgate (B.involution.convolution A)) / 2)
      (ICgate B.convolutionSquare) hC).mpr hdisc
  rcases hq with ⟨lam, hlam⟩
  refine ⟨lam, ?_⟩
  rw [twoSpan_gate_qform_expand]
  nlinarith

theorem twoSpan_gate_qform_expand_symmetric
    (A B : CompactLogTest) (lam : ℝ) :
    (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![A, B] *ᵥ (![1, -lam] : Fin 2 → ℝ)) =
      ICgate A.convolutionSquare + lam ^ 2 * ICgate B.convolutionSquare -
        2 * lam * ICgate (A.involution.convolution B) := by
  rw [twoSpan_gate_qform_expand, ICgate_pairTest_swap A B]
  ring

theorem exists_twoSpan_gate_qform_nonpos_iff_symmetric_discriminant
    (A B : CompactLogTest) (hC : 0 < ICgate B.convolutionSquare) :
    (∃ lam : ℝ,
      (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![A, B] *ᵥ (![1, -lam] : Fin 2 → ℝ)) ≤ 0) ↔
      ICgate A.convolutionSquare * ICgate B.convolutionSquare ≤
        ICgate (A.involution.convolution B) ^ 2 := by
  constructor
  · rintro ⟨lam, hlam⟩
    apply (exists_quadratic_nonpos_iff_discriminant
      (ICgate A.convolutionSquare)
      (ICgate (A.involution.convolution B))
      (ICgate B.convolutionSquare) hC).mp
    refine ⟨lam, ?_⟩
    rw [twoSpan_gate_qform_expand_symmetric] at hlam
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlam
  · intro hdisc
    have hq := (exists_quadratic_nonpos_iff_discriminant
      (ICgate A.convolutionSquare)
      (ICgate (A.involution.convolution B))
      (ICgate B.convolutionSquare) hC).mpr hdisc
    rcases hq with ⟨lam, hlam⟩
    refine ⟨lam, ?_⟩
    rw [twoSpan_gate_qform_expand_symmetric]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlam

theorem twoSpan_p2Aggregate_eq_archimedean_plus_rangeProfile
    (A B : CompactLogTest) (lam R : ℝ)
    (hA : Function.support A.test ⊆ Set.Ioo (-R) R)
    (hB : Function.support B.test ⊆ Set.Ioo (-R) R) :
    p2AggregateValue (spanObj ![A, B] ![(1 : ℝ), -lam]) =
      archimedeanTerm (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare +
        ∑ n ∈ Finset.range (Nat.ceil (Real.exp (2 * R)) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (2 * ((spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare.test
              (Real.log n)).re) := by
  have hspan : Function.support (spanObj ![A, B] ![(1 : ℝ), -lam]).test ⊆
      Set.Ioo (-R) R := by
    intro x hx
    by_contra hout
    rw [Function.mem_support] at hx
    apply hx
    have hA0 : A.test x = 0 := by
      by_contra hne
      exact hout (hA (Function.mem_support.mpr hne))
    have hB0 : B.test x = 0 := by
      by_contra hne
      exact hout (hB (Function.mem_support.mpr hne))
    simp [spanObj_apply, hA0, hB0]
  have hsq : Function.support
      (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare.test ⊆
      Set.Ioo (-(2 * R)) (2 * R) := by
    exact CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo
      (spanObj ![A, B] ![(1 : ℝ), -lam])
      (fun x hx => Set.Ioo_subset_Icc_self (hspan hx))
  exact p2AggregateValue_eq_archimedean_plus_rangeProfile
    (spanObj ![A, B] ![(1 : ℝ), -lam]) hsq

end
end C1P2SpanProfileMatrix
end Source
end ConnesWeilRH
