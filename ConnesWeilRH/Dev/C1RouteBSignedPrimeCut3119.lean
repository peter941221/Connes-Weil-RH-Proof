import ConnesWeilRH.Dev.C1RouteBAdaptivePoweredTail3117
import ConnesWeilRH.Dev.C1RouteBPoweredSeedCarrier3110

/-! Exact signed prime-cut accounting on the actual powered spans.

The stored n=3 span has a proved finite prime coverage bound, independently
of any hypothetical-zero premise. The legacy cutoff is kept separate from
that bound. No sign, Fourier readback, or numerical remainder is supplied.
-/

namespace ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119

open CC20YoshidaConvolution CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil C1OrbitWindowSemiLocalGate C1FourPointSpectralPrefixTransport
open C1TwoPointSpectralDecomposition C1RouteBAdaptivePoweredTail3117
open C1RouteBPoweredSeedCarrier3110 C1RowBStoredCapture2722F
open scoped BigOperators

noncomputable section

def primeCut3119 (F : CompactLogTest) (M : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (M + 1), finitePrimeTerm F q

def primeRemainder3119 (F : CompactLogTest) (M : ℕ) : ℝ :=
  ∑ q ∈ (globalPrimeIndexSet F).filter (fun q => M < q), finitePrimeTerm F q

def cutGate3119 (g : CompactLogTest) (M : ℕ) : ℝ :=
  archimedeanTerm g.convolutionSquare + primeCut3119 g.convolutionSquare M

theorem primeCut_eq_visible_filter3119 (F : CompactLogTest) (M : ℕ) :
    primeCut3119 F M =
      ∑ q ∈ (globalPrimeIndexSet F).filter (fun q => q ≤ M), finitePrimeTerm F q := by
  symm
  apply Finset.sum_subset
    (show (globalPrimeIndexSet F).filter (fun q => q ≤ M) ⊆ Finset.range (M + 1) from by
      intro q hq
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hq).2))
  intro q hq hnot
  by_contra hterm
  have hcomplex : finitePrimeTermComplex F q ≠ 0 := by
    intro hz
    apply hterm
    simp [finitePrimeTerm, hz]
  exact hnot (Finset.mem_filter.mpr
    ⟨(mem_globalPrimeIndexSet_iff F q).mpr
      ⟨finitePrimeTermComplex_nonzero_primePower F hcomplex, hcomplex⟩,
      Nat.le_of_lt_succ (Finset.mem_range.mp hq)⟩)

theorem finitePrimeSum_eq_cut_add_remainder3119 (F : CompactLogTest) (M : ℕ) :
    finitePrimeSum F = primeCut3119 F M + primeRemainder3119 F M := by
  rw [primeCut_eq_visible_filter3119]
  unfold finitePrimeSum primeRemainder3119
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not (globalPrimeIndexSet F)
      (fun q => q ≤ M) (finitePrimeTerm F)).symm

/-- This is an equality of signed quantities, not an absolute-value allowance. -/
theorem full_gate_eq_cut_add_remainder3119 (g : CompactLogTest) (M : ℕ) :
    archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare =
      cutGate3119 g M + primeRemainder3119 g.convolutionSquare M := by
  rw [finitePrimeSum_eq_cut_add_remainder3119 g.convolutionSquare M]
  simp only [cutGate3119, add_assoc]

theorem gate_iff_signed_remainder_budget3119 (g : CompactLogTest) (M : ℕ) :
    orbitWindowSemiLocalGate g ↔
      primeRemainder3119 g.convolutionSquare M ≤ -cutGate3119 g M := by
  unfold orbitWindowSemiLocalGate
  rw [full_gate_eq_cut_add_remainder3119]
  constructor <;> intro h <;> linarith

theorem poweredFamily_full_gate3119
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (M : ℕ) :
    archimedeanTerm (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare +
        finitePrimeSum (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare =
      cutGate3119 (poweredFamilySpan3117 rho N nodes n lambda) M +
        primeRemainder3119 (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare M :=
  full_gate_eq_cut_add_remainder3119 _ M

def storedSpan3119 (rho : ℂ) (lambda : ℝ) : CompactLogTest :=
  annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator poweredSeedStoredCarrierSourceTest3110 rho)
    poweredSeedStoredCarrierSourceTest3110 lambda

theorem storedSpan_support3119 (rho : ℂ) (lambda : ℝ) :
    Function.support (storedSpan3119 rho lambda).test ⊆ Set.Ioo (-56 : ℝ) 56 := by
  have hg : Function.support poweredSeedStoredCarrierSourceTest3110.test ⊆
      Set.Ioo (-55 : ℝ) 55 :=
    poweredSeedCarrier_sourceTest_support3110 storedTargets2722F storedNodes2722F storedY2722F
  have hu := fullFunctionalEquationOrbitAnnihilator_support_subset_Icc
    poweredSeedStoredCarrierSourceTest3110 rho (hg.trans Set.Ioo_subset_Icc_self)
  apply annihilatorDetectorSpanVector_support_subset_Ioo _ _ lambda 56
  · intro x hx
    have h := hu hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro x hx
    have h := hg hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- A finite upper bound, not an exact support or visibility endpoint. -/
theorem storedSpan_visible_prime_bound3119 (rho : ℂ) (lambda : ℝ) :
    ∀ q ∈ globalPrimeIndexSet (storedSpan3119 rho lambda).convolutionSquare,
      q ≤ Nat.ceil (Real.exp 112) := by
  intro q hq
  have hx := mem_globalPrimeIndexSet_convolutionSquare_lt_exp
    (storedSpan3119 rho lambda) (storedSpan_support3119 rho lambda) hq
  have hceil := Nat.le_ceil (Real.exp (112 : ℝ))
  have hreal : (q : ℝ) ≤ (Nat.ceil (Real.exp (112 : ℝ)) : ℝ) := by
    have harg : (2 : ℝ) * 56 = 112 := by norm_num
    rw [harg] at hx
    exact hx.le.trans hceil
  exact_mod_cast hreal

theorem storedSpan_remainder_at_complete_bound3119 (rho : ℂ) (lambda : ℝ) :
    primeRemainder3119 (storedSpan3119 rho lambda).convolutionSquare
      (Nat.ceil (Real.exp 112)) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hvis, hlarge⟩ := Finset.mem_filter.mp hq
  exact False.elim ((not_lt_of_ge (storedSpan_visible_prime_bound3119 rho lambda q hvis)) hlarge)

theorem storedSpan_complete_prime_cut3119 (rho : ℂ) (lambda : ℝ) :
    finitePrimeSum (storedSpan3119 rho lambda).convolutionSquare =
      primeCut3119 (storedSpan3119 rho lambda).convolutionSquare
        (Nat.ceil (Real.exp 112)) := by
  rw [finitePrimeSum_eq_cut_add_remainder3119
      (storedSpan3119 rho lambda).convolutionSquare (Nat.ceil (Real.exp 112)),
    storedSpan_remainder_at_complete_bound3119, add_zero]

theorem storedSpan_full_gate3119 (rho : ℂ) (lambda : ℝ) (M : ℕ) :
    orbitWindowSemiLocalGate (storedSpan3119 rho lambda) ↔
      primeRemainder3119 (storedSpan3119 rho lambda).convolutionSquare M ≤
        -cutGate3119 (storedSpan3119 rho lambda) M :=
  gate_iff_signed_remainder_budget3119 _ M

end
end ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119
