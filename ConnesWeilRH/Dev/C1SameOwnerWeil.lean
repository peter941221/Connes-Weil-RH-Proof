import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability

/-!
# C1SameOwnerWeil - the complete compact-log Weil functional

This module keeps the three coordinate-sensitive operations on one
`CompactLogTest` owner:

* Mellin evaluation is the bilateral Laplace transform in the additive log
  coordinate.
* The finite-prime term reads `F (log n)` and `F (-log n)`.
* The archimedean distribution reads the supplied formula test `F` directly.

For a route test `g`, the caller supplies `F = g.involution.convolution g`
exactly once. Compact support makes the visible prime-power set finite for each
`F`. No sign theorem or RH statement is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SameOwnerWeil

open MeasureTheory
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open scoped BigOperators

/-- The pole functional `W_(0,2)` in additive log coordinates. -/
noncomputable def poleTerm (F : CompactLogTest) : Real :=
  (CompactLogTest.laplaceAt F (1 / 2) +
    CompactLogTest.laplaceAt F (-1 / 2)).re

/-- The complex prime-power term before its real scalar readout. -/
noncomputable def finitePrimeTermComplex
    (F : CompactLogTest) (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex) *
    (((1 / Real.sqrt (n : Real) : Real) : Complex) *
      (F.test (Real.log n) + F.test (-Real.log n)))

/-- The real prime-power term used in the Weil functional. -/
noncomputable def finitePrimeTerm
    (F : CompactLogTest) (n : Nat) : Real :=
  (finitePrimeTermComplex F n).re

/-- The numerator of the direct archimedean distribution at a formula test. -/
noncomputable def archimedeanNumerator
    (F : CompactLogTest) (y : Real) : Complex :=
  Complex.ofRealCLM (Real.exp (y / 2)) *
      (F.test y + F.test (-y)) -
    2 * F.test 0

/-- The direct archimedean density. -/
noncomputable def archimedeanIntegrand
    (F : CompactLogTest) (y : Real) : Complex :=
  archimedeanNumerator F y /
    (SelectedWeilSquareOwner.archimedeanDenominator y : Complex)

/-- The archimedean functional reads `F` itself; it does not square `F`. -/
noncomputable def archimedeanTerm (F : CompactLogTest) : Real :=
  ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
        F.test 0) +
      ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re

/-- A radius containing the support of the supplied formula test. -/
noncomputable def rawSupportRadius (F : CompactLogTest) : Real :=
  Classical.choose F.compactSupport.isBounded.exists_norm_le

noncomputable def supportRadius (F : CompactLogTest) : Real :=
  max (rawSupportRadius F) 0

theorem supportRadius_nonnegative (F : CompactLogTest) :
    0 <= supportRadius F :=
  le_max_right _ _

theorem support_subset_Icc (F : CompactLogTest) :
    Function.support F.test ⊆
      Set.Icc (-supportRadius F) (supportRadius F) := by
  intro x hx
  have hxtsupport : x ∈ tsupport F.test := subset_tsupport _ hx
  have hraw := Classical.choose_spec F.compactSupport.isBounded.exists_norm_le
  have habs : |x| <= supportRadius F := by
    simpa [Real.norm_eq_abs, supportRadius, rawSupportRadius] using
      (hraw x hxtsupport).trans (le_max_left (rawSupportRadius F) 0)
  exact abs_le.mp habs

theorem finitePrimeTermComplex_nonzero_primePower
    (F : CompactLogTest) {n : Nat}
    (hterm : finitePrimeTermComplex F n ≠ 0) :
    IsPrimePow n := by
  by_contra hn
  apply hterm
  simp [finitePrimeTermComplex, ArithmeticFunction.vonMangoldt_apply, hn]

theorem abs_log_le_supportRadius_of_finitePrimeTermComplex_ne_zero
    (F : CompactLogTest) {n : Nat}
    (hterm : finitePrimeTermComplex F n ≠ 0) :
    |Real.log n| <= supportRadius F := by
  have hsum : F.test (Real.log n) + F.test (-Real.log n) ≠ 0 := by
    intro hzero
    apply hterm
    simp [finitePrimeTermComplex, hzero]
  have hpoint :
      F.test (Real.log n) ≠ 0 ∨ F.test (-Real.log n) ≠ 0 := by
    by_cases hleft : F.test (Real.log n) ≠ 0
    · exact Or.inl hleft
    by_cases hright : F.test (-Real.log n) ≠ 0
    · exact Or.inr hright
    exfalso
    apply hsum
    rw [not_ne_iff.mp hleft, not_ne_iff.mp hright]
    simp
  rcases hpoint with hpoint | hpoint
  · exact abs_le.mpr (support_subset_Icc F hpoint)
  · have hbounds := support_subset_Icc F hpoint
    simpa only [abs_neg] using (abs_le.mpr hbounds)

/-- A finite bound containing every visible prime-power index. -/
noncomputable def globalIndexBound (F : CompactLogTest) : Nat :=
  Nat.ceil (Real.exp (supportRadius F)) + 1

theorem index_lt_globalIndexBound
    (F : CompactLogTest) {n : Nat}
    (hprime : IsPrimePow n)
    (hterm : finitePrimeTermComplex F n ≠ 0) :
    n < globalIndexBound F := by
  have hnpos : (0 : Real) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt (IsPrimePow.one_lt hprime))
  have hlogle : Real.log n <= supportRadius F :=
    (le_abs_self (Real.log n)).trans
      (abs_log_le_supportRadius_of_finitePrimeTermComplex_ne_zero F hterm)
  have hnexp : (n : Real) <= Real.exp (supportRadius F) := by
    have h := Real.exp_le_exp.mpr hlogle
    simpa [Real.exp_log hnpos] using h
  have hexpceil :
      Real.exp (supportRadius F) <=
        (Nat.ceil (Real.exp (supportRadius F)) : Real) :=
    Nat.le_ceil (Real.exp (supportRadius F))
  have hnceil : n <= Nat.ceil (Real.exp (supportRadius F)) := by
    exact_mod_cast hnexp.trans hexpceil
  exact Nat.lt_succ_iff.mpr hnceil

/-- The exact finite set of visible prime powers for `F`. -/
noncomputable def globalPrimeIndexSet (F : CompactLogTest) : Finset Nat :=
  (Finset.range (globalIndexBound F)).filter fun n =>
    IsPrimePow n ∧ finitePrimeTermComplex F n ≠ 0

theorem mem_globalPrimeIndexSet_iff
    (F : CompactLogTest) (n : Nat) :
    n ∈ globalPrimeIndexSet F ↔
      IsPrimePow n ∧ finitePrimeTermComplex F n ≠ 0 := by
  simp only [globalPrimeIndexSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_bound, hprime, hterm⟩
    exact ⟨hprime, hterm⟩
  · rintro ⟨hprime, hterm⟩
    exact ⟨index_lt_globalIndexBound F hprime hterm, hprime, hterm⟩

/-- The complete finite prime-power sum visible to `F`. -/
noncomputable def finitePrimeSum (F : CompactLogTest) : Real :=
  ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n

/-- `Psi(F) = W_(0,2)(F) - W_R(F) - sum_p W_p(F)`. -/
noncomputable def psi (F : CompactLogTest) : Real :=
  poleTerm F - archimedeanTerm F - finitePrimeSum F

/-- The quadratic Weil value, with the half-density square formed once. -/
noncomputable def qw (g : CompactLogTest) : Real :=
  psi g.convolutionSquare

@[simp] theorem psi_eq_components (F : CompactLogTest) :
    psi F = poleTerm F - archimedeanTerm F - finitePrimeSum F :=
  rfl

@[simp] theorem qw_eq_psi_square (g : CompactLogTest) :
    qw g = psi g.convolutionSquare :=
  rfl

/-- On an actual half-density square, the direct archimedean integrand is the
existing selected-owner integrand. -/
theorem archimedeanIntegrand_square_eq_selected
    (g : CompactLogTest) (y : Real) :
    archimedeanIntegrand g.convolutionSquare y =
      (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand y := by
  rfl

/-- The direct pole term agrees with the canonical selected-square owner. -/
theorem poleTerm_square_eq_selected (g : CompactLogTest) :
    poleTerm g.convolutionSquare =
      ((SelectedWeilSquareOwner.ofCompactLogTest g).poleTerm).re := by
  have hsource :
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest = g := by
    rfl
  simp [poleTerm, CompactLogTest.laplaceAt,
    CompactLogTest.exponentialWeight_apply,
    SelectedWeilSquareOwner.poleTerm,
    SelectedWeilSquareOwner.laplaceAt,
    SelectedWeilSquareOwner.convolutionSquare, hsource]

/-- Every direct prime-power term agrees with the canonical selected-square
owner before the real scalar readout. -/
theorem finitePrimeTermComplex_square_eq_selected
    (g : CompactLogTest) (n : Nat) :
    finitePrimeTermComplex g.convolutionSquare n =
      (SelectedWeilSquareOwner.ofCompactLogTest g).finitePrimeTerm n := by
  rfl

/-- The computed all-prime-power index set is the canonical selected-owner set
on an actual half-density square. -/
theorem globalPrimeIndexSet_square_eq_selected (g : CompactLogTest) :
    globalPrimeIndexSet g.convolutionSquare =
      (SelectedFinitePrimeSupportData.ofOwner
        (SelectedWeilSquareOwner.ofCompactLogTest g)).globalPrimeIndexSet := by
  rfl

/-- The complete real prime-power sum agrees term-for-term with the canonical
selected-square owner. -/
theorem finitePrimeSum_square_eq_selected (g : CompactLogTest) :
    finitePrimeSum g.convolutionSquare =
      ∑ n ∈
        (SelectedFinitePrimeSupportData.ofOwner
          (SelectedWeilSquareOwner.ofCompactLogTest g)).globalPrimeIndexSet,
        (SelectedWeilSquareOwner.ofCompactLogTest g).finitePrimeTermReal n := by
  rfl

/-- The direct archimedean term agrees with the canonical selected-square
owner. This guards against accidentally forming a second convolution square. -/
theorem archimedeanTerm_square_eq_selected (g : CompactLogTest) :
    archimedeanTerm g.convolutionSquare =
      ((SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanTerm).re := by
  rfl

/-- The archimedean integral used by the C1 consumer is legal on every actual
half-density square. -/
theorem archimedeanIntegrand_square_integrableOn_Ioi
    (g : CompactLogTest) :
    IntegrableOn (archimedeanIntegrand g.convolutionSquare) (Set.Ioi (0 : Real)) := by
  simpa only [archimedeanIntegrand_square_eq_selected] using
    (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand_integrableOn_Ioi

end C1SameOwnerWeil
end Source
end ConnesWeilRH
