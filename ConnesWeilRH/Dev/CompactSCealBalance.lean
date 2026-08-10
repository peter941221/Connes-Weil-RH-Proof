import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula

/-!
# CompactSCealBalance — the finite-prime (and owner-level) balance of lane-B SCAL

The lane-B residual `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`
carries `scopedArchimedeanContributionBalance (SCAB)`, the global-vs-restricted
balance of the Weil explicit-formula decomposition (docs/945).  That identity
splits into an archimedean/pole part (the real Weil explicit formula, open) and
a finite-prime part; at the `SelectedWeilFormulaOwner` level the whole balance
appears as `restricted = global + omitted`.

This module closes two verifiable pieces:

  * `finitePrimePart_scaled`: `globalSum - restrictedSum = omittedSum` - the
    finite-prime half, from `globalFinitePrimeTerm_eq_restricted_add_omitted`.
  * `restrictedWeilValue_re_eq_weilValue_re_add_omitted_re`: the real
    arch/finite/omitted decomposition,
    `restrictedWeilValue.re = weilValue.re + omittedTerm.re`
    (complex `.im = 0` in-library), i.e. the scalar balance at the owner level.

RH NOT claimed; the total arch-pole Weil explicit formula stays open.
-/
namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CompactSCealBalance

open SelectedWeilFormula
open SelectedWeilFormulaOwner

/-- The finite-prime half of the SCAL: the global finite-prime sum minus the
   restricted (`lambda`-cut) sum equals exactly the omitted prime-power terms.
   From `globalFinitePrimeTerm_eq_restricted_add_omitted` (ring over C). -/
theorem finitePrimePart_scaled (ow : SelectedWeilFormulaOwner) (lambda : ℝ) :
    ow.globalFinitePrimeTerm - ow.restrictedFinitePrimeTerm lambda =
      ow.omittedFinitePrimeTerm lambda := by
  rw [globalFinitePrimeTerm_eq_restricted_add_omitted ow lambda]
  ring

/-- The owner-level real balance: `restrictedWeilValue.re = weilValue.re + omitted.re`.
   Since the imaginary parts of all three vanish and `restricted = weil + omitted`
   (`restrictedWeilValue_eq_weilValue_add_omitted`), this is the scalar
   arch/finite-prime balance with the arch terms absorbed. -/
theorem restrictedWeilValue_re_eq_weilValue_re_add_omitted_re
    (ow : SelectedWeilFormulaOwner) (lambda : ℝ) :
    (ow.restrictedWeilValue lambda).re =
      (ow.weilValue).re + (ow.omittedFinitePrimeTerm lambda).re := by
  rw [restrictedWeilValue_eq_weilValue_add_omitted]
  simp [Complex.add_re]


/-- The real part of the global Weil value splits over R: poleTerm.re - archimedeanTerm.re - globalTerm.re.  This is the scalar side of Wall-A step 1.3 (the real psi/Weil identity). -/
theorem weilValue_re_split (ow : SelectedWeilFormulaOwner) :
    (ow.weilValue).re = (ow.square.poleTerm).re - (ow.square.archimedeanTerm).re - (ow.globalFinitePrimeTerm).re := by
  unfold weilValue
  simp [Complex.sub_re]
end CompactSCealBalance
end CCM25Concrete
end Source
end ConnesWeilRH