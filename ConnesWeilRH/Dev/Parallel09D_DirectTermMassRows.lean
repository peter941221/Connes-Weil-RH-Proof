import ConnesWeilRH.Route.CC20RouteRealization

/-!
# 09D direct term mass rows

Scratch lane for the source-Weil-form direct finite-prime term mass rows.
This file is intentionally lane-local: it records whether the two term-mass
rows are ordinary source-side read-offs or whether they force pole-collapse
statements.
-/

namespace ConnesWeilRH
namespace Route

open scoped BigOperators

set_option linter.style.longLine false

abbrev Parallel09DDirectTermMassRowsCalibration
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration) :
    Prop :=
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
    hweil

def Parallel09DRestrictedQWPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) : Prop :=
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  let lambda := r.bridge.sourceTraceReadOff.lambda
  W.qwLambda lambda f f = W.polePairing f

def Parallel09DGlobalPsiPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) : Prop :=
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  W.psi (W.convolutionStar f f) = W.poleFunctional (W.convolutionStar f f)

theorem parallel09D_directRestrictedTermMass_iff_restrictedQWPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    (let witness := hweil r
     let sourceWeilForm := witness.2.1
     let W := sourceWeilForm.toWeilFormSymbols
     let f := r.sourceBackedTest.weilTest
     let lambda := r.bridge.sourceTraceReadOff.lambda
     (∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
        W.finitePrimeTerm n (W.convolutionStar f f)) =
      W.archimedeanTerm (W.convolutionStar f f)) ↔
      Parallel09DRestrictedQWPoleCollapse hweil r := by
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  let lambda := r.bridge.sourceTraceReadOff.lambda
  let C := W.convolutionStar f f
  let A := W.archimedeanTerm C
  let P := W.polePairing f
  let R :=
    ∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
      W.finitePrimeTerm n C
  let Runfiltered :=
    ∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f f
  let Q := W.qwLambda lambda f f
  have hfilter :
      (W.restrictedPrimeIndexSet lambda).filter IsPrimePow =
        W.restrictedPrimeIndexSet lambda := by
    apply Finset.filter_eq_self.2
    intro n hn
    exact
      ((sourceWeilForm.toWeilFormSymbols_restrictedPrimeIndex_exact
        lambda C n).1 hn).1
  have hsum : Runfiltered = R := by
    calc
      Runfiltered =
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.finitePrimeTerm n C := by
        refine Finset.sum_congr rfl ?_
        intro n _hn
        exact
          (sourceWeilForm.toWeilFormSymbols_finitePrimeTerm_convolutionStar
            f f n).symm
      _ = R := by
        simp [R, hfilter]
  have hformula : Q = A + P - R := by
    have hformula0 :
        Q = A + P - Runfiltered := by
      simpa [W, f, lambda, C, A, P, Runfiltered, Q] using
        Source.AnalyticCore.SourceWeilFormData.qw_lambda_formula_statement
          sourceWeilForm lambda r.bridge.sourceTraceReadOff.oneLtLambda f
    rw [hformula0, hsum]
  constructor
  · intro hmass
    have hR : R = A := by
      simpa [witness, sourceWeilForm, W, f, lambda, C, A, R] using hmass
    have hQ : Q = P := by
      rw [hformula, hR]
      ring
    simpa [Parallel09DRestrictedQWPoleCollapse, witness, sourceWeilForm, W, f,
      lambda, Q, P] using hQ
  · intro hcollapse
    have hQ : Q = P := by
      simpa [Parallel09DRestrictedQWPoleCollapse, witness, sourceWeilForm, W, f,
        lambda, Q, P] using hcollapse
    have hR : R = A := by
      linarith
    simpa [witness, sourceWeilForm, W, f, lambda, C, A, R] using hR

theorem parallel09D_directGlobalTermMass_iff_globalPsiPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    (let witness := hweil r
     let sourceWeilForm := witness.2.1
     let W := sourceWeilForm.toWeilFormSymbols
     let f := r.sourceBackedTest.weilTest
     (∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
        W.finitePrimeTerm n (W.convolutionStar f f)) =
      -W.archimedeanTerm (W.convolutionStar f f)) ↔
      Parallel09DGlobalPsiPoleCollapse hweil r := by
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  let C := W.convolutionStar f f
  let A := W.archimedeanTerm C
  let P := W.poleFunctional C
  let G :=
    ∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
      W.finitePrimeTerm n C
  let Psi := W.psi C
  have hfilter :
      W.globalPrimeIndexSet.filter IsPrimePow = W.globalPrimeIndexSet := by
    apply Finset.filter_eq_self.2
    intro n hn
    exact
      ((sourceWeilForm.toWeilFormSymbols_globalPrimeIndex_exact
        C n).1 hn).1
  have hsum :
      (∑ n ∈ W.globalPrimeIndexSet, W.finitePrimeTerm n C) = G := by
    simp [G, hfilter]
  have hformula : Psi = P - A - G := by
    have hformula0 :
        Psi = P - A -
          ∑ n ∈ W.globalPrimeIndexSet, W.finitePrimeTerm n C := by
      simpa [W, f, C, A, P, Psi] using
        Source.AnalyticCore.SourceWeilFormData.psi_sign_statement
          sourceWeilForm C
    rw [hformula0, hsum]
  constructor
  · intro hmass
    have hG : G = -A := by
      simpa [witness, sourceWeilForm, W, f, C, A, G] using hmass
    have hPsi : Psi = P := by
      rw [hformula, hG]
      ring
    simpa [Parallel09DGlobalPsiPoleCollapse, witness, sourceWeilForm, W, f, C,
      P, Psi] using hPsi
  · intro hcollapse
    have hPsi : Psi = P := by
      simpa [Parallel09DGlobalPsiPoleCollapse, witness, sourceWeilForm, W, f, C,
        P, Psi] using hcollapse
    have hG : G = -A := by
      linarith
    simpa [witness, sourceWeilForm, W, f, C, A, G] using hG

theorem parallel09D_directTermMassRows_imply_sourceWeilFormPoleCollapses
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (rows :
      Parallel09DDirectTermMassRowsCalibration hweil)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    Parallel09DRestrictedQWPoleCollapse hweil r ∧
      Parallel09DGlobalPsiPoleCollapse hweil r := by
  constructor
  · exact
      (parallel09D_directRestrictedTermMass_iff_restrictedQWPoleCollapse
        hweil r).mp (rows.restrictedMass r)
  · exact
      (parallel09D_directGlobalTermMass_iff_globalPsiPoleCollapse
        hweil r).mp (rows.globalMass r)

theorem parallel09D_restrictedQWPoleCollapse_iff_routeRestrictedQWPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    Parallel09DRestrictedQWPoleCollapse hweil r ↔
      NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapse r := by
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let hsymbols := witness.2.2
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  let lambda := r.bridge.sourceTraceReadOff.lambda
  constructor
  · intro hcollapse
    simpa [
      Parallel09DRestrictedQWPoleCollapse,
      NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapse,
      witness, sourceWeilForm, hsymbols, W, f, lambda] using hcollapse
  · intro hcollapse
    simpa [
      Parallel09DRestrictedQWPoleCollapse,
      NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapse,
      witness, sourceWeilForm, hsymbols, W, f, lambda] using hcollapse

theorem parallel09D_globalPsiPoleCollapse_iff_routePsiPoleCollapse
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration)
    (r : NormalizedRouteBackedCC20SquareRestrictedTest) :
    Parallel09DGlobalPsiPoleCollapse hweil r ↔
      NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse r := by
  let witness := hweil r
  let sourceWeilForm := witness.2.1
  let hsymbols := witness.2.2
  let W := sourceWeilForm.toWeilFormSymbols
  let f := r.sourceBackedTest.weilTest
  let C := W.convolutionStar f f
  constructor
  · intro hcollapse
    simpa [
      Parallel09DGlobalPsiPoleCollapse,
      NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse,
      witness, sourceWeilForm, hsymbols, W, f, C] using hcollapse
  · intro hcollapse
    simpa [
      Parallel09DGlobalPsiPoleCollapse,
      NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse,
      witness, sourceWeilForm, hsymbols, W, f, C] using hcollapse

theorem parallel09D_directTermMassRows_iff_routePoleCollapses
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration) :
    Parallel09DDirectTermMassRowsCalibration hweil ↔
      ∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
        NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapse r ∧
          NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse r := by
  constructor
  · intro rows r
    let hcollapses :=
      parallel09D_directTermMassRows_imply_sourceWeilFormPoleCollapses
        hweil rows r
    exact
      ⟨(parallel09D_restrictedQWPoleCollapse_iff_routeRestrictedQWPoleCollapse
          hweil r).mp hcollapses.1,
        (parallel09D_globalPsiPoleCollapse_iff_routePsiPoleCollapse
          hweil r).mp hcollapses.2⟩
  · intro hcollapses
    refine
      { restrictedMass := ?_
        globalMass := ?_ }
    · intro r
      exact
        (parallel09D_directRestrictedTermMass_iff_restrictedQWPoleCollapse
          hweil r).mpr
          ((parallel09D_restrictedQWPoleCollapse_iff_routeRestrictedQWPoleCollapse
            hweil r).mpr (hcollapses r).1)
    · intro r
      exact
        (parallel09D_directGlobalTermMass_iff_globalPsiPoleCollapse
          hweil r).mpr
          ((parallel09D_globalPsiPoleCollapse_iff_routePsiPoleCollapse
            hweil r).mpr (hcollapses r).2)

theorem parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations
    (hweil :
      NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration) :
    Parallel09DDirectTermMassRowsCalibration hweil ↔
      NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapseCalibration ∧
        NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapseCalibration := by
  constructor
  · intro rows
    have hcollapses :=
      (parallel09D_directTermMassRows_iff_routePoleCollapses hweil).mp rows
    exact
      ⟨fun r => (hcollapses r).1,
        fun r => (hcollapses r).2⟩
  · intro hcalibrations
    exact
      (parallel09D_directTermMassRows_iff_routePoleCollapses hweil).mpr
        (fun r => ⟨hcalibrations.1 r, hcalibrations.2 r⟩)

end Route
end ConnesWeilRH
