# 945 - Lane-B target: the single Archimedean-balance identity on the healthy carrier

Date: 2026-08-10. Type: route-target scoping note. No proof claimed, no new axiom.
RH NOT claimed.

## 0. Where this sits

The `#print axioms` residual of `UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems`
is 5 project axioms (see Dev/RhOutputAxiomLedger.lean). One of them,
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`, is the lane-B finite-prime
source data. This note pins down the exact open identity that axiom needs, so any follow-up
proof session has a single, stably-phrased target.

## 1. The exact open identity

`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot :
CommonFinitePrimeArithmeticSourceData W` (UnconditionalSkeleton.lean:653,
W = normalizedCoreSourceWeilFormData.toWeilFormSymbols).

`CommonFinitePrimeArithmeticSourceData` (Source/CCM25Concrete/FinitePrimeSourceData.lean:626) has two functional fields:

  finitePrimeData : FinitePrimeArithmeticSourceData W (concreteCommonSourceTest W commonTest)
  scopedArchimedeanContributionBalance (SCAB) :
    forall lambda, forall globalData, forall restrictedData,
      SourceScopedArchimedeanContributionBalance W f lambda globalData restrictedData

where (FinitePrimeSourceData.lean:25-45):

  SourceScopedRestrictedArchimedeanFormula = W.archimedeanTerm (f⋆f) + W.polePairing f
                                             − restrict.FiniteSum(lambda, restrictedData)
  SourceScopedGlobalArchimedeanFormula     = W.poleFunctional (f⋆f) − W.archimedeanTerm (f⋆f)
                                             − global.FiniteSum(globalData)
  SCB :  restrictedFormula = globalFormula
         i.e.  polePairing f + poleFunctional(f⋆f) − 2·archimedeanTerm(f⋆f)
               = global.FiniteSum − restricted.FiniteSum

So SCB is the global-vs-restricted balance of the Weil explicit-formula decomposition:
archimedean terms / pole pairing against the finite-prime sums. This is a real analytic
identity, not an assembly step.

## 2. Current carrier state (evidence)

- Healthy Mellin carrier exists and is axiom-clean:
  Dev/HealthySourceMellinAlgebra.lean (healthyConvStar = SchwartzMap.convolution, real
  Mellin product, fixes additive 2=1) + Dev/WellFormHealthyRepoint.lean (healthyWeilForm,
  #print axioms = [propext, Classical.choice, Quot.sound]).
- But the SourceWeilFormData-style `archimedeanTerm : Test -> Real` is set to
  fun _ => 0 in every constructible carrier (ConcreteP1SupportProbe.lean:169,
  AmbientWeilFormSeam.lean:53, WellFormHealthyRepoint.lean:106).
- A REAL nonzero archimedean term DOES exist in library math: SelectedWeilFormula.lean
  defines archimedeanTerm owner = (log(4*pi) + gamma) * (test 0) + Integral_y>0 integrand
  (CCM25 Eq. 3.7), where the integrand is (e^(y/2)(f(y)+f(-y)) - 2 f 0)/(e^y-e^-y). It is
  per-owner (for a selected convolution square with compact support), not yet lifted to a
  `Test → Real` arc on the healthy/global carrier.  So the missing piece is NOT a formula
  hunt: it is lifting/encoding that Eq. 3.7 term into the healthy carrier's archimedeanTerm
  and proving the SCB under it.
- The healthy carrier is NOT imported by any Route/skeleton consumer (grep: only self-refs),
  so it feeds nothing today.

## 3. The single target to close lane-B

On the healthy Mellin carrier, define the true nonzero archimedeanTerm (the archimedean
explicit-formula term) and prove

   healthyBalance :
     SourceScopedArchimedeanContributionBalance
       healthyMellinSourceTestAlgebra.toWeilFormSymbols f lambda global restricted
     (given the matching global/restricted finite-prime sums)

then use it to construct `CommonFinitePrimeArithmeticSourceData` and wire it into the
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` slot, turning the axiom into the
resulting identity. That would reduce the residual by one row (5 -> 4).

## 4. What this note does NOT claim

It is not a proof. `archimedeanTerm = 0` remains an open placeholder. The "healthy re-point
= wiring" is explicitly ruled out (the carrier is un-wired; and even wired, SCB needs the real
nonzero archimedean term). This is a scoping/roadmap note for one Mill-reserve, one target.
