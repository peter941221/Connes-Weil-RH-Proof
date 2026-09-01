import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1HealthyDetectorPinning - consumer #2 exit: the pinned healthy log detector

This module advances consumer 2 of `RH_MAINLINE_FREEZE.md` ("Allowed Work",
item 2): *a genuine compact-log detector with explicit support radius and
finite visible-prime set*.

The object is unconditional and per off-line source zero: the four-node
interpolator (`exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf`)
supplies the test, the root-support window `[-log 2 / 2, log 2 / 2]` is the
explicit radius, and this module promotes the prime-free square to the
EXPLICIT visible-prime statement `globalPrimeIndexSet g.convolutionSquare
= ∅` - the finite visible-prime set in its minimal (empty) form.

The sign obligation is deliberately NOT claimed here.  For the pinned
detector, the full `HealthyYoshidaDetectorData` package is EQUIVALENT to the
single scalar gate `selectedDetectorArchimedeanGate`, which is exactly the
opening obligation of consumer 3 (semi-local positive-trace/readback data).
The numerical chain `docs/proofs/1077` - `1079` measures that gate deeply
positive (sink 33.78% of lever at the second source zero, node residual
4.5e-18) with an explicit named test family; no numerical content is
consumed by any theorem here.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorPinning

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1SameOwnerWeil

/-! ### Square support and the visible-prime set -/

/-- Root support in the centered Yoshida window already places the Hermitian
square in the open prime-free window. -/
theorem convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
  have hwindow :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have htwo : (2 : Real) * (Real.log 2 / 2) = Real.log 2 := by ring
  rw [htwo] at hwindow
  exact hwindow

/-- A square supported strictly inside the first prime-power locations has an
EMPTY visible prime-power index set: every prime power `n >= 2` has
`log n >= log 2`, outside the open window on both sides. -/
theorem globalPrimeIndexSet_eq_empty_of_support_subset_open_log_two
    (F : CompactLogTest)
    (hsupport : Function.support F.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2)) :
    globalPrimeIndexSet F = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro n hn
  have hpair := (mem_globalPrimeIndexSet_iff F n).mp hn
  have hprime : IsPrimePow n := hpair.1
  have hterm : finitePrimeTermComplex F n ≠ 0 := hpair.2
  have htwo : (2 : Real) ≤ n := by
    exact_mod_cast hprime.two_le
  have hlog2le : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) htwo
  have hsumne : F.test (Real.log n) + F.test (-Real.log n) ≠ 0 := by
    intro hzero
    apply hterm
    simp [finitePrimeTermComplex, hzero]
  by_cases hpos : F.test (Real.log n) = 0
  · by_cases hneg : F.test (-Real.log n) = 0
    · exact absurd (by rw [hpos, hneg]; simp) hsumne
    · have hinside := hsupport hneg
      have hgt : -Real.log 2 < -Real.log n := hinside.1
      have hlt : Real.log n < Real.log 2 := by linarith
      exact absurd hlt (not_lt.mpr hlog2le)
  · have hinside := hsupport hpos
    exact absurd hinside.2 (not_lt.mpr hlog2le)

/-! ### The pinned detector (consumer #2 exit) -/

/-- CONSUMER #2 EXIT.  For every off-line source zero there is a genuine
compact-log detector that vanishes on the triple node set, detects the zero
with the normalized value `-1`, carries the EXPLICIT support radius
`log 2 / 2`, and has the EXPLICIT finite (empty) visible-prime set. -/
theorem exists_pinnedHealthyDetector_rootWindow
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ g : CompactLogTest,
      HealthyMinimalLaplaceRealizes rho g ∧
        CompactLogTest.laplaceAt g rho = -1 ∧
          Function.support g.test ⊆
            Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
            globalPrimeIndexSet g.convolutionSquare = ∅ := by
  rcases exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf hrho hoff
    with ⟨g, hrealizes, hrhoValue, hsupport⟩
  refine ⟨g, hrealizes, hrhoValue, hsupport, ?_⟩
  exact
    globalPrimeIndexSet_eq_empty_of_support_subset_open_log_two g.convolutionSquare
      (convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf g hsupport)

/-! ### The consumer-2 to consumer-3 handoff gate -/

/-- The single scalar gate that consumer 3 (semi-local positive-trace /
readback data) must discharge on a pinned detector: strict positivity of the
archimedean term of the Hermitian square. -/
def selectedDetectorArchimedeanGate (_rho : Complex) (g : CompactLogTest) :
    Prop :=
  0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare

/-- On a pinned detector the full healthy detector data package is EQUIVALENT
to the scalar archimedean gate: consumer 3 owes exactly one inequality. -/
theorem healthyDetectorData_iff_selectedDetectorArchimedeanGate
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyMinimalLaplaceRealizes rho g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    HealthyYoshidaDetectorData rho g ↔
      selectedDetectorArchimedeanGate rho g := by
  have hprimefree :=
    convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf g hsupport
  constructor
  · intro hdata
    exact
      (weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
        g h.vanishesOn_cc20Triple hprimefree).mp hdata.weilSquareSumPositive
  · intro hgate
    exact
      healthyDetectorData_of_HealthyMinimalLaplaceRealizes_of_archimedeanTerm_pos
        h hprimefree hgate

/-- A pinned detector whose archimedean gate holds yields the full healthy
detector package - the consumer-3 entry point, with no other obligation. -/
theorem exists_healthyDetectorData_of_gate_of_pinnedHealthyDetector
    {rho : Complex} {g : CompactLogTest}
    (hpinned : HealthyMinimalLaplaceRealizes rho g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hgate : selectedDetectorArchimedeanGate rho g) :
    ∃ g' : CompactLogTest, HealthyYoshidaDetectorData rho g' :=
  ⟨g, (healthyDetectorData_iff_selectedDetectorArchimedeanGate hpinned
    hsupport).mpr hgate⟩

end C1HealthyDetectorPinning
end Source
end ConnesWeilRH
