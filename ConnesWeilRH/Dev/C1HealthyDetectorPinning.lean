import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1HealthyDetectorPinning - ROOT-window pinned interpolation

This module records the ROOT-supported interpolation alternative. It does not
supply item 2 of `RH_MAINLINE_FREEZE.md`: the test constructed here is not the
convolution-orbit detector returned by
`exists_healthyDetectorData_of_sourceNontrivialZero_right`.

The object is unconditional and per off-line source zero: the four-node
interpolator (`exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf`)
supplies the test, the root-support window `[-log 2 / 2, log 2 / 2]` is the
explicit radius, and this module promotes the prime-free square to the
EXPLICIT visible-prime statement `globalPrimeIndexSet g.convolutionSquare
= ∅` - the finite visible-prime set in its minimal (empty) form.

The sign obligation is not claimed here. For the pinned test, the full
`HealthyYoshidaDetectorData` package is equivalent to the scalar predicate
`selectedDetectorArchimedeanGate`. That predicate is `arch > 0`, hence it
produces the strict-negative `qw < 0` branch at ROOT support. It is not the
active C3/P2 premise `qw >= 0` for the formal orbit detector. Records
1077--1079 measured a surrogate, while records 1086--1087 proved no continuum
sign. No numerical result is consumed by a theorem here. RH is not claimed.
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

/-! ### The pinned ROOT-window interpolation test -/

/-- For every off-line source zero there is a compact-log interpolation test
that vanishes on the triple node set, detects the zero with normalized value
`-1`, has support radius `log 2 / 2`, and has an empty visible-prime set. This
statement supplies no `HealthyYoshidaDetectorData` sign field. -/
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

/-! ### The ROOT-supported negative-detector gate -/

/-- The scalar sign needed to promote a pinned ROOT test to strict-negative
detector data: positivity of the square's archimedean term. This is not the
semi-local nonnegativity premise of the active C3 exit. -/
def selectedDetectorArchimedeanGate (_rho : Complex) (g : CompactLogTest) :
    Prop :=
  0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare

/-- On a pinned ROOT test, the full healthy detector data package is equivalent
to the scalar archimedean gate. This characterizes the conditional
ROOT-supported negative-detector branch. -/
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

/-- A pinned ROOT test whose archimedean gate holds yields the full healthy
strict-negative detector package. -/
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
