import ConnesWeilRH.Dev.C1HealthyYoshidaDetector

/-!
# CC20 Archimedean readback on the same compact-log owner

CC20 writes the real Archimedean distribution in positive coordinates and then
uses the half-density variable

`F y = exp (y / 2) * f (exp y)`.

This leaf records the resulting logarithmic-coordinate expression on the
existing `CompactLogTest` owner.  The expression is deliberately written out
instead of defining it as an alias for `archimedeanTerm`, so the dictionary
readback is a checked equality.  The positive-coordinate change-of-variables
theorem is not asserted here; only the displayed log-coordinate formula and
its sign convention are formalized.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20ArchimedeanReadback

open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1HealthyYoshidaDetector

/-- CC20's `W_R` after the half-density substitution, in log coordinates.

The constant term and density are exactly the same terms displayed in the
paper's Archimedean formula, with `F` living on the healthy compact-log owner.
-/
noncomputable def cc20WRLog (F : CompactLogTest) : Real :=
  ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
        F.test 0) +
      ∫ y in Set.Ioi (0 : Real), C1SameOwnerWeil.archimedeanIntegrand F y).re

/-- The log-coordinate `W_R` is definitionally the same-owner Archimedean
functional. -/
theorem cc20WRLog_eq_archimedeanTerm (F : CompactLogTest) :
    cc20WRLog F = C1SameOwnerWeil.archimedeanTerm F := by
  rfl

/-- CC20's sign convention `W_infinity = -W_R`, in log coordinates. -/
noncomputable def cc20WInfinityLog (F : CompactLogTest) : Real :=
  -cc20WRLog F

theorem cc20WInfinityLog_eq_neg_archimedeanTerm (F : CompactLogTest) :
    cc20WInfinityLog F = -C1SameOwnerWeil.archimedeanTerm F := by
  rw [cc20WInfinityLog, cc20WRLog_eq_archimedeanTerm]

/-- The zero Mellin value is one of the three explicit CC20 vanishing nodes. -/
theorem laplaceAt_zero_eq_zero_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    CC20YoshidaConvolution.CompactLogTest.laplaceAt g (0 : ℂ) = 0 := by
  simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
    hvanishes CriticalVanishingPoint.zero
      (by simp [cc20TripleFiniteVanishingSet])

/-- The rank-one error term in CC20's endpoint estimate, expressed on the
same owner.  `normSq` is the real quantity denoted by `|g-hat(0)|^2`. -/
noncomputable def cc20RankOneBadDirection
    (c : Real) (g : CompactLogTest) : Real :=
  c * Complex.normSq
    (CC20YoshidaConvolution.CompactLogTest.laplaceAt g (0 : ℂ))

theorem cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple
    (c : Real) (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    cc20RankOneBadDirection c g = 0 := by
  rw [cc20RankOneBadDirection,
    laplaceAt_zero_eq_zero_of_vanishesOn_cc20Triple g hvanishes,
    Complex.normSq_zero, mul_zero]

/-- Once the triple vanishing kills the rank-one direction, CC20's conditional
endpoint inequality has no residual subtraction.  The trace inequality itself
remains a caller-supplied analytic premise. -/
theorem cc20WInfinityLog_ge_trace_of_endpoint_bound
    (c trace : Real) (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hbound : trace - cc20RankOneBadDirection c g ≤
        cc20WInfinityLog g.convolutionSquare) :
    trace ≤ cc20WInfinityLog g.convolutionSquare := by
  rw [cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple
    c g hvanishes, sub_zero] at hbound
  exact hbound

/-- The exact analytic payload still needed from the CC20 endpoint argument.
The trace term is required to be nonnegative, while the endpoint lower bound
is kept separate from that sign fact. -/
structure CC20EndpointTraceCertificate (g : CompactLogTest) where
  coefficient : Real
  trace : Real
  trace_nonnegative : 0 ≤ trace
  endpoint_bound :
    trace - cc20RankOneBadDirection coefficient g ≤
      cc20WInfinityLog g.convolutionSquare

/-- A CC20 endpoint certificate implies nonnegativity of the same-owner Weil
value once the Hermitian square is prime-free. -/
theorem qw_nonneg_of_cc20EndpointTraceCertificate
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (hcertificate : CC20EndpointTraceCertificate g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have htrace : hcertificate.trace ≤
      cc20WInfinityLog g.convolutionSquare :=
    cc20WInfinityLog_ge_trace_of_endpoint_bound
      hcertificate.coefficient hcertificate.trace g hvanishes
      hcertificate.endpoint_bound
  have hwinf : cc20WInfinityLog g.convolutionSquare =
      C1SameOwnerWeil.qw g := by
    calc
      cc20WInfinityLog g.convolutionSquare =
          -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare :=
        cc20WInfinityLog_eq_neg_archimedeanTerm g.convolutionSquare
      _ = C1SameOwnerWeil.qw g := by
        symm
        exact
          qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
            g hvanishes hsupport
  rw [hwinf] at htrace
  exact hcertificate.trace_nonnegative.trans htrace

/-- Root-support form of the endpoint consumer.  The support propagation and
endpoint-vanishing lemmas supply the open square window automatically. -/
theorem qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hcertificate : CC20EndpointTraceCertificate g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  apply qw_nonneg_of_cc20EndpointTraceCertificate g hvanishes _ hcertificate
  have hwindow :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have htwo : (2 : Real) * (Real.log 2 / 2) = Real.log 2 := by
    ring
  rw [htwo] at hwindow
  exact hwindow

/-- On the Yoshida root window, an endpoint trace certificate forces the
Archimedean term of the Hermitian square to be nonpositive.  This is the
sign-facing form of the endpoint theorem: triple vanishing kills the pole,
root support kills every prime term, and the remaining identity is
`qw g = -archimedeanTerm (g □)`. -/
theorem archimedeanTerm_nonpos_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hcertificate : CC20EndpointTraceCertificate g) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0 := by
  have hqw : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
      g hvanishes hsupport hcertificate
  have hreadback :=
    qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
      g hvanishes hsupport
  rw [hreadback] at hqw
  linarith

/-- A CC20 endpoint certificate and strict healthy detector data cannot live
on the same root-supported test.  The endpoint certificate gives `qw g ≥ 0`,
whereas detector data gives a strictly negative spectral value and hence
`qw g < 0` through the proved center-`2` readback.

This theorem is a route guard: four-node interpolation inside the endpoint
window supplies vanishing and nonzero detection, but a proof of its strict
detector sign would already cross the RH-level boundary. -/
theorem not_healthyYoshidaDetectorData_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hcertificate : CC20EndpointTraceCertificate g)
    (rho : Complex) :
    ¬ C1HealthyYoshidaDetector.HealthyYoshidaDetectorData rho g := by
  intro hdetector
  have hqwNonnegative : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
      g hdetector.vanishesOnF hsupport hcertificate
  have hspectralNegative :
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (C1HealthyYoshidaDetector.weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hdetector.weilSquareSumPositive
  have hqwNegative : C1SameOwnerWeil.qw g < 0 := by
    rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
    exact hspectralNegative
  exact (not_lt_of_ge hqwNonnegative) hqwNegative

/-- The exact RH-level boundary exposed by the endpoint route.  If every
off-line source zero had strict healthy detector data on the Yoshida root
window, and every triple-vanishing test on that window carried the published
CC20 endpoint certificate, then the two preceding signs would contradict one
another and every source zero would lie on the critical line.

The current four-node interpolation theorem does not discharge
`hrootDetector`: it supplies vanishing and nonzero detection, but not the
strict Weil sign. -/
theorem sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates
    (hrootDetector : forall {rho : Complex},
      RHDefinitionBridge.standard.sourceNontrivialZero rho ->
        rho.re ≠ 1 / 2 ->
          exists g : CompactLogTest,
            C1HealthyYoshidaDetector.HealthyYoshidaDetectorData rho g /\
              Function.support g.test ⊆
                Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hendpoint : forall g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g ->
        Function.support g.test ⊆
            Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ->
          Nonempty (CC20EndpointTraceCertificate g)) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · obtain ⟨g, hdetector, hsupport⟩ := hrootDetector hrho hline
    obtain ⟨hcertificate⟩ :=
      hendpoint g hdetector.vanishesOnF hsupport
    exact False.elim
      ((not_healthyYoshidaDetectorData_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
        g hsupport hcertificate rho) hdetector)

/-- On a triple-vanishing root with the prime-free Hermitian square, the
sign-corrected CC20 Archimedean distribution reads back exactly to `qw`.

This is a ledger identity only; it does not provide the missing endpoint
nonpositivity theorem for the Archimedean term.
-/
theorem cc20WInfinityLog_eq_qw_of_vanishesOn_cc20Triple_of_primeFreeSquare
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2)) :
    cc20WInfinityLog g.convolutionSquare = C1SameOwnerWeil.qw g := by
  calc
    cc20WInfinityLog g.convolutionSquare =
        -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare :=
      cc20WInfinityLog_eq_neg_archimedeanTerm g.convolutionSquare
    _ = C1SameOwnerWeil.qw g := by
      symm
      exact
        qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
          g hvanishes hsupport

end C1CC20ArchimedeanReadback
end Source
end ConnesWeilRH
