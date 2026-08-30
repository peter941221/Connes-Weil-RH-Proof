import ConnesWeilRH.Dev.C1CC20ArchimedeanReadback
import ConnesWeilRH.Source.CC20YoshidaConvolution

/-!
# GATE 1 delta wiring: the CC20 (141)-(143) comparison chain as a certificate

The GATE 1 assembly (`C1CC20Gate1Assembly`) ends at the `K_I`-side residual
shape `trace - (4*a/log 2) * rank <= 0` and explicitly does NOT claim the
archimedean comparison of that residual against `W_infinity` - the delta
payload of GATE 1 (docs/proofs/1046, 1056, 1057 s2, 1059 s5).

CC20 proves its final inequality (141) by a three-step chain, verbatim in
docs/proofs/1057 section 2 (tex:1958-1990):

  (142)  tr(rep(f) S) = W_infinity(f) + E(f),        f = g * g*
  chain  E(f) = <xi | N_I xi> <= gamma * |<xi_0 | xi>|^2
                   = (gamma / log 2) * |k-hat(0)|^2
  (143)  k-hat(0) = -2 * g-hat(0),  support k subset [2^(-1/2), 2^(1/2)]

This leaf packages the chain as a named contract
`CC20ArchimedeanComparison` and proves the wiring theorem: consumed at a
triple-vanishing test the chain yields the `CC20EndpointTraceCertificate`
that the same-owner `qw >= 0` consumers in `C1CC20ArchimedeanReadback`
already eat.  The content is the vanishing mechanism, not new analysis:

* the chain rank `|k-hat(0)|^2` becomes zero through (143) plus vanishing at
  the CRITICAL half-density node `s = 1/2` (the paper's `rho = 0`), so
  `E(f) <= 0` and `tr <= W_infinity`;
* the certificate rank coordinate `laplaceAt g 0` (the paper's `rho = i/2`)
  is separately zeroed by the zero node of the same triple vanishing - the
  identity of the two nodes is NOT asserted anywhere (docs/proofs/1057 s5
  flag: intro vanishes at +i/2 AND 0, final theorem at -i/2; this owner's
  triple set {0, 1/2, 1} is the union of all three, so every consumer
  hypothesis here holds by design).

The premises `h142`, `hEchain`, `h143` are the remaining analytic payload:
`hEchain` is exactly the GATE 1 gamma-side estimate (140) transplanted to
the rep-theoretic vector, and `h142` is the trace identification.  Neither
is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20ArchimedeanComparisonWiring

open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1CC20ArchimedeanReadback

/-- The `half` node of the triple vanishing reads back as
`laplaceAt g (1/2) = 0` on the compact-log owner. -/
theorem laplaceAt_half_eq_zero_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    CC20YoshidaConvolution.CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 := by
  simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
    hvanishes CriticalVanishingPoint.half
      (by simp [cc20TripleFiniteVanishingSet])

/-- The CC20 comparison chain (142)-(143) plus the `E(f)` estimate, packaged
as the named delta payload of GATE 1 for one compact-log test.

Coordinate note: all Mellin evaluations are on the half-density log owner,
so the paper's `rho = 0` values (`k-hat(0)`, `g-hat(0)` of the `E`-chain)
are `laplaceAt` at `s = 1/2` here, while the endpoint certificate's rank
coordinate is `laplaceAt` at `s = 0` (see the module docstring). -/
structure CC20ArchimedeanComparison
    (g : CompactLogTest) where
  /-- CC20's auxiliary test `k` of eq-(143). -/
  k : CompactLogTest
  /-- The representation-side trace `tr(rep(f) S)`, `f = g * g*`. -/
  trace : Real
  /-- The error term `E(f)` of eq-(142). -/
  eTerm : Real
  /-- The chain constant `gamma` of the `E(f) <= gamma * |<xi_0|xi>|^2`
  estimate (the same letter carried by `CC20OperatorGapData.gamma`). -/
  gamma : Real
  trace_nonnegative : 0 ≤ trace
  /-- Eq-(142): the trace splits into the archimedean part plus `E(f)`. -/
  h142 : trace = cc20WInfinityLog g.convolutionSquare + eTerm
  /-- The `E`-chain of tex:1963-1990 through the rank-one direction of `k`. -/
  hEchain : eTerm ≤ (gamma / Real.log 2) *
      Complex.normSq
        (CC20YoshidaConvolution.CompactLogTest.laplaceAt k (1 / 2 : ℂ))
  /-- Eq-(143): `k-hat(0) = -2 g-hat(0)` at the paper's `rho = 0` node. -/
  h143 : CC20YoshidaConvolution.CompactLogTest.laplaceAt k (1 / 2 : ℂ) =
      -(2 : ℂ) •
        CC20YoshidaConvolution.CompactLogTest.laplaceAt g (1 / 2 : ℂ)

/-- Delta wiring: at a triple-vanishing compact-log test, the CC20
comparison chain (142)-(143) produces the endpoint trace certificate with
the paper's coefficient `4 * gamma / log 2` of eq-(141).

No analysis is invented here: the theorem is the exact statement that the
two rank-one coordinates are killed by the two nodes of the triple
vanishing, and that the surviving inequality `trace <= W_infinity` is
`E(f) <= 0` read off eq-(142). -/
noncomputable def cc20EndpointTraceCertificate_of_archimedeanComparison
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (H : CC20ArchimedeanComparison g) :
    CC20EndpointTraceCertificate g where
  coefficient := 4 * H.gamma / Real.log 2
  trace := H.trace
  trace_nonnegative := H.trace_nonnegative
  endpoint_bound := by
    -- the certificate's rank coordinate dies at the zero node
    have hrank : cc20RankOneBadDirection
        (4 * H.gamma / Real.log 2) g = 0 :=
      cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple
        (4 * H.gamma / Real.log 2) g hvanishes
    rw [hrank, sub_zero]
    -- the chain rank dies at the half node, so E(f) <= 0
    have hghalf :
        CC20YoshidaConvolution.CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 :=
      laplaceAt_half_eq_zero_of_vanishesOn_cc20Triple g hvanishes
    have hezero : H.eTerm ≤ 0 := by
      have hkk : CC20YoshidaConvolution.CompactLogTest.laplaceAt
          H.k (1 / 2 : ℂ) = 0 := by
        rw [H.h143, hghalf, smul_zero]
      calc H.eTerm
          ≤ (H.gamma / Real.log 2) *
              Complex.normSq
                (CC20YoshidaConvolution.CompactLogTest.laplaceAt H.k (1 / 2 : ℂ)) :=
            H.hEchain
        _ = (H.gamma / Real.log 2) * 0 := by rw [hkk, Complex.normSq_zero]
        _ = 0 := mul_zero _
    -- eq-(142): trace = W_infinity + E(f) with E(f) <= 0
    rw [H.h142]
    linarith

/-- Composition closure: the wired certificate feeds the unconditional
same-owner positivity consumer; under the root-support window the endpoint
chain gives `0 <= qw g` from the published comparison premises alone. -/
theorem qw_nonneg_of_archimedeanComparison
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (H : CC20ArchimedeanComparison g) :
    0 ≤ C1SameOwnerWeil.qw g :=
  qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
    g hvanishes hsupport
    (cc20EndpointTraceCertificate_of_archimedeanComparison g hvanishes H)

end C1CC20ArchimedeanComparisonWiring
end Source
end ConnesWeilRH
