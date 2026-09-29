import ConnesWeilRH.Dev.C1CC20ArchimedeanComparisonWiring
import ConnesWeilRH.Dev.C1PsiLinearity

/-!
# CC20 comparison: discharge of the exposed (143) premise

`CC20ArchimedeanComparison` stores an auxiliary compact-log test `k` and the
single equation

  `laplaceAt k (1/2) = -2 * laplaceAt g (1/2)`.

At this interface the equation is not an independent analytic input: the
auxiliary test can be chosen to be the negative of `g + g`.  This file keeps
the two genuinely analytic fields, (142) and the `E`-chain, as hypotheses and
constructs the comparison package with that canonical `k`.  It therefore
removes `h143` from the caller contract without changing the owner `g` or
asserting a trace identity.

No endpoint sign, root-support statement, or RH conclusion is supplied here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20ArchimedeanComparisonH143

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1CC20ArchimedeanReadback
open C1CC20ArchimedeanComparisonWiring
open C1PsiLinearity

noncomputable section

/-! The canonical auxiliary test for the exposed (143) interface. -/

noncomputable def cc20AuxiliaryNegTwo (g : CompactLogTest) : CompactLogTest :=
  testNeg (testAdd g g)

theorem support_cc20AuxiliaryNegTwo_subset (g : CompactLogTest) :
    Function.support (cc20AuxiliaryNegTwo g).test ⊆ Function.support g.test := by
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro hg
  apply hx
  simp [cc20AuxiliaryNegTwo, testNeg_apply, testAdd_apply, hg]

theorem laplaceAt_cc20AuxiliaryNegTwo
    (g : CompactLogTest) (s : ℂ) :
    laplaceAt (cc20AuxiliaryNegTwo g) s =
      -(2 : ℂ) • laplaceAt g s := by
  rw [cc20AuxiliaryNegTwo, laplaceAt_testNeg, laplaceAt_testAdd]
  simp [smul_eq_mul]
  ring

theorem laplaceAt_cc20AuxiliaryNegTwo_half_eq_zero_of_vanishes
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    laplaceAt (cc20AuxiliaryNegTwo g) (1 / 2 : ℂ) = 0 := by
  rw [laplaceAt_cc20AuxiliaryNegTwo,
    laplaceAt_half_eq_zero_of_vanishesOn_cc20Triple g hvanishes,
    smul_zero]

theorem cc20Echain_iff_nonpos_of_vanishes
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (eTerm gamma : ℝ) :
    eTerm ≤ (gamma / Real.log 2) *
        Complex.normSq (laplaceAt (cc20AuxiliaryNegTwo g) (1 / 2 : ℂ)) ↔
      eTerm ≤ 0 := by
  rw [laplaceAt_cc20AuxiliaryNegTwo_half_eq_zero_of_vanishes g hvanishes,
    Complex.normSq_zero, mul_zero]

/-! Once the already-consumed triple vanishing is in scope, the canonical
auxiliary test makes the vector-valued `E`-chain exactly the scalar sign
obligation `eTerm ≤ 0`.  This constructor therefore removes both the stored
equation (143) and the now-zero norm expression from the caller contract. -/

noncomputable def cc20ArchimedeanComparison_of_h142_eNonpos
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (trace eTerm gamma : ℝ)
    (htrace : 0 ≤ trace)
    (h142 : trace = cc20WInfinityLog g.convolutionSquare + eTerm)
    (heNonpos : eTerm ≤ 0) :
    CC20ArchimedeanComparison g := by
  refine
    { k := cc20AuxiliaryNegTwo g
      trace := trace
      eTerm := eTerm
      gamma := gamma
      trace_nonnegative := htrace
      h142 := h142
      hEchain := ?_
      h143 := laplaceAt_cc20AuxiliaryNegTwo g (1 / 2 : ℂ) }
  exact (cc20Echain_iff_nonpos_of_vanishes g hvanishes eTerm gamma).2 heNonpos

theorem qw_nonneg_of_h142_eNonpos
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (trace eTerm gamma : ℝ)
    (htrace : 0 ≤ trace)
    (h142 : trace = cc20WInfinityLog g.convolutionSquare + eTerm)
    (heNonpos : eTerm ≤ 0) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_archimedeanComparison g hvanishes hsupport
    (cc20ArchimedeanComparison_of_h142_eNonpos g hvanishes trace eTerm gamma
      htrace h142 heNonpos)

/-! Constructor with (143) proved rather than supplied. -/

noncomputable def cc20ArchimedeanComparison_of_h142_hEchain
    (g : CompactLogTest)
    (trace eTerm gamma : ℝ)
    (htrace : 0 ≤ trace)
    (h142 : trace = cc20WInfinityLog g.convolutionSquare + eTerm)
    (hEchain : eTerm ≤ (gamma / Real.log 2) *
      Complex.normSq (laplaceAt (cc20AuxiliaryNegTwo g) (1 / 2 : ℂ))) :
    CC20ArchimedeanComparison g :=
  { k := cc20AuxiliaryNegTwo g
    trace := trace
    eTerm := eTerm
    gamma := gamma
    trace_nonnegative := htrace
    h142 := h142
    hEchain := hEchain
    h143 := laplaceAt_cc20AuxiliaryNegTwo g (1 / 2 : ℂ) }

theorem qw_nonneg_of_h142_hEchain
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (trace eTerm gamma : ℝ)
    (htrace : 0 ≤ trace)
    (h142 : trace = cc20WInfinityLog g.convolutionSquare + eTerm)
    (hEchain : eTerm ≤ (gamma / Real.log 2) *
      Complex.normSq (laplaceAt (cc20AuxiliaryNegTwo g) (1 / 2 : ℂ))) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_archimedeanComparison g hvanishes hsupport
    (cc20ArchimedeanComparison_of_h142_hEchain g trace eTerm gamma htrace
      h142 hEchain)

end
end C1CC20ArchimedeanComparisonH143
end Source
end ConnesWeilRH
