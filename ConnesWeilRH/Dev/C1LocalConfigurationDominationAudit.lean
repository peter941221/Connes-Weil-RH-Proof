/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1LocalConfigurationDomination

/-!
# C1 record 1117 audit: axiom bookkeeping for the Stage-B contract

`#print axioms` on every load-bearing theorem of
`C1LocalConfigurationDomination`, plus end-to-end plumbing examples:

* a Platt-Trudgian-shaped floor hypothesis really inhabits
  `ICStageBContraction g` for an arbitrary test (the k=1 toy cell);
* contraction data plus the budget really yields the 1089 gate Prop
  (typechecked at an arbitrary `g`, no detector claimed).

Expected axiom sets (gate G2 of record 1117): each list is a subset of
{propext, Classical.choice, Quot.sound} - the same three Mathlib base
axioms that already support records 1089/1098/1115; choice enters only
through the inherited `supportRadius`/`globalIndexBound` machinery.
RH unclaimed; this audit certifies plumbing, never a sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LocalConfigurationDominationAudit

open ConnesWeilRH.Source.C1LocalConfigurationDomination
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

#print axioms orbitWindowSemiLocalGate_iff
#print axioms ICgate_congr
#print axioms hasCompactSupport_finset_sum
#print axioms ICintegrable_sum
#print axioms support_ICdefect_subset
#print axioms archimedeanNumerator_ICdefect
#print axioms archimedeanIntegrand_ICdefect
#print axioms ICdefect_integrand_integrable
#print axioms archimedeanTerm_packTest_add
#print axioms archimedeanTerm_packTest_sub
#print axioms archimedeanTerm_packTest_smul
#print axioms finitePrimeSum_packTest_eq_sum_range
#print axioms finitePrimeSum_packTest_add
#print axioms finitePrimeSum_packTest_sub
#print axioms finitePrimeSum_packTest_smul
#print axioms ICgate_packTest_add
#print axioms ICgate_packTest_sub
#print axioms ICgate_packTest_smul
#print axioms ICgate_ICdefect
#print axioms orbitWindowSemiLocalGate_of_contraction
#print axioms ICStageBContraction_of_below_floor

/-! ### End-to-end plumbing examples -/

/-- The k=1 cell: the height-47 verified-zero ball (the 7 tabulated zeros
below height 47 live inside the Platt-Trudgian regime, record 1114 §4(3)),
together with an off-line zero hypothesis, is geometrically vacuous, and the
toy theorem really inhabits the contraction type for every test. -/
example (rho : ℂ) (g : CompactLogTest)
    (hz : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hfloor : ∀ z : ℂ,
        RHDefinitionBridge.standard.sourceNontrivialZero z →
          |z.im| ≤ (47 : ℝ) → z.re = 1 / 2)
    (hh : |rho.im| ≤ (47 : ℝ)) (hoff : rho.re ≠ 1 / 2) :
    ICStageBContraction g :=
  ICStageBContraction_of_below_floor rho 47 g hz hh hfloor hoff

/-- The bridge edge, stated at an arbitrary test: contraction data plus the
budget really yields the 1089 gate Prop, no detector, no instance claimed. -/
example (g : CompactLogTest) (c : ICStageBContraction g)
    (hb : c.epsilon ≤ ∑ i ∈ c.s, c.lam i * c.mu i) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g :=
  orbitWindowSemiLocalGate_of_contraction g c hb

/-- The vacuous k=1 cell closes directly: floor + off-line zero is absurd,
so the gate Prop follows for every test (the configuration, not the
plumbing, is what's empty here). -/
example (rho : ℂ) (g : CompactLogTest)
    (hz : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hfloor : ∀ z : ℂ,
        RHDefinitionBridge.standard.sourceNontrivialZero z →
          |z.im| ≤ (47 : ℝ) → z.re = 1 / 2)
    (hh : |rho.im| ≤ (47 : ℝ)) (hoff : rho.re ≠ 1 / 2) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g :=
  absurd (hfloor rho hz hh) hoff

end -- the noncomputable section opened above

end C1LocalConfigurationDominationAudit
end Source
end ConnesWeilRH
