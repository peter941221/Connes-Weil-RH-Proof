/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1TboxPullthroughQ28M
import ConnesWeilRH.Dev.C1ConcreteClassMomentCertificate
import ConnesWeilRH.Dev.C1Q28ClassGramIntervalTransfer

/-!
# Record 1218: entrywise binding of the true-box consumption chain

Capstone of the consumption-chain regeneration (prereg
1218_consumption_chain_regen_preregistration.md).  Assembles the 1218
Hbox instance for the TRUE gate matrix out of:

- M side: `q28_hboxM_of_sameParity` (record 1217 certified boxes;
  mixed parity closed by the landed D1 parity theorem, same parity
  consumed as the named hypothesis `hsp` - the registered entrywise
  envelope campaign);
- G side: `q28_classGram_bounds_of_baseMomentBounds`, fed by the
  UNCONDITIONAL landed record-1145 concrete certificate
  `q28_baseMoment_bounds_of_concrete_certificate` (I_0/I_2).

and closes the whole consumption chain:

`hsp + representation/normalization slots -> ICgate <= -mu_q28M`.

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Q28MEntrywiseBinding

open Matrix
open C1HboxRationalData
open C1GateMatrixBoxData
open C1ClassGramOwner
open C1ClassWindowObjects
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1ConcreteClassMomentCertificate
open C1Q28ClassGramIntervalTransfer
open C1WindowRationalIngest
open C1GateLevelTransferClassesQ28M
open C1TboxPullthroughQ28M
open CCM25Concrete.CompactLogConvolution

/-- The class owner radius `a = 2`. -/
theorem htwo : (0 : ℝ) < 2 := by norm_num

/-- **The 1218 Hbox instance** (conditional): given the 20 same-parity
entrywise enclosures (the registered follow-up campaign), the TRUE
gate matrix and the TRUE class Gram matrix sit entrywise inside the
committed true boxes. -/
theorem q28_hbox_1218_of_sameParity
    (hsp : ∀ i j : Fin 8, Even ((i : ℕ) + (j : ℕ)) →
      MLo_q28M i j ≤ gateMatrix (classTestFamily 2 htwo) i j ∧
        gateMatrix (classTestFamily 2 htwo) i j ≤ MHi_q28M i j) :
    Hbox GLo_q28 GHi_q28 MLo_q28M MHi_q28M
      (classGramMatrix 2 htwo)
      (gateMatrix (classTestFamily 2 htwo)) := by
  refine hbox_of_classGramBounds 2 htwo GLo_q28 GHi_q28 MLo_q28M MHi_q28M
    (gateMatrix (classTestFamily 2 htwo)) ?_ ?_
  · have hMom := q28_baseMoment_bounds_of_concrete_certificate
    exact q28_classGram_bounds_of_baseMomentBounds hMom.1 hMom.2
  · exact q28_hboxM_of_sameParity 2 htwo hsp

/-- **THE 1218 HEADLINE**: the entire consumption chain of the class
(2,8) window leg reduces to the 20 same-parity entrywise facts plus
the representation/normalization slots. -/
theorem q28_absolute_1218_of_sameParity {w : CompactLogTest}
    {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare
      = c ⬝ᵥ (gateMatrix (classTestFamily 2 htwo) *ᵥ c))
    (hker : Q28.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (classGramMatrix 2 htwo *ᵥ c) = 1)
    (hsp : ∀ i j : Fin 8, Even ((i : ℕ) + (j : ℕ)) →
      MLo_q28M i j ≤ gateMatrix (classTestFamily 2 htwo) i j ∧
        gateMatrix (classTestFamily 2 htwo) i j ≤ MHi_q28M i j) :
    ICgate w.convolutionSquare ≤ -mu_q28M :=
  absolute_true_q28M hrep hker hnorm (q28_hbox_1218_of_sameParity hsp)

end C1Q28MEntrywiseBinding
end Source
end ConnesWeilRH
