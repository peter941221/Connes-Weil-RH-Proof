/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Q28MEntrywiseBinding

namespace ConnesWeilRH
namespace Source
namespace C1Q28MEntrywiseBindingAudit

open Matrix
open C1HboxRationalData
open C1GateMatrixBoxData
open C1ClassGramOwner
open C1ClassWindowObjects
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1WindowRationalIngest
open C1GateLevelTransferClassesQ28M
open C1TboxPullthroughQ28M
open C1Q28MEntrywiseBinding
open CCM25Concrete.CompactLogConvolution

#print axioms C1WindowRationalIngest.Q28M.top
#print axioms C1GateLevelTransferClassesQ28M.hslack_q28M
#print axioms C1HboxRationalDataQ28M.hrevM_q28M
#print axioms C1TboxPullthroughQ28M.tbox_true_q28M
#print axioms C1TboxPullthroughQ28M.absolute_true_q28M
#print axioms C1Q28MEntrywiseBinding.q28_hbox_1218_of_sameParity
#print axioms C1Q28MEntrywiseBinding.q28_absolute_1218_of_sameParity

/-- The margin is the named positive rational. -/
example : (0 : ℝ) < mu_q28M := mu_q28M_pos

/-- The conditional headline reads off as stated: same-parity
entrywise facts + representation/normalization slots pin the gate. -/
example (w : CompactLogTest) (c : Fin 8 → ℝ)
    (hrep : ICgate w.convolutionSquare
      = c ⬝ᵥ (gateMatrix (classTestFamily 2 htwo) *ᵥ c))
    (hker : Q28.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (classGramMatrix 2 htwo *ᵥ c) = 1)
    (hsp : ∀ i j : Fin 8, Even ((i : ℕ) + (j : ℕ)) →
      C1GateMatrixBoxData.MLo_q28M i j ≤
          gateMatrix (classTestFamily 2 htwo) i j ∧
        gateMatrix (classTestFamily 2 htwo) i j ≤
          C1GateMatrixBoxData.MHi_q28M i j) :
    ICgate w.convolutionSquare ≤ -mu_q28M :=
  q28_absolute_1218_of_sameParity hrep hker hnorm hsp

/-- The Hbox instance composes the landed I_0/I_2 G side with the
conditional 1217 M side. -/
example (hsp : ∀ i j : Fin 8, Even ((i : ℕ) + (j : ℕ)) →
    C1GateMatrixBoxData.MLo_q28M i j ≤
        gateMatrix (classTestFamily 2 htwo) i j ∧
      gateMatrix (classTestFamily 2 htwo) i j ≤
        C1GateMatrixBoxData.MHi_q28M i j) :
    Hbox GLo_q28 GHi_q28 C1GateMatrixBoxData.MLo_q28M
      C1GateMatrixBoxData.MHi_q28M (classGramMatrix 2 htwo)
      (gateMatrix (classTestFamily 2 htwo)) :=
  q28_hbox_1218_of_sameParity hsp

end C1Q28MEntrywiseBindingAudit
end Source
end ConnesWeilRH
