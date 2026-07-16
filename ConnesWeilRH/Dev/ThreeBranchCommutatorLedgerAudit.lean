/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ThreeBranchCommutatorLedger

namespace ConnesWeilRH.Dev.ThreeBranchCommutatorLedgerAudit

open ConnesWeilRH Source CC20Concrete

#check @cc20Commutator
#check @cc20OuterCommutatorBranch
#check @cc20SecondSupportCommutatorBranch
#check @cc20ReflectedOuterCommutatorBranch
#check @cc20ProlateCommutatorBranch
#check @cc20ThreeBranchCommutator
#check @cc20Commutator_eq_threeBranch_of_eq
#check @cc20Inner_commutator_eq_threeBranch_of_eq
#check @cc20CommutatorResidueResponse
#check @cc20ThreeBranchResidueResponse
#check @cc20CommutatorResidueResponse_eq_threeBranch_of_eq
#check @cc20CommutatorResidueResponse_zero

#print axioms cc20Commutator_eq_threeBranch_of_eq
#print axioms cc20Inner_commutator_eq_threeBranch_of_eq
#print axioms cc20CommutatorResidueResponse_eq_threeBranch_of_eq
#print axioms cc20CommutatorResidueResponse_zero

end ConnesWeilRH.Dev.ThreeBranchCommutatorLedgerAudit
