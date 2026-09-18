/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninScaleMonotonicity

/-!
Audit for `SoninScaleMonotonicity.lean`: print the statements and the axiom
footprint of every declaration.
-/

open ConnesWeilRH.Dev.SoninScaleMonotonicity

#check @ccm24LogRadialSupportClosedSubspace_mono
#print axioms ccm24LogRadialSupportClosedSubspace_mono
#check @ccm24ArchimedeanFourierSupportClosedSubspace_mono
#print axioms ccm24ArchimedeanFourierSupportClosedSubspace_mono
#check @ccm24ArchimedeanSoninClosedSubspace_mono
#print axioms ccm24ArchimedeanSoninClosedSubspace_mono
#check @archimedeanSoninCarrier_nontrivial_of_le
#print axioms archimedeanSoninCarrier_nontrivial_of_le
#check @archimedeanSoninCarrier_nontrivial_of_not_of_le
#print axioms archimedeanSoninCarrier_nontrivial_of_not_of_le
