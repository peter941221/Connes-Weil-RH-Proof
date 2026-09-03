/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1WindowRationalIngestQ28
import ConnesWeilRH.Dev.C1WindowRationalIngestQ38
import ConnesWeilRH.Dev.C1WindowRationalIngestQ48

/-!
# Audit for record 1115 (rational-Cholesky ingestion brick)

Focused axiom prints for the generic ingestion theorem and the three
concrete instance headlines (classes (2,8), (3,8), (4,8)); acceptance
(1115 pre-registration §1/§3c) is exactly the three standard axioms on
each, with zero `sorryAx` lines in the build log.  The `isTopBound`
statements themselves re-printed here as the outward contract check.
-/

#print axioms ConnesWeilRH.Source.C1WindowRationalIngest.isTopBound_of_closure_sos
#print axioms ConnesWeilRH.Source.C1WindowRationalIngest.Q28.top
#print axioms ConnesWeilRH.Source.C1WindowRationalIngest.Q38.top
#print axioms ConnesWeilRH.Source.C1WindowRationalIngest.Q48.top

example : ConnesWeilRH.Source.E0SlemmaBridge.isTopBound
    ConnesWeilRH.Source.C1WindowRationalIngest.Q28.U
    ConnesWeilRH.Source.C1WindowRationalIngest.Q28.G
    ConnesWeilRH.Source.C1WindowRationalIngest.Q28.M
    ConnesWeilRH.Source.C1WindowRationalIngest.Q28.R :=
  ConnesWeilRH.Source.C1WindowRationalIngest.Q28.top

example : ConnesWeilRH.Source.E0SlemmaBridge.isTopBound
    ConnesWeilRH.Source.C1WindowRationalIngest.Q38.U
    ConnesWeilRH.Source.C1WindowRationalIngest.Q38.G
    ConnesWeilRH.Source.C1WindowRationalIngest.Q38.M
    ConnesWeilRH.Source.C1WindowRationalIngest.Q38.R :=
  ConnesWeilRH.Source.C1WindowRationalIngest.Q38.top

example : ConnesWeilRH.Source.E0SlemmaBridge.isTopBound
    ConnesWeilRH.Source.C1WindowRationalIngest.Q48.U
    ConnesWeilRH.Source.C1WindowRationalIngest.Q48.G
    ConnesWeilRH.Source.C1WindowRationalIngest.Q48.M
    ConnesWeilRH.Source.C1WindowRationalIngest.Q48.R :=
  ConnesWeilRH.Source.C1WindowRationalIngest.Q48.top
