/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RouteWWindowTailNormalForm

/-!
# Audit for the Route-W window/tail normal form
-/

namespace ConnesWeilRH
namespace Dev

section Audit

open Source.CC20Concrete.PositiveTrace

#check @survivorCore_of_windowStrip_of_tailGate
#check @survivorCore_of_twoWindowStrips_of_tailGate

#print axioms survivorCore_of_windowStrip_of_tailGate
#print axioms survivorCore_of_twoWindowStrips_of_tailGate

end Audit

end Dev
end ConnesWeilRH
