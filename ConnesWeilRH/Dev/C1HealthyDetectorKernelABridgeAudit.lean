import ConnesWeilRH.Dev.C1HealthyDetectorKernelABridge

/-!
# Audit for `C1HealthyDetectorKernelABridge`

Checks the public surface of the kernel (a) / pinned-detector bridge and
pins the axiom profile of every headline statement.  The expected axiom
base is exactly `[propext, Classical.choice, Quot.sound]` and `sorryAx`
must be absent.
-/

namespace ConnesWeilRH.Source.C1HealthyDetectorKernelABridgeAudit

open ConnesWeilRH.Source
open ConnesWeilRH.Source.C1HealthyDetectorKernelABridge

-- public surface
#check @C1HealthyDetectorKernelABridge.convolutionSquare_negTest
#check @C1HealthyDetectorKernelABridge.archimedeanNumerator_negTest
#check @C1HealthyDetectorKernelABridge.archimedeanIntegrand_negTest
#check @C1HealthyDetectorKernelABridge.archimedeanTerm_negTest
#check @C1HealthyDetectorKernelABridge.exists_pinnedDetector_of_kernelAInterpolant

-- axiom pins
#print axioms C1HealthyDetectorKernelABridge.convolutionSquare_negTest
#print axioms C1HealthyDetectorKernelABridge.archimedeanNumerator_negTest
#print axioms C1HealthyDetectorKernelABridge.archimedeanIntegrand_negTest
#print axioms C1HealthyDetectorKernelABridge.archimedeanTerm_negTest
#print axioms C1HealthyDetectorKernelABridge.exists_pinnedDetector_of_kernelAInterpolant

end ConnesWeilRH.Source.C1HealthyDetectorKernelABridgeAudit
