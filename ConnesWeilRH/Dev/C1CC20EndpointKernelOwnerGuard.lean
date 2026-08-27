/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.EndpointKernelFormula
import ConnesWeilRH.Source.CC20Concrete.RegularKernel

/-!
# CC20 endpoint-kernel owner guard

The paper's endpoint compact operator has the additive raw kernel from CC20
equation (104), whereas the existing `cc20RegularKernel` owns the separate
`Q(delta)` profile.  This leaf puts both kernels on the same positive
coordinate domain and proves only the literal pointwise nonidentification
forced by their diagonal values.

Designated downstream consumer: the eventual concrete `kf_I` input of
`C1CC20OperatorGap`, which in turn supplies `CC20EndpointTraceCertificate`.
No almost-everywhere or induced-operator claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointKernelOwnerGuard

open CC20Concrete

/-- The raw paper endpoint kernel written on the positive coordinates used by
the existing regular-kernel owner.  This is a log-coordinate lift only; it is
not a claim that either integral-operator action has been constructed. -/
noncomputable def endpointKernelOnPositiveCoordinates
    (data : CC20EndpointSpectralData)
    (p : PositiveCoordinate × PositiveCoordinate) : Real :=
  data.endpointAdditiveKernel (Real.log p.2 - Real.log p.1)

theorem endpointKernelOnPositiveCoordinates_diagonal
    (data : CC20EndpointSpectralData) (u : PositiveCoordinate) :
    endpointKernelOnPositiveCoordinates data (u, u) = 0 := by
  simp [endpointKernelOnPositiveCoordinates, data.endpointAdditiveKernel_zero]

/-- The current `Q(delta)` kernel cannot be literally the raw endpoint kernel
from CC20 equation (104).  This is strictly a pointwise statement: equality
almost everywhere or equality of induced integral operators needs a separate
off-diagonal or continuity argument. -/
theorem cc20RegularKernel_ne_endpointKernelOnPositiveCoordinates
    (data : CC20EndpointSpectralData) :
    cc20RegularKernel ≠ endpointKernelOnPositiveCoordinates data := by
  apply cc20RegularKernel_ne_of_pointwise_zero_diagonal
  intro u
  exact endpointKernelOnPositiveCoordinates_diagonal data u

end C1CC20EndpointKernelOwnerGuard
end Source
end ConnesWeilRH
