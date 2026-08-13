import ConnesWeilRH.Dev.C1HealthyTestSpace

/-! # C1WeilExplicit - route-facing names for the same-owner Weil functional

The implementation lives in `C1SameOwnerWeil`. This module keeps the earlier
route-facing names while removing the former singleton `{2}` truncation.

For every compact formula test `F`, compact support computes an exact finite set
containing all visible prime powers. For a route test `g`, `healthyQw g` applies
the functional to `g^* * g` exactly once.

No sign theorem is asserted. RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WeilExplicit

open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil

/-- The complete compact-log Weil functional. -/
noncomputable def healthyPsi (F : CompactLogTest) : Real :=
  C1SameOwnerWeil.psi F

/-- `QW(g,g)` reads `Psi(g^* * g)` with one square. -/
noncomputable def healthyQw (g : CompactLogTest) : Real :=
  healthyPsi g.convolutionSquare

/-- The route-facing name expands to all three same-owner components. -/
theorem healthyPsi_components (F : CompactLogTest) :
    healthyPsi F =
      C1SameOwnerWeil.poleTerm F -
        C1SameOwnerWeil.archimedeanTerm F -
          C1SameOwnerWeil.finitePrimeSum F := by
  rfl

/-- The quadratic readout agrees with the owning implementation. -/
theorem healthyQw_eq_sameOwner (g : CompactLogTest) :
    healthyQw g = C1SameOwnerWeil.qw g := by
  rfl

end C1WeilExplicit
end Source
end ConnesWeilRH
