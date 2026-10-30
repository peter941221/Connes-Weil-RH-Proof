import ConnesWeilRH.Dev.C1RouteAOwnerNodeIntervalCertificate3173

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerSignedTailBridge3191

open C1G8R0OrbitGeometry
open C1RouteAOwnerNodeIntervalCertificate3173
open C1RouteAOwnerPhysicalKernelCertificate3172
open C1P2OrbitPhysicalProfileReadback
open C1P2SignedBudget
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/--
An owner-preserving decomposition of the signed full-line budget.

The finite-window and tail numbers are not accepted independently: the
`decomposition` field must identify their sum with the aggregate over the
same `geometry` and the same node upper bounds.  This is the fail-closed
boundary between an external tail calculation and the Route A producer
certificate.
-/
structure RouteAOwnerSignedTailCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  lower : Nat → Real
  upper : Nat → Real
  finite_window_upper : Real
  full_line_tail_upper : Real
  lower_le_upper : ∀ n ∈ orbitVisiblePrimeRange geometry, lower n ≤ upper n
  node_lower : ∀ n ∈ orbitVisiblePrimeRange geometry,
    lower n ≤ routeAOwnerPhysicalKernelNodeValue geometry n
  node_upper : ∀ n ∈ orbitVisiblePrimeRange geometry,
    routeAOwnerPhysicalKernelNodeValue geometry n ≤ upper n
  decomposition :
    archimedeanTerm g.convolutionSquare +
        Finset.sum (orbitVisiblePrimeRange geometry) upper =
      finite_window_upper + full_line_tail_upper
  combined_upper : finite_window_upper + full_line_tail_upper ≤ 0

def RouteAOwnerSignedTailCertificate.toNodeInterval
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerSignedTailCertificate geometry) :
    RouteAOwnerNodeIntervalCertificate geometry :=
  { lower := certificate.lower
    upper := certificate.upper
    lower_le_upper := certificate.lower_le_upper
    node_lower := certificate.node_lower
    node_upper := certificate.node_upper
    aggregate_upper := by
      rw [certificate.decomposition]
      exact certificate.combined_upper }

def RouteAOwnerSignedTailCertificate.toPhysicalKernelEnvelope
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerSignedTailCertificate geometry) :
    RouteAOwnerPhysicalKernelEnvelope geometry :=
  certificate.toNodeInterval.toEnvelope

theorem orbitWindowSemiLocalGate_of_owner_signed_tail_certificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (certificate : RouteAOwnerSignedTailCertificate geometry) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g :=
  orbitWindowSemiLocalGate_of_owner_node_interval_certificate geometry
    certificate.toNodeInterval

end
end C1RouteAOwnerSignedTailBridge3191
end ConnesWeilRH.Source
