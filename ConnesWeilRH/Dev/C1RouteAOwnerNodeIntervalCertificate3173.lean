import ConnesWeilRH.Dev.C1RouteAOwnerPhysicalKernelCertificate3172

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerNodeIntervalCertificate3173

open C1G8R0OrbitGeometry
open C1RouteAOwnerPhysicalKernelCertificate3172
open C1P2OrbitPhysicalProfileReadback
open C1P2SignedBudget
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

structure RouteAOwnerNodeIntervalCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  lower : Nat → Real
  upper : Nat → Real
  lower_le_upper : ∀ n ∈ orbitVisiblePrimeRange geometry, lower n ≤ upper n
  node_lower : ∀ n ∈ orbitVisiblePrimeRange geometry,
    lower n ≤ routeAOwnerPhysicalKernelNodeValue geometry n
  node_upper : ∀ n ∈ orbitVisiblePrimeRange geometry,
    routeAOwnerPhysicalKernelNodeValue geometry n ≤ upper n
  aggregate_upper :
    archimedeanTerm g.convolutionSquare +
        Finset.sum (orbitVisiblePrimeRange geometry) upper ≤ 0

def RouteAOwnerNodeIntervalCertificate.center
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) : Nat → Real :=
  fun n => (certificate.lower n + certificate.upper n) / 2

def RouteAOwnerNodeIntervalCertificate.error
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) : Nat → Real :=
  fun n => max 0 ((certificate.upper n - certificate.lower n) / 2)

theorem RouteAOwnerNodeIntervalCertificate.error_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) :
    ∀ n, 0 ≤ certificate.error n := by
  intro n
  exact le_max_left _ _

theorem RouteAOwnerNodeIntervalCertificate.enclosure
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) :
    ∀ n ∈ orbitVisiblePrimeRange geometry,
      |routeAOwnerPhysicalKernelNodeValue geometry n - certificate.center n| ≤
        certificate.error n := by
  intro n hn
  have hlow := certificate.node_lower n hn
  have hupp := certificate.node_upper n hn
  have hwidth : 0 ≤ (certificate.upper n - certificate.lower n) / 2 := by
    linarith [certificate.lower_le_upper n hn]
  dsimp [RouteAOwnerNodeIntervalCertificate.center,
    RouteAOwnerNodeIntervalCertificate.error]
  rw [max_eq_right hwidth]
  rw [abs_le]
  constructor <;> linarith

def RouteAOwnerNodeIntervalCertificate.toEnvelope
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) :
    RouteAOwnerPhysicalKernelEnvelope geometry :=
  { center := certificate.center
    error := certificate.error
    error_nonneg := certificate.error_nonneg
    aggregate_upper := by
      have hsum :
          Finset.sum (orbitVisiblePrimeRange geometry)
              (fun n =>
                certificate.center n + certificate.error n) =
            Finset.sum (orbitVisiblePrimeRange geometry) certificate.upper := by
        apply Finset.sum_congr rfl
        intro n hn
        have hwidth : 0 ≤ (certificate.upper n - certificate.lower n) / 2 := by
          linarith [certificate.lower_le_upper n hn]
        dsimp [RouteAOwnerNodeIntervalCertificate.center,
          RouteAOwnerNodeIntervalCertificate.error]
        rw [max_eq_right hwidth]
        ring
      rw [hsum]
      exact certificate.aggregate_upper
    enclosure := certificate.enclosure }

theorem orbitWindowSemiLocalGate_of_owner_node_interval_certificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (certificate : RouteAOwnerNodeIntervalCertificate geometry) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g :=
  orbitWindowSemiLocalGate_of_owner_physicalKernel_envelope geometry
    certificate.toEnvelope

end
end C1RouteAOwnerNodeIntervalCertificate3173
end ConnesWeilRH.Source
