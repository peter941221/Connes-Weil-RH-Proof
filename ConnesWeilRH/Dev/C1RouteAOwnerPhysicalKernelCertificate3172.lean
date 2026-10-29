import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerPhysicalKernelCertificate3172

open C1G8R0OrbitGeometry
open C1SameOwnerWeil
open C1P2OrbitPhysicalProfileReadback
open C1P2SignedBudget
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

def routeAOwnerPhysicalKernelNodeValue
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) : Real :=
  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
    (orbitPhysicalKernel geometry (Real.log n) +
      orbitPhysicalKernel geometry (-Real.log n)).re

structure RouteAOwnerPhysicalKernelEnvelope
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  center : Nat → Real
  error : Nat → Real
  error_nonneg : ∀ n, 0 ≤ error n
  aggregate_upper :
    archimedeanTerm g.convolutionSquare +
        Finset.sum (orbitVisiblePrimeRange geometry)
          (fun n => center n + error n) ≤ 0
  enclosure :
    ∀ n ∈ orbitVisiblePrimeRange geometry,
      |routeAOwnerPhysicalKernelNodeValue geometry n - center n| ≤ error n

def RouteAOwnerPhysicalKernelEnvelope.nodeBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (envelope : RouteAOwnerPhysicalKernelEnvelope geometry) : Nat → Real :=
  fun n => envelope.center n + envelope.error n

theorem RouteAOwnerPhysicalKernelEnvelope.node_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (envelope : RouteAOwnerPhysicalKernelEnvelope geometry) :
    ∀ n ∈ orbitVisiblePrimeRange geometry,
      routeAOwnerPhysicalKernelNodeValue geometry n ≤
        envelope.nodeBound n := by
  intro n hn
  have h := envelope.enclosure n hn
  have hupper := (abs_le.mp h).2
  dsimp [RouteAOwnerPhysicalKernelEnvelope.nodeBound]
  linarith

def RouteAOwnerPhysicalKernelEnvelope.toCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (envelope : RouteAOwnerPhysicalKernelEnvelope geometry) :
    OrbitPhysicalKernelNodeCertificate geometry :=
  { nodeBound := envelope.nodeBound
    arch_bound := envelope.aggregate_upper
    node_bound := envelope.node_bound }

theorem orbitWindowSemiLocalGate_of_owner_physicalKernel_envelope
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (envelope : RouteAOwnerPhysicalKernelEnvelope geometry) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g :=
  orbitWindowSemiLocalGate_of_physicalKernel_certificate geometry
    envelope.toCertificate

end
end C1RouteAOwnerPhysicalKernelCertificate3172
end ConnesWeilRH.Source
