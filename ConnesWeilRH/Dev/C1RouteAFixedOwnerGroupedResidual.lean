import ConnesWeilRH.Dev.C1P2DirectCoboundaryResidualReduction
import ConnesWeilRH.Dev.C1RouteASelectedOwnerResidualReadback

namespace ConnesWeilRH
namespace Source
namespace C1RouteAFixedOwnerGroupedResidual

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalKernelIntegrandBounds
open C1P2OrbitPhysicalKernelCoboundary
open C1P2DirectCoboundaryResidualReduction
open C1P2BilateralProfile
open C1LocalConfigurationDomination
open C1SameOwnerWeil

noncomputable section

/-! The fixed-owner reduction keeps the whole visible-prime aggregate grouped.
It is an equality, not a sign assumption. -/
theorem archimedean_plus_actualResidual_eq_ICgate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    archimedeanTerm g.convolutionSquare +
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          orbitPhysicalKernelCoboundaryResidual geometry t =
      ICgate g.convolutionSquare := by
  have hres :
      (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitPhysicalKernelCoboundaryResidual geometry t) =
        ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t := by
    simpa [physicalKernelWindowLeft, physicalKernelWindowRight] using
      (intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_actualResidual
        geometry).symm
  calc
    archimedeanTerm g.convolutionSquare +
          ∫ t in (physicalKernelWindowLeft geometry)..
            (physicalKernelWindowRight geometry),
            orbitPhysicalKernelCoboundaryResidual geometry t =
        archimedeanTerm g.convolutionSquare +
          ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
            (((geometry.orbitIndex + 2 : Nat) : Real)),
            orbitFinitePhysicalKernelIntegrand geometry t := by
      simpa [physicalKernelWindowLeft, physicalKernelWindowRight] using
        congrArg (fun x => archimedeanTerm g.convolutionSquare + x) hres
    _ = archimedeanTerm g.convolutionSquare +
          finitePrimeSum g.convolutionSquare := by
      rw [finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand geometry]
    _ = ICgate g.convolutionSquare := by
      rw [← p2AggregateValue_eq_ICgate_convolutionSquare]
      unfold p2AggregateValue
      rw [finitePrimeSum_eq_bilateralProfile_weighted_sum]

theorem strict_groupedResidual_iff_strict_ICgate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (archimedeanTerm g.convolutionSquare +
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          orbitPhysicalKernelCoboundaryResidual geometry t < 0) ↔
      ICgate g.convolutionSquare < 0 := by
  rw [archimedean_plus_actualResidual_eq_ICgate geometry]

end
end C1RouteAFixedOwnerGroupedResidual
end Source
end ConnesWeilRH
