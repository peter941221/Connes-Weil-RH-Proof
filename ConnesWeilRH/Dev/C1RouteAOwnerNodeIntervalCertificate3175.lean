import ConnesWeilRH.Dev.C1RouteAOwnerNodeIntervalCertificate3173
import ConnesWeilRH.Dev.C1RouteAFixedOwnerGroupedResidual

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerNodeIntervalCertificate3175

open C1G8R0OrbitGeometry
open C1LocalConfigurationDomination
open C1RouteAFixedOwnerGroupedResidual
open C1RouteAOwnerNodeIntervalCertificate3173
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- A genuine same-owner node interval certificate is exactly a contradiction
under the hypothetical right-hand off-line zero.  The theorem is a guard for
the producer boundary: it does not construct the certificate or assert that a
right-hand zero exists. -/
theorem no_owner_node_interval_certificate_of_right_off_line_zero
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ¬ Nonempty (RouteAOwnerNodeIntervalCertificate geometry) := by
  rintro ⟨certificate⟩
  have hgate :=
    orbitWindowSemiLocalGate_of_owner_node_interval_certificate geometry certificate
  have hnonpos : ICgate g.convolutionSquare ≤ 0 := by
    exact hgate
  have hpositive := ICgate_pos_of_healthyOrbitGeometry geometry hoff hright
  linarith

end
end C1RouteAOwnerNodeIntervalCertificate3175
end ConnesWeilRH.Source
