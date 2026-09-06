import ConnesWeilRH.Dev.C1BombieriP2Bridge

namespace ConnesWeilRH.Source.C1BombieriP2Bridge

open C1BombieriFiniteQuadraticBridge
open C1BombieriSection7Gamma
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution

noncomputable section

noncomputable def probe_of_bombieriP2BridgeData
    {g : CompactLogTest} (p : BombieriP2BridgeData g) :
    BombieriQuadraticP2BridgeData g := by
  refine
    { n := p.n, t := p.t, ht := p.ht, gamma := p.gamma, z := p.z
      qw_eq_quadratic := ?_ }
  obtain hform := lambda_mass_eq_bombieriHMatrix_quadraticForm
    p.t p.gamma p.z p.Lam p.lam p.heigen p.hrecip
  have hreal := congrArg Complex.re hform
  rw [p.qw_eq_mass]
  simpa [Complex.mul_re] using hreal

end
end ConnesWeilRH.Source.C1BombieriP2Bridge
