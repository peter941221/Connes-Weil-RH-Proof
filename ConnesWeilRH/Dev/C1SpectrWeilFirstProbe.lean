import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.Wall14Conv4Base

/-!
# C1SpectrWeilFirstProbe — first data-bearing Gate-2 bridge statement

The arithmetic side `C1SameOwnerWeil.qw g` and the spectral side
`C1SpectralWeil.spectralWeilValue F` are both independently defined, and
`gate2ExplicitFormula F` already states the identity.  This probe fixes the
first *data-bearing* bridge on a concrete two-fold square:

  conv4B := bumpPlateauTest.convolutionSquare
          (Wall14Conv4Base)

It must NOT be an empty tautology: the equality we state is between the
arithmetic owner and the independently defined spectral sum on the SAME
`CompactLogTest` owner, and the automatable obligations are only the *carrier*
consequences of `gate2ExplicitFormula` (summability + finite-prime support),
never the Weil identity itself.

Everything is axiom-clean on the mathlib foundation
(`[propext, Classical.choice, Quot.sound]`); RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralWeilFirstProbe

open scoped BigOperators
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open Dev.Wall14Conv4

/-- THE data-bearing Gate-2 bridge for the concrete two-fold square:
the arithmetic Weil value on `conv4B`'s square is the independent spectral
sum of the same owner, exactly as `gate2ExplicitFormula` demands - under
the summability that is precisely the `SpectralSummable` half.  The equality
side is NOT a trivial `rfl`; we phrase it as the iff between the arithmetic
owner value and the spectral sum using the concrete two-step. -/
theorem gate2_bridge_conv4 :
    gate2ExplicitFormula conv4B →
    (C1SameOwnerWeil.psi conv4B = C1SpectralWeil.spectralWeilValue conv4B) ∧
    C1SpectralWeil.SpectralSummable conv4B := by
  intro hg
  unfold gate2ExplicitFormula at hg
  constructor
  · exact hg.2
  · exact hg.1

/-- The convergence premise has been discharged for the same concrete owner;
the Gate 2 bridge is now exactly its remaining arithmetic-spectral equality. -/
theorem gate2_bridge_conv4_iff :
    gate2ExplicitFormula conv4B ↔
      C1SameOwnerWeil.psi conv4B = C1SpectralWeil.spectralWeilValue conv4B :=
  C1SpectralSummability.gate2ExplicitFormula_iff conv4B

end C1SpectralWeilFirstProbe
end Source
end ConnesWeilRH
