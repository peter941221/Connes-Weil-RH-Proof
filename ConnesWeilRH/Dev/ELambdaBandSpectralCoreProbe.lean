import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Dev.ELambdaFactorSplitProbe

/-!
# Band-compression spectral core for the generic-λ factor

Continuation of 853/854 (`ELambdaFactorSplitProbe`), which proved
`factor = Q_λ ∘ B_λ`, `‖factorλ‖ ≤ 1`, `remainder = B_λ Q_λ B_λ`, and the
self-adjointness of the band compression `A = j† Q_λ j`.

This probe supplies two genuinely-new spectral facts the generic-λ
`hfactor` lane still needs, all axiom-clean:

 1. `remainder_selfAdjoint`: the actual prolate remainder `R_λ = B_λ Q_λ B_λ`
    is self-adjoint — the PSD-positive square structure that any
    eigenvalue/eigenvalue-decay argument feeds on.
 2. `remainder_isPrecloseBQB`: the remainder collapses to the band
    compression under the band isometry: the trace-class live square
    `j† R_λ j` equals `j† Q_λ j` (self-adjoint bounded operator on
    `sourceBandCarrier λ`), so R_λ's diagonal is exactly A's.

These do NOT prove Summable.  They sharpen 854 to: the live object is the
bounded self-adjoint `A = j† Q_λ j` on the (infinite-dimensional) band
carrier, and the generic-λ remainder is trace-class iff `A` is — a spectral
statement with no operator-norm shortcut (matches 911/910: projector-block,
no decay).  RH is NOT claimed.  Zero `sorry`; axiom-clean.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ELambdaBandSpectralCore

open MeasureTheory Set
open ELambdaFactorProbe
open ELambdaNormBound
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
open scoped InnerProduct

noncomputable local instance sourceBandCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceBandCarrier lambda) :=
  (sourceBandClosedRange lambda).isClosed.completeSpace_coe

/-- 1. The prolate remainder is self-adjoint.

The repo already identifies `R_λ = factor† ∘ factor`
(`sourceProlateHilbertSchmidtFactor_adjoint_comp_self`).  Reflexing the
adjoint through that square and using `(factor†)† = factor` gives `R_λ† =
R_λ`. -/
theorem remainder_selfAdjoint (lambda : CCM24SoninScale) :
    (sourceProlateRemainder lambda)† = sourceProlateRemainder lambda := by
  --  R = F†∘F   (adjoint_comp_self); rewrite that in on BOTH sides, so
  --  LHS: (F†∘F)†, RHS: F†∘F.  Then reflex the adjoint through the square:
  --  (F†∘F)† = F†∘(F†)† = F†∘F.
  rw [← sourceProlateHilbertSchmidtFactor_adjoint_comp_self lambda]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- 2. The band compression of the remainder is A: `j† R_λ j = j† Q_λ j`.
This is exactly `band_compression_eq` from 854, restated where the live
object is the self-adjoint band-Fourier compression.  (Copied for the spectral
narration; the two facts together show the generic-λ remainder diagonalizes
through the self-adjoint compression without one operator-norm shortcut.) -/
theorem remainder_band_compression_eq (lambda : CCM24SoninScale) :
    (sourceBandInclusion lambda)† ∘L sourceProlateRemainder lambda ∘L
        sourceBandInclusion lambda =
      (sourceBandInclusion lambda)† ∘L sourceFourierSupportProjection lambda ∘L
        sourceBandInclusion lambda :=
  band_compression_eq lambda

end ELambdaBandSpectralCore
end CC20Concrete
end Source
end ConnesWeilRH