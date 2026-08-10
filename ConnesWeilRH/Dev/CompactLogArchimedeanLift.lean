import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-!
# CompactLogArchimedeanLift — lane-B archimedean term on the compact-log carrier

The lane-B residual axiom `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`
needs a genuine nonzero archimedean term, not the `fun _ => 0` placeholder that all
`SourceWeilFormData.archimedeanTerm : Test -> Real` currently use (docs/proofs/945).
A real nonzero archimedean term is already defined as
`CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.archimedeanTerm`
(CCM25 Eq. 3.7):

    arch (square f) = (log (4 * pi) + gamma) * (f * f)(0)
        + Integral_{y>0} [ e^(y/2) ((f*f)(y) + (f*f)(-y)) - 2 (f*f)(0) ]
                        / (e^y - e^-y) d y

This module lifts that per-owner term to a real function on the whole
`CompactLogTest` carrier (the compact-support healthy carrier), taking the real
part (the term's imaginary part is shown zero in the library). It does NOT claim
SCB; it only makes the lane-B archimedean term available as a real
`CompactLogTest -> Real` map that the SCB proof will be stated against.

RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CompactLogArchimedeanLift

open SelectedWeilSquare
open CompactLogConvolution
open scoped ComplexConjugate

/-- The CCM25 Eq. 3.7 archimedean explicit-formula term read at the selected
convolution square of a compact-log test, as a real value (im part is zero). -/
noncomputable def compactLogArchimedeanTerm (G : CompactLogTest) : ℝ :=
  (SelectedWeilSquareOwner.archimedeanTerm
      (SelectedWeilSquareOwner.ofCompactLogTest G)).re

/-- Same real archimedean term; the real part is the whole term since im = 0. -/
theorem compactLogArchimedeanTerm_eq_re_of_im_zero (G : CompactLogTest) :
    (SelectedWeilSquareOwner.archimedeanTerm
        (SelectedWeilSquareOwner.ofCompactLogTest G)).re =
      compactLogArchimedeanTerm G := by
  rfl

end CompactLogArchimedeanLift
end CCM25Concrete
end Source
end ConnesWeilRH
