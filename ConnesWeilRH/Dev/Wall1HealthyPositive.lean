/-
Wiring the closed strict-positive diagonal onto the concrete healthy test.

Dev/Wall1GlobalConvNonzero.lean proves the strict positive diagonal for ANY
nonzero Schwartz kernel h on the global log-carrier.  This module instantiates
it at the concrete nonzero test the A3 healthy HS gate already carries
(nonzeroTest = unit Fourier-core bump), so the "non-empty producer" for
fullWeilPositivity has a concrete, verified, strictly-positive diagonal.

RH not claimed: producer instantiation only.
-/
import ConnesWeilRH.Dev.Wall1GlobalConvNonzero
import ConnesWeilRH.Dev.A3NonzeroCompactLogGateProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall1HealthyPositive

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open A3NonzeroCompactLogGateProbe
open CCM25Concrete.CompactLogConvolution

/-- Strict positive diagonal on the healthy log-carrier at the concrete
nonzero test. -/
theorem healthy_strict_positive_diagonal :
    ∃ u : CC20Concrete.cc20GlobalLogCrossingL2,
      0 < (⟪u, CC20Concrete.cc20GlobalConvolutionPositive nonzeroTest.test u⟫_ℂ).re :=
  CC20Concrete.cc20GlobalConvolutionPositive_strict_diagonal
    nonzeroTest.test nonzeroTest_test_ne_zero

end Wall1HealthyPositive
end Dev
end Source
end ConnesWeilRH
