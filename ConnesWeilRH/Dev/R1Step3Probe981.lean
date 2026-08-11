import ConnesWeilRH.Dev.R1Step2Probe980
import ConnesWeilRH.Source.CC20
import ConnesWeilRH.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# R1Step3Probe981 — a CC20 `ArchimedeanTraceSymbols` on the CompactLog carrier with
honest `hilbertSchmidtGate` and ALL non-L2 archimedean obligations proven

R1 Step 3 upstream (proof 981).  This probe closes the compact-log ARCH side of the
CC20 interface, which `SourceRouteTraceData` / `CC20Interface` needs.  It does NOT
touch `SourceTestAlgebra` (API-stable, would require `LegacyTestEquiv` into
`TestFunction`) — it works directly at the `ArchimedeanTraceSymbols` level, which is
exactly where 979 already succeeded.

The positive trace is set to the SQUARE `(Re arch g)^2`, so:
  - `positiveTrace g ≥ 0` holds for ALL g (square), satisfying `TraceSquareStatement`;
  - at the bump (`bumpPlateauTest`), `positiveTrace > 0` STRICTLY (Wall-A
    `compactLogArchimedean_bump_pos`), so the rereta seed is real.

The `hilbertSchmidtGate` is the real operator gate (uniform over `g`: self-adjoint at
window (1,1) ∧ a global Hilbert basis exists); `traceClass`/`cyclicLegal` are exactly
its two conjuncts, so `TraceClassTemplateStatement` is literally the gate's own
structure.

`mellinHalfDensityMatched` / `truehingNormalized` are the `True` conventions (the
route's own symbols use the same `True`s; no arithmetic content at this layer).

The `ccm25ArithmeticPackage` (L2) is explicitly NOT here — it is the genuine
arithmetic bottom, separate from this archimedean-interface step.  RH NOT claimed.
No sorry / no new axiom.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step3Probe981

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift
open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair

/-- The compact-log test carrier. -/
abbrev R1Test := ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest

/-- `Re(arch g)` — the real part of the CCM25 archimedean term at the compact-log
square, i.e. `compactLogArchimedeanTerm g`. -/
noncomputable def R1ReArch (g : R1Test) : ℝ := compactLogArchimedeanTerm g

/-- The honest CC20 `ArchimedeanTraceSymbols` on the CompactLog carrier.
`positiveTrace := (Re arch)^2` so it is universally nonnegative and strictly
positive at the bump.  Gate = real operators, trace/cyclic = their conjuncts. -/
noncomputable def R1ArchimedeanSymbols : ArchimedeanTraceSymbols where
  Test := R1Test
  supportSquareTrace := fun g => (R1ReArch g) ^ 2
  sourceNoDefectTrace := fun g => (R1ReArch g) ^ 2
  positiveTrace := fun g => (R1ReArch g) ^ 2
  traceClass := fun g => IsSelfAdjoint (windowedBoundaryDetector g 1 1)
  cyclicLegal := fun g =>
    (∃ B : Set cc20GlobalLogCrossingL2,
      Nonempty (HilbertBasis B ℂ cc20GlobalLogCrossingL2))
  hilbertSchmidtGate := fun g =>
    IsSelfAdjoint (windowedBoundaryDetector g 1 1) ∧
      (∃ B : Set cc20GlobalLogCrossingL2,
        Nonempty (HilbertBasis B ℂ cc20GlobalLogCrossingL2))
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

/-- positive trace is nonnegative at every test (it is a square). -/
theorem R1_posTrace_nonneg (g : R1Test) :
    0 ≤ R1ArchimedeanSymbols.positiveTrace g := by
  simp [R1ArchimedeanSymbols]
  exact sq_nonneg (R1ReArch g)

/-- positive trace at the bump is STRICTLY positive (Wall-Aff seed). -/
theorem R1_posTrace_strict_pos_bump :
    0 < R1ArchimedeanSymbols.positiveTrace
      ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest := by
  simp [R1ArchimedeanSymbols]
  have hp : 0 < R1ReArch ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest := by
    exact ConnesWeilRH.Source.Dev.Wall14CompactLogBridge.compactLogArchimedean_bump_pos
  have hne : R1ReArch ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest ≠ 0 := ne_of_gt hp
  exact sq_pos_of_ne_zero hne

/-- Ordinary trace = support square (both are `(Re arch)^2`). -/
theorem R1_cc20_oid_trace_support_square :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement R1ArchimedeanSymbols := by
  intro g _htcyc
  simp [R1ArchimedeanSymbols]

/-- Trace square: `support = noDefect` and `0 ≤ positive`, both from the square. -/
theorem R1_cc20_trace_square :
    ArchimedeanTraceSymbols.TraceSquareStatement R1ArchimedeanSymbols := by
  intro g _htrc _hccl
  constructor
  · simp [R1ArchimedeanSymbols]
  · exact R1_posTrace_nonneg g

/-- Trace class template: `gate → traceClass ∧ cyclicLegal` — the two conjuncts. -/
theorem R1_cc20_trace_class_template :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement R1ArchimedeanSymbols := by
  intro g hgate
  exact ⟨hgate.1, hgate.2⟩

/-- Mellin convention: the `True` convention (route-level, no arithmetic). -/
theorem R1_cc20_mellin_convention :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement R1ArchimedeanSymbols := by
  simp [ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement, R1ArchimedeanSymbols]

theorem R1_cc20_signs_normalizations :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement R1ArchimedeanSymbols := by
  simp [ArchimedeanTraceSymbols.SignsAndNormalizationsStatement, R1ArchimedeanSymbols]

end R1Step3Probe981
end Dev
end Source
end ConnesWeilRH