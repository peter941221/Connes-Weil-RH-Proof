import ConnesWeilRH.Basic
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.Wall14CompactLogBridge

/-!
# R1ShapeProbe979 — lock the R1-1 object-layer shape hypothesis, standalone

Strategy-B probe for the R1/C1 plan.  Before re-typing the shared
`archimedeanSymbols`/`CC20TraceObjectPackage` to the CompactLog carrier, this probe
tests the ONE shape assumption everything downstream depends on: can
`ArchimedeanTraceSymbols` be instantiated with `Test := CompactLogTest` and
`positiveTrace g := (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanTerm.re`
so that the already-closed `compactLogArchimedean_bump_pos > 0` (Wall14CompactLogBridge)
directly feeds `positiveTraceNonnegative (0 ≤ …)` at the concrete bump?

It deliberately does NOT touch the shared `archimedeanSymbols` / `CC20TraceObjectPackage`
definitions (those are the 14-file re-type that strategy-A would do).  It only builds a
LOCAL `ArchimedeanTraceSymbols` copy on the CompactLog carrier and locks the shape.

Honest scope: `traceClass`/`cyclicLegal`/`hilbertSchmidtGate` on this local copy are
left permissive True sockets (the operator-level content lives in 914b/914c).  This
probe pins only the SHAPE (that a CompactLog-carriered archimedean symbols exists and
the positive real-part feeds `0 ≤ …`), not the full gate.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev

open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift

/-- A helper: the real part of the archimedean term at the compact-log square. -/
noncomputable abbrev R1CompactLogArch
    (g : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest) : ℝ :=
  (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanTerm.re

/-- The R1 object-layer shape: an `ArchimedeanTraceSymbols` whose test carrier is the
compact-log test type and whose positive-trace is the real part of the archimedean
term.  `traceClass`/`cyclicLegal`/`hilbertSchmidtGate` are left `[irreducible]` as
permissive True sockets — this probe tests only the SHAPE (that a CompactLog-carriered
archimedean symbols exists and the positive real-part feeds `0 ≠ …`), not the full
gate.  Made an `abbrev` so `Test` is reducible to `CompactLogTest`. -/
noncomputable abbrev R1CompactArchimedeanSymbols : ArchimedeanTraceSymbols where
  Test := ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest
  supportSquareTrace := fun g => R1CompactLogArch g
  sourceNoDefectTrace := fun g => R1CompactLogArch g
  positiveTrace := fun g => R1CompactLogArch g
  traceClass := fun _ => True
  cyclicLegal := fun _ => True
  hilbertSchmidtGate := fun _ => True
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

/-- KEY: on the concrete bump, `positiveTrace bumpPlateauTest > 0`, so
`0 ≤ positiveTrace` holds and the R1 positive-nonnegative shape is closed. -/
theorem R1_compact_shape_positive_nonneg_bump :
    0 ≤ R1CompactArchimedeanSymbols.positiveTrace
      ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest := by
  unfold R1CompactArchimedeanSymbols R1CompactLogArch
  exact le_of_lt ConnesWeilRH.Source.Dev.Wall14CompactLogBridge.compactLogArchimedean_bump_pos

/-- Under the `hilbertSchmidtGate` hypothesis the route's `positiveTraceNonnegative`
signature demands, the same holds. -/
theorem R1_compact_shape_positive_nonneg_of_gate :
    let g := ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest
    0 ≤ R1CompactArchimedeanSymbols.positiveTrace g := by
  exact R1_compact_shape_positive_nonneg_bump

/-- The strict real part form (mirror of the route's `arch(>0)`). -/
theorem R1_compact_shape_positive_pos_bump :
    0 < R1CompactArchimedeanSymbols.positiveTrace
      ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest := by
  unfold R1CompactArchimedeanSymbols R1CompactLogArch
  exact ConnesWeilRH.Source.Dev.Wall14CompactLogBridge.compactLogArchimedean_bump_pos

end Dev
end Source
end ConnesWeilRH