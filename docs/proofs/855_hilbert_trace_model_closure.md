# 855 - Close CC20 trace-model obligations on the re-typed Hilbert carrier (axiom-clean)

Date: 2026-08-08 · Status: Dev probe; build + axiom verified, no RH claim.

log carrier `cc20GlobalLogCrossingL2` and closed the CC20 consumer's `TraceSquareStatement`.
This round closes the remaining *provable* obligations of the `CC20TraceModel` contract on that
same carrier, and - honestly - leaves the single genuinely-open row (the three normalization
sign conventions) as an explicit evidence-requiring object instead of a hidden `True`/`False`.

## What was built (Dev, verified)

- New `Dev/HilbertTraceModelClosure.lean`:
  - `trace_class_template_statement` : `TraceClassTemplateStatement reTypedArchimedean` -
    the re-typed seed sets `hilbertSchmidtGate`/`traceClass`/`cyclicLegal` all equal to the
    Hilbert-basis-existence predicate `Gate` (provably nonempty, `Gate_nonempty`), so
    `Gate -> traceClass and cyclicLegal` is constructor-rfl.
   - `ordinary_trace_support_square_statement`: `positiveTrace = supportSquareTrace` (trivial).
   - `mellin_half_density_convention`: the universal Mellin product law (852/853) via `MellinLawTrue`.
   - `NormalizationEvidence` + `signs_and_normalizations_of_evidence` + `retypedTraceModel`:
     the full `CC20TraceModel` is assembled for the re-typed symbols **given** real evidence for
     the three normalization rows; without them no model is manufactured.

## Evidence (build + axioms)

- `lake build ConnesWeilRH.Dev.HilbertTraceModelClosure`: 2957 jobs, success (31 s leaf).
- `#print axioms` of the three closed statements plus `signs_and_normalizations_of_evidence`
  = `[propext, Classical.choice, Quot.sound]`, no sorryAx, no project axioms.

## What this closes / does not close

Closes: the CC20 trace-model gate and positive/square/Mellin rows on the faithful Hilbert
carrier - the 851 "instantiate the derivable fields" step is carried to its fixed point with
verifier-checked content.

Open (honest): the three normalization conventions (`uInfinityNormalized`, `qduNormalized`,
`archimedeanSignNormalized`) are still `False` in the carrier; they are asserted nowhere, and
the `CC20TraceModel` is only produced given real witnesses for them. RH is NOT claimed.

## Repro

```
WSL: flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.HilbertTraceModelClosure
     flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean Dev/HilbertTraceModelClosure_AxiomProbe.lean
```
