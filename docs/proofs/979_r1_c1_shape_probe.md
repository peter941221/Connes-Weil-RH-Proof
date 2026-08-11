# 979 — R1/C1 strategy-B shape probe: lock the object-layer re-type hypothesis

Status: execution record + forward contract.  RH NOT claimed.

## Goal (R1/C1 plan, strategy-B)
Before re-typing the shared `archimedeanSymbols` / `CC20TraceObjectPackage` onto the
CompactLog carrier (strategy-A, ~14-file blast), lock the ONE shape assumption the
whole C1 exit rests on:

> Can `ArchimedeanTraceSymbols` be instantiated with `Test := CompactLogTest` and
> `positiveTrace g := (ofCompactLogTest g).archimedeanTerm.re` so that the
> already-closed `compactLogArchimedean_bump_pos > 0` (Wall14CompactLogBridge)
> directly feeds `0 ≤ positiveTrace` at the concrete bump?

## Result — SHAPE IS LOCKED, axiom-clean
`Dev/R1ShapeProbe979.lean` (build 3206 jobs green, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry):

- `R1CompactArchimedeanSymbols` : a **local** `ArchimedeanTraceSymbols` with
  `Test := CompactLogTest`, `positiveTrace := R1CompactLogArch` (the archimedean
  real part), `supportSquareTrace`/`sourceNoDefectTrace` same.
- `R1_compact_shape_positive_pos_bump : 0 < positiveTrace bumpPlateauTest`
  (strict, directly from `compactLogArchimedean_bump_pos`).
- `R1_compact_shape_positive_nonneg_bump : 0 ≤ positiveTrace bumpPlateauTest`.

This proves the R1-1 formal shape is constructible on the CompactLog carrier, and
that today's Wall-A closure (`compactLogArchimedean_bump_pos`) is the required "real
正性 seed" — the positive real part is NOT 0, so the healthy SCB/Wall-A refutation
seed is nonzero on the compact carrier.

## What it deliberately did NOT do (honest scope)
- Did NOT touch shared `archimedeanSymbols` / `CC20TraceObjectPackage` (the real
  re-type is strategy-A / next step). `hilbertSchmidtGate`/`traceClass`/`cyclicLegal`
  are permissive `True` sockets here — their operator content is 914b/914c.
- Did NOT claim universal `0 ≤ positiveTrace g` for all compact tests (that would be
  an over-claim; `Re(arch g)` is not universally nonnegative). Only the bump-specific
  positivity seed is asserted.

## Lean gotcha this session
- `ArchimedeanTraceSymbols.Test : Type` is a structure field; to type-check a
  statement like `positiveTrace bumpPlateau`, the test-level `[abbrev]` (reducible)
  of the symbols **and** fully-qualified carrier types are needed. Inside the deep
  `Dev` namespace, unqualified `CompactLogTest`/`ArchimedeanTraceSymbols` resolve
  differently than in the isolated test; using `ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest`
  (fully qualified) sidesteps it.
- A doc-comment directly before a namespace `end` is a parse error ("expected
  'lemma'"); keep the README seam in the header `/-!`.

## Next (R1 proper)
- Phase-1 Step 2: attach the bump's explicit `arch > 0` through
  `positiveTraceNonnegative` / `hilbertSchmidtGate` (permissive socket → real gate via
  914b/914c operator content).
- Phase-1 Step 3: assemble `SourceRouteTraceData` at the bump
  (`λ`, transport, compatibility) → `FullWeilPositivity` witness → feed L1552
  C1→RH exit.
- The object-layer carrier re-type (`archimedeanSymbols.Test := CompactLogTest`) is
  now shape-verified; the actual multi-file re-type is the next finite act.