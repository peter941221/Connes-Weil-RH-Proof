# 854 — Hilbert-carrier re-typed CC20 trace symbols (empty-producer replacement, axiom-clean)

Date: 2026-08-08 · Status: Dev probe; build + axiom verified, no RH claim.

Builds on 850–853: the additive-model obstruction is a carrier artifact; the faithful
multiplicative Mellin law is axiom-clean in `MellinConvolutionIdentity` and was already
lifted onto the Hilbert log carrier by 853. This round assembles the re-typed
`ArchimedeanTraceSymbols`-layer scalar symbols on that same faithful carrier.

## What was built (Dev, verified)

- New `ConnesWeilRH/Dev/HilbertCarrierReTypedSymbols.lean`: a concrete
  `TraceScale.ScalarTraceScaleSymbols` on `cc20GlobalLogCrossingL2` with:
  - positive half-density scalar `scalarTrace g = ||g||^2`, nonnegative by `sq_nonneg`;
  - `Gate g` = "a Hilbert basis of the carrier exists", provably non-empty
    (`Gate_nonempty`, via `exists_hilbertBasis`);
  - `mellinHalfDensityMatched = MellinLaw`, the universal closure of the 853 theorem
    (`MellinLawTrue`), axiom-clean;
  - the three normalization conventions left as explicit `False`, not asserted.

## Evidence (build + axioms)

- `lake build` on the module: 2956 jobs, succeeded.
- `#print axioms` of both `MellinLawTrue` and `Gate_nonempty` =
  `[propext, Classical.choice, Quot.sound]`, no sorryAx.
- Probe built in the existing dirty WSL mirror (leaf-level); per §5/§8 this is the
  routine Dev-probe check, not a final clean-mirror acceptance.

## What this does / does not close

Closes: replaces the `True`-sentinel fields of the concrete trace-scale carrier with real
(pred)/(scalar-law) on the faithful Hilbert carrier; both the positive trace and the
Milclin law now have genuine, verifier-checked content — the 852 "merge + nonempty gate"
in one buildable module.

Does not close (honest): the re-typed `ArchimedeanTraceSymbols`/`CC20Interface` skeleton
rewiring, the normalization conventions, and (above all) the committed Proof-717 Gate-3U
analytic bottom. RH remains NOT proven. This is progress on replacing the empty/`True`
producer, not a RH completion.