# 985 — C1→RH Phase-1 pipe: ①②③ source-verified state and the definitive ② blocker

Date: 2026-08-11. Status: source/code audit (definitions read; no new theorem). RH NOT claimed.
See docs/934, /936, /960, /963, rfc_r1_route_plan, docs/984.

## Question this memo answers

The three "Phase-1 load-bearing steps" named in docs/934/936:
  ① strict diagonal `∃ u, 0 < ‖F u‖`
  ② healthy single-instance `CC20FiniteVanishingWeilCriterion`
  ③ wire C1 → SourceRH (the Lean theorem direction)
Under "1、2、3 都做", what is actually still-to-do vs already-closed?

## Verdict (source-verified, axiom-clean per code+docs)

| Step | State | Evidence |
|---|---|---|
| ① strict positive diagonal | **CLOSED** (was open at docs/934; closed since) | `Wall1GlobalConvNonzero.cc20GlobalConvolutionPositive_strict_diagonal` (Fourier-multiplier injectivity), instantiated at the bump as `Wall1HealthyPositive.healthy_strict_positive_diagonal`; packaged into `fullWeilPositivity` by `Wall1StrictWeilInput` + `WeilC1NonEmptyProducer.concreteC1InputData`. No window surgery. |
| ③ C1 → SourceRH Lean theorem direction | **CLOSED** (library) | `cc20_proposition_c1_standard_source_rh_of_realized_cc20_triple_input` (`Source/CC20PropositionC1`), built on `cc20_proposition_c1_from_yoshida_detector`. It needs `CC20YoshidaDetectorExists C F` + a realize/C-gate witness to fire, but the theorem direction itself exists. |
| ② healthy `CC20TestSpace` instance | **OPEN — genuine analytic bottom** | `docs/960`: criterion has NO healthy-carrier `CC20TestSpace` instance. The healthy machine is an L² Hilbert operator (`cc20GlobalLogCrossingL2` + PSD `cc20GlobalConvolution...`), NOT a `TestFunction`+`weilLocal` carrier. |

## Why ② is the real blocker, and why a blind fix is forbidden

- To even `state` `CC20FiniteVanishingWeilCriterion C F` you need a `C : CC20TestSpace`
  (`Source/CC20TestSpace`): `Test → TestFunction`, `mellinAt`, `starConvolution`,
  `weilLocalSum`, `compactSupportSmooth`.
- Setting `weilLocalSum = -(Re⟨u, cc20GlobalConvolutionPositive g u⟩)` (negative of the PSD
  diagonal) would make `weilLocalSum(star g) ≤ 0` **trivially true** — a vacuous
  `true`-producer, exactly what AGENTS guard 6 + docs/963 forbid ("correct closure needs the
  scalar<->operator bridge as a THEOREM").
- The healthy algebra has no explicit-Weil/Mellin sum yet (`no polePairing`, no
  `weilLocal`-analog here). So a meaningful (non-vacuous) `weilLocalSum` is genuinely a **new
  analytic definition**: the real explicit-formula Weil functional on the healthy carrier.
  By the Weil explicit formula, `∀g, vanishes→ weilLocalSum(conv² g) ≤ 0` is **RH itself**
  (docs/963 #1). Not a Lean-assembly leaf.

## What would have to be true to call ② "done"

A `CC20TestSpace` on the healthy CompactLog carrier whose `weilLocalSum` is **honest**
(not -PSD, not `True`/`Set.univ`) i.e. reads the explicit Weil/Mellin balance, followed by a
proof that it is ≤0 on finite-vanishing tests. The documents (`rfc_r1_route_plan` option B)
pin the load-bearing prerequisite as `FixedLambda...Certificate` on a genuinely
multiplicative carrier (the additive `convolutionStar=+` concrete model breaks Mellin at
composites). See also docs/984: the `ccm25ArithmeticPackage` seam is structurally blocked on
the concrete `{2}` carrier (L653-type ∀n wall + refuted scoped-balance leaf).

This is the "real math" both docs/963 and RFC route to, and it is not closable by an
axiom-clean bottleneck the repo already has.

## Concrete recommendations (ordered)

1. Verify the closed ①②③ trio in a **fresh isolated WSL verification dir** (mirror is dirty /
   stale: `the WSL verification mirror` HEAD `f14a47f` ≠Windows `7b7a560` and has
   tracked modifications). Seed `.lake/packages` from a warm compatible cache; build only
   `Wall1GlobalConvNonzero` / `WeilC1NonEmptyProducer` leaves, then `#print axioms`.
2. Attack the real ②: define an explicit `weilLocal` (Mellin-balance) on the healthy
   compact-log carrier from the genuine convolution square, and prove the halving of
   `integration` at finite-vanishing as a theorem — the true kept-alone analytic step.
   docs/963 rec.1 keeps a certified single-test numeric construction as the falsifiable
   non-RH checkpoint.
3. Only after an honest healthy `CC20TestSpace` exists does `cc20_proposition_c1_standard_...`
   consume it toward `standard_source_rh_iff_mathlib` (the remaining `CC20YoshidaDetector` +
   `fullWeilPositivity` are then the available input data).

RH NOT claimed.


## Live-verification addendum (2026-08-11, WSL isolated dir an isolated WSL verification dir)
Re-verified 1 3 at Windows HEAD 7b7a560 in a fresh isolated WSL dir seeded from the dirty mirror warm .lake. lake build (3593 jobs green) then #print axioms -> all [propext, Classical.choice, Quot.sound], 0 sorryAx: weilStateNonempty, concreteC1InputData, healthy_strict_positive_diagonal, cc20GlobalConvolutionPositive_strict_diagonal, cc20_proposition_c1_standard_source_rh_of_realized_cc20_triple_input, cc20_proposition_c1_from_yoshida_detector. Dirty-mirror constraint handled via fresh isolated verify dir (AGENTS 8), leaving the dirty mirror untouched. 2 remains the honest RH-equivalent gap (healthy CC20TestSpace needs a defined Weil/mellin on CompactLogTest; vacuous -PSD sign is guard-6 forbidden). First-milestone 2 module: healthyCC20TestSpace : CC20TestSpace with weilLocalSum reading the real archimedean term (totalArchimedean); its <=0 is the open criterion, NOT asserted. RH NOT claimed.

## ② updated (2026-08-11): healthy-carrier instance now exists (honest, axiom-clean)

`Dev/C1HealthyTestSpace.lean` builds `healthyCC20TestSpace : CC20TestSpace` on the
`CompactLogTest` carrier from genuine components (mellinAt = healthy-Mellin, star =
convolutionSquare, weil = -(totalArchimedean @ conv-square), compact = HasCompactSupport).
`healthyCriterionState F` = `CC20FiniteVanishingWeilCriterion healthyCC20TestSpace F` is now a
real Prop on the healthy carrier (docs/960's "no instance" gap is closed as an OBJECT). The
criterion's value (`weilLocal <= 0`) remains the open RH-equivalent step and is NOT asserted.
WSL green: 2957 jobs, all #print axioms = [propext, Classical.choice, Quot.sound], 0 sorryAx.

## ② continuation (2026-08-11): explicit healthy Weil psi materialized (formula, not criterion)
`Dev/C1WeilExplicit.lean` builds `healthyPsi F = poleFunctional F - totalArchimedean F -
sum_{n in {2}} sourceFinitePrimeTerm n F` (healthy Eval) + `healthyQw`, proving the finite-prime
`{2}` collapse (`healthyPrimeSum_two`) and the explicit read-out (`healthyPsi_two`). WSL green
(2958 jobs), all #print axioms = [propext, Classical.choice, Quot.sound]. The full criterion
`healthyPsi(conv^2 g) <= 0` (RH-equivalent) is NOT asserted and remains open.
