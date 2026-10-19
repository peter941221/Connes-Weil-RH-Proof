# Project memory

## 2026-10-19 Route B theta rectangle bridge

- Added `ConnesWeilRH/Dev/C1RouteBThetaSharpToCoarse2997.lean`.
- The theorem `routeBThetaTSharperMemCoarse2997` transports the tightened
  theta rectangle from record 2996 into the coarse rectangle consumed by the
  existing Route B argument chain.
- WSL check passed with `lake env lean`; no error output and exit status 0.
- This is an interface bridge only. It does not yet prove the independent
  exponential rectangle or the global Route B contradiction.

## 2026-10-19 Route B coordinate boundary

- Added `C1RouteBThetaSharpCoordinates2998.lean`.
- `routeBThetaTSharperCoordinates2998` exposes the 2996 complex rectangle as
  four rational real-coordinate inequalities for the quotient proof.
- WSL Lean check passed with exit status 0.

## 2026-10-19 Route B dependency diagnosis

- Record 3000 shows the independent `x,y` box from 2998 fails the committed
  doubled-argument target at its corners.
- The next proof must preserve the shared theta correlation; do not use
  corner-based `nlinarith` bounds or silently widen the target rectangle.

- Added `C1RouteBThetaSharpCircle2999.lean`; the Lean theorem
  `routeBThetaTSharperCircle2999` exports the exact constraint
  `x^2 + y^2 = 1/400` for the sharp theta coordinates. WSL Lean passed.

- Added `C1RouteBThetaQuotientCircleReduction3001.lean`. Under the circle
  constraint it proves the exact reductions `N.re = (399/100)x`,
  `N.im = (401/100)y`, and `D = (401/400)^2 - 4x^2`. WSL Lean passed.

- Added `C1RouteBThetaRealQuotientBounds3002.lean` and
  `C1RouteBThetaImagQuotientBounds3003.lean`; both target coordinate bounds
  pass under the circle constraint and positive denominator.
- Added `C1RouteBThetaArgumentRectMem3004.lean`, which assembles those bounds
  into formal membership in `routeBArgumentTargetRect2988`. WSL Lean passed.
- Added `C1RouteBThetaExpRectMem3005.lean`, connecting the formal argument
  rectangle to the existing exponential rectangle consumer. WSL Lean passed.
- Added `C1RouteBThetaExpNormBound3006.lean`, deriving the downstream norm
  bound `||exp(argument)|| <= 2` from the formal rectangle. WSL Lean passed.
- Added `C1RouteBThetaExpNormGlobal3007.lean`; for every theta it proves the
  analytic global bound `||exp(doubledArgument)|| <= exp(80/399)`, independent
  of the local rectangle. WSL Lean passed.
- Added `C1RouteBThetaDoubledArgumentNormGlobal3008.lean`; exports the matching
  global argument norm bound `||doubledArgument|| <= 80/399`. WSL Lean passed.
- Added `C1RouteBExpRealPartPositive3009.lean`; proves the global exponential
  real-part positivity needed to lower-bound `exp(z)+1` on the frontier.
  WSL Lean passed.
- Added `C1RouteBExpPlusOneNormLower3010.lean` and
  `C1RouteBCayleyNormBound3011.lean`; these formalize the denominator lower
  bound and generic Cayley quotient norm estimate needed for tanh control.
  WSL Lean passed.

## 2026-10-19 Route B denominator positivity

- Added `C1RouteBThetaDenominatorLower2999.lean`.
- `routeBThetaDoubledDenominatorLower2999` exposes the existing norm-square
  lower bound as the real polynomial denominator bound needed for safe cross
  multiplication.
- WSL Lean check passed with exit status 0.

- Added `C1RouteBComplexTanhExpCayley3012.lean` and
  `C1RouteBCenteredQExpForm3013.lean`; formally connect Mathlib `Complex.tanh`
  and `routeBCenteredQ` to the exponential Cayley quotient.
- Added `C1RouteBThetaCenteredQNormBound3014.lean`; proves the theta-parameter
  family bound `||routeBCenteredQ(t(theta))|| <= exp(80/399)`. WSL Lean passed.
- Added `C1RouteBGenericExpPos3015.lean` and
  `C1RouteBGenericCenteredQNorm3016.lean`; generalized the exponential sign
  and centered-Q norm bounds to every `||t|| <= 1/20`.
- Added `C1RouteBFrontierCenteredQBound3017.lean` and
  `C1RouteBCauchyGlobalBound3018.lean`; the frontier-to-sphere geometry,
  closed-ball maximum principle, and Cauchy tail bound are now formally
  connected. WSL Lean passed.
- Added `C1RouteBD4D7CauchyTailBridge3019.lean`; finite D4/D7 ledger bounds
  plus formal Cauchy tails are assembled into the strict 1500 / 2e9 targets.
  WSL Lean passed.
- Added `C1RouteBSourceChargeAggregate3020.lean`; provides the exact Finset
  aggregation bridge from per-cell endpoint norm envelopes to total source
  charge. WSL Lean passed.

## 2026-10-19 Deep-think correction

- Record 3021 caught an owner mismatch: records 3015--3018 bound the
  `routeBCenteredQ2900` Cauchy tail, while D4/D7 assembly integrates fourth and
  seventh derivatives of `Real.smoothTransition`. Record 3019 is generic
  arithmetic only and must not be read as a semantic D4/D7 tail bridge.

- Added `C1RouteBConcretePartitionGeometry3022.lean`; the concrete 8192-cell
  endpoint partition is now connected to the existing D4/D7 evaluator
  membership theorem. WSL Lean passed.

- Record 3023 corrects the blocker audit: `results/2730_seed_derivative_bounds.json`
  and `results/2804_seed_cell_ledger.json` already contain the 8192-cell
  envelopes and aggregate checks. Replayed both checkers successfully. The
  remaining gap is formal artifact-to-Lean soundness, not data generation.

- Deep-think review found formal analytic source chain already present in
  `C1SeedJetSemantics2731.lean`, `C1SeedEndpointMajorants2732.lean`, and
  `C1SeedEndpointIntegral2733.lean`. These prove source recurrences, pointwise
  order-4/7 majorants, and the endpoint integral charge. The nonformal gap is
  only the finite interval replay on `[1/4096, 1/2]` and its 8192-cell
  aggregate-to-Lean provenance.

- Added `scripts/generate_seed_ledger_arithmetic_3024.py` and generated
  `C1RouteBSeedLedgerArithmetic3024.lean` from the exact 2804 ledger. Lean
  proves both 8192-row lengths and exact D4/D7 charge sums; WSL check passed.
  This is arithmetic provenance only and does not yet prove evaluator soundness.

- Added `scripts/seed_interval_jet_global_control_3027.py` and record 3027.
  Canonical vs legacy interval recurrences agree on all 8192 cells, all slots
  contained, maximum normalized deviation below 1.1e-37. This is a global
  convention control, not a Lean soundness proof.

- 3028 direct canonical-charge comparison found exact containment failures,
  despite displayed ratios rounding to 1.0: D4 excess 1.46e-39 (cell 7890),
  D7 excess 6.68e-33 (cell 1360). Preserve the failure; repair requires an
  explicit directed-rounding allowance and aggregate re-price.

- 3029 prices that allowance under the same imported legacy evaluator context:
  total D4 excess 2.36e-36 and D7 excess 2.59e-30, both far below the
  1500/2e9 margins. The initial zero reading was an instrument-context bug and
  was corrected by loading the parent evaluator before setting interval dps.
- Added `C1RouteBGenericExpPos3015.lean` and
  `C1RouteBGenericCenteredQNorm3016.lean`; generalized the exponential sign
  and centered-Q norm bounds from theta points to every `||t|| <= 1/20`.
- Added `C1RouteBFrontierCenteredQBound3017.lean`; uses the frontier-to-sphere
  inclusion to obtain a full Cauchy frontier bound.
- Added `C1RouteBCauchyGlobalBound3018.lean`; connects the frontier bound to
  the closed-ball maximum principle and proves the Cauchy tail is below
  `1e-13`. WSL Lean passed.

- Added 3031 formal allowance contract: uniform 1/10 per cell, with Lean arithmetic proving aggregate targets under the explicit pointwise evaluator-to-ledger premise. This is a contract, not yet the missing evaluator soundness proof.

- Added 3032 finite-target allowance consumer and 3033 cell-level source-charge bridge. The remaining premise is explicit: exact evaluator norm <= certified norm, and row charge <= ledger + allowance.
