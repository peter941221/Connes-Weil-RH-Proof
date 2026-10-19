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

- Added 3034 exact cell norm bridge: existing seedTransitionJetInterval_mem2734 and cell geometry now directly prove the Lean derivative norm is bounded by routeBSourceNorm2834 on every cell.

- Added 3035: combines exact cell derivative norm soundness (3034) with row allowance comparison (3033), yielding the weighted derivative charge <= ledger + allowance premise needed by finite-target assembly.

- Added 3036 finite-sum bridge: pointwise row charge <= ledger + allowance plus separate ledger/allowance sums yields aggregate + margin, isolating the remaining row-wise numeric-to-Lean premise.

- Record 3037 exports an exact rational allowance of 1e-20 for each of 8192 rows (aggregate 8.192e-17 per order), comfortably above the 3029 max excess and below D4/D7 margins. It is an input budget, not evaluator soundness.

- Added 3038 Lean arithmetic anchor for 3037: defines 1/10^20 allowance over Fin 8192, proves exact sum, and proves it is below both D4 and D7 margins.

- Linux-native Mathlib build completed (8474 jobs). First real 3038 compile exposed and fixed noncomputable Real division and inverse-normalization issues; ext4 compile produced /tmp/3038.olean successfully.

- Linux-native verification: Mathlib built successfully (8474 jobs); 3034, 3033, 3035 built; fixed 3031 to use the 1e-20 row allowance and explicit margins; 3036 then built successfully (8476 jobs total).

- Record 3039 exports per-row canonical interval uppers for all 8192 cells; both D4 and D7 rows pass canonical_upper <= exact ledger rational + 1e-20 allowance in the mpmath replay. This is stronger row-level numerical evidence, still not Lean evaluator soundness.

- Record 3040 exports 8192 per-cell D4/D7 interval upper rationals, including equal endpoint-majorant shares; sums reproduce 2730 totals exactly (D4 1400.650853119245, D7 592705254.0438685). This is numerical input for the Lean evaluator bridge, not yet its soundness proof.

- Added 3041 Lean arithmetic projection generated from 3040's 8192 rational D4/D7 cell uppers; it proves row lengths and exact aggregate sums once Linux-native compiled. Evaluator semantic soundness remains separate.
## 3043 poweredSeed same-owner sign scan (2026-10-19)

`scripts/fourpoint_powered_seed_3043_scan.py` scanned the repaired
`poweredSeed` owner over 5 rho points and sigma = 0, 0.5, 1.0, with n = 0..4.
The result is `results/3043_powered_seed_sign_scan.json` and is explicitly
model-grade only: known zeta zeros under-approximate the owner, the orbit is
hypothetical, and the xi integrals use a sampled trapezoid.

Observed counts: 15 scan points; 25 rows satisfy the vertex sign predicate
`C > 0`, `b > 0`, `det < 0`; 39 rows have the fixed-lambda-24 quadratic value
negative. The successful row indices vary substantially with rho, sigma, and
n. Hence determinant negativity is not a stable same-owner producer, and the
fixed lambda 24 signal does not establish the mainline gate prerequisites.
This does not prove Route B impossible; it closes the current numerical probe
as a route to a universal producer. Do not promote these numbers to Lean
premises. Route A remains the binding producer lane.
## 3044 correction: high-resolution C3' margin survives (2026-10-19)

The first 3044 low-resolution diagnostic used 1024 cells and read a negative
base endpoint margin. A cross-read of the authoritative 2533 artifact shows
that this is a resolution effect: at 2560/5120/10240 cells the sampled margins
for sigma = -0.5 are 0.0411/0.0836/0.0907 and for sigma = +0.5 are
0.0530/0.0953/0.1024. Thus the sampled C3' margin survives refinement. The
remaining obligation is stronger: replace the sampled 17-point familywise
third-derivative supremum by a certified whole-cell enclosure. Do not use the
1024-cell negative reading as a Route-A no-go.
## 2535-to-2686 interface audit (2026-10-19)

The existing `C1RouteAWeightedFamilyCell2538` / record-2535 certificate
proves a whole-cell bound for one weighted external-family channel and its
third-derivative curvature construction. The generic 2686 consumer requires
four independent per-cell rectangle/charge inputs:
`baseM0`, `baseD2`, `correctionM0`, and `correctionD2`.

Therefore record 2535 cannot be connected to `chargeRest` merely by matching
the 30-family count or the sigma values. A valid bridge must identify the
2535 function with one of the four live channel definitions and separately
provide the other three channels, or prove a new four-channel composition.
Until that owner/channel identity is formal, the 2535 positive margin remains
a single-channel external enclosure and does not license Producer GO.
## 2535 refined identity result (2026-10-19)

Symbol-level inspection corrects the earlier overly broad warning. The 2535
evaluator squares each stored support width, matching the corrected physical
owner used by `externalPhysical2344`; Lean's
`weightedFunction2348 (externalFamilyValue2344 ...)` is the same weighted
family form. Thus 2535 is a valid candidate enclosure for the `baseM0`
channel. The identity is still not a completed bridge because the coefficient
centres, modulation vector, and coefficient-ball error must be matched to
`record2678BaseCoefficient` / `capturedModulations2584` in Lean. The other
three channels (`baseD2`, `correctionM0`, `correctionD2`) remain separate.
## 3045 exact base-M0 identity audit (2026-10-19)

The exact audit changed the status of the proposed 2535 -> `baseM0` bridge.
All 30 modulations match `capturedModulations2584` exactly, and the squared
support convention matches. However, all 30 Lean binary64 coefficient casts
 differ from the exact 2338 interval midpoints and all 30 lie outside the
2338 coefficient boxes. Float conversion had hidden this because it rounded
the midpoint to the same binary64 value. Therefore 2535 cannot be consumed by
the 2686 base-M0 owner as-is. The next task is a named coefficient-owner
reconciliation (or a fresh enclosure for the 2678 midpoint-cast owner); do not
claim a base-M0 identity from the 2535 artifact.

## 2026-10-19 producer-first direction review

The 3047 external base-M0 enclosure and 3048/3049 rational projections do
not discharge the selected-detector signed producer. In
C1RouteAProducerWired.lean, chargeRest is a free Real parameter constrained
by hcharge, not a definition of the actual physical residual. Record 2800
still assumes hidentity, and its repaired total integrates only from zero
to record2675CellRight. Neither fact supplies a full-support residual bound.

The exact target remains the same-owner selected gate identity in
C1RouteASelectedOwnerResidualReadback.lean: ICgate equals archimedeanTerm
plus selectedOwnerVisiblePrimeProfileWeightedSum. Under triple vanishing,
qw is the negative of that sum. Any proposed numerical import must name
which premise of this selected-owner statement it removes and prove the
owner, domain and orientation connection before batch expansion.

The scoped record-2319 obstruction remains binding: the recorded quartic
Hermitian transform is zero at the target while the selected convolution
square has value -1 under the target pins. This does not close Route A;
it rules out identifying those two expressions. Pause further 3047-3049
expansion until a valid connection is established. Lean compilation of
3049 remains unverified; source-level Python readback is not a substitute.

## 2026-10-19 selected-geometry entry audit

OrbitG8Geometry requires base_support and correction_support inside Ioo(-1,1),
selected_owner_test, exact raw_target_values, minimal interpolation, and tail
fields. The numerical correctedPhysical family has a proved support upper
radius about 6.5536 (C1RouteAOwnerSupport, record 2314), which does not by
itself establish either unit-window field. A large upper bound alone is not
proof of a unit-window violation; actual nonvanishing outside the window or
an explicit support-transfer theorem would be needed. No rescaling can be
silently used: it changes Laplace arguments, derivative costs and the
support-derived prime owner.

The 3045 cast-vs-exact coefficient mismatch was already documented in
record 2678 (docs/proofs/2678_owner_alignment_no_go.md). Treat 3045 as a
repeat audit, not a novel obstruction. Fixed binary64 casts are not proved
to realize the exact target equations by numerical closeness. Before any
further full-grid import, require a named construction satisfying the actual
geometry fields or a proved alternative consumer with its own support rules.

## 2026-10-19 unit-support direct substitution ruled out

Exact source readback at family index 4 gives base coefficient real part
-41859404295843/4096 and correction coefficient real part
-6001732121601251/32; both are nonzero. The existing proved
correctedPhysical_six_ne_zero specializes to either vector for any modulation.
Thus both untransformed correctedPhysical functions are nonzero at x=6,
outside Ioo(-1,1). They cannot directly fill OrbitG8Geometry.base or
.correction with its unit-support fields. This is an exact mathematical
consequence of existing source lemmas plus exact coefficient decoding, not a
fresh Lean compilation of the specializations. It does not exclude their use
in a different support-aware consumer or a proved transformed construction.

## 2026-10-19 geometry construction versus numerical owner

`exists_indexed_orbitG8Geometry_of_sourceNontrivialZero_right` already
constructs, for every hypothetical off-line source zero under its hypotheses,
a base and correction with support in `Ioo (-1,1)`, target values, minimal
interpolation, orbit index and spectral-tail fields. Therefore unit support is
not the missing producer premise.

The missing analytic statement is the signed physical-kernel budget for the
constructed `geometry`:

```text
archimedeanTerm geometry.g.convolutionSquare
 + sum visiblePrimeRange geometry
     weight(n) * Re(K(log n) + K(-log n)) <= 0
```

The fixed 2678/2680 binary64 numerical owner is not proved equal to this
existential construction. Its support mismatch is therefore a transfer
failure, not a no-go for the abstract Route-A geometry. Do not use its
positive norm margin as evidence for the constructed geometry until that
identity is proved.

## 2026-10-19 norm-majorant routing test

The common-factor profile norm consumer is sufficient, not equivalent to the
signed budget. Let h(t)=orbitRawFactor(-t), P(t)=the finite complex profile,
F(t)=Re(conj(h(t))*P(t)), and U(t)=|h(t)|*|P(t)| on the actual support
window. Then U-F>=0 pointwise and the excess cost is exactly integral(U-F).
Consequently Arch+integral(U)<=0 requires Arch<=0. Preserving cancellation
inside P does not preserve the phase cancellation between h and P, nor
cancellation across t. Before pricing this method, establish Arch's sign on
the same constructed geometry and bound the excess cost relative to the
signed margin. The existing source theorem takes this budget as hbudget;
its presence is not a quantitative producer construction.

## 2026-10-19 record-3051 direction correction

The evaluator-to-Lean batch belongs to the item-5 weighted-zero charge lane,
not directly to the selected-detector physical-kernel producer. Record 2686's
four-channel total is a captured repaired-owner integral on
`[0, record2675CellRight]`; record 2800 proves its `chargeRest` consumer only
under `hidentity`; record 2802 leaves the item-5 owner comparison open. The
selected detector is built from hypothetical-zero geometry, and record 2319
rules out direct replacement by the P-only transform. Therefore an 8192-cell
import can close a repaired-owner item-5 enclosure, but cannot close the live
B5 physical-kernel budget.

Correct next gate: keep the item-5 owner comparison and the selected-detector
signed physical-kernel certificate as separate obligations. Continue the
item-5 batch only if it removes a named item-5 premise. For the binding route,
derive a certificate for the actual `orbitFinitePhysicalKernelIntegrand` over
`orbitVisiblePrimeRange geometry`, preserving signed cancellation and support
ownership. This is a source-level direction correction, not a new no-go
theorem or RH result.

## 2026-10-19 selected profile reduction

The actual selected-owner common-factor prime profile has the exact algebraic
form `P(t) = 2 exp(-t) sum_n Lambda(n) phi(log(n)-t)`. In the source definition,
each term is `2 Lambda(n)/sqrt(n) * exp(log(n)/2-t) * phi(log(n)-t)`;
`exp(log(n)/2)=sqrt(n)` for n >= 2, while the n=0,1 von Mangoldt terms are
zero. The physical integrand is `2 exp(-t) Re(conj(phi(-t)) * sum_n
Lambda(n) phi(log(n)-t))`, with `phi = orbitRawFactor geometry`. This keeps
all prime cancellation grouped and displays the exact selected correction
against a smoothed von Mangoldt profile.

Record 1736's Stieltjes identity applies to the same selected square under
triple vanishing: `qw = Q_cont + 2 integral R(y) H_g'(y) dy`. Thus the
remaining Route-A analysis is a signed discrepancy estimate for this actual
owner. The identity is a target reduction, not a sign result; its integrand
can change sign, and setting the discrepancy to zero does not yield the
needed inequality. Item-5 repaired-owner charges remain separate.

## 2026-10-19 exact continuous energy threshold

Combining record 1736's exact `Q_cont` formula with `f(y)=M-E_g(y)/2` gives
`Q_cont=(4-K)M+integral v(y)E_g(y)dy`, where
`v(y)=exp(-y/2)/(exp(2y)-1)>0`. Its second moment is
`16 sum_{k>=0}(4k+5)^(-3) <= 15914/91125 < 1/5`; therefore
`Q_cont <= -(K-4)M + ||g'||_2^2/5`, improving the previous coefficient 18
by a factor 90. If `||g'||_2^2/M < 5(K-4)`, the continuous term is strictly
negative, and the actual prime discrepancy must supply a positive
mass-scale correction. This is a paper-level bound, not a selected-owner
measurement or Lean theorem. The selected correction API does not yet prove
the needed derivative-to-mass ratio; see record 3053.

## 2026-10-19 fourth-order tail and derivative energy

On the critical line `s=i*t`, the exact source identity gives
`laplaceAt (g.convolutionSquare) s = |laplaceAt g s|^2`. Restricting the
geometry's fourth-order tail field to `z=1/2+i*t` yields, with
`T*=max(T,1,2|Im rho|)`, `|laplaceAt g (i*t)| <= 4 epsilon/t^2` for
`|t|>=T*`. Plancherel then gives the paper-level bound
`D <= T*^2 M + 16 epsilon^2/(pi*T*)`, where `D=integral |g'|^2` and
`M=integral |g|^2`. The low-frequency term grows with the tail threshold, so
this bridge alone does not prove the record-3053 small-derivative condition
at large zero height. This is an insufficiency of the derived bound, not a
no-go for stronger same-owner use of the interpolation data. See record 3054.

## 2026-10-19 finite interpolation nullspace

For a fixed support interval and finite Laplace node set, add a modulated bump
`u_N=exp(-i*N*x) psi` after applying the product of the exact differential
shifts `D_s h=h'+s*h` over all nodes. The transform law
`L(D_s h,z)=(s-z)L(h,z)` makes this perturbation vanish at every pinned node;
after normalization by `N^m`, its mass stays bounded while its derivative
energy grows like `N^2`. Thus support plus finite pins alone cannot bound
`D/M`. This does not preserve or refute the full OrbitG8Geometry fourth-order
tail field, so the no-go is only for the interpolation-only API. See record
3055; the remaining target combines finite pins with the full tail to bound
the low-frequency Fourier energy.
