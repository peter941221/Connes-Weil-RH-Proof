# Project Memory

Last compressed: 2026-10-29.

This file is a current-state handoff, not a chronological experiment ledger.
Detailed evidence and historical incidents remain in `docs/proofs/` and Git
history. The project does not claim `SourceRH` or RH.

## Current decision tree

```text
Route A healthy CompactLog owner
        |
        +--> selected detector has qw < 0
                 |
                 +--> prove qw >= 0 for that same owner
                          |
                          +--> SourceRH -> Mathlib RH
```

The binding producer bottleneck is the selected-owner signed physical-kernel /
C3' budget. Route B and row-B results are scoped results, not automatic
transfers to the Route A owner.

## Hard verification gate

Every non-trivial Lean build must use a Linux-native WSL2 ext4 workspace. The
repository `lean-toolchain` must be copied or synchronized before building and
must be checked with:

```text
cat lean-toolchain
lean --version
```

Required result: `leanprover/lean4:v4.30.0` and Lean `4.30.0`. If the file is
missing, the version differs, or the build runs on `/mnt/c`, verification stops
and no `.olean` result may be reported as valid. This rule was added after the
3130 build: the temporary WSL tree initially selected Lean 4.33.1 because it
lacked `lean-toolchain`; copying the file corrected the build.

Focused builds and audits must preserve logs, inspect the full error list, and
print exactly `[propext, Classical.choice, Quot.sound]`. Never treat a build
footer alone as proof.

## Mathematical red lines

- No `sorry`, `admit`, new axioms, fake data, or `True`/`Set.univ` shortcuts.
- Preserve owner identity, signed cancellation, support ownership, and the
  correct `2*pi` frequency normalization.
- A finite prime cutoff requires a same-test omitted-term proof or aggregate
  bound. A signed partial remainder is not a sign for the full remainder.
- Do not exchange infinite sums and integrals without proving integrability.
- Numerical experiments need a named decision target and reproducible exact or
  interval evidence.

## Completed records

- `2722F`: stored row-B capture compiled in the WSL dependency chain.
- `3110`, `3119`, `3120`: Route-B powered seed, signed prime cut, and Fourier
  readback dependencies compiled under Lean 4.30.0.
- `3128`: names the owner-specific prime-power residual and proves its exact
  additive decomposition; no residual sign or bound is proved.
- `3130`: defines the finite owner symbol and proves the exact pointwise and
  whole-line integral decomposition under explicit `Integrable` premises.
  Audit passed with the standard axiom trio. This is an interface, not a
  residual estimate or RH proof.
- `3160`-`3165`: indexed producer contracts and support prototypes were audited;
  `3163` proves the current concrete common-only producer construction is a
  no-go, and `3164` records the fixed-index versus test-indexed API boundary.
- `3170`: the selected-owner residual now has a conservative pointwise
  absolute allowance equal to the existing prime-part allowance plus the
  finite-owner kernel coefficient allowance. The focused WSL build and audit
  passed under Lean 4.30.0 with only the standard axiom trio.
- `3171`: combines the finite-owner and residual allowances into the explicit
  same-owner margin gate
  `finite allowance + residual allowance <= -c3Sigma xi -> routeAJointSymbol >= 0`.
  This is a parameterized diagnostic only; because the residual allowance
  already contains the finite allowance, the displayed condition counts it
  twice and is weaker than the direct 3080 lower bound. It is not the binding
  producer route.
- `3172`: defines the live same-owner physical-kernel envelope contract with
  signed centers and nonnegative errors, proves it yields an
  `OrbitPhysicalKernelNodeCertificate`, and bridges it to the existing
  semi-local gate. No numerical node producer has been supplied yet; WSL
  Lean 4.30.0 build and audit passed with the standard axiom trio.
- `3173`: defines the concrete same-owner lower/upper node interval contract,
  converts it to the 3172 center/error envelope, and bridges it to the physical
  kernel gate. Audit passed with the standard axiom trio. Record 2038 remains
  the binding warning that the old one-copy G8-H numerical interval payload is
  not closed.
- `3174`: audited the existing numerical payloads against the 3173 contract.
  The repository has no data-bearing same-owner interval producer: 2523 is a
  fixed midpoint model, 2530 is diagnostic, 2535 is an external whole-cell
  enclosure, 2539 leaves coefficient/numeric membership open, and 2038 leaves
  the one-copy full-line certificate unclosed. This closes the current
  payload-to-producer attempt, not Route A globally.
- `3175`: the same-owner interval certificate is now guarded by an audited
  contradiction theorem. Under a hypothetical right-hand off-line zero,
  `orbitWindowSemiLocalGate_of_owner_node_interval_certificate` gives
  `ICgate <= 0`, while healthy owner geometry gives `ICgate > 0`. The WSL2
  Lean 4.30.0 target and audit passed (3796/3797 jobs) with exactly the
  standard axiom trio. This is a producer-boundary guard; it constructs no
  numerical certificate and makes no RH claim.

## Open obligations

`3176` adds a fail-closed evidence gate for the same-owner Route-A producer.
Running `python scripts/routea_same_owner_budget_audit_3176.py` returns
`STOP_MISSING_PRODUCER_PREMISE`: the current legacy payload has no closed
signed two-frequency kernel, exact owner/support transfer, full-line tail, or
Lean-imported negative aggregate margin. This is a diagnostic boundary, not a
new mathematical no-go.

The 2353 same-owner tail supplier was replayed with current Python/Arb
dependencies and reproduced `T = 128`, `q = 1/16384`, and the committed
whole-line constants. Its scope flags remain external and `producer_go = false`.
After a provenance-only refresh, both 2353 and 2354 selftests pass. The refresh
does not change the mathematical payload and does not promote the supplier
into Lean; `full_signed_kernel_priced` and `producer_go` remain false.

`3178` bridges the refreshed 2353/2354 tail evidence into an explicit ledger.
The two scalar acceptance lanes have exact headroom of about 23.96 percent and
75.43 percent, but both rows are explicitly `not_a_gate_row`; they cannot be
added to the signed prime-node aggregate. The ledger therefore remains
`TAIL_BRIDGED_MAIN_BUDGET_STILL_OPEN` with finite-window and full-line producer
components still missing.

`3179` preserves the signed real-part cancellation for the current owner and
replays the finite-window integral with a coefficient uncertainty charge. The
composite-trapezoid diagnostic is positive for both height signs:
approximately `1.0000000013672649` at sigma `-0.5` and exactly `1` to the
displayed precision at sigma `+0.5`; the uncertainty charge is about
`4.22e-45`. This is not a certified quadrature enclosure and is not a global
Route-A no-go, but it is a current-owner quantitative obstruction: tighter
error accounting alone cannot make this captured signed midpoint negative.
The next admissible numerical step is a parameterized owner/correction scan
with an explicit negative-margin stop condition, or a justified owner repair.

`3180` adds a narrow sigma scan without changing owner coefficients or support.
It is diagnostic only and is intended to distinguish a bad height parameter
from a bad current owner geometry. The scan must not be promoted to a theorem;
only a negative candidate with a separately closed quadrature and tail budget
would justify another producer attempt.
The corrected endpoint alpha 1 is different: the 3181 diagnostic gives a
stable signed midpoint near -1.41516724417e-8 at sigma -0.5, with a
coefficient uncertainty charge near 8.05e-42, after refinement from 640 to
2560 cells. This is the first current-owner candidate with a negative signed
finite-window midpoint. It remains diagnostic because curvature, quadrature,
full-line tail, exact owner transfer, and Lean import are still open. The next
producer attempt should target this endpoint rather than the base coefficient.


Record 3182 applied an Arb interval-style signed finite-window enclosure to the
correction candidate. The signed node upper remained negative, about
-3.54e-9, but the cellwise curvature remainder upper was about 65011.55,
giving a positive total upper. This does not refute the correction endpoint; it
identifies the current failure mechanism as an overly conservative uniform
derivative budget near support boundaries. The next numerical artifact should
use boundary-cell splitting or a local curvature envelope before any Lean
assembly.

Record 3184 preserved signed cancellation in the aggregate third derivative.
The curvature remainder fell from about 65011.55 to about 9157.13 at 2560
cells, while the signed node upper stayed near -3.54e-9. This confirms that
family-by-family absolute third-derivative pricing was a real loss, but the
remaining fourth-derivative envelope is still far too conservative for the
candidate margin. No producer or RH claim follows.

Record 3185 switched to a symmetric fourth-order midpoint Taylor enclosure.
The remainder fell from about 9157.13 in 3184 to about 214.76 at 2560 cells,
but the total upper remained positive. The h^5 improvement works, while the
familywise absolute fourth-derivative envelope remains the dominant loss. The
candidate is still numerical only; no Lean or full-line certificate exists.

Record 3186 used cell-local Arb interval arithmetic for the aggregate fourth
derivative, with a conservative fallback only at support crossings. The total
upper fell from about 214.76 in 3185 to about 22.9241 at 2560 cells. This
validates local aggregate interval evaluation as the correct direction, but
the finite-window upper is still positive and no producer claim is available.

A Taylor-8 experiment was rejected as evidence: high-order interval dependency
caused denominator growth to hundreds of millions of digits, and a spurious
large negative result appeared at production cells. The artifacts were removed.
Do not treat high-order interval output as valid unless finiteness, bounded
serialization, and independent scale checks all pass.

A 40960-cell rerun of record 3187 is the first negative interval-style
finite-window result in this sequence: total upper approximately
-3.51105083224e-9, with sixth-order remainder approximately 2.68672781838e-11.
This materially changes the next action: audit the finite-window artifact and
connect the same correction endpoint to the full-line tail. It is still not a
Lean certificate or an RH claim.

Record 3189 compares the negative 3187 finite-window upper with the external
2353 contour tail. The tail is approximately 1.7182e-16, and the exact
rational sum remains approximately -3.5110506604e-9. This is a promising
numeric margin, not a producer result: same-owner transfer, signed full-kernel
pricing, Lean import, and the full theorem bridge remain open.

Record 3190 corrected the 3189 comparison by using the 2353 correction contour
row. Repair/capture hashes and all 30 family dimensions match. The correction
tail upper is approximately 1.1725259700e-16, and the exact finite-plus-tail
sum remains approximately -3.5110507150e-9. This closes the data-level owner
identity audit, but not the Lean signed full-line kernel theorem or producer
import.
The 2530 center-plus-error payload was replayed on 2026-10-30. Its modulus
majorant node sums are approximately `2.6868873764` and `2.6752114629` for
the two sigma signs, but the payload is explicitly diagnostic: it uses a
center norm plus scalar coefficient error, has no signed aggregate readback,
and has no Lean transcendental or curvature enclosure. These values must not
be treated as Route-A node bounds.

1. Construct an owner-specific `OrbitPhysicalKernelNodeCertificate` for the
   actual geometry, preserving signed cancellation and both frequency signs.
2. Prove its finite aggregate bound on `orbitVisiblePrimeRange geometry` with
   the same owner and support; absolute-value replacement is not sufficient.
3. Feed that certificate into `sourceRH_of_right_orbitGeometry_physicalKernel_certificate`.
4. Reassess the indexed producer only after obtaining a genuine arbitrary-
   convolution support theorem; common-only support is already blocked by the
   3163 concrete no-go.

The immediate producer checkpoint is now explicit: construct one fully closed
same-owner node family with exact lower/upper bounds, both frequency signs,
and a separately verified full-line/tail enclosure before adding any new Lean
producer assembly.

Record 3191 adds the owner-preserving signed-tail bridge in
ConnesWeilRH/Dev/C1RouteAOwnerSignedTailBridge3191.lean. Its certificate
requires one fixed geometry, node lower and upper bounds, a finite-window
upper, a full-line tail upper, the exact decomposition of the existing
archimedean-plus-node aggregate into those two bounds, and a nonpositive
combined upper. It then converts to the existing node-interval and physical-
kernel envelope certificates. The external 3190 tail rows and 3187 numerical
finite-window result are still not imported into Lean. Focused WSL2 build and
audit passed on Lean 4.30.0 with exactly the standard axiom trio; producer GO,
SourceRH, and RH remain unproved.

Record 3192 extends `C1RouteABumpDerivativeLadder.lean` and
`C1RouteAOwnerDerivativeBudget.lean` from fourth to sixth order. Lean verifies
the fifth and sixth bump polynomials, their recurrence, absolute-value
constants, and the explicit theorem
`correctedPhysical_sixth_iteratedDeriv_budget2350`. This is a real prerequisite
for replaying the 3187 Taylor-6 remainder, but it is not the Taylor integral
identity or a numerical producer certificate. The 3187 JSON still contains
only a total upper, so no cell-level data was imported. Focused WSL2 Lean
4.30.0 build and audit passed with the standard axiom trio.

Record 3193 adds intervalIntegral_symmetricTaylor6_upper3193. Given a
pointwise sixth-order symmetric Taylor upper on one cell, Lean integrates the
polynomial exactly and proves the coefficients h^3/24, h^5/1920, and
h^7/322560. The theorem deliberately does not assert the pointwise Taylor
remainder; that remains the next analytic obligation. Focused WSL2 Lean
4.30.0 build and audit passed with exactly the standard axiom trio.

Record 3194 closes the one-sided Taylor-6 remainder obligation under the
correct smoothness interface. `taylor5_upper_on_right_half3194` uses
Mathlib's Lagrange remainder theorem, so the sixth derivative bound is divided
by 6! = 720. The earlier `taylor_mean_remainder_bound` route was rejected
because it divides by 5! = 120 and cannot support the 3193 coefficient.
The final theorem requires global `ContDiff ℝ 6` and a global bound on
`iteratedDeriv 6`; this is deliberate because a closed-set `ContDiffOn`
assumption alone does not justify identifying endpoint `uIcc` and fixed-cell
within derivatives. The global interface matches the existing owner derivative
budget theorem. WSL2 Lean 4.30.0 focused build and axiom audit passed with
exactly `[propext, Classical.choice, Quot.sound]`. This remains an analytic
prerequisite only; no numerical cell producer, SourceRH, or RH claim follows.

Record 3195 generalizes the pointwise remainder to a full cell. The theorem
`taylor5_upper_on_cell3195` handles both `position >= center` and
`position <= center`, normalizes each local `uIcc` Taylor expansion to the
fixed cell `Icc left right`, and retains the exact sixth-order denominator
720. It reuses the global `ContDiff ℝ 6` and global sixth-derivative budget
interface from 3194, avoiding an unproved endpoint within-derivative
transport. Focused WSL2 Lean 4.30.0 build and axiom audit passed with exactly
`[propext, Classical.choice, Quot.sound]`. This is the full-cell analytic
boundary; numerical cell inputs and the producer gate remain open.

Record 3196 adds `intervalIntegral_taylor5_upper_cancel_odd3196`. It accepts
the complete degree-five Taylor upper plus a sixth-order remainder on a
centered cell, integrates the polynomial exactly, and proves that the odd
Taylor terms vanish. The resulting even coefficients are exactly those of
3193: h^3/24, h^5/1920, and h^7/322560. Focused WSL2 Lean 4.30.0 build and
axiom audit passed with exactly `[propext, Classical.choice, Quot.sound]`.
The analytic bridge is now closed through the symmetric integral; the next
missing artifact is replayable per-cell numerical data, not another generic
Taylor identity.

Record 3197 packages the complete analytic bridge in
`intervalIntegral_taylor6_upper_from_global3197`. It derives the full-cell
Taylor upper from 3195, feeds it to the odd-cancellation integral theorem
3196, and returns the exact Route A coefficients using the fixed-cell second
and fourth within-derivatives. Focused WSL2 Lean 4.30.0 build and axiom audit
passed with exactly `[propext, Classical.choice, Quot.sound]`.

The 3187 script now has an optional `--cell-output` JSONL sidecar. The formal
record `results/3187_signed_taylor6_interval_40960.jsonl` contains one header
plus 40960 exact-rational cell rows. Structural validation passed: indices are
continuous, adjacent endpoints match, the full radius is covered, and exact
row sums equal both aggregate totals in the main JSON. This remains external
diagnostic input and is not yet imported into Lean. Each serialized upper is
rounded upward to the explicit `10^-80` decimal grid, so the finite decimal
rounding is part of the bound rather than an undocumented display conversion.

Record 3198 adds `intervalIntegral_le_sum_cell_upper3198`. It aggregates a
finite grid of separately proved cell-integral upper bounds into a whole-window
upper using Mathlib's adjacent-interval identity. Raw JSONL rows remain data,
not proofs: the missing owner-specific row proof and readback binding are now
isolated as the next interface boundary. Focused WSL2 Lean 4.30.0 build and
axiom audit passed with exactly `[propext, Classical.choice, Quot.sound]`.

Record 3199 adds the exact external replay checker
`scripts/audit_routea_taylor6_jsonl_3199.py`. It replays all 40960 cell
formulas and remainder formulas with `Fraction`, checks grid continuity and
radius coverage, verifies exact equality with both aggregate totals, and
checks all 163840 serialized coefficient uppers against the explicit 10^-80
rounding grid. The audit passes. It remains numerical evidence only: owner
derivative readback, Lean import, and the full-line tail are still absent.

Record 3200 audits the Python family evaluator against the Lean owner. The
exponential, bump denominator, sigma weight, and modulation phase are aligned,
and captured radii match `storedWidth[index]^2`. The diagnostic Python window
is `65536001/10000000 = 6.5536001`, while the Lean owner's maximum support is
`storedWidth 4 ^ 2 ~= 6.553600000000003`; this requires a zero-support bridge
or exact-window regeneration. More importantly, Lean still has no concrete
coefficient and modulation readback theorem for the JSON inputs, so 3200 is a
binding owner-identity boundary, not a producer certificate.

## Reproducibility lessons

- Build continuity is not mathematical progress; each experiment needs a named
  target and a stop condition.
- Native WSL source copies must include `lean-toolchain`; otherwise a different
  Lean version can silently invalidate cached `.olean` evidence.
- Keep the Windows source authoritative, use WSL ext4 for heavy builds, and
  copy logs/artifacts back in the same invocation.
- Avoid quoted `wsl.exe bash -lc` interpolation for `$?`, `$((...))`, and target
  lists. Use WSL-side scripts and explicit status files.
- For cancellation-sensitive enclosures, bind the gate to the same object or
  stencil being enclosed, carry `|value| + error`, and use independent-engine
  anchors.

## Evidence index

- `docs/proofs/3130_routea_owner_residual_margin_bridge.md`
- `docs/proofs/3163_indexed_producer_concrete_no_go.md`
- `docs/proofs/3164_fixed_vs_indexed_prime_support_boundary.md`
- `docs/proofs/3165_test_indexed_prime_support_prototype.md`
- `docs/proofs/3170_routea_residual_absolute_bound.md`
- `docs/proofs/3171_routea_owner_residual_margin_gate.md`
- `docs/proofs/3172_routea_owner_physical_kernel_certificate.md`
- `docs/proofs/3173_routea_owner_node_interval_certificate.md`
- `docs/proofs/3174_routea_owner_interval_producer_no_go.md`
- `docs/proofs/3175_routea_owner_interval_no_go.md`
- `docs/proofs/3176_routea_same_owner_budget_audit.md`
- `docs/proofs/3179_routea_signed_finite_window_diagnostic.md`
- `docs/proofs/3180_routea_signed_sigma_scan.md`
- `docs/proofs/3191_routea_owner_signed_tail_bridge.md`
- `build-logs/3191_wsl_build.log`
- `ConnesWeilRH/Dev/C1RouteAOwnerSignedTailBridge3191.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerSignedTailBridge3191Audit.lean`
- `docs/proofs/3192_routea_sixth_derivative_budget.md`
- `build-logs/3192_wsl_build.log`
- `ConnesWeilRH/Dev/C1RouteABumpDerivativeLadder.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerDerivativeBudget.lean`
- `docs/proofs/3193_routea_taylor6_cell_panel.md`
- `build-logs/3193_wsl_build.log`
- `ConnesWeilRH/Dev/C1RouteATaylor6CellPanel3193.lean`
- `ConnesWeilRH/Dev/C1RouteATaylor6CellPanel3193Audit.lean`
- `docs/proofs/3194_routea_taylor6_remainder.md`
- `build-logs/3194_wsl_build.log`
- `build-logs/3194_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteATaylor6Remainder3194.lean`
- `ConnesWeilRH/Dev/C1RouteATaylor6Remainder3194Audit.lean`
- `docs/proofs/3195_routea_taylor5_cell_upper.md`
- `build-logs/3195_wsl_build.log`
- `build-logs/3195_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteATaylor5CellUpper3195.lean`
- `ConnesWeilRH/Dev/C1RouteATaylor5CellUpper3195Audit.lean`
- `docs/proofs/3196_routea_taylor5_integral_odd_cancellation.md`
- `build-logs/3196_wsl_build.log`
- `build-logs/3196_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteATaylor5Integral3196.lean`
- `ConnesWeilRH/Dev/C1RouteATaylor5Integral3196Audit.lean`
- `docs/proofs/3197_routea_taylor6_integral_bridge.md`
- `build-logs/3197_wsl_build.log`
- `build-logs/3197_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteATaylor6IntegralBridge3197.lean`
- `ConnesWeilRH/Dev/C1RouteATaylor6IntegralBridge3197Audit.lean`
- `docs/proofs/3198_routea_cell_upper_aggregate.md`
- `build-logs/3198_wsl_build.log`
- `build-logs/3198_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteACellUpperCertificate3198.lean`
- `ConnesWeilRH/Dev/C1RouteACellUpperCertificate3198Audit.lean`
- `scripts/routea_signed_taylor6_interval_3187.py`
- `results/3187_signed_taylor6_interval_40960.jsonl`
- `docs/proofs/3199_routea_taylor6_jsonl_replay.md`
- `scripts/audit_routea_taylor6_jsonl_3199.py`
- `results/3199_routea_taylor6_jsonl_audit.json`
- `build-logs/3175_wsl_build.log`
- `build-logs/3175_wsl_audit.log`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualMargin3130Audit.lean`
- `ConnesWeilRH/Dev/IndexedProducerApiAudit3161.lean`
- `ConnesWeilRH/Dev/IndexedProducerConcreteNoGo3163.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualBound3170Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerResidualMargin3171Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPhysicalKernelCertificate3172Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3173Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175Audit.lean`
- `docs/proofs/3206_routea_owner_weighted_interval_integrable.md`
- `build-logs/3206_focused_build.log`
- `build-logs/3206_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAOwnerWeightedIntervalIntegrable3206.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerWeightedIntervalIntegrable3206Audit.lean`
- `docs/proofs/3207_routea_concrete_owner_window_decomposition.md`
- `build-logs/3207_focused_build.log`
- `build-logs/3207_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerWindowDecomposition3207.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerWindowDecomposition3207Audit.lean`
- `docs/proofs/3208_routea_concrete_owner_cell_upper.md`
- `build-logs/3208_focused_build.log`
- `build-logs/3208_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerCellUpper3208.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerCellUpper3208Audit.lean`
- `docs/proofs/3209_routea_concrete_owner_aggregate_upper.md`
- `build-logs/3209_focused_build.log`
- `build-logs/3209_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerAggregateUpper3209.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerAggregateUpper3209Audit.lean`
- `docs/proofs/3210_routea_concrete_owner_global_jet_bridge.md`
- `build-logs/3210_focused_build.log`
- `build-logs/3210_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalJetBridge3210.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalJetBridge3210Audit.lean`
- `docs/proofs/3211_routea_concrete_owner_global_aggregate_upper.md`
- `build-logs/3211_focused_build.log`
- `build-logs/3211_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalAggregateUpper3211.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalAggregateUpper3211Audit.lean`
- `docs/proofs/3212_routea_concrete_owner_40960_grid.md`
- `build-logs/3212_focused_build.log`
- `build-logs/3212_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGrid3212.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGrid3212Audit.lean`
- `docs/proofs/3213_routea_concrete_owner_40960_aggregate_upper.md`
- `build-logs/3213_focused_build.log`
- `build-logs/3213_focused_audit.log`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwner40960AggregateUpper3213.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwner40960AggregateUpper3213Audit.lean`

Record 3201 closes the support part of the 3200 window mismatch. Lean proves that correctedPhysical is exactly zero for abs(position) >= storedWidth 4 ^ 2, because every non-owner squared width is <= 6 and owner family 4 has squared width > 6. It also proves the Python diagnostic radius 65536001/10000000 is larger than the exact owner radius. This is only a pointwise support bridge; interval-integral equality still needs interval integrability and adjacent-interval splitting. Focused WSL Lean 4.30.0 build and axiom audit passed with exactly the standard trio.
The 3201 support bridge now also proves the weighted external owner integral is zero on both concrete outer intervals [storedWidth 4 ^ 2, diagnosticRadius3201] and [-diagnosticRadius3201, -(storedWidth 4 ^ 2)] using intervalIntegral.integral_congr on uIcc. The remaining window bridge is the exact decomposition of the expanded diagnostic integral into those zero outer pieces plus the inner owner window, followed by the concrete coefficient/modulation readback.
Record 3203 corrects the 3200 readback boundary. Concrete Lean owner data already exists: record2680CorrectionCoefficient and capturedModulations2584. All 30 modulations exactly match the captured hex values, but 0/30 concrete correction coefficients lie inside the extremely narrow 2338 ideal_correction_coefficient boxes. Therefore 3187's ideal-box center/error evaluator is not an enclosure of the concrete record2680 owner. The next numerical step is to reprice Taylor-6 using the actual binary64 owner coefficients or an explicitly widened box containing them.
Record 3204 reprices the Taylor-6 diagnostic with exact record2680CorrectionCoefficient binary64 values and zero coefficient error. At 40960 cells / 192-bit precision the upper remains negative, approximately -3.51105083244727867065463511235e-9. Record 3205 replays the concrete-owner JSONL exactly: 40960 rows, 163840 rounded coefficient fields, continuous grid, exact cell formulas, and exact aggregates all pass. This is still external evidence; Lean row import, derivative-row proofs, and the full-line tail remain open.
Record 3202 proves the exact diagnostic-to-owner window decomposition: the weighted integral over [-diagnosticRadius3201, diagnosticRadius3201] equals the integral over [-(storedWidth 4 ^ 2), storedWidth 4 ^ 2]. It uses adjacent-interval identities and explicit IntervalIntegrable premises for the three pieces. Focused WSL Lean 4.30.0 build and audit passed with the standard axiom trio.

Record 3206 closes the missing interval-integrability premise for the 3202
window bridge. `weightedExternal3201` is definitionally identified with the
real part of the `ContDiff` weighted physical owner, hence it is continuous
and interval-integrable on arbitrary finite intervals. Rebuilding this target
also exposed and fixed the old four-order boundary in the 2536/2537/2538
weighted-family envelope chain: the local bump numerator and coupled envelope
now cover orders 0 through 6, including the fifth- and sixth-order absolute
value bounds needed by the sixth-derivative budget. Focused WSL2 Lean 4.30.0
build and audit passed; all three 3206 declarations use exactly
`[propext, Classical.choice, Quot.sound]`. This is an analytic interface
closure only; concrete owner specialization, per-cell Lean certificates, the
full-line tail, SourceRH, and RH remain open.

Record 3207 specializes the 3202 window decomposition to the actual owner
`record2680CorrectionCoefficient` with `capturedModulations2584`. The theorem
`intervalIntegral_record2680_weightedExternal_eq_ownerWindow3207` supplies the
exact equality between the expanded diagnostic integral and the exact owner
support-window integral, using 3206 for all three interval-integrability
premises and 3201 for the zero outer pieces. Focused WSL2 Lean 4.30.0 build
and audit passed with exactly `[propext, Classical.choice, Quot.sound]`.
This closes the owner-specific window/readback boundary only; JSONL row
consumption, per-cell Taylor certificates, the full-line tail, SourceRH, and
RH remain open.

Record 3208 adds the concrete-owner per-cell Taylor-6 interface. Given exact
cell geometry, a midpoint value upper, second- and fourth-within-derivative
uppers, and a nonnegative sixth-derivative bound, Lean proves the cell
integral upper with coefficients `1/24`, `1/1920`, and `1/322560`. The numeric
premises remain explicit; no JSONL row is treated as a proof. Focused WSL2
Lean 4.30.0 build and audit passed with exactly the standard axiom trio.

Record 3209 connects 3208 to the 3198 finite partition aggregator. For a
concrete-owner grid and arrays of per-cell bounds, Lean proves interval
integrability from 3206, derives every cell upper from 3208, and sums the
pieces into a finite-window upper. The remaining blocker is now sharply
isolated: prove the bound arrays for the same owner and grid. JSONL replay,
the full-line tail, SourceRH, and RH remain open. Focused WSL2 Lean 4.30.0
build and audit passed with exactly the standard axiom trio.

Record 3210 closes the derivative-representation boundary between the external
3204/3205 rows and the Lean Taylor bridge. At a midpoint strictly inside a
cell, Lean identifies `iteratedDerivWithin 2` and `iteratedDerivWithin 4` with
the corresponding global derivatives, then exposes a cell-upper theorem that
accepts global jet bounds directly. Focused WSL2 Lean 4.30.0 build and audit
passed with exactly the standard axiom trio.

Record 3211 packages the global-jet form at the aggregate level. It accepts
global value, second-derivative, fourth-derivative, and sixth-derivative bound
arrays for the same concrete owner, converts the jet representation through
3210, and feeds each cell into 3208 and 3198. The remaining blocker is now
numeric: independently prove those arrays. JSONL replay, the full-line tail,
SourceRH, and RH remain open. Focused WSL2 Lean 4.30.0 build and audit passed
with exactly the standard axiom trio.

Record 3212 formalizes the exact 40960-cell uniform diagnostic grid. Lean
proves both endpoints, every adjacent-cell strict inequality, and the exact
midpoint formula. Record 3213 specializes the global aggregate theorem to this
fixed grid, leaving only the concrete owner bound arrays as premises. Focused
WSL2 Lean 4.30.0 builds and audits passed with exactly the standard axiom trio;
JSONL replay, numeric bound proofs, the full-line tail, SourceRH, and RH remain
open.
