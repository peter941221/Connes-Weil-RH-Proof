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

Record 3269 completes Lean-verified staged phase infrastructure for the
remaining cell-16923 families 0..9 and 15..29. The 25-family module contains
75 base/step/final theorems; the WSL2 ext4 Lean 4.30.0 build and independent
audit pass with exactly `[propext, Classical.choice, Quot.sound]`.

Record 3270 combines all 30 cell-16923 phase boxes with the exact owner
coefficients into family coefficient-phase rectangles and six five-family
block rectangle definitions. All 30 family membership theorems pass the
standard axiom audit. A direct `reHi < 0` proof for the externally negative
blocks was intentionally not retained: independent rectangular family sums
lose phase correlation and remain too conservative. The next formal step is
a correlated block phase-sum enclosure, followed by the weighted bump and
finite-window aggregate. The tail, B5 readback, `producer_go`, SourceRH, and
RH remain open.

Record 3268 adds Lean-verified staged phase boxes for families 10 through 14
at the formal weighted-original diagnostic cell 16923. The generator uses
outward rational rounding and four-corner interval products; a first version
was rejected because its `2*x*y` propagation used only two corners when an
interval crossed zero, and was corrected before verification. The focused
WSL2 ext4 Lean 4.30.0 build succeeds, and all 15 base/step/final audit entries
report exactly `[propext, Classical.choice, Quot.sound]`. This is phase
infrastructure only; the block coefficient sign, finite-window aggregate,
full-line tail, B5 readback, `producer_go`, SourceRH, and RH remain open.

Record 3267 replays the complete 40960-cell weighted-original Taylor-6
finite-window diagnostic with contiguous five-family blocks priced
separately. The block upper contributions are approximately `-9.45675e-11`,
`-1.43474885e-8`, `+2.91092718e-10`, `+4.47412240e-13`, `+1.70894775e-15`,
and `+1.12367661e-15`; their sum is approximately `-1.4150513089e-8`.
This remains negative and is close to the aggregate 3238 upper
`-1.4151657849e-8`, so the five-family decomposition preserves enough signed
cancellation for a formal block route. The sixth-order envelopes are priced
per block and therefore incur a small decomposition loss; this is diagnostic,
not yet a Lean certificate. The next formal target is the block-level
weighted-original enclosure on the 40960-cell grid, with 16923 retained as
the strongest local sign witness and 17168 retained only for reusable phase
infrastructure.

Record 3214 validates every row of the concrete-owner 3204 JSONL and retains
indices 0, 17168, and 40959 as representative cells. The two outer diagnostic
boundary cells have zero value, second-derivative, and fourth-derivative uppers;
their charge is entirely the sixth-order remainder. Index 17168 is the most
negative cell, approximately -38.0161. The full grid has 18695 negative and
22265 positive cell uppers, so the final margin comes from signed aggregate
cancellation rather than a single central cell. This is a proof-design probe
only: Arb interval containment, derivative-row proofs, Lean import, the
full-line tail, SourceRH, and RH remain open. The next formalization target is
one outer cell and one interior cell, not another full-grid diagnostic.


The 3215 geometry probe is now a valid negative result: the first diagnostic
cell midpoint is strictly inside the owner support. Therefore its 3204
`value_upper = 0` is only a one-sided signed upper bound, not a support-zero
identity. The support-zero theorem cannot close this cell; the next proof
primitive must establish a concrete signed midpoint inequality.

Record 3215 is a focused Lean geometry result for the first 40960-cell
midpoint. It proves `|record2680Center3212 0| < storedWidth 4 ^ 2` and the
negation of the support-zero condition. Thus the first cell midpoint is inside
the owner support; its 3204 `value_upper = 0` is a signed one-sided upper bound,
not a zero identity. The WSL2 Lean 4.30.0 build and audit passed with exactly
the standard axiom trio. The next cell theorem must prove the signed midpoint
inequality and derivative bounds, not use the support-zero theorem.


A second 3216 reuse check found that `record2680CorrectionM0CellContained`
only encloses the legacy normalized interval `[0, record2675CellRight]`. It is
not a certificate for the 3212 diagnostic coordinate at index 0, so it cannot
be reused without an owner-coordinate transfer theorem. Preserve this boundary:
the next producer artifact must generate a rectangle or signed upper directly
at `record2680Center3212 0` (and later on its actual cell), not relabel the old
cell containment result.


Record 3216 evaluates the actual record2680 owner at the actual 3212 cell-0
midpoint `-2684289064959 / 409600000000`, not the legacy normalized coordinate.
After outward rounding to the `10^-80` rational grid, only family 4 is nonzero
and the aggregate real rectangle is `[-1/10^80, 0]`, matching the 3204
`value_upper = 0` row. This remains external Arb evidence: Lean has not yet
proved family-4 interval membership at that midpoint, and coordinate transfer,
full-line tail, producer_go, SourceRH, and RH remain open.

Record 3217 closes the support part of that midpoint boundary in Lean. At the
actual `record2680Center3212 0`, every family index other than 4 is outside
its squared support radius, so `externalPhysical2344` reduces exactly to the
family-4 term. It also expands that remaining term's real part into the exact
real formula using `cos` and `sin`, so the next numeric proof can operate on a
single real inequality. The theorem was built in WSL2 with Lean 4.30.0 and audited to
`[propext, Classical.choice, Quot.sound]`. The family-4 signed real upper is
still open; no external rectangle was imported as a theorem, and
producer_go, SourceRH, and RH remain open.

A direct attempt to prove the family-4 midpoint sign with the existing
small-angle `cosPin2676`/`sinPin2676` lemmas was rejected: the exact phase at
cell 0 has absolute value about 257, not at most 1. The failure is structural,
not a numerical margin issue. The next phase certificate must split or scale
`Complex.exp (angle * I)` into bounded pieces before applying the small-angle
Taylor pin, then compose the pieces with interval multiplication.

Record 3218 implements the first phase-scaling primitive. Lean proves the
exact identity
`exp(angle * I) = exp((angle / 512) * I)^512` using `Complex.exp_nat_mul`,
and proves the actual cell-0 scaled phase has absolute value at most 1. This
does not yet compose the 512 rectangles or prove the family-4 sign, but it
removes the direct high-frequency obstruction without importing numeric phase
data. The same file now proves that the actual record2680 cell-0 phase lies
in the recursively composed 512-factor rectangle. The remaining local step
is coefficient/bump multiplication and extraction of a nonpositive real upper.


Record 3218 is now fully verified. In addition to the exact identity
`exp(angle * I) = exp((angle / 512) * I)^512` and the scaled small-angle
membership theorem, Lean proves the actual cell-0 phase lies in a coarse
rectangle with real part in `[9/10, 1]` and imaginary part in `[-2/5, -3/10]`.
The numerical enclosure uses `complexRectPowSq3218`: nine repeated-squaring
levels represent the exact 512th power and avoid the heartbeat timeout from
unfolding 512 sequential interval multiplications. The focused WSL2 Lean
4.30.0 build and axioms audit pass with exactly `[propext, Classical.choice,
Quot.sound]`. The next local obligation is multiplying this phase rectangle
by the family-4 coefficient and bump rectangle to prove a strictly negative
real upper at the same owner and coordinate; producer_go remains false.

The 3218 local phase certificate now also includes an exact binary64-derived coarse
box for the selected owner family-4 correction coefficient:
`re in [-200000000000000, -100000000000000]` and
`im in [-100000000000000, 0]`. Lean proves the actual coefficient is in this
box and proves the real upper of its product with the phase coarse box is
strictly negative. This is a deliberately wider, transparent box than the
legacy generated correction box; it is sufficient for the sign and avoids
silently transferring an unrelated coefficient enclosure. The new theorems
pass the WSL2 Lean 4.30.0 axioms audit with the standard trio. The remaining
step is to prove the bump at the actual midpoint is strictly positive and
transport the negative coefficient-phase upper through the exact family-4
real-part formula.

The 3218 chain now closes the selected-owner cell-0 midpoint sign in Lean:
strict bump positivity follows from the same-owner support-inside theorem and
`Real.exp_pos`; the phase is transferred into the coarse phase rectangle; the
family-4 coefficient-phase real part is strictly negative; the other 29
families are removed by the exact 3217 support identity; and the positive
`weightedExternal3201` exponential factor preserves strict negativity. The
resulting `record2680_first_center_weighted_value_upper3218` proves the cell-0
hvalue premise with upper 0. This is not yet a producer certificate: the other
40959 cell value bounds, second/fourth derivative bounds, sixth-derivative
norm bounds, and the signed finite aggregate are still open.

A boundary probe for the last diagnostic midpoint was rejected and removed:
`record2680Center3212 40959` is still inside the selected owner radius because
`storedWidth 4 ^ 2` is approximately `6.5536`, while the diagnostic radius is
only slightly larger. Therefore the outer cell's external `value_upper = 0`
row cannot be justified by support-zero at its midpoint; it remains a signed
Taylor upper with a nonzero local physical function. This preserves the same
owner/support boundary already found at cell 0 and rules out a shortcut based
on endpoint proximity.

Record 3219 formalizes the outer-boundary check: Lean proves
`|record2680Center3212 40959| < storedWidth 4 ^ 2`. Thus even the final
40960-grid midpoint is inside the selected owner's support. The theorem builds
and audits in WSL2 Lean 4.30.0 with exactly `[propext, Classical.choice,
Quot.sound]`. This closes the boundary fact as a reusable premise and confirms
that both end cells require signed Taylor bounds; support-zero cannot discharge
any endpoint midpoint in the current diagnostic grid.

Record 3220 closes the uniform sixth-derivative input for the concrete
record2680 owner. The theorem keeps the complex 30-family weighted sum intact,
uses the existing 2538 family-cell envelope with conservative near/far
parameters, applies exact support-zero outside each family radius, and then
projects to the real-valued producer function. It exports a nonnegative
`record2680UniformSixthBound3220` array wrapper accepted by the 3213 aggregate
shape for every index and coordinate. The focused WSL2 Lean 4.30.0 build and
axioms audit pass with exactly `[propext, Classical.choice, Quot.sound]`.
This changes the producer ledger by closing only the sixth-derivative array;
value, second-derivative, fourth-derivative, signed finite aggregate, and
full-line tail remain open.

Record 3226 closes the positive outer midpoint value upper. The proof mirrors
3218 with a positive-imaginary phase rectangle, proves exact family-4 support
reduction, and obtains a strictly negative coefficient-phase real upper; the
midpoint remains inside support, so this is not support-zero. Record 3227 wires
the two endpoint value bounds into the aggregate and reduces the remaining
value premise to interior indices `1` through `40958`. The internal signed
value array, finite aggregate, full-line tail, and `producer_go` remain open.

Record 3224 replaces the conservative uniform second/fourth derivative inputs
with cell-local bounds. It explicitly distinguishes a cell that crosses a
family support boundary from a midpoint that is outside that support; the
latter uses the exact derivative-zero theorem. Record 3225 wires these local
jets, together with the verified uniform sixth bound, into the 40960-cell
aggregate. The aggregate now has only the signed midpoint `valueUpper` array
as an explicit premise. This is the correct cancellation-preserving boundary;
the value array, finite signed aggregate, full-line tail, and producer gate
remain open.

Record 3222 proves same-owner uniform second- and fourth-derivative bounds for
the concrete record2680 correction using the 2538 family envelope. Record 3223
wires those bounds, together with 3220's sixth bound, into the 40960-cell
aggregate. The aggregate interface now has only the midpoint `valueUpper`
array as an explicit per-cell premise. This is not yet a negative finite
aggregate: the uniform derivative geometry is deliberately conservative and
may lose the observed signed margin. The next numerical/formal target is a
cell-local value/jet certificate that preserves cancellation.

Record 3221 wires the verified 3220 uniform sixth bound into the fixed-grid
40960-cell aggregate theorem. The resulting adapter no longer asks for a
sixth-derivative array or its nonnegativity; only the concrete value, second-
derivative, and fourth-derivative arrays remain as aggregate premises. The
focused WSL2 Lean 4.30.0 build and audit pass with exactly
`[propext, Classical.choice, Quot.sound]`. This is an interface reduction,
not yet a negative finite aggregate or producer result.

Record 3228 closes one genuine interior signed midpoint value premise at
`record2680Center3212 40958`. The proof reuses the family-4 phase rectangle
method from the endpoint chain, but separately proves exact family-4 support
reduction at the interior midpoint and proves the midpoint bump is positive
by an explicit rational support inequality. The focused WSL2 Lean 4.30.0
build and axioms audit pass with exactly `[propext, Classical.choice,
Quot.sound]`. This removes one interior array entry only; the remaining
interior value array, finite signed aggregate, full-line tail, `producer_go`,
`SourceRH`, and RH remain open.

Record 3229 extracts the reusable family-4 signed midpoint kernel and closes
the adjacent interior values at `record2680Center3212 40956` and
`record2680Center3212 40957`. The kernel takes
exact family-4 support reduction, a negative coefficient-phase real upper,
and positive support as premises, then derives the weighted value upper `<= 0`.
The 40957 phase uses a wider formal rectangle `[0.8, 1] x [0.2, 0.5]` than
3228 because repeated axis-aligned interval squaring widens the enclosure;
the coefficient product remains strictly negative. Focused WSL2 Lean 4.30.0
build and axioms audit pass with exactly `[propext, Classical.choice,
Quot.sound]`. The remaining interior array, finite signed aggregate,
full-line tail, `producer_go`, `SourceRH`, and RH remain open.

Record 3230 wires the verified right-band values for indices `40956`, `40957`,
and `40958`, together with both endpoint values, into a new aggregate adapter.
Its remaining midpoint premise excludes exactly `{0, 40956, 40957, 40958,
40959}` and is required only for the other 40955 cells. The focused WSL2 Lean
4.30.0 build and axioms audit pass with exactly `[propext, Classical.choice,
Quot.sound]`. This reduces the aggregate interface but does not prove its
finite sum negative, close the full-line tail, or set `producer_go`.

Records 3231-3232 build the first multi-family interior enclosure bridge at
`record2680Center3212 17168`, the most negative diagnostic cell. Lean proves
the point bump interval for every one of the 30 families using only the owner
definition and scaled exponential Taylor bounds, then proves each phase and
family contribution rectangle and the exact 30-family aggregate membership.
The independent axis-aligned aggregate rectangle is deliberately not claimed
to have negative real upper: it loses shared phase/cancellation information.
This identifies the next root cause for the producer: the final value proof
needs a correlated signed evaluator, not a sum of independently widened family
rectangles. Focused WSL2 Lean 4.30.0 builds and audits pass with exactly
`[propext, Classical.choice, Quot.sound]`; `producer_go` remains open.

The 3231 bump interval was tightened after the first enclosure screen: its
upper endpoint now uses the same point-specific `tAdd` exponential Taylor
upper as the lower endpoint, rather than the uniform `exp(-30)` pin. The
independent 30-family rectangle screen consequently drops from an estimated
upper of about `59934` to about `52`, but still does not certify the observed
negative midpoint. The remaining loss is phase/cancellation correlation, so
the next evaluator must preserve shared phase error instead of summing
independent axis-aligned family rectangles.

Record 3233 adds `ComplexNormBall3233`, a center-plus-radius complex enclosure
using the standard complex norm.
Its sum theorem accumulates one shared norm error radius and its multiplication
theorem propagates product error without replacing the final signed aggregate
by independent real/imaginary rectangles. The generic definitions and audit
build under WSL2 Lean 4.30.0 use exactly `[propext, Classical.choice,
Quot.sound]`. This is an enclosure primitive, not yet a negative numerical
bound.

Record 3234 connects the existing 30-family `17168` midpoint rectangles to
that correlated-ball interface. Lean proves each family contribution is in
the ball obtained from its existing rectangle, and proves the full signed
30-family aggregate is in the sum ball. The rectangle endpoint ordering is
now discharged structurally: every `ComplexRect2427.mul` output is ordered,
and the bump/phase/power order lemmas are separately available. An attempted
direct `fin_cases` plus large `norm_num` discharge of all endpoint facts was
stopped after more than ten minutes of high-CPU expansion; it was removed and
left no running Lean process. The structural bridge and axiom audit rebuilt
successfully in WSL2.

Record 3235 adds `ComplexTaxiBall3235`. This uses the rational-friendly
taxicab norm `|re| + |im|`, proves its triangle and multiplicative bounds, and
supports center-preserving addition, multiplication, and finite sums.
Focused WSL2 Lean 4.30.0 build and audit pass with exactly the standard axiom
trio.

Record 3236 connects the taxi-ball evaluator to the actual Route-A owner at
`17168`: the scaled phase Taylor remainder, the midpoint bump interval, all
30 owner family products, and the signed aggregate are formally enclosed.
The phase power is transferred back through the exact 512th-power identity;
the bump coercion is proved directly from its existing interval certificate.
Focused WSL2 Lean 4.30.0 build and audit pass with exactly the standard axiom
trio. A direct full aggregate `norm_num` sign screen was attempted but left
an enormous unresolved rational absolute-value expression, so it was deleted
and is not evidence of a sign. No negative aggregate sign, remaining midpoint
array, full-line tail, producer GO, SourceRH, or RH claim follows.

Record 3237 resolves the apparent contradiction between the 3204 external
negative window diagnostic and the 3236 owner midpoint evaluation. The Lean
target used by records 3208-3230 is `weightedExternal3201 sigma`, namely the
real part of `exp (sigma * x) * externalPhysical2344 x`. In contrast, the
Python `jets` function used by 3204 starts at `raw[j + 2]`; its `jets(...)[0]`
is the second derivative of the weighted family, not the weighted function
value. Consequently, 3204's `value_upper`, its Taylor terms, and its negative
aggregate price the integral of the weighted second derivative (with the
corresponding higher derivative remainder), while the Lean aggregate theorem
prices the integral of the weighted original function. The 3204 negative
number cannot discharge the `hvalue` premise of records 3225 or 3230.

Record 3236 encloses `externalPhysical2344` itself, but does not yet multiply
the taxi ball by the real weight and does not prove a sign. At the diagnostic
midpoint `17168`, independent reproduction gives approximately `52.2935` for
the unweighted owner real value and `88.8289` for the sigma `-1/2` weighted
real value; the old `-38.0161` row is therefore a second-derivative diagnostic,
not an original-function value. The next producer step is an object-alignment
decision: either build a correlated Lean certificate for the weighted original
function and prove its 40960-cell aggregate negative, or explicitly move the
producer target to the second-derivative channel and prove the exact integration
by parts and detector interface needed by that channel. Do not copy the 3204
negative array into the current weighted-original-function aggregate.

The current `producer_go` dependency chain is therefore: aligned integrand
identity; all-cell weighted midpoint/jet certificates; negative finite signed
aggregate; full-line tail bound for the same owner and integrand; exact B5
readback; then the producer theorem. `producer_go`, `SourceRH`, and RH remain
false.

Record 3238 corrects the external evaluator to the formal integrand instead
of the second-derivative diagnostic. It computes the original weighted
function jets, with `raw[j]` rather than `raw[j + 2]`, on the same concrete
owner, sigma `-1/2`, and 40960-cell grid. The upward-rounded Taylor-6 window
upper is approximately `-1.4151657848627206e-8`, with a sixth-order remainder
of approximately `1.4593071872206805e-14`. A coarser 2560-cell run is positive
at approximately `3.563796884971633e-6`, so the fine grid is not cosmetic: it
is needed to control the boundary derivative budget. The minimum 40960-cell
upper occurs at index `16923` and is approximately `-0.0267471569005385`.

This is still external Arb evidence: no JSON row is imported into Lean, no
all-cell midpoint/jet array is proved, and no full-line tail or B5 readback is
closed. It does restore the correct numerical target and justifies continuing
Route A with the weighted-original-function evaluator. The next formal step
is a same-owner weighted correlated-ball theorem, starting from the existing
3236 unweighted midpoint enclosure and an explicit exponential weight interval.

Record 3239 closes that first formal weighted-original-function step at
`record2680Center3212 17168`. It builds an explicit order-30 Taylor interval
for `exp ((-1/2) * midpoint)`, multiplies that real weight ball with the
existing 3236 same-owner correlated taxi ball, and proves membership for the
actual `weightedFunction2348` applied to `externalPhysical2344`. A generic
real-part projection then yields a formal upper bound for the exact
`weightedExternal3201` value. The theorem does not claim the midpoint upper is
negative; its purpose is object alignment and a reusable weighted enclosure.
The focused WSL2 Lean 4.30.0 build completed successfully and the audit for
all three new theorems reported exactly `[propext, Classical.choice,
Quot.sound]`. The remaining midpoint array, finite aggregate sign, full-line
tail, B5 readback, and `producer_go` remain open.

Record 3241 extracts the index-independent weighted component bridge from the
fixed 3239 midpoint proof. The generic theorem
weighted_owner_taxi_ball_mem_of_component_balls3241 multiplies a weight ball
and an owner aggregate ball while preserving one shared taxicab-norm error
radius; weighted_owner_value_upper_of_component_balls3241 then projects the
final ball to the real weightedExternal3201 upper. The concrete theorem
record2680_middle_point_weighted_value_upper_via_bridge3241 reuses the existing
3239 weight ball and 3236 same-owner aggregate ball at index 17168. The 3240
aggregate adapter now imports 3241 and calls this bridge theorem. Focused
WSL2 Lean 4.30.0 builds of 3241 and 3240 and their audits passed with exactly
[propext, Classical.choice, Quot.sound]. This is an interface reduction, not
a negative sign result: 40954 midpoint value certificates, the strict finite
aggregate, the same-owner full-line tail, and exact B5 readback remain open.
See docs/proofs/3241_routea_weighted_taxi_ball_bridge.md.Record 3241 now also exposes the cell-facing facade
weighted_owner_value_upper_of_component_members3241. Given one weight ball,
family-indexed bump balls, family-indexed phase balls, and their three
membership proofs, it constructs the 30-family aggregate ball and returns the
weightedExternal3201 real upper in one theorem. The focused build and audit
still pass with exactly [propext, Classical.choice, Quot.sound]. This is the
next reusable unit for covering the remaining 40954 midpoint values; it does
not yet instantiate any new cell or prove the finite signed aggregate.Record 3241 additionally exposes weighted_owner_phase_ball3241 and
weighted_owner_phase_ball_mem3241. These reuse the existing exact 512-fold
phase identity and require only the explicit scale condition
|(capturedModulations2584 family * x) / 512| <= 1. The phase theorem audits to
the standard axiom trio. The remaining cell-specific work is now concentrated
in the weight interval, bump interval, and signed aggregate endpoint bound.Record 3241 now includes the generic weight interval
weighted_owner_weight_ball3241 and its membership theorem
weighted_owner_weight_ball_mem3241 for arbitrary sigma and x under
|sigma * x| <= 1. The bridge API therefore covers arbitrary-cell weight,
phase, family aggregation, and final real projection. Focused build and
axioms audit pass with the standard trio. Cell-specific bump enclosures and
the signed aggregate are still the binding numerical obligations.

Record 3243 adds a real-part-preserving rectangle interface for the strongly
cancelling weighted-original-function cell 16923. It replaces the independent
taxicab-ball sign experiment with `ComplexRect2427` interval multiplication:
the exact coefficient point, the cell-specific bump interval, and the exact
512-fold phase rectangle are multiplied family by family and then summed.
Lean proves bump, phase, family, and aggregate rectangle membership, and exports
the exact unweighted physical real-part upper as the aggregate rectangle's
`reHi`. The focused WSL2 Lean 4.30.0 build and audit pass with exactly
[propext, Classical.choice, Quot.sound]. A direct 30-family `norm_num` sign
closure was intentionally not retained: it exceeded the practical heartbeat
budget, so 3243 is an enclosure interface rather than a negative certificate.

Record 3244 screened the concrete owner family terms at the actual strongest
3204 Taylor-6 diagnostic cell 17168 using the existing 192-bit Arb evaluator.
The contiguous five-family block uppers were approximately 149622.0804,
10.2088, -779289.2658, 516789.7806, -5868.8726, and -65.2596, with total
midpoint upper approximately -118801.3282. A first attempt to prove six
five-family ComplexRect2427 block signs by fully unfolding the 3243 rectangles
was rejected: Lean 4.30.0 exceeded the simplifier step limit even after
10,000,000 heartbeats. The failed files were removed. The next formal target
is a family-level rectangle endpoint lemma at 17168, followed by sign-aware
grouping based on the exact rectangle bounds; midpoint screening is not a
Lean certificate and is not imported into Lean.

Record 3247 proves the exact shared-bump cancellation identity for families
8 through 29 at midpoint 17168. Their storedWidth values are definitionally
the same rational, so the physical sum is exactly common_bump multiplied by
the coefficient-phase aggregate. The module proves shared width, bump and
phase aggregate rectangle membership, shared block membership, and the exact
target equality. WSL2 Lean 4.30.0 audit passes with exactly the standard trio.

Direct sign expansion of the 22-family phase rectangle, and even a five-family
phase subblock, was then rejected as a simplifier-step no-go under 10,000,000
heartbeats. The next formal unit is therefore a set of local phase endpoint
lemmas, not another larger norm_num expansion. The shared-bump identity remains
the correct cancellation-preserving producer boundary.

Record 3245 moves the rectangle interface to the correct strongest Taylor-6
cell 17168. It reuses the audited 3231 bump interval and 3236 phase/taxi-ball
objects, proves bump, phase, family, aggregate rectangle membership, and the
unweighted real-part upper. A WSL2 ext4 Lean 4.30.0 lake build and audit pass
with exactly [propext, Classical.choice, Quot.sound]. It remains an enclosure
interface, not a sign result.

Record 3246 rejects direct family endpoint sign expansion. Even family 10 alone
hit Lean 4.30.0 simplifier step exhaustion after roughly 183 seconds under a
10,000,000-heartbeat focused build. The failed files were removed. The next
producer-facing evaluator must preserve coefficient-phase cancellation before
applying a shared positive bump envelope; repeating full rectangle expansion
for 30 families is not an acceptable route.
The next step is a smaller sign-aware block decomposition with local `reHi`
thresholds; the finite aggregate, full-line tail, exact B5 readback,
`producer_go`, `SourceRH`, and RH remain open.

Record 3251 adds a generic staged repeated-squaring API for the Route A phase
rectangle. `complexRectPowSq_staged_mem3251` separates the mechanical product
rectangle at each squaring layer from a separately checked outer rectangle, so
future family-specific endpoint lemmas do not unfold the full Taylor evaluator
and all nine products in one simplifier call. The structural bridge and audit
must be run in WSL2 with Lean 4.30.0; no numerical phase box or sign is claimed
by this record, and `producer_go` remains false.

Record 3256 now verifies the family-10 tight staged phase enclosure at cell
17168. The initial box remains the exact rational Taylor-rectangle target, but
stages 1 through 9 were recomputed from the actual four-corner products in
`ComplexRect2427.mul` and rounded outward at approximately `1e-15` resolution.
The previous `1e-12` stage-1 lower endpoint was above the mechanical product
lower bound by about `1.2e-12`, so it was not a valid enclosure. The corrected
module builds in WSL2 ext4 with Lean 4.30.0; its audit reports exactly
`[propext, Classical.choice, Quot.sound]` for the base, step, and final phase
theorems. This verifies only the family-10 phase box. The coefficient-phase
aggregate sign, the full-line tail, B5 readback, `producer_go`, `SourceRH`, and
RH remain open.
Record 3257 extends the corrected staged enclosure route to families 8 and 9
at cell 17168. The first generated endpoints were rejected because the
midpoint generator used `17169 / 2`; the owner definition requires
`17168 + 1 / 2 = 34337 / 2`. After correction, both families pass the base
Taylor membership, all nine four-corner repeated-squaring steps, and the final
512-fold phase membership in WSL2 Lean 4.30.0. Their exact coefficient-point
rectangles and the pair-sum membership also pass. Family 8 alone has a proved
strict coefficient-phase real upper `reHi < 0`. The 8+9 pair is intentionally
not given a sign theorem because family 9 contributes positively at this cell.
The audit contains only `[propext, Classical.choice, Quot.sound]`; no `sorry`
or `error` appears in the focused logs. This is progress toward the signed
coefficient-phase aggregate, but the complete families 8..29 aggregate, shared
bump, tail, B5 readback, `producer_go`, `SourceRH`, and RH remain open.
Record 3258 starts the negative candidate at cell 2825 with an owner-specific
family-8 phase box. The first generated 2825 propagation was rejected by Lean:
the center-error estimate did not contain the four-corner interval product.
The accepted version computes each staged rectangle from the previous
rectangle's exact `RealInterval2429.mul` corners and adds an explicit outward
margin. The focused WSL2 ext4 Lean 4.30.0 build succeeds, and the audit for
the scale, base, nine staged steps, and final phase theorem reports exactly
`[propext, Classical.choice, Quot.sound]`. This is only a mechanical family-8
enclosure; the 22-family aggregate, signed physical-kernel budget, full-line
tail, B5 readback, `producer_go`, `SourceRH`, and RH remain open.

Record 3259 completes the cell-2825 coefficient-phase aggregate sign by
splitting all 22 family `reHi` endpoint bounds into independent Lean modules.
Each family module imports only its own corrected tight staged phase box and
proves its rational upper bound with `norm_num`; the focused batch builds in
WSL2 ext4 with `leanprover/lean4:v4.30.0`. A thin aggregation module then uses
`Finset.sum_le_sum`, expands the finite `Fin 22` sum before arithmetic
normalization, and proves the aggregate rectangle has `reHi < 0`. The
independent audit reports exactly `[propext, Classical.choice, Quot.sound]`.
This is a verified coefficient-phase aggregate at cell 2825 only. It does not
prove the shared positive bump budget, the signed physical-kernel/C3' bound,
the full-line tail, B5 readback, `producer_go`, `SourceRH`, or RH.

Record 3260 connects the verified cell-2825 aggregate to the actual owner
value and preserves the shared-bump identity. The aggregate module now proves
that the 22-family coefficient-phase rectangle contains the exact owner phase
sum, and therefore proves its actual real part is strictly negative. A new
module proves that every test-indexed family from 8 through 29 has the same
stored width and rewrites the exact physical family sum as one common bump
value multiplied by that same negative phase sum. Both the focused build and
the independent audit pass in WSL2 ext4 with Lean 4.30.0 and exactly
`[propext, Classical.choice, Quot.sound]`. This still does not prove the
2825 bump is positive, pay the signed physical-kernel/C3' budget, close the
full-line tail, establish B5, or set `producer_go`.

Record 3261 closes the named cell-2825 mechanism as a support no-go. Lean
proves that the exact cell center lies outside `storedWidth 8 ^ 2`, so the
shared bump is exactly zero; using the 3260 identity, the actual 22-family
physical block is exactly zero as well. Thus the strictly negative
coefficient-phase aggregate at 2825 is physically inactive and cannot pay any
signed physical-kernel/C3' budget. The focused WSL2 ext4 Lean 4.30.0 build and
audit pass with exactly [propext, Classical.choice, Quot.sound]. Do not spend
more phase-box work on 2825 unless the owner support or center definition
changes; this is not a global Route A no-go.

Record 3262 promotes the support check for the formal Route-A candidate cell
17168 into an independent theorem. For every stored family, Lean proves
`|record2680Center3212 17168| < storedWidth family ^ 2`; it also proves the
family-8 bump is strictly positive. The focused WSL2 ext4 Lean 4.30.0 build and
axiom audit pass with exactly [propext, Classical.choice, Quot.sound]. This
closes the support prerequisite for the 17168 weighted-original route, but it
proves no negative value, finite aggregate, tail, C3' budget, B5 readback,
`producer_go`, SourceRH, or RH.

Record 3263 factors the formal weighted-original candidate block at cell
17168 for families 10 through 14. Lean proves the five families have one
stored width and proves the exact owner-preserving identity
`weighted block = common positive weight * common bump * coefficient-phase
block`. This preserves signed cancellation and avoids five independent
physical rectangles. The WSL2 ext4 Lean 4.30.0 build and audit pass with
exactly [propext, Classical.choice, Quot.sound]. Record 3265 supersedes the
proposed strict-upper-bound target: the corrected coefficient-phase block is
strictly positive, so this grouping is not a negative contribution. No
finite aggregate, tail, C3' budget, B5 readback, `producer_go`, SourceRH, or
RH is claimed.

Record 3264 extends the corrected staged repeated-squaring phase enclosure to
families 11 through 14 at cell 17168. The explicit rational rectangles use
outward margins and are checked from the Taylor phase rectangle through all
nine stages. The focused WSL2 ext4 Lean 4.30.0 build succeeds, and the
independent audit for all four base/final phase theorems reports exactly
[propext, Classical.choice, Quot.sound]. This is phase infrastructure only;
it does not claim a block sign.

Record 3265 corrects the sign target for the 17168 family block 10..14. The
3244 screen used the legacy `jets[0]` path from the second-derivative
evaluator, while the formal 3263 factorization targets the weighted original
function. Using the 3264 phase boxes and exact owner coefficient points, Lean
proves the conservative lower bound
`coefficient-phase block 10..14 >= 200000000000000000`, hence strict
positivity. The focused WSL2 ext4 Lean 4.30.0 build and independent audit pass
with exactly [propext, Classical.choice, Quot.sound]. Because the remaining
exponential weight and shared bump are positive at 17168, this grouping cannot
pay the needed negative C3' budget. Keep 3264 as reusable enclosure
infrastructure, but do not pursue a negative upper bound for 10..14.

Record 3266 replays the family screen with the formal weighted-original
evaluator from 3238, not the legacy second-derivative path from 3244. At cell
17168 the complete midpoint family sum has upper approximately `+88.8289`,
so 17168 is not a negative local target for the formal object. At cell 16923,
the complete midpoint family sum has upper approximately `-83.5854`; the
contiguous block uppers are approximately `62.81`, `-0.48`, `-395.17`,
`250.05`, `-0.70`, and `-0.10`. This is diagnostic only, but it changes the
next formal target: use 16923 for the corrected family/block grouping screen,
while retaining 17168 only as reusable phase infrastructure. The finite-window
aggregate, full-line tail, B5 readback, `producer_go`, SourceRH, and RH remain
open.

Record 3271 closes the next local enclosure step at cell 16923. Instead of
summing independent coefficient-phase rectangles, it groups exact
same-modulation families before multiplying by a phase rectangle. The groups
`0,1,4`, `2,3`, and zero-frequency `5,6,7` use one shared phase; the other
families retain their own phase boxes. Lean 4.30.0 membership proofs and the
independent sign audit pass with exactly
`[propext, Classical.choice, Quot.sound]`. The four diagnostic blocks
`5..9`, `10..14`, `20..24`, and `25..29` each prove `reHi < 0` at cell 16923.
This remains a local cell certificate: the 40960-cell finite aggregate,
tail bridge, B5 readback, `producer_go`, `SourceRH`, and RH remain open.

Record 3272 corrects the physical weighting gap in 3271. The physical family
term is `coefficient * bump(radius, center) * phase`, and the family-specific
bump cannot be pulled outside a correlated coefficient-phase enclosure when
stored widths differ. 3272 first encloses coefficient times bump for each
family, then combines same-modulation families, and only then multiplies by
the shared phase rectangle. At cell 16923, Lean proves membership for all six
five-family block rectangles `0..4`, `5..9`, `10..14`, `15..19`, `20..24`, and
`25..29`. The strict real upper endpoint is negative for blocks `5..9`,
`10..14`, `20..24`, and `25..29`. The focused WSL2 ext4 Lean 4.30.0 build
and independent audit are required to report exactly
`[propext, Classical.choice, Quot.sound]`; this is still only a local
value-level certificate. The 40960-cell finite aggregate, full-line tail,
signed physical-kernel/C3' budget, B5 readback, `producer_go`, `SourceRH`,
and RH remain open.

The 3272 physical-sign bridge is also complete. For each negative
bump-correlated block `5..9`, `10..14`, `20..24`, and `25..29`, Lean derives
the exact physical block's real part `< 0` from the certified membership
theorem and the rectangle endpoint theorem. This removes the semantic gap
between “the enclosure endpoint is negative” and “the enclosed physical value
is negative”; it does not enlarge the result to the 40960-cell aggregate or
any tail, derivative, or B5 obligation.

Record 3273 generates the complete 40960-row sidecar for the corrected
weighted-original Taylor-6 evaluator from 3238. The sidecar uses the exact
formal target, sigma `-1/2`, 192-bit Arb, and upward `10^-80` rounding. Its
replay audit checks all 40960 grid rows, midpoint identities, continuity,
Taylor-6 formulas, rounded fields, and exact aggregate closure; it passes with
the same negative total and minimum cell 16923. This is external evidence
only: the JSONL is not imported into Lean, so the Lean per-cell midpoint
enclosure proofs and the formal 40960-cell aggregate remain open.

The 3274 prototype tested extending the 3272 bump-aware rectangles across all
six five-family blocks at cell 16923. Directly asking `norm_num` to unfold the
full rectangle, the 30th-order finite exponential sums, and all nested
`min`/`max` endpoint conditionals leaves unsolved goals even after increasing
`maxRecDepth`. This is a proof-generation scalability boundary, not a
mathematical sign result. Do not use one-shot full-rectangle unfolding for the
40960-cell certificate; generate explicit rational endpoint manifests and
verify them with smaller Lean arithmetic lemmas.

Record 3275 implements the first small manifest interface for that plan. It
defines the cell-16923 full bump-correlated rectangle as the nested sum of the
six existing 3272 block rectangles and proves, by definitional reduction, that
its real upper endpoint is the sum of the six block real upper endpoints. A
second theorem accepts six independently proved block upper bounds and returns
the corresponding full-rectangle upper bound by linear arithmetic. The
focused WSL2 ext4 Lean 4.30.0 build and axiom audit pass with exactly
`[propext, Classical.choice, Quot.sound]`.

The attempted one-shot numerical proof in the same prototype was removed after
it reached a deterministic 200000-heartbeat `simp` timeout while expanding all
30 family endpoints. This confirms that the next productive unit is one group
or one block endpoint manifest lemma, not a larger global `norm_num` call.
The 3275 interface is structural only: it does not yet prove the six numeric
endpoint bounds, full cell value membership, the 40960-cell aggregate, or any
downstream Route A producer conclusion.

Record 3277 adds the finite-cell rational certificate interface.  It defines a
rational weight rectangle, a rational family-rectangle sum, and the derived
cell upper endpoint.  If a cell's weight interval contains
`exp((-1/2) * center)` and every one of its 30 family rectangles contains the
corresponding formal family value, Lean derives the midpoint `hvalue` for
that cell.  A second theorem maps all 40960 such local premises into the
existing Taylor-6 finite aggregate theorem.  No JSON, floating-point value,
or unproved numeric manifest is imported by this layer.  The focused WSL2
ext4 build under Lean 4.30.0 passed, and the four audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.  The actual 40960 weight,
phase, bump, and family endpoint premises are still open; therefore this
record is an interface and closure bridge, not the completed aggregate proof.

Record 3278 adds the first reusable rational weight generator.  `RatInterval3276.powNat`
and its membership induction lift a rational interval through powers.  The
new `ratTaylorExp60_mem3278` theorem combines the audited two-sided Taylor pin
`expTwoSided2676` with the identity `exp(60*x) = exp(x)^60`: a rational
interval containing the Taylor sum plus/minus error for `|x| <= 1` yields a
rational interval containing `exp(60*x)`.  This is the intended range-reduced
weight route because every diagnostic midpoint satisfies the small-argument
condition after dividing the exponent by 60.  The focused WSL2 ext4 Lean
4.30.0 build and audit pass with exactly `[propext, Classical.choice,
Quot.sound]`.  No concrete 40960-cell weight manifest is claimed yet.

Record 3287 closes the per-cell rational bump enclosure. The proof uses the
same rational radius and absolute center as the formal owner, proves the bump
argument is nonpositive, and delegates active cells to the audited central or
tail interval. Inactive cells use the exact zero interval. The final evenness
step is proved by sq_abs. The focused WSL2 ext4 Lean 4.30.0 build and audit
pass with exactly [propext, Classical.choice, Quot.sound].

Record 3288 defines the cell-family rectangle from the exact coefficient,
cell bump interval, and nine-stage rational phase rectangle. Active families
reuse the 3282 canonical-family theorem. Inactive families use a separate
zero path: the bump interval is [0,0], rectangle multiplication reduces to
the zero rectangle, and the owner family value is zero by its support
condition. The focused WSL2 ext4 build and audit pass with exactly
[propext, Classical.choice, Quot.sound].

Record 3289 defines the rational midpoint weight with x equal to the negative
midpoint divided by 120, encloses exp(x) with the 30-term Taylor interval,
and raises that interval to the 60th power. The proof establishes |x| <= 1
for every index below 40960 and rewrites exp(60*x) to the formal
exp((-1/2) * center). The focused WSL2 ext4 build and audit pass with exactly
[propext, Classical.choice, Quot.sound]. These records close the local weight
and family containment generators, but the 40960-cell aggregate closure,
derivative-bound premises, full-line tail, B5 readback, producer_go,
SourceRH, and RH remain open.

Record 3290 instantiates the formal 3277 cell-certificate interface with the
3288 family rectangles and 3289 weight intervals. It proves every midpoint
upper bound and invokes the existing 3225 derivative infrastructure, yielding
an actual Lean theorem for the interval integral to be bounded by the
40960-term Finset.sum of Taylor-6 cell uppers. The WSL2 ext4 Lean 4.30.0 build
and independent audit pass with exactly [propext, Classical.choice, Quot.sound].

A direct Record-3291 experiment attempted to prove the sign of the full
40960-term rational midpoint sum with native_decide. It consumed about 4 GB
and remained active for more than 15 minutes. A 256-cell block reduced the
term count but showed the same repeated rectangle-expansion bottleneck. Both
experimental files were removed because they were not compiled artifacts.
The next numerical step must use a generated, independently checked endpoint
manifest or a new optimized rational evaluator; do not use a JSON sidecar as
an imported Lean conclusion. The full Taylor-6 aggregate sign remains open.

Record 3293 adds the final manifest-consumer bridge. Given a Lean-checked
per-cell endpoint function that dominates ratCellValueUpper3289 and a Lean
proof that the corresponding Taylor-6 Finset.sum is strictly negative, it
proves the full interval integral is strictly negative. The proof uses
monotonicity of the nonnegative grid step and Finset.sum_le_sum. Its WSL2
ext4 Lean 4.30.0 build and independent audit pass with exactly
[propext, Classical.choice, Quot.sound].

The formal 40960-cell aggregate objective is now closed at the upper-bound
level by Record 3290: all 40960 midpoint certificates are generated from the
3288 and 3289 containment theorems, and Lean closes them through the existing
Taylor-6 Finset.sum theorem. This does not claim that the resulting finite
sum is negative; that is a separate numerical sign certificate consumed by
3293, and the full-line tail, B5 readback, producer_go, SourceRH, and RH remain
open.

Record 3294 adds an external 160-block manifest for the 3273 weighted-original
40960-cell JSONL, using blocks of 256 cells. The generator replays the grid,
upward 10^-80 rounding, Taylor-6 cell formula, and exact aggregate before
writing block sums. It reports 66 negative blocks and 94 nonnegative blocks;
the exact finite-window aggregate remains negative. The manifest does not
claim that its values dominate `ratCellValueUpper3289`, and it is not imported
into Lean.

Record 3295 adds the 2353 correction-owner contour tail to the 3294 finite
window. The external rational replay remains negative, approximately
-1.415165773137461e-8. This is same-owner numeric evidence only; the tail
supplier, finite endpoint dominance, signed full-line kernel, producer_go,
SourceRH, and RH remain open.

The Lean 3294 module adds a generic range-to-160-block decomposition and a
block-manifest consumer theorem. The consumer requires explicit endpoint
dominance, per-block upper bounds, and a negative block-bound sum, so no JSON
number is silently promoted to a theorem. Focused WSL2 ext4 Lean 4.30.0 build
and audit passed; both audited declarations use exactly
[propext, Classical.choice, Quot.sound].

The required `python scripts/mathlib_brick_check_2049.py` check was rerun before
using `Finset.sum_range_add`; it completed and wrote
`results/2049_mathlib_brick_check.json`. A direct Lean `#check` in the same
Lean 4.30.0 WSL environment resolved `Finset.sum_range_add` with the expected
finite-range shift theorem.

Record 3296 added an exact `Fraction` mirror of the 3289 rational endpoint.
The repository filename was corrected from the stale `C1RouteARationalBump3287`
path to `C1RouteARationalCellBump3287`. A one-cell exact run exceeded five
minutes without producing a value, so direct Fraction expansion is not an
acceptable 40960-cell evaluator and must not be used as a Lean certificate.

Record 3297 added a high-precision Decimal mirror for magnitude diagnosis. It
shows the current 3289 endpoint is close to the 3273 Arb upper near the negative
minimum (index 16923 gap about 5.06e-31), but fails endpoint dominance badly in
support-edge regions: index 12000 gives about +34.40 versus Arb -0.1426, and
index 15000 gives about +39.01 versus Arb -4.4187. The named obstruction is
the 3285 tail branch, which uses a uniform exp(-38) upper bound. Multiplied by
the approximately 1e14 owner coefficients, that bound destroys signed
cancellation. Record 3297 is a diagnostic no-go for consuming the 3294
manifest through the current 3289 endpoint; it is not imported into Lean and
does not claim producer_go, SourceRH, or RH.

Record 3298 repairs that obstruction with a `t`-dependent tail ladder: Taylor
interval powers at denominators 8, 16, 32, and 64, followed by an `exp(-94)` tail
for `t < -64`. It also projects each coefficient-phase rectangle to a real
interval before multiplying by the nonnegative bump, preserving signed real
cancellation. A Decimal diagnostic at all 160 block-start indices found no
dominance failure; the largest sampled gap was about 2.75e-23. This remains
external diagnostic evidence only.

The Lean 3298 modules prove the tight bump containment, real coefficient-phase
projection, 30-family real interval sum, and per-cell endpoint dominance. The
focused WSL2 ext4 Lean 4.30.0 builds completed at 3958, 3959, and 3961 jobs;
independent audits for the declarations report exactly
[propext, Classical.choice, Quot.sound].

Record 3299 connects `ratCellValueUpperTight3298` to the existing 40960-cell
Taylor-6 integral upper theorem. Its focused WSL2 ext4 Lean 4.30.0 build
completed at 3968 jobs and its audit reports the standard axiom trio. The new
40960-term endpoint sum has not yet been replayed or shown negative in Lean, so
the 3294 external block manifest is still not consumable by 3299.

Record 3300 completes the first external replay of the 3298 endpoint over all
40960 cells. The endpoint-only Decimal sum is approximately
-4.42239757055052677353400699803e-5. Reusing the existing 3238 derivative
rows and applying the exact `record2680CellUpper3209` formula shape gives the
new finite-window diagnostic aggregate
-1.415165784862719484304109681996e-8. The replay has 160 contiguous blocks of
256 cells, 40960 formula rows, and 62 negative blocks. Exact summation of the
serialized Decimal rows, block fractions, and total closes in the structural
audit. The largest positive block is approximately +3.1975547438816613 and
the largest negative block is approximately -3.7521994713139876, so signed
block cancellation is required.

The artifacts are `results/3299_routea_tight_endpoint_manifest.json`,
`results/3299_routea_tight_cell_manifest.json`, and
`results/3299_routea_tight_manifest_audit.json`; the generators are
`scripts/routea_tight_endpoint_manifest_3299.py`,
`scripts/routea_tight_cell_manifest_3299.py`, and
`scripts/audit_routea_tight_manifest_3299.py`. This is still external
diagnostic evidence: the endpoint arithmetic uses Decimal `ROUND_HALF_EVEN`,
not directed rounding, and no JSON value is imported into Lean. The next
formal target is a directed-rounding endpoint/block manifest plus a Lean
consumer proving dominance of `ratCellValueUpperTight3298` and a strictly
negative block-bound sum. Full-line tail, B5 readback, `producer_go`,
`SourceRH`, and RH remain open.

Record 3301 upgrades the endpoint replay to outward Decimal interval arithmetic:
lower operations use `ROUND_FLOOR`, upper operations use `ROUND_CEILING`, and
each final endpoint is rounded upward to the exact `10^-80` grid. The 40960
cells were evaluated in eight chunks, merged after index/grid checks, and then
attached to the existing Taylor-6 derivative rows. The directed external
aggregate is approximately
-1.41516578486271948430410968199638e-8. Its audit passes with 40960 formula
rows, 160 contiguous blocks, exact serialized row/block/total closure, and 62
negative blocks. Artifacts:
`results/3300_routea_directed_endpoint_manifest.json`,
`results/3300_routea_directed_cell_manifest.json`, and
`results/3300_routea_directed_manifest_audit.json`; scripts:
`scripts/routea_tight_directed_endpoint_manifest_3300.py`,
`scripts/merge_routea_directed_endpoint_manifest_3300.py`, and
`scripts/audit_routea_tight_manifest_3299.py`. This remains external evidence:
the directed replay is not imported into Lean. The Taylor-6 cell recombination
uses exact rational arithmetic over the serialized endpoint grid and existing
rational derivative rows, so no second Decimal rounding is introduced. The next
formal target is an
exact Lean endpoint/block certificate for `ratCellValueUpperTight3298` and the
strictly negative block-bound sum. Full-line tail, B5 readback, `producer_go`,
`SourceRH`, and RH remain open.

Record 3302 adds a Lean arithmetic mirror of the directed 3301 block manifest.
`routeADirectedBlockUpper3302 : Fin 160 -> Rat` contains the 160 serialized
rational block constants, and Lean proves both their rational sum and their
real-cast sum are strictly negative.  The focused WSL2 ext4 Lean 4.30.0 build
and audit use the standard axiom trio.  This is arithmetic only: it does not
show dominance over `ratCellValueUpperTight3298` and does not import JSON.

Record 3303 adds the tight-endpoint block consumer.  The adapter
`routeADirectedBlockUpper3302Real : Nat -> Real` is zero outside the 160-block
range and agrees with the `Fin 160` manifest on valid indices.  The module
proves exact equality of the natural-range sum and the finite `Fin` sum, then
provides `intervalIntegral_record2680_40960_strict_upper_of_tight_block_manifest3303`.
This consumer keeps `ratCellValueUpperTight3298` as the endpoint object and
requires only the explicit 160 per-block dominance inequalities.  The focused
WSL2 ext4 build completed at 3974 jobs; its independent audit completed at 3975
jobs and reports exactly `[propext, Classical.choice, Quot.sound]`.

A first-block `norm_num` probe was not retained because it expanded the 256
tight endpoint rows but stopped at the existing 3224 derivative rows.  Those
rows contain `Real.exp` and non-rational bump upper expressions, so the 3302
rational constants cannot be consumed by definitional reduction alone.  The
next named obligation is therefore a rational upper envelope for the derivative
rows, followed by the 160 explicit `hblock` proofs.  No finite-window strict
negative Lean theorem, full-line tail, B5 readback, `producer_go`, SourceRH, or
RH claim is made.

Record 3304 is a named no-go for consuming the directed 3302 manifest through
the existing 3224 derivative rows.  The 3224 rows are absolute-value family
majorants, while the 3302 rows retain signed family cancellation.  An Arb
diagnostic using the same owner and Taylor-6 formula checked all 160 blocks:
every formal 3224 block upper is strictly above its directed manifest block
constant.  The smallest gap is approximately 6.385559487775981e-12 and the
largest is approximately 6.1361560960921005e-2.  The result is external
diagnostic evidence only and is recorded in
`results/3304_formal_derivative_block_no_go.json`.

Record 3305 adds
`intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3305`.
This Lean consumer keeps `ratCellValueUpperTight3298` and the signed block
manifest shape, but accepts second-, fourth-, and sixth-derivative upper rows
as explicit premises instead of hard-wiring the 3224 absolute-value rows.  It
therefore isolates the next real obligation: a same-owner signed derivative-row
provider plus 160 block dominance proofs.  The WSL2 ext4 Lean 4.30.0 build
completed at 3975 jobs; the independent audit completed at 3976 jobs and
reports exactly `[propext, Classical.choice, Quot.sound]`.

Record 3306 adds
`weightedExternal3306_real_jet_le` and the selected-owner instances
`record2680_signed_real_second_bound3306` and
`record2680_signed_real_fourth_bound3306`. The provider decomposes the exact
owner derivative into a signed center jet plus coefficient-error jets. It keeps
`real(center sum)` intact and charges only the errors by
`sum(error_i * norm(unit jet_i))`, so it does not repeat the 3224
family-by-family absolute-value loss. The concrete record 2680 rows use the
owner coefficients as centers and zero errors. The WSL2 ext4 Lean 4.30.0
provider build completed at 3940 jobs and the independent audit completed at
3941 jobs; all audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`.

3306 does not close the 3305 consumer. The sixth-order premise still asks for a
complex norm upper bound, and the 160 signed block dominance inequalities remain
open. The formal route is now:

```text
3306 signed real second/fourth rows
        |
        v
3305 parameterized signed block consumer
        |
        +--> open: same-owner sixth-order norm provider
        +--> open: 160 block dominance proofs
```

Record 3307 is superseded. Its probe used
`abs(real(signed aggregate jet))`, which discarded the sign of negative
derivative rows and was not the corrected 3306 upper shape. The historical
result is retained for reproducibility, but it is not a current no-go.

Record 3308 reruns the block screen with the corrected
`real(signed aggregate jet)` rows. The total of the 160 corrected block uppers
is approximately `-1.312998292365491e-8`, while 110 individual blocks are
above the old 3302 constants. This means the old manifest is too tight for the
corrected derivative-row object, but the aggregate sign remains viable. The
next named target is a new outward-rounded 160-block manifest, followed by its
Lean arithmetic mirror and consumer. The diagnostic script is
`scripts/routea_signed_real_upper_block_probe_3308.py` and the result is
`results/3308_signed_real_upper_block_probe.json`; neither is imported into
Lean.

The 3307 Arb replay used the installed Windows Python 3.13 `flint` runtime
because the WSL2 system Python lacked `flint` and the configured package mirror
did not provide it during the run. This environment exception applies only to
external diagnostic evidence; the 3306 Lean provider and its audit still ran in
the required WSL2 ext4 Lean 4.30.0 workspace.

Record 3309 converts the corrected 3308 signed-real block uppers into a new
outward-rounded 160-block manifest. The generator
`scripts/routea_signed_real_upper_manifest_3309.py` rounds each source value
upward to the common `10^-80` grid, records the 3308 source hash and rounding
slack, and rejects a nonnegative aggregate. The rounded exact sum is
`-656499146182745501736821251496030290980612928457864067127693217116763489 /
50000000000000000000000000000000000000000000000000000000000000000000000000000000`,
approximately `-1.312998292365491e-8`; the maximum rounding slack is about
`4.09e-81`.

The Lean arithmetic mirror
`C1RouteARationalCorrectedSignedBlockManifest3309.lean` proves the rational
sum and real-cast sum are negative. The new consumer
`C1RouteARationalCorrectedSignedBlockConsumer3309.lean` wires the 3306 signed
real second/fourth bounds, the 3220 sixth-order norm row, the 3298 tight
endpoint, and the 3309 block adapter into the 3305 parameterized theorem. Its
four audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.

WSL2 ext4 Lean 4.30.0 verification completed at 3970 jobs for the manifest
audit and 3979 jobs for the consumer audit. The remaining formal obligation is
still the 160 explicit `hblock` inequalities: the external 3308 Arb rows are
not imported into Lean, and the current cell expressions contain transcendental
and interval-bound terms that require a separate rational envelope proof.

Record 3310 begins the rational signed-jet interval bridge. The bump interval
module `C1RouteARationalSignedJetInterval3310.lean` defines the exact rational
polynomial numerator for derivative orders 0 through 6 and combines it with
the existing 3298 outward interval for the bump exponential. The theorem
`ratBumpJetInterval_mem3310` proves containment for every positive rational
radius and every rational position, including the inactive support branch. The
unused position-in-interval hypothesis was removed so inactive family centers
outside the bump support remain admissible.

The rectangle module `C1RouteARationalSignedJetRect3310.lean` adds:

```text
lambda singleton rect + weight interval + phase power rect
        |
        v
per-order bump derivative rect
        |
        v
weighted unit-jet term rect
        |
        v
finite derivative-order sum rect
        |
        v
coefficient-weighted physical family rect
        |
        v
256-cell physical block rect
```

The active branch uses the rational lambda power, 3289 weight interval,
3279 phase power rectangle, and 3310 bump interval. The inactive branch proves
the bump rectangle is exactly zero and uses exact rectangle zero multiplication;
it does not require a phase enclosure. The block theorem
`ratWeightedPhysicalBlockRect_mem3310` currently proves the structural
256-cell complex-rectangle containment for every `block < 160` and every
derivative order at most 6.

The independent audit
`C1RouteARationalSignedJetRect3310Audit.lean` reports exactly
`[propext, Classical.choice, Quot.sound]` for the 3310 interval, per-term,
family-sum, physical-sum, and block-sum declarations. WSL2 ext4 Lean 4.30.0
builds completed at 3962 jobs for the interval target, 3964 jobs for the
rectangle target, and 3965 jobs for the rectangle audit. Build logs are
`results/3310_signed_jet_interval_build.log`,
`results/3310_signed_jet_rect_build.log`, and
`results/3310_signed_jet_rect_audit_build.log`.

3310 still does not prove any 3309 manifest inequality. The next named bridge
is a real-part projection from each block rectangle to a rational upper bound,
followed by a block-0 comparison against
`routeACorrectedSignedBlockUpper3309`; only after that prototype succeeds
should the comparison be generated for all 160 blocks.

Record 3311 adds `C1RouteARationalSignedJetRealUpper3311.lean`. It defines
`ratWeightedPhysicalBlockRealUpper3311` as the `reHi` endpoint of the 3310
block rectangle and proves the real-part upper-bound theorem needed by the
3309 `hblock` consumer. The focused WSL2 ext4 Lean 4.30.0 build completed at
3973 jobs, and the independent audit reports exactly
`[propext, Classical.choice, Quot.sound]` for both the general order theorem
and its order-0 specialization.

The companion block-0 probe attempted to evaluate the exact 3310 rational
rectangle directly through Lean's interpreter. It produced no value within
180 seconds even after reducing the probe to order 0, so direct interpreter
evaluation is not an acceptable numeric producer for the 256-cell block.
This is a tooling/performance boundary, not a mathematical no-go. The next
numeric target is a generator-side rational manifest for the 3310 `reHi`
values, followed by a small Lean arithmetic mirror and the block-0 comparison;
do not expand all 160 blocks in the kernel before that comparison passes.

The finer-grained follow-up also timed out: evaluating a single cell,
`ratWeightedPhysicalRect3310 0 0`, through `lake env lean --run` produced no
value within 120 seconds. Therefore the bottleneck is the interpreter's
reduction of the nested exact-rational interval products themselves, not only
the 256-cell block sum. Any future numeric producer must use a compiled
evaluator or an independently audited generator-side interval implementation;
more interpreter probes are not productive.

Record 3311 now has a generator-side Arb probe
`scripts/routea_signed_jet_rect_arb_probe_3311.py` and a block comparison
driver `scripts/routea_signed_jet_block_compare_3311.py`. The probe mirrors the
finite rational structure of 3310 using Arb endpoints, then converts each
upper endpoint to an exact rational. For block 0 and orders 0, 2, and 4, it
combines those rows with the existing directed endpoint and uniform sixth row.
The resulting 3310-derived block upper is approximately
`2.22511792783590538e-27`, while the 3309 target is approximately
`6.38555948777598357e-12`; the target therefore dominates by about 15 orders
of magnitude. This is external generator evidence, not yet a producer
certificate.

Record 3329s adds signed singleton interval endpoint rules in
`C1RouteARationalSignedInterval3329.lean`: multiplying a point interval by an
ordered interval selects `c * hi` when the singleton coefficient is
nonnegative and `c * lo` when it is nonpositive. Both declarations build and
audit under Lean 4.30.0 with exactly the standard axiom trio. This matches the
stored coefficient rectangles, whose real and imaginary coordinates are
singletons, and is the first retained endpoint rule that preserves coefficient
sign instead of replacing it with an absolute value.

`C1RouteARationalSignedJetBlockComparison3311.lean` records both block-0
values after upward rounding to the common `10^-80` grid and proves their
exact rational comparison with `norm_num`. Its WSL2 ext4 Lean 4.30.0 build
completed at 3970 jobs. The independent audit
`C1RouteARationalSignedJetBlockComparison3311Audit.lean` is required to check
that the comparison theorem uses only the standard axiom trio; the theorem
proves only the arithmetic comparison of the recorded constants and does not
import the Arb calculation as a theorem.

The same prototype was then run for block 1. Its generator-side upper is
approximately `1.57087137373338338e-27`, versus the 3309 target
`6.38555948777598292e-12`, so block 1 also passes with a margin of roughly 15
orders of magnitude. The Lean arithmetic mirror is
`C1RouteARationalSignedJetBlock1Comparison3311.lean`; its audit is
`C1RouteARationalSignedJetBlock1Comparison3311Audit.lean`. These two blocks
are still local validation only; no 160-block manifest or producer theorem is
claimed.

Record 3312 ran the Arb generator across all 160 blocks and rendered the upward-rounded constants into `C1RouteARationalSignedJetBlockManifest3312.lean`. The exact rational sum of those recorded constants is proved strictly negative, and its independent audit reports exactly `[propext, Classical.choice, Quot.sound]`. The generator also found that 50 of the new rectangle-derived block uppers are larger than the old 3309 block manifest values; therefore the old manifest cannot be used as the consumer target for the 3310 rectangle bounds. The new aggregate remains strictly negative, but this is not a proof of the block inequalities.

`C1RouteARationalSignedJetBlockConsumer3312.lean` now exposes the correct consumer boundary. It feeds the 3312 block constants into the existing 3305 aggregate theorem, while keeping all 160 inequalities as an explicit `hblock` premise. Its WSL2 ext4 Lean 4.30.0 build completed at 3978 jobs, and `C1RouteARationalSignedJetBlockConsumer3312Audit.lean` reports exactly `[propext, Classical.choice, Quot.sound]` for the sum bridge, strict-negative sum, and interval-integral consumer. This closes the Lean plumbing only; the remaining formal bottleneck is to prove each real block cell sum is bounded by its corresponding 3312 constant using an auditable Arb-to-rational certificate or a fully internal Lean derivation.

Record 3313 adds `scripts/verify_routea_signed_jet_manifest_3313.py`, an
independent replay check for the 3312 generator artifact. It verifies all 160
block indices, exact Fraction parsing, upward rounding to 10^-80, inward-round
rejection, recorded aggregate equality, and the presence of the 160-entry Lean
manifest. The replay passes with the exact recorded aggregate
`-1415165784607358228138426130120484001944986633817436027685162235071038723 /
10^80`. This is an artifact-consistency check only; `arb_enclosure_proved`
remains false and the 160 Lean `hblock` inequalities remain open.

Record 3314 introduces a decomposed per-block certificate format through
`scripts/routea_signed_jet_block_certificate_3314.py`. Each 256-cell block
stores four independently named contributions: endpoint, second-order,
fourth-order, and sixth-order. The companion
`scripts/verify_routea_signed_jet_block_certificate_3314.py` replays every cell
term from the stored `step` and input upper bounds, recomputes all four sums,
recomputes the source total, and checks the exact upward rounding. Blocks 0 and
1 both pass this stronger replay. Their recorded block uppers match the 3312
manifest entries, while `arb_enclosure_proved` remains false. This is now a
reproducible generator-side certificate shape, but not yet a Lean proof that
the Arb-derived input upper bounds enclose the corresponding Lean expressions.

Record 3315 refines the 3314 certificate boundary. The Arb probe now exposes
`cell_family_rects`, and each block certificate stores 30 family-level real
upper endpoints for both the second- and fourth-order rows in every cell. The
replay verifier checks the family count and exact family sum before rebuilding
the weighted cell terms. Regenerated block 0 and block 1 certificates both
pass. This confirms the family-to-cell arithmetic decomposition, while the
underlying Arb enclosure of each family rectangle is still not imported into
Lean; `arb_enclosure_proved` remains false.

Record 3316 adds a compact all-block family-aggregated certificate in
`scripts/routea_signed_jet_family_manifest_3316.py`. Each of the 160 blocks
stores the endpoint sum, 30 second-order family sums, 30 fourth-order family
sums, sixth-order sum, reconstructed second/fourth contributions, source, and
outward-rounded block upper. The replay script
`scripts/verify_routea_signed_jet_family_manifest_3316.py` recomputes all these
relations exactly. An initial equality check correctly exposed extra outward
rounding from family-level aggregation on blocks 19..140. The verifier was
then changed to the sound monotonic condition: the family-aggregated upper may
be lower than the earlier cell-aggregated upper, but must never exceed it. All
160 blocks pass this condition, and the aggregate remains approximately
`-1.4151657846073583e-8`; the family aggregation is more conservative by about
`4.24e-58` in total. This is a stronger generator-side decomposition, not a
Lean enclosure proof; `arb_enclosure_proved` remains false.

Record 3317 adds the Lean-side family decomposition bridge in
`C1RouteARationalSignedJetFamilyBridge3317.lean`. It proves that the
`reHi` endpoint of a 3310 physical cell rectangle is the finite sum of the 30
family-term `reHi` endpoints, that a block rectangle `reHi` is the sum of its
256 cell endpoints, and that the block endpoint is therefore the nested
cell/family sum. The focused WSL2 ext4 Lean 4.30.0 build completed at 3965
jobs; the independent audit reports exactly `[propext, Classical.choice,
Quot.sound]` for all three declarations. This closes the formal algebraic
composition needed by the family certificate. It does not yet prove that the
external Arb family endpoints enclose the corresponding Lean rectangles, so
the 160 `hblock` inequalities remain open.

## Record 3319: generator correspondence failure

The 3311 Arb evaluator used `taylor_interval(-center / 120)` directly for
the cell weight. Lean's `ratCellWeightInterval3289` raises that interval to
the 60th power. The evaluator also used Python `min` and `max` on Arb balls,
whose overlapping comparisons do not provide a total order, and grouped the
jet rectangle multiplications differently from 3310. These discrepancies
invalidate claims that the historical 3311, 3312, 3314, or 3316 generated
endpoints enclose the 3310 Lean rectangles. The exact rational negativity of
the recorded 3312 constants and its conditional consumer theorem remain valid;
neither establishes the missing endpoint inequalities.

The separate 3311 single-block comparison script also used indices 0..255 for
the derivative rows regardless of the selected block. Its historical block-1
comparison therefore is not a block-1 computation. The script now uses the
selected block's actual cell indices. The all-block driver had its own correct
index range, but remains affected by the evaluator discrepancies above.

The 3311 evaluator now uses the 60th power, Arb interval `min`/`max`, and the
3310 multiplication grouping. `scripts/test_routea_signed_jet_arb_3319.py`
checks the weight against exp(3) at center -6 and checks product extrema for
overlapping input balls. These checks are not a Lean proof of enclosure.
The earlier record 3316 description of a lower upper bound as "more
conservative" is incorrect: a smaller upper bound is tighter, and has no
enclosure meaning without a proof.
The corrected 192-bit, 160-block diagnostic completed with an upper-endpoint
sum of approximately -1.4151657848627195e-8. Compared with the historical
3311 block endpoints, 68 corrected endpoints are larger, 26 equal, and 66
smaller. Fifty corrected unrounded block values exceed their 3309 comparison
targets. These are external diagnostic comparisons, not Lean enclosures or a
proof that the historical block constants bound the Lean expressions.
The 2049 Mathlib brick checker was rerun successfully; it reports the listed
bricks present except the von Neumann trace inequality.

The existing 3318 cell-0, order-2, family-4 leaf was checked in the WSL ext4
workspace after syncing the source and `lean-toolchain`, and Lean reported
version 4.30.0. The check failed at line 13 with `simp` maximum steps exceeded;
the log also reports local changes in three dependency repositories. No axiom
audit was run for this failed leaf. The WSL status file is empty, so the
recorded error log, not that status file, is the evidence for the outcome.

Record 3320 adds a Lean-verified inactive-family reduction in
`C1RouteARationalSignedJetInactive3320.lean`. If a cell center is outside the
same family's squared support radius, every jet rectangle is exactly the zero
rectangle, so the weighted physical family rectangle and its `reHi` endpoint
are exactly zero. The focused WSL2 ext4 Lean 4.30.0 build completed and the
independent audit passed for the generic zero theorem, its `reHi` projection,
the concrete cell-0/family-0 zero case, and the concrete cell-0/family-4
active-boundary check. All four declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

This removes inactive family terms only after a Lean proof of the exact
support inequality is supplied; the external count of inactive combinations
is diagnostic and is not imported as a theorem. It does not yet provide the
active-family endpoint enclosures required by the 3318 certificate boundary.

The same 3320 module now also instantiates the active cell-0/family-4 chain:
Lean proves the weighted phase rectangle contains its target phase value and
the order-2 bump rectangle contains the corresponding second derivative. The
proof uses the existing rational-to-real cast lemmas explicitly; an initial
attempt without those casts failed and was corrected. The two new declarations
also pass the standard three-axiom audit. These are membership lemmas, not
upper-endpoint inequalities; the active family endpoint remains open.

Record 3323 adds `C1RouteARationalSignedJetEndpointDecomp3323.lean`, proving
the exact order-2 decomposition of a family sum into the three indices 0, 1,
and 2, followed by coefficient multiplication. The focused WSL2 ext4 Lean
4.30.0 build and audit pass with exactly the standard axiom trio. This is a
structural reduction for endpoint certification; it does not assert a numeric
bound for the active terms.

A direct experiment showed that `native_decide` can evaluate the concrete
cell-0/order-2/family-4 endpoint and that its `reHi` is at most 10^-14 but not
at most 10^-15. That proof was rejected and removed because the audit exposed
the extra `native_decide` axiom. Kernel `decide` gets stuck on the rational
comparison, and whole-expression `norm_num` still exceeds its simplifier
step limit. The 3321 and 3322 probe logs document this distinction; they are
diagnostics, not accepted certificates.

Record 3325 adds a kernel-checked interval multiplication bound in
`C1RouteARationalEndpointBounds3325.lean`. The upper endpoint of a rational
interval product is bounded by the product of the two endpoint absolute-value
bounds, avoiding direct reduction of nested `min`/`max` expressions. The
focused WSL2 ext4 Lean 4.30.0 build and independent audit pass with exactly
`[propext, Classical.choice, Quot.sound]`. This is reusable bound
infrastructure; it does not yet instantiate the active family numerical
certificate.

Record 3326 extends the interval bound to complex rational rectangles: the
real upper endpoint of a rectangle product is bounded by twice the product of
the two coordinate-wise absolute endpoint bounds. Record 3328 proves the
matching subadditivity of the rectangle absolute endpoint bound. Record 3329
combines these with the exact order-2 three-jet decomposition to obtain a
generic family `reHi` bound from the coefficient rectangle and the three jet
rectangle absolute bounds. All focused WSL2 Lean 4.30.0 builds and audits pass
with exactly the standard axiom trio.

The attempted direct cell-0/family-4 coarse certificate was deliberately not
retained: the absolute-value bound discards the signed phase cancellation and
does not close the target 10^-14 endpoint. This confirms the next mathematical
step is a correlated or sign-aware endpoint certificate, not further widening
of the absolute-value bound.

Record 3332 was repaired after a failed focused build identified one misspelled
identifier in the certificate consumer: `ratWeightedUnitRect3310` was corrected
to the existing `ratWeightedUnitJetRect3310`. The WSL2 ext4 Lean 4.30.0 build
then completed successfully, and the independent audit reported exactly
`[propext, Classical.choice, Quot.sound]` for the coefficient-sign theorem,
the generic family-4 signed endpoint equality, the concrete cell-0/order-2
signed equality, and the certificate consumer. The consumer still accepts an
explicit active-support hypothesis, but Lean reports it as unused because the
current theorem is a pure algebraic implication from the supplied endpoint
bound; this is intentional interface scaffolding, not an enclosure proof.

A follow-up endpoint probe was not retained. Explicitly unfolding the active
support branch still left the four-level `ratTailBumpInterval3298` selector
(`t/8`, `t/16`, `t/32`, `t/64`) and its large Taylor-power expressions. Raising
the simplifier step limit to one million did not close the rational inequality.
The evidence therefore rejects whole-expression unfolding as the next route.
The next endpoint lemmas must first prove the selected tail branch and local
sign/magnitude facts, then compose interval endpoint rules without expanding
all Taylor powers in one tactic call. No new endpoint enclosure was proved in
this probe.

Record 3330 extends the signed singleton interval rules to all four endpoint
directions (`hi`/`lo` crossed with nonnegative/nonpositive singleton). Record
3331 proves the exact complex rectangle formula for a singleton coefficient:
`reHi = max(cRe * b.reLo, cRe * b.reHi) -
min(cIm * b.imLo, cIm * b.imHi)`. Record 3332 instantiates the formula for
family 4, whose real and imaginary coefficient coordinates are both negative,
and proves the cell-0/order-2 signed `reHi` equality after deriving the needed
rectangle endpoint order from the existing membership theorems. The focused
WSL2 Lean 4.30.0 build and independent audit pass with exactly the standard
axiom trio. The resulting equality is a genuine endpoint reduction, but the
final rational inequality for that active family is still open.

Record 3335-3337 isolates the active cell-0/family-4 bump control flow. Exact
kernel-checked rational arithmetic proves that `|t / 8| > 1` and `t < -64`
for `t = ratBumpT3286 (storedWidthRat3287 4 ^ 2)
|record2680CenterRat3279 0|`. Therefore `ratTailBumpInterval3298` selects its
final fallback interval `[0, base^188.hi]`, rather than the `t/8`, `t/16`,
`t/32`, or `t/64` scaled branches. The selector theorem and fallback equality
pass an independent audit with exactly `[propext, Classical.choice, Quot.sound]`.

Record 3336 proves, for this same cell/family/order, that the order-2 bump
rational factor is nonnegative and gives a reusable lower-endpoint lemma for
the product of two coordinate intervals whose four endpoints are nonnegative.
Record 3337 composes these facts with the fallback tail and proves the exact
endpoint equality `(ratBumpJetInterval3310 2 radius position).lo = 0` for
cell 0/family 4. Its focused WSL2 ext4 Lean 4.30.0 build and independent audit
pass with the standard three axioms. This is a genuine endpoint component,
not yet a bound for any complete jet rectangle or family sum.

Record 3339 reuses the same fallback selector to prove the order-0 bump
endpoint is exactly zero for cell 0/family 4. The resulting structural
real-bump multiplication lemma gives
`(ratWeightedUnitJetRect3310 2 2 0 4).reLo ≤ 0` for index 2. The focused WSL2
ext4 Lean 4.30.0 build and independent audit pass with exactly the standard
three axioms. At this point indices 0 and 2 have signed real lower-endpoint
nonpositivity; index 1 and the complete signed family bound remain open.

Record 3340 resolves the remaining order-2 real lower-endpoint sign for the
cell-0/family-4 jet. The raw cell center is negative, so the order-1 numerator
`-60 * (position / radius)` is nonnegative; confusing it with the absolute
position used by the tail selector would reverse the sign. After fixing that
coordinate distinction, the fallback tail and nonnegative product factor give
the order-1 bump lower endpoint exactly zero, and the structural real-bump
lemma gives `(ratWeightedUnitJetRect3310 2 1 0 4).reLo ≤ 0`. The focused build
passes; independent axioms audit is the remaining check for this record.

Record 3341 composes the three audited lower-endpoint facts and proves the
order-2 cell-0/family-4 jet sum has `reLo ≤ 0`. This is useful sign metadata,
but it is not yet the desired upper bound: family 4 has a negative real
coefficient, so multiplying a nonpositive `reLo` contributes a nonnegative
term to the signed formula. The next proof must establish a quantitative lower
bound for the jet-sum real endpoint or a correlated bound with its imaginary
upper endpoint; sign-only information is insufficient for the 10^-14 target.
The focused build and independent audit pass with the standard three axioms.

Record 3342 adds a coordinate-wise signed endpoint bridge. For a singleton
coefficient with both coordinates nonpositive, the selected signed expression
`cRe * b.reLo - cIm * b.imHi` is bounded by
`(-cRe) * max(|b.reLo|, |b.reHi|) +
 (-cIm) * max(|b.imLo|, |b.imHi|)`.
The family-4 consumer is connected to the audited 3332 equality without
reconstructing the rectangle multiplication definition. Focused WSL2 Lean
4.30.0 build and independent axioms audit pass with exactly the standard
three axioms. The remaining missing inputs are numerical coordinate bounds for
the concrete three-jet sum; this bridge does not claim that those bounds meet
the `10^-14` target.

A concrete 3343 probe attempted to prove a deliberately loose `10^-100`
coordinate bound for the cell-0/family-4 three-jet by fully unfolding the
3310 rectangles. Even this loose target hit Lean's simplifier step limit after
124 seconds. The probe is not retained as a theorem. This confirms that the
remaining numerical coordinate bounds must be built from layered endpoint
lemmas (tail selector, Taylor powers, phase powers, and interval products),
not by one whole-expression `norm_num` call.

Record 3344 adds the reusable positivity layer needed by the fallback bump
proofs. It proves both endpoints of `ratBaseInterval3284` are nonnegative and
then proves recursively that the upper endpoint of `RatInterval3276.powNat a n`
is nonnegative whenever both endpoints of `a` are nonnegative. The focused
WSL2 ext4 Lean 4.30.0 build and independent audit pass with exactly the
standard three axioms. Records 3337, 3339, and 3340 now use this theorem
instead of repeatedly unfolding the 188-fold base power; their dependency
chain and the 3341 jet-sum consumer were rebuilt after explicit source
synchronization and passed.

Record 3338 adds the first structural jet-endpoint consumer. If a real bump
interval has lower endpoint zero, the real lower endpoint of multiplying any
complex rational rectangle by that real interval is at most zero. The proof
uses the explicit `min`/`max` definition of interval multiplication, so it
does not assume an ordering invariant that `RatInterval3276` does not store.
Instantiating the result with the audited 3337 bump endpoint proves
`(ratWeightedUnitJetRect3310 2 0 0 4).reLo ≤ 0`. The focused build and
independent audit pass with exactly `[propext, Classical.choice, Quot.sound]`.

Record 3345 adds the endpoint algebra needed to avoid unfolding concrete
products. For intervals with nonnegative ordered endpoints, it proves that
the upper endpoint of `RatInterval3276.mul` is exactly `a.hi * b.hi`; it also
proves recursively that the upper endpoint of `powNat a n` is `a.hi ^ n`.
The focused WSL2 ext4 Lean 4.30.0 build and independent audit pass with only
`[propext, Classical.choice, Quot.sound]`. The source emits one existing
unused-variable linter warning for `haLo`; this does not affect the proof.

Record 3346 instantiates 3345 for `ratBaseInterval3284`. It derives the
rational endpoint order from the audited real enclosure of `exp (-1/2)`,
proves `(powNat ratBaseInterval3284 n).hi = ratBaseInterval3284.hi ^ n`,
and rewrites the cell-0/family-4 fallback tail selector's upper endpoint as
`ratBaseInterval3284.hi ^ 188`. The focused WSL2 ext4 Lean 4.30.0 build and
independent audit pass with exactly `[propext, Classical.choice, Quot.sound]`.
This is still only an endpoint rewrite; it does not prove the complete
three-jet coordinate enclosure, the 160 block inequality, `SourceRH`, or RH.

Record 3347 proves the next concrete endpoint layer for cell 0/family 4.
For a fallback tail interval with lower endpoint zero and a nonnegative
singleton factor, its product upper endpoint is exactly the tail upper
endpoint times the factor. This gives exact upper-endpoint formulas for bump
orders 0, 1, and 2, after the fallback selector and the order-specific
nonnegativity facts are applied. The focused WSL2 ext4 Lean 4.30.0 build and
independent audit pass with exactly the standard three axioms. The formulas
are still bump-only: phase rectangles, lambda powers, signed coefficient
multiplication, and the final family/block margin remain open.

Record 3348 adds a first concrete phase endpoint bound. For the canonical
cell-0/family-4 phase rectangle, exact rational normalization proves
`ratRectEndpointAbsBound3326 <= 2`. The focused WSL2 ext4 Lean 4.30.0 build
and independent audit pass with exactly the standard three axioms. The bound
is intentionally a composable coarse input, not the final numerical margin;
the next layer must propagate it through `powSq 9` and the weighted phase
rectangle while preserving enough information for the signed family bound.

Record 3349 adds a generic complex-rectangle multiplication bound. If `A` and
`B` are the maximum absolute values of the four endpoints of two rational
rectangles, every endpoint of their product is bounded by `2 * A * B`.
The proof reduces the real part to interval multiplication plus subtraction,
the imaginary part to two interval products plus addition, and uses the
audited interval endpoint bounds from 3325. The focused WSL2 ext4 Lean 4.30.0
build and independent audit pass with exactly the standard three axioms.

Record 3350 tests the phase-power propagation strategy. Directly unfolding
the concrete cell-0/family-4 phase powSq 9 caused a million-character
arithmetic goal and did not close. The repaired theorem instead defines the
recursive coarse bound B(0) = 2 and B(n+1) = 2 * B(n) * B(n), then uses the
audited 3349 rectangle multiplication theorem inductively to prove the phase
powSq 9 endpoint bound. The focused WSL2 ext4 Lean 4.30.0 build and
independent audit pass with exactly the standard three axioms. This result is
structurally valid but deliberately too coarse for the final signed margin;
it identifies the next required refinement as a phase-specific correlated
bound rather than further generic absolute-value multiplication.

Record 3351 splits the concrete cell-0/family-4 canonical phase rectangle
into coordinate bounds. Exact rational normalization proves the maximum
absolute real endpoint is at most 1 and the maximum absolute imaginary
endpoint is at most 1/2. The focused WSL2 ext4 Lean 4.30.0 build and
independent audit pass with exactly the standard three axioms. These bounds
are stronger inputs than the single endpoint bound from 3348 and are intended
for a correlated phase-squaring layer; they still do not bound the final
powSq 9 rectangle or the signed family margin.

Record 3352 adds coordinate-wise propagation for squaring a rational complex
rectangle. It bounds each interval-product endpoint by the product of input
endpoint absolute-value maxima, then proves real <= R * R + I * I and
imag <= 2 * R * I from those interval bounds. Instantiating the result with
the cell-0/family-4 phase inputs from 3351 gives first-square bounds
real <= 5/4 and imag <= 1. The focused WSL2 ext4 Lean 4.30.0 build and
independent axiom audit pass with exactly the standard three axioms. This is
a valid correlated layer, but repeated squaring still needs tighter
phase-specific propagation before it can support the final signed family or
160-block margin.

Record 3353 packages the 3352 one-step square inequalities into a recursive
coordinate invariant for the full RatRect.powSq sequence. The real bound starts
at 1 and updates as R(n+1) = R(n) squared + I(n) squared; the imaginary bound starts at 1/2
and updates as I(n+1) = 2 * R(n) * I(n). Lean proves nonnegativity of both
recurrences and the cell-0/family-4 bounds for every n, including n = 9,
without unfolding the concrete rational rectangle. The focused WSL2 ext4
Lean 4.30.0 build and independent audit pass with exactly the standard three
axioms. The resulting bounds are structurally reusable, but their numerical
growth still must be checked against the signed family margin before they can
serve as the final endpoint certificate.

Record 3354 replaces the failed generic phase-power strategy with direct exact
rational endpoint normalization for the selected cell-0/family-4 phase. Lean
proves `ratRectEndpointAbsBound3326 (RatRect3276.powSq phase n) <= 2` for
every concrete prefix n = 2, 3, ..., 9; in particular the required n = 9
phase rectangle has endpoint absolute bound <= 2. Each theorem builds under
WSL2 ext4 with Lean 4.30.0, and the independent audit reports exactly the
standard three axioms. The earlier 3350/3353 bounds remain valid but are
numerically irrelevant for this owner because their generic recurrence grows
to about 7.2e89 at n = 9.

Record 3355 adds a concrete small bump endpoint for cell 0, family 4, order 2:
the upper endpoint of the selected rational bump interval is at most 10^-16.
The proof rewrites the selector and endpoint formula from 3335/3347, replaces
the 188-fold tail by the audited 3346 power identity, and closes the remaining
rational inequality with `norm_num`. Its independent audit passes with exactly
the standard three axioms. The next required lemma is a structural product
bound that combines this bump endpoint with the exact phase bound without
re-expanding the entire weighted jet expression.

Record 3356 adds the structural real-product endpoint bridge needed for that
composition. If a rational complex rectangle has real-coordinate absolute
bound A and a real interval has lower endpoint zero and nonnegative upper
endpoint b, then the real upper endpoint of their rectangle product is at most
A * b. The proof unfolds only the interval endpoint algebra and keeps the
complex rectangle abstract. The focused WSL2 ext4 Lean 4.30.0 build and
independent audit pass with exactly the standard three axioms. This bridge is
not yet the family certificate: a separate bound for the weighted phase
rectangle is still required before the 10^-14 jet target can be discharged.

Record 3357 adds a concrete endpoint bound for the active cell weight at cell
0. The proof first bounds the rational Taylor interval for the weight argument,
proves its endpoints are nonnegative and ordered, then applies the audited
nonnegative interval-power endpoint theorem before evaluating the remaining
rational power. The resulting endpoint absolute bound is:

```text
ratIntervalEndpointAbsBound3325 (ratCellWeightInterval3289 0) <= 32
```

This is a local cell-0 weight bound only. It is not a family certificate, a
block inequality, `SourceRH`, or the Riemann Hypothesis.

Record 3358 extends the real-product bridge to real intervals whose lower
endpoint is nonnegative rather than exactly zero. Combining that bridge with
the exact cell-0/family-4 phase bound from 3354 and the cell-weight bound from
3357 proves the local product endpoint:

```text
(RatRect3276.mul phasePowSq9 (ratRealRect3281 (ratCellWeightInterval3289 0))).reHi <= 64
```

The result removes the generic complex-product factor for this local weighted
phase term. It still does not bound the complete signed jet, family aggregate,
160-block inequality, `SourceRH`, or the Riemann Hypothesis.

The same record also proves the two-sided real-coordinate version: the maximum
of the absolute real lower and upper endpoints after multiplying by a
nonnegative real interval is bounded by the original real-coordinate bound
times the interval upper endpoint. This is the form needed before multiplying
the weighted phase rectangle by a bump interval.

Record 3360 adds the fieldwise commutativity lemma for multiplying a rational
rectangle by a real rational interval. It is proved on the four rectangle
coordinates with generic variables, so it does not unfold any concrete phase
or Taylor numerals. The focused WSL2 build succeeds; its separate audit is
the required bridge for rewriting the existing weighted-phase definition into
the phase-times-weight orientation used by the 3358 endpoint theorems.

Record 3361 applies that generic bridge to the existing weighted-phase
definition for every cell and family. It rewrites the stored
`weight * phase` rectangle into the equivalent `phase * weight` orientation,
without expanding the concrete cell data. This is the direct interface needed
to reuse the 3358 scaling bounds in the signed jet chain.

Record 3362 consumes the orientation theorem and the two-sided 3358 scaling
bound to prove the concrete weighted-phase coordinate endpoint for cell 0 and
family 4:

```text
ratRectRealCoordinateAbsBound3356 (ratWeightedPhaseRect3310 0 4) <= 64
```

This is the exact input needed to multiply the weighted phase by the small
order-2 bump interval without re-expanding the phase, weight, or Taylor power.

Record 3363 completes the selected local endpoint composition for cell 0,
order 2, index 0, family 4. It proves:

```text
(ratWeightedUnitJetRect3310 2 0 0 4).reHi <= 64 / 10^16
```

The proof is deliberately layered: it obtains the phase-rectangle order from
its audited membership theorem, proves the scalar-one rectangle identity,
uses the 3358 real-coordinate `reHi` bridge, and consumes the 3355 bump upper
endpoint. The focused WSL2 ext4 Lean 4.30.0 build and independent audit both
succeed; the audit reports exactly `[propext, Classical.choice, Quot.sound]`.
This is one local jet leaf only. It does not establish the complete family
certificate, any 160-block inequality, `SourceRH`, or the Riemann Hypothesis.
The next live work is to repeat the same decomposition for order-2 indices 1
and 2, then compose the three index endpoints with the signed cancellation
logic.
Record 3364 quantifies the active cell-0/family-4 order-1 bump endpoint:

```text
(ratBumpJetInterval3310 1 (storedWidthRat3287 4 ^ 2)
  (record2680CenterRat3279 0)).hi <= 10^-31
```

The focused WSL2 Lean 4.30.0 build and independent audit pass with exactly
the standard three axioms. The bound is deliberately rounded upward from the
exact rational endpoint and is used only as a compositional budget.

Record 3365 proves the selected order-2/index-1 weighted jet leaf:

```text
(ratWeightedUnitJetRect3310 2 1 0 4).reHi <= 10^-26
```

The proof bounds the lambda rectangle by 40, the weighted phase rectangle by
128 through the audited complex-product bridge, and the order-1 bump by 10^-31.
It then applies the real-coordinate `reHi` scaling bridge. The focused WSL2
build and independent audit pass with exactly the standard three axioms.

Record 3366 quantifies the active cell-0/family-4 order-0 bump endpoint:

```text
(ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
  (record2680CenterRat3279 0)).hi <= 10^-40
```

The focused WSL2 build and independent audit pass with exactly the standard
three axioms.

Record 3367 proves the selected order-2/index-2 weighted jet leaf:

```text
(ratWeightedUnitJetRect3310 2 2 0 4).reHi <= 10^-33
```

The proof uses a conservative lambda-squared endpoint budget, the same 128
weighted-phase bound, and the order-0 bump bound from 3366. The focused WSL2
build and independent audit both pass with exactly the standard three axioms.

Record 3368 composes all three selected order-2/index endpoints and proves the
local signed jet upper endpoint:

```text
(RatRect3276.add
  (RatRect3276.add
    (ratWeightedUnitJetRect3310 2 0 0 4)
    (ratWeightedUnitJetRect3310 2 1 0 4))
  (ratWeightedUnitJetRect3310 2 2 0 4)).reHi <= 10^-14
```

This is still a cell-0/family-4 local result. It is not yet the complete
30-family cell sum, the physical coefficient-weighted term, any 160-block
inequality, `SourceRH`, or the Riemann Hypothesis.
Record 3369 packages the selected cell-0/family-4 order-2 signed jet into one
local interval:

```text
signed jet reLo <= 0
signed jet reHi <= 10^-14
```

The lower endpoint comes from the earlier 3341 cancellation consumer, while
the upper endpoint comes from the newly audited 3368 composition. The 3369
focused WSL2 build and independent audit pass with exactly the standard three
axioms. This is now a complete local signed-jet interval for one family, not a
30-family cell certificate or a 160-block certificate.
Record 3370 adds the audited parameterized physical-term budget interface for
family 4. Given the signed-rectangle ordering and explicit real/imaginary
endpoint budgets for the order-2 weighted jet, it proves the coefficient-
weighted real endpoint is bounded by
`(-coefficient.reHi) * realBudget + (-coefficient.imHi) * imagBudget`.
This consumes the previously audited signed multiplication theorem 3342 and
preserves owner/family identity. It is not yet a numerical choice of the two
coordinate budgets and therefore does not close the cell-0 physical endpoint,
the 30-family sum, or any block certificate. The focused WSL2 Lean 4.30.0
build and independent audit pass with exactly the standard three axioms.
Record 3371 adds three small endpoint-budget bridges. The imaginary and real
coordinate absolute endpoint bounds used by the signed coefficient consumer
are each bounded by the full complex rectangle endpoint bound, and the
imaginary bound of a rectangle sum is bounded by the sum of the full endpoint
bounds of its summands. These are structural bridges, not a numerical budget:
they preserve the distinction between a coordinate bound and a full complex
rectangle bound. The focused WSL2 Lean 4.30.0 build and independent audit pass
with exactly `[propext, Classical.choice, Quot.sound]`.
