# 042 — G8 diagonal leg operator-bridge audit: what record 1497 supplies, what it does not, and the two remaining work orders

Date: 2026-09-16.

**Authority:** supporting.

**Status:** source-level interface audit. Zero new Lean, zero digits. The
complete selected-root source-Sonin leakage square-sum (record 1497) does
**not** supply either G8 diagonal energy hypothesis (`hSurvivor`,
`hBoundary`); the two operators share an owner and a word ("leakage") but
differ in left factor, input map, and an inserted ambient factor. The audit
fixes the exact committed operator chains, derives from committed
definitions that **every actual G8 metric coframe is of the form
`ambient ∘L sourceInclusion λ ∘L sourceSide`**, and uses that to split each
diagonal obligation into an **in-Sonin family** and a **leakage-band
family** on the source carrier. One consequence is ready for immediate
formalization: the survivor leg's out-of-Sonin half is already dominated by
record 1497 through bounded right precomposition. Both diagonal energy
obligations remain open; no estimate is claimed.

**Status update (2026-09-16, same day):** bricks S1, S2, B1, B2 are now
LANDED — S1/S2 in [1498](../proofs/1498_r3_survivor_coframe_source_bridge.md)
(`C1G8R3SurvivorCoframeBridge.lean`, unconditional
`hSurvivor ↔ in-Sonin square-sum`, OUT leg free via 1497), B1/B2 in
[1499](../proofs/1499_r3_boundary_output_factorization_bridge.md)
(`C1G8R3BoundaryOutputFactorizationBridge.lean`, exact per-output three-leg
split feeding the 1492 consumer unchanged). S3 and B3/B4 remain open; the
audit below is unchanged except for the §5 row markers.

**Status update (2026-09-16, second wave):** endpoint limit ρ4 is now
FORMAL GIVEN the survivor core (record 1502), and record 1504 makes the
remaining ρ5 identification an exact iff normal form. Record 1505 supplies
the Route-W window/tail decomposition, but its tail square-sum is still the
actual S3 mathematics. These bricks narrow the live obligations; they do not
prove the survivor or boundary estimates.

**Status update (2026-09-16, S3 assembly):** record 1506 formally removes
the already-controlled prolate-range leg from S3. The exact range-plus-
Fourier-leakage identity now supplies the full band-root square-sum from one
remaining hypothesis: square-summability of
`sourceRootCompletedRightCommutatorLeftLeg`. That hypothesis is still OPEN;
this is a reduction, not an S3 closure.

**Consumer:** the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](012_g8_same_owner_readback_rh_reachability.md)); the binding route in
[003](003_b1_b5_minimal_exit_route_selection.md) is unchanged.

**Status update (2026-09-17, formal no-go):** record [1512](../proofs/1512_hs_orthonormal_obstruction.md) and `C1G8R3HilbertSchmidtOrthonormalObstruction.lean` prove that the unprojected ambient leakage operator `sourceRootCompletedRightCommutatorLeftLeg` is not Hilbert--Schmidt on any Hilbert basis whenever the selected source Laplace value is nonzero. The proof transports any basis square-sum to the separated orthonormal translation orbit, whose leakage columns have a uniform positive lower bound. This removes the shortcut of feeding the ambient leakage operator directly as an S3 Hilbert--Schmidt factor. It does not close S3: the live target remains the Sonin-compressed gate `P C P`, and the projection may destroy the ambient obstruction.

**Status update (2026-09-17, second formal no-go):** the same orbit argument now proves `sourceRootCompletedBandRoot_not_hilbertSchmidt`: the full ambient `rootConvolution owner ∘L sourceBandProjection unitSoninScale` cannot have a square-summable diagonal on any Hilbert basis. Its committed range-plus-leakage decomposition has an HS range leg, which tends to zero on the separated orbit, and a leakage leg with a uniform positive lower bound. Thus the full ambient band-root cannot replace the source-compressed `P C P` target; the source projection remains essential for S3.

**Status update (2026-09-18, exact target audit):** record [1614](../proofs/1614_s3_operator_target_boundary.md) checks the definitions themselves: the ambient right-leg consumer is `C ∘ E ∘ (I − Q) ∘ E`, whereas the live survivor gate is the source-compressed `J† C J` completed Gram. The ambient non-Hilbert--Schmidt obstruction therefore blocks only the ambient shortcut; it neither closes nor refutes the source-compressed gate. The existing source-basis theorem for `((I − P) C J)` is also a different operator and cannot be substituted for the ambient right-leg consumer. S3 remains **OPEN**.

**Status update (2026-09-18, direct-kernel interface):** record [1615](../proofs/1615_source_compressed_root_kernel.md) introduces the actual source-carrier operator `J† C J` and its exact ambient matrix-coefficient readback. This is the chosen direct-kernel route for S3; it supplies no energy estimate, so S3 and B4 remain **OPEN**.

**Status update (2026-09-19, Hardy bridge and no-go):** records [1653](../proofs/1653_hardy_off_diagonal_hankel_factor.md) and [1654](../proofs/1654_hardy_off_diagonal_column_consumer.md) formally factor the Hardy defect and give a conditional bridge from off-diagonal columns to the ambient leakage consumer. Record [1655](../proofs/1655_hardy_off_diagonal_full_basis_no_go.md) then proves that the corresponding full-basis estimate is impossible at unit scale whenever the selected source Laplace value is nonzero, using the existing ambient non-Hilbert--Schmidt obstruction. This closes the global-HS shortcut; the live S3 producer remains the detector-specific source-compressed quadratic-energy estimate, and S3 is still **OPEN**.

**Status update (2026-09-19, source-Schur transport):** record [1704](../proofs/1704_survivor_source_leg_is_unit_s3_transport.md) and `g8SurvivorSourceLeg_isUnit` prove that the finite source-side Schur leg in the survivor coframe is an algebraic unit. The forward and reverse transition products multiply in both orders to the positive Schur--Markov scalar, while both Gram inverse-square-root factors are units. Thus the coframe transport is reversible at finite visible-prime level. This removes algebraic kernel-loss as an explanation for S3, but supplies no analytic square-summability estimate; S3 remains **OPEN**.

**Status update (2026-09-20, sharp S3 normal form):** record [1705](../proofs/1705_survivor_energy_iff_bare_source_compressed_energy.md) proves the coframe energy is equivalent, in both directions, to the bare source-compressed square-sum `sum ||J† C J e_i||²`. The equivalence uses the finite source-Schur unit and the existing bounded-precomposition transport, so no Schur/coframe factor remains in the analytic target. S3 remains **OPEN**, with only the detector-specific bare source-compressed energy estimate left.

**Status update (2026-09-20, projected-root endpoint):** record [1706](../proofs/1706_survivor_to_source_projection_endpoint.md) composes the bare source-compressed consumer with the Hardy/prolate normal forms. The survivor obligation is now exactly the square-summability of `P C J`, where `P` is the source Sonin projection; the Hardy compression and prolate remainder are equivalent bookkeeping layers, with the remainder already controlled. S3 remains **OPEN** at this projected-root estimate.

**Status update (2026-09-20, finite-window no-go):** record [1707](../proofs/1707_annular_trace_compact_window_bound_no_go.md) combines the projected-root finite-window criterion with the committed compact-kernel trace-growth theorem. Fixed-window Hilbert--Schmidt energy is available for every `n`, but its compact-kernel bound grows with window length and cannot supply the required uniform annular trace bound. The remaining producer must use the source carrier's coupled radial/Fourier geometry; an ambient compact-kernel or unwindowed norm bound is not a valid substitute. S3 remains **OPEN**.

**Independence audit (2026-09-16):** S3 and B3/B4 are best treated as one
total diagonal-energy producer with two currently separate estimates. The
same-owner positivity conclusion C3 is a downstream theorem of the readback
consumer, not a fourth independent analytic obligation. The remaining
independent producer obligations are therefore the total energy package and
the `rho5` aggregate-to-`qw` bridge.

## 1. The compared objects, quoted from committed source

Throughout, `C = rootConvolution owner`
(`CCM24FiniteSBandTrace.lean:36-39`), `J = sourceInclusion λ`
(`CCM24FiniteSGramResponse.lean:41-43`), `P = sourceSoninProjection λ`,
`E = radialSupportProjection λ`, `Q = sourceFourierSupportProjection λ`
(`CCM24FiniteSProjectionTrace.lean:94-103,230-238`), and `sourceBasis` is a
Hilbert basis of `sourceSoninCarrier λ`.

| Tag | Object | Committed shape | Site |
| :-- | :-- | :-- | :-- |
| O1 | record-1497 source-Sonin leakage | `Summable i, ‖((I − P) ∘L C ∘L J)(e_i)‖²` | `C1G8R3InternalProlateGapEnergy.lean:523-528` |
| O2 | survivor diagonal premise `hSurvivor` | `Summable i, ‖(C ∘L g8MetricSurvivorCoframe λ family)(e_i)‖²` | `C1G8R3PhysicalMetricCutoffTotalTraceLimit.lean:66-68` |
| O3 | boundary diagonal premise `hBoundary` | `Summable i, ‖(C ∘L g8MetricVisibleBoundaryCoframe λ family)(e_i)‖²` | `C1G8R3PhysicalMetricCutoffTotalTraceLimit.lean:69-71` |
| O4 | necessary-direction uncut compressed leg | `g8MetricGlobalDetectorRootLeg = C ∘L leg ∘L g8SourceCompressedGlobalConvolution λ owner.sourceTest` | `C1G8R3DiagonalRootEnergyLimitConstraint.lean:42-48` |

The conditional-limit target of [1485](../proofs/1485_r3_diagonal_trace_limit_energy_constraint.md)
is the cutoff-free form `Summable i, ‖(C ∘L leg)(e_i)‖²` for the two legs
`leg ∈ {survivor coframe, visible-boundary coframe}`
(`C1G8R3DiagonalRootEnergyLimitConstraint.lean:163-164`). O4 differs from it
only by the source-side right factor
`g8SourceCompressedGlobalConvolution`, so everything below applies to O4
with that factor absorbed into the source-side operators.

## 2. Verdict: three position mismatches, one non-mismatch

Comparing O1 with O2/O3 position by position:

```text
O1 (1497):            (I - P) ∘L C ∘L J
G8 survivor (O2):      C ∘L S ,   S = u • J ∘L s_S              (see §3, B1)
G8 boundary (O3):      C ∘L B ,   B = u • Σ_p M_p ∘L J ∘L N_p    (see §3, B2)
```

1. **Left factor.** O1 ends in the projection `I − P`; the G8 obligations
   take the full norm of `C`. Since `P` is an orthogonal projection,
   `‖C x‖² = ‖P C x‖² + ‖(I − P) C x‖²`. O1 controls only the second
   summand. The first summand is not error mass: it is the in-Sonin
   response, i.e. the signal the G8 trace reads out. No leakage estimate
   can dominate it in principle, and none is needed — it has its own
   family (§4).
2. **Input map.** O1 is fed by `J` alone. The survivor leg is fed by
   `J ∘L s_S` with a nontrivial Schur source-side operator `s_S`
   (transition adjoint and Gram inverse-sqrts); the boundary legs are fed
   by `M_p ∘L J ∘L N_p` with ambient factors `M_p` built from prime Euler
   transports and rectangular boundary projections. Neither input is
   `J` verbatim, so O1's series cannot be instantiated on them directly.
3. **Ambient factor.** For the boundary legs an ambient `M_p` sits between
   `C` and `J`. Boundedness of `M_p` does not transfer O1: `(I − P) C M_p J`
   is not `(I − P) C J` composed with anything on either side; the ambient
   factor must enter the estimate itself.

The one thing that does match: the sufficient-direction target is the
**uncut** `C ∘L leg` on the **same** owner, scale, family, and basis — no
cutoff bookkeeping stands between O1 and the obligations. The failure is
exactly items 1–3.

## 3. Bridge facts (consequences of committed definitions)

**B0 (frames factor through `J`).** By definition,

```text
parameterizedSoninFrame λ α S
  = parameterizedFiniteEulerFactor α S ∘L sourceInclusion λ
```

(`CCM24FiniteSFrameGramCalculus.lean:113-118`); `sourceInclusion` is
literally the same `subtypeL` used there
(`CCM24FiniteSGramResponse.lean:41-43`). Both `oldSuffixFrame` and
`newSuffixFrame` are `parameterizedSoninPolarFrame λ 1 S = frame ∘L GramInvSqrt`
(`CCM24FiniteSActualSchurCascade.lean:48-57`,
`CCM24FiniteSFixedSourcePolar.lean:230-235`), hence of the form
`ambient ∘L J ∘L sourceSide`. For the empty list the Euler factor is the
identity (`CCM24FiniteSParameterizedEulerProduct.lean:32-37`, `| _, [] => 1`).

**B1 (survivor factorization).** Unfolding
`g8MetricSurvivorCoframe` (`C1G8P1MetricChannels.lean:43-49`) with B0 and
the empty-list identity:

```text
g8MetricSurvivorCoframe λ V
  = (finiteEulerUpperFactor V : ℂ) • J ∘L s_S ,
  s_S = parameterizedSoninGramInvSqrt λ 1 []
        ∘L (suffixEulerTransitionProduct λ V)†
        ∘L parameterizedSoninGramInvSqrt λ 1 V .
```

`s_S : sourceSoninCarrier λ →L[ℂ] sourceSoninCarrier λ` is bounded. One
rewrite lemma; no new analysis.

**B2 (boundary factorization).** `g8MetricVisibleBoundaryCoframe`
(`C1G8P1MetricChannels.lean:53-57`) is the upper-factor scalar times the
sum of `finiteEulerMetricCoframeBoundaryMaps`
(`CCM24FiniteSSchurPolarTelescoping.lean:394-400`): each summand is a
`suffixEulerBoundaryOutputMaps` output composed with the source-side Gram
inverse-sqrt. The outputs are built recursively
(`CCM24FiniteSSchurPolarTelescoping.lean:235-245`) from

```text
boundaryDagger = (I − newFrame ∘L newFrame†) ∘L transport† ∘L oldFrame
```

(`CCM24FiniteSJuliaCoDefect.lean:255-262, 67-75`). Since `oldFrame` and
`newFrame` are B0-factors and the ambient product / transition factors are
ambient-side / source-side respectively
(`CCM24FiniteSSchurPolarTelescoping.lean:52-65`), induction over the
visible-prime list proves every boundary output, hence every summand, has
the form

```text
b_p = M_p ∘L J ∘L N_p ,
M_p : finiteSCarrier →L[ℂ] finiteSCarrier ,  N_p : source-side bounded .
```

One structural induction; no new analysis. Note `M_p` is genuinely
non-identity for `p ∈ V`: the rectangular projection
`(I − newFrame ∘L newFrame†)` does not act trivially on the old frame's
image — that defect is the boundary content of the Schur step.

## 4. Consequences: the two remaining estimate families

Using `‖C x‖² = ‖P C x‖² + ‖(I − P) C x‖²` and the isometry of `J`
(`J† ∘L J = id`, `CCM24FiniteSGramResponse.lean:46-48`; on range-`J` inputs
`P = J ∘L J†`, the closed-subspace projection identity to be cited or added
in the bridge brick):

```text
‖(C ∘L leg)(e_i)‖²  =  ‖(I − P) C (leg e_i)‖²  +  ‖J† C (leg e_i)‖²
                     (leakage band, OUT)          (in-Sonin response, IN)
```

**Family OUT** — `(I − P) C (ambient ∘L J ∘L sourceSide)` applied to the
basis. By the record-1494 identity `(I − P) B J = (I − E) B J + (E − P) E B J`
(valid for every ambient `B` because `P E = P`), the boundary cases split
further into a radial-boundary leg `(I − E) C M_p J` and an internal-gap
leg `(E − P) E C M_p J`. Records 1495/1496/1497 prove these legs for the
bare root (`M = I`); the boundary cases carry the extra `M_p` and need the
same two estimates adapted to it. In particular the record-1495
finite-window support identity used the root's compact support; the
composite window must combine the root window with the visible-prime
transport range, which is exactly the data `OrbitG8Geometry` exports
([1464](../proofs/1464_g8_r0_raw_orbit_geometry.md)).

**Family IN** — `J† C (ambient ∘L J ∘L sourceSide)` columns. For the
survivor (`ambient = I`) this is the moving-scale compressed detector on
the source carrier: the range-leg square-sum is formal
([028](028_r3_moving_scale_detector_root_range_energy.md), record 1465) and
the leakage/common-right detector-root legs are the long-open obligations
([019](019_r3_leakage_doubled_shift_normal_form.md)–[024](024_r3_source_leakage_translated_decay.md),
[022](022_r3_common_right_causal_telescope.md)). The boundary cases carry
`M_p` inside the sandwich and are strictly harder.

**Free corollary (formalize now).** For the survivor leg, the OUT half is
already dominated: record 1497 states O1 for an *arbitrary* source basis,
and `PositiveTrace.summable_normSq_precomp` (used inside 1497 itself)
preserves column square-sums under bounded right precomposition. Hence
`Σ_i ‖((I − P) C J) (s_S e_i)‖² < ∞` is a two-line corollary of committed
material. Combined with B1, this reduces the survivor obligation exactly
to `Σ_i ‖J† C J (s_S e_i)‖² < ∞` on the named basis.

## 5. The two work orders

### WO-S (survivor diagonal energy)

| Brick | Content | Type | Status |
| :-- | :-- | :-- | :-- |
| S1 | B1 factorization lemma `g8MetricSurvivorCoframe λ V = u • J ∘L s_S` | definitional rewrite | **LANDED** [1498](../proofs/1498_r3_survivor_coframe_source_bridge.md) |
| S2 | orthogonal split + the free OUT corollary of §4; conclusion `hSurvivor ↔ Summable i, ‖J† C J (s_S e_i)‖²` (given 1497) | assembly from committed material | **LANDED** [1498](../proofs/1498_r3_survivor_coframe_source_bridge.md) |
| S3 | the IN estimate: moving-scale in-Sonin compressed-detector square-sum `J† C J ∘L s_S` — continue the 018/022/028 partition (range leg formal; leakage/common-right legs open) | the open mathematics | **OPEN** (sole survivor obligation) |

Stop rule ([012](012_g8_same_owner_readback_rh_reachability.md) §3): any S3
bound that presumes a `qw` sign, `SourceRH`, or a universal gate is
circular and stops.

### WO-B (boundary diagonal energy, per visible prime)

| Brick | Content | Type | Status |
| :-- | :-- | :-- | :-- |
| B1 | B2 factorization induction: every boundary output is `M_p ∘L J ∘L N_p` | structural induction | **LANDED** [1499](../proofs/1499_r3_boundary_output_factorization_bridge.md) |
| B2 | per-output split into IN/OUT families; per-output OUT split into radial-boundary and internal-gap legs via the record-1494 identity applied to `B = C ∘L M_p` | assembly | **LANDED** [1499](../proofs/1499_r3_boundary_output_factorization_bridge.md) |
| B3 | composite radial-boundary estimate `(I − E) C M_p J` — record-1495-analog window/support identity for the composite, then the 1496 transfer | actual physical columns closed; generic reduction formal | **LANDED** (records 1558, 1561) |
| B4 | composite internal-gap estimate `(E − P) E C M_p J` — source-range split and commutator reduction, with `M_p` inside | formal reduction landed; commutator-root square-sum open | **OPEN** [1520](../proofs/1520_commutator_form_b4_consumer.md) |

Per-output B3/B4 results feed the existing consumers unchanged:
[1492](../proofs/1492_g8_boundary_energy_finite_output_reduction.md)
(`g8MetricVisibleBoundary_root_energy_summable_of_each_output`) and
[1493](../proofs/1493_g8_boundary_output_trace_consumer.md)’s Lean twin
(`C1G8R3BoundaryOutputTraceConsumer.lean`), then the conditional total
trace limit [1486](../proofs/1486_r3_total_metric_cutoff_trace_limit.md).

Hard constraints on both work orders:

- Ambient Hilbert–Schmidt shortcuts are formally blocked: the ambient
  leakage leg has a non-summable orthonormal orbit
  ([1488](../proofs/1488_r3_leakage_orthonormal_translation_orbit.md),
  [1489](../proofs/1489_r3_leakage_orthonormal_orbit_energy_obstruction.md)),
  and projecting that orbit into the source carrier destroys it
  ([1490](../proofs/1490_g8_source_projection_translated_orbit_decay.md)).
- Any new boundary estimate must not factor through
  `sourceInclusion† ∘L sourceProlateFactor ∘L sourceInclusion`: that
  pullback is identically zero
  ([1491](../proofs/1491_g8_source_prolate_pullback_zero.md)), which is
  what voided the earlier visible-boundary energy lemma.
- Hilbert–Schmidt does not upgrade to trace-class by itself; the G8 trace
  consumer needs the trace-class owners already wired in the cutoff ledger.

Recommended order: S3 and the B4 commutator-root estimate are now the active
analytic targets. B3 is closed for the actual physical columns. S3 shares its
open core (leakage/common-right detector-root legs) with the long-running
018–028 program; B4 now requires the corresponding atomic commutator estimates
for the finite Euler factors.

## 6. What this audit does not do

It proves nothing new in Lean, supplies neither energy estimate, does not
touch the mixed channels (closed by
[1483](../proofs/1483_r3_actual_cutoff_survivor_boundary_trace_limit.md)),
does not change the conditional assemblies of [040](040_r3_diagonal_trace_limit_energy_constraint.md)/[041](041_r3_total_metric_cutoff_trace_limit.md),
and does not alter the binding route [003](003_b1_b5_minimal_exit_route_selection.md),
the R2/R3 readback obligations, endpoint/P2 signs, C3, or RH. No RH result
is claimed in either direction.

## Work-order status (updated 2026-09-16, records 1508–1510)

```text
  WO-S:  S1 LANDED (1498)   S2 LANDED (1498)   S3 = (★), OPEN
         (1508: (★) ⟺ ambient P C P Hilbert–Schmidt, any named bases)
  WO-B:  B1 LANDED (1499)   B2 LANDED (1499)   B3/B4 FORMAL REDUCTION LANDED
         (1510: composite radial/internal-gap reductions under hwide/hwideHT;
          analytic support inputs remain open, 1491 guard active)
```

Record [1508](../proofs/1508_r3_gate_ambient_normal_form.md) lands the
1503 §2 normal form: the sole survivor obligation (★) is HS membership of
the ambient projection-conjugate `P ∘L C ∘L P`. Record
[1509](../proofs/1509_route_w_strip_hs.md) lands the 1503 §3 Route W strip
lemma with free window parameters; the tail composition stays the
phase-typed irreducible remainder. The estimates remain open; RH not
claimed.

Record [1510](../proofs/1510_r3_composite_boundary_formal_bridges.md) lands
the formal B3/B4 composite reductions. The wider-half-line difference, strip
HS columns, radial OUT leg, Hardy conjugation bridge, and internal-gap OUT
leg are machine-checked under the caller-supplied composite support facts.
Record 1530 adds a reusable monotonicity lemma: if an ambient factor `M` is
already fixed by the original radial projection, then it is fixed by every
wider radial projection. Thus `hwide` is discharged for that subclass of
factors. Its Hardy variant reduces `hwideHT` in the same way for `H ∘L M`.
Record 1533 strengthens both declarations to the exact source-composed forms,
so only `M ∘L J` (or `H ∘L M ∘L J`) needs the original-scale support identity;
no global range condition is required.
The actual visible-prime factors `M_p` and their Hardy conjugates are not yet
shown to satisfy the original radial-support premise, so the analytic inputs
remain open for the boundary outputs and WO-B is not closed. RH is not
claimed.

Record 1535 adds the first concrete source-composed instance: the normalized
forward one-prime Euler transport satisfies both the original and wider radial
support identities after `sourceInclusion`. This is formal and feeds the same
`hwide` consumer when that forward factor is exposed at the right edge. The
actual boundary head still contains adjoint transport/projection blocks, so
this instance does not close B3/B4 or change the WO-B status.
The complete finite forward Euler transport now has the same source-composed
original and wider support identities. This covers a factorization exposing
the full forward product at the source edge; adjoint/projection remainder
blocks remain the unresolved boundary input.

Record 1540 adds a formal adjoint leakage identity: the radial-complement
part of the adjoint normalized one-prime transport is exactly a scalar multiple
of the committed `primeEulerRadialBoundaryStep`. This identifies the outer
adjoint channel structurally, but supplies no square-sum estimate and does not
control the inner radial or metric/projection factors. WO-B therefore remains
open with a narrower, explicit leakage target.
The matching ambient-loss factor identity is now formal as well, so the
`suffixEulerFrameAmbientLossColumn` outer component has the same boundary-step
normal form. The remaining task is its source-basis energy bound and the
coupled inner component.

Record 1545 closes the actual-column interface: the old suffix frame is shown
radially supported, and the radial complement of
`suffixEulerFrameAmbientLossColumn` is identified exactly with the scaled
`primeEulerRadialBoundaryStep` pulled back through that frame.  This narrows
WO-B to the source-basis energy of this explicit outer channel together with
the coupled inner metric/projection channel; no B3/B4 estimate is claimed.

The old-frame radial support fact is now a named theorem rather than a local
proof detail.  It can be reused when proving source-basis energy for the
root-convolved actual column, while the ambient-loss leakage identity remains
an exact structural bridge with no Hilbert--Schmidt estimate.

Record 1555 supplies the missing wide-radial support for the actual ambient-loss
column at the canonical shift `s = log p`.  Thus the composite B3 radial
reduction can be instantiated for this outer column without a caller-supplied
support premise.  The source-basis square-sum and the inner metric/projection
channel remain open; B4 for the Hardy-conjugated factor is unchanged.

Record 1558 closes the B3 radial OUT estimate for the actual ambient-loss
column.  A generic source-column wrapper realizes `A` as `A ∘L J† ∘L J`,
then instantiates the composite reducer; the actual column supplies its
canonical wide-support premise at `s = log p`.  WO-B is therefore reduced to
its coupled inner metric/projection channel (B4/Hardy side still open), while
S3 remains the independent survivor IN estimate.

Record 1560 adds the generic source-column B3 transfer and its postcomposition
form, then instantiates both on the actual ambient-loss column.  The radial
OUT square-sum is now available after arbitrary bounded ambient rows; the
remaining boundary work is the inner metric/projection channel and the B4
Hardy side.  WO-S remains open.

Record 1561 adds the matching wide-radial support theorem for the actual
Schur boundary dagger.  Its positive adjoint transport, followed by the new
range projection and complement, stays in the widened radial subspace at
`s = log p`.  The generic B3 source-column wrapper therefore closes the radial
OUT square-sum for the boundary dagger as well, including bounded ambient-row
postcomposition.  Both physical boundary coordinates now have radial OUT B3;
the Hardy-conjugated B4 input and the survivor IN/S3 estimate remain open.

Record 1562 adds the matching B4 source-column interface.  For any bounded
source column `A`, the existing internal-gap reducer can be invoked after
factoring `A` through `J† ∘L J`; its only analytic premise is the exact
source-composed Hardy support identity for `H ∘L A`.  This does not yet prove
that identity for either physical boundary column, so WO-B remains open at
the Hardy side.

Record 1513 adds the exact S3 input-energy reduction.  On every named source
basis, the compressed gate `J† ∘L C ∘L J` has a square-summable diagonal if
and only if the full source-input leg `C ∘L J` does.  The proof uses the
pointwise Sonin Pythagoras identity and the already formal source-Sonin
leakage square-sum; it does not invoke the impossible ambient leakage or
band-root Hilbert--Schmidt shortcuts.  Thus S3 is now isolated as the full
detector energy on included source vectors, with the source projection retained
in the exact equivalence to the ambient `P C P` gate.

The same record further reduces this source-input energy to the single
Hardy-compressed root `E Q E C J`: the prolate remainder `R C J` is formally
HS from the all-scale prolate factor and the identity `R = K† K`.  Hence the
remaining S3 estimate is precisely the square-sum of `E Q E C J`; no ambient
HS shortcut is available or needed.

Record 1514 exports the exact identity `E Q E C J = P C J + R C J` and the
resulting square-sum equivalence between `E Q E C J` and the source-projection
leg `P C J`. This sharpens the consumer: the prolate remainder is already
controlled, while the sole analytic target is `P C J` (equivalently the source
gate lift). The controlled complementary band leg `B C J` is not substituted
for it; the operators are distinct. Status remains S3 OPEN.

Record 1515 proves the source-range Hardy support bridge `E H P = H P` and
its widened-scale consequence: any column satisfying `P M J = M J` meets the
B4 Hardy support premise automatically. This is a genuine conditional split;
the physical ambient-loss and Schur boundary columns are not yet known to be
source-range, so WO-B and S3 remain open.

Record 1516 proves the corresponding generic B4 square-summability theorem
for the source-range component.  After factoring a bounded source column
through `J† ∘L J`, the source projection `P` supplies the Hardy support
premise and the composite internal-gap reducer gives the full square-sum.
Thus the `P` component of each physical boundary column is formally covered.
The `(I - P)` complement and the source-range decomposition of the actual
boundary columns remain open, so WO-B and S3 are unchanged.

Record 1517 supplies the exact pointwise split of every factored physical gap
leg into the `P ∘L M ∘L J` source-range term plus the
`(id - P) ∘L M ∘L J` complement.  Together with 1516, this removes the
source-range term from the analytic obligation.  The sole remaining B4 gap
target is the complement square-sum; no route status changes.

Record 1518 packages the reduction as a single consumer theorem: a
square-sum estimate for the complement input implies the full physical gap
square-sum.  The B4 gap work order is now exactly the complement estimate for
the finite visible-prime boundary factors; the source-range term is discharged
and no other hidden gap is introduced.

Record 1519 identifies that complement exactly as
`(id - P) (M P - P M) J`.  The remaining B4 analytic target is therefore a
source-projection commutator estimate for each ambient boundary factor,
followed by the root-gap operator.  This is a sharper target than an
arbitrary complement-column bound, but it remains open.

Record 1520 wires that commutator normal form directly into the complete B4
consumer.  It is now sufficient to prove square-summability of
`(E - P) E C (id - P) (M P - P M) J N` for each actual factor.  All projection
and source-range bookkeeping is discharged; the commutator-root estimate is
the only remaining analytic statement in this branch.

Record 1521 proves the exact Leibniz rule `[A B, P] = A [B, P] + [A, P] B`.
The remaining B4 commutator-root estimate can therefore be attacked by finite
induction over the actual Euler boundary factorization, with only atomic
transport/projection commutators requiring analytic estimates.

Record 1522 adds the matching Hilbert--Schmidt induction consumer: if the two
atomic commutator families are square-summable on one source basis, then the
product commutator family is square-summable after any bounded surrounding
factor.  This is a whole-basis `PositiveTrace.summable_normSq_add` argument,
so the remaining B4 target is now explicitly the finite list of atomic
commutator-root estimates.  No atomic estimate is supplied by this formal
consumer; WO-B, S3, G8, and C3 remain open.

Record 1523 closes the zero branch for any source-range factor: from
`P M J = M J` it derives the exact vanishing
`(I - P) (M P - P M) J = 0`.  The physical Euler transport and Schur factors
are not yet certified source-range, so this sharpens the atomic checklist but
does not change WO-B's OPEN status.

Record 1524 closes the complementary branch algebraically: if `P M J = 0`,
then `(I - P) (M P - P M) J = (I - P) M J`.  Thus the finite induction now
has a three-way exact classification for each factor: source-range gives zero,
source-orthogonal gives the existing complementary column, and only a mixed
source projection needs a new commutator estimate.  The physical factors have
not yet been classified, so WO-B remains OPEN.

Record 1525 identifies the source commutator with the committed signed
three-branch owner `E Q [E,M] + E [Q,M] E + [E,M] Q E - [K,M]`.  The B4
commutator-root target can therefore reuse the existing outer, second-support,
reflected-outer, and prolate branch interfaces while keeping the physical
factor `M` on the ambient side.  This is an exact algebraic rewrite; no branch
estimate or route closure follows yet.

Record 1526 adds the corresponding four-branch Hilbert--Schmidt consumer.
Square-summability of the four signed branch columns, after bounded ambient
postcomposition and source-side precomposition, now implies the complete
source-commutator square-sum.  The analytic obligation is therefore exactly
the four branch estimates for each mixed physical factor; the recombination
and sign bookkeeping are closed.

Record 1527 compresses that obligation to two collective estimates: the
outer-plus-reflected-outer pair and the signed second-support-minus-prolate
remainder.  This follows the existing trace owner and preserves its
cancellation.  The physical-factor instantiation of these two estimates is
still open, so WO-B remains OPEN but now has the same two-block shape as the
completed source trace ledger.

Record 1528 adds an exact Fourier-support fixing identity for the source
inclusion and expands the signed outer pair on that inclusion as
`E Q E M J - E Q M J + E M Q J - M E Q J`.  The surviving `M E Q J` term
shows that a two-term radial-leakage rewrite would require a new compatibility
theorem between the radial and Fourier projections.  No such theorem is
available on the healthy carrier, so the proposed generic two-term shortcut is
rejected.  The two-block consumer remains valid, while its physical-factor
instantiation still requires the full non-commuting outer-pair estimate; WO-B
is OPEN.

Record 1529 qualifies the preceding no-go at the actual ledger interface.  The
Fourier support projection is not arbitrary there: it fixes the source
inclusion, `Q J = J`.  Substituting this proved compatibility into the exact
four-term expansion yields the specialized identity
`(outer + reflected outer) J = - E Q (I - E) M J - (I - E) M J`.
The paired consumer now formally proves whole-source-basis square-summability
of this outer pair after bounded ambient postcomposition and source-side
precomposition from the single raw radial leakage square-sum
`sum ||(I - E) M J N e_i||^2`.  This is a conditional reduction only: no
analytic estimate for the raw leakage of the actual boundary factors has been
proved, so WO-B remains OPEN.  Record 1528's arbitrary-`Q` obstruction remains
valid outside this fixed-support specialization.

Record 1530 closes the strategy audit for the new consumer.  The committed
orthonormal-orbit theorem
`sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt`, together with
`sourceRootCompletedBandRoot_not_hilbertSchmidt`, rules out an independent
Hilbert--Schmidt estimate for the unit-scale root-completed leakage branch:
the leakage remains uniformly nonzero on a separated translation orbit while
the prolate range leg vanishes there.  Hence record 1529 is retained as a
conditional algebraic interface only; its raw-leakage premise cannot be the
physical producer target under the present root ordering.  The next viable
work order must preserve the signed cancellation with the second/prolate or
common-right block, or prove a new compactifying factor before readback.  The
independent outer-pair split is NO-GO, and WO-B remains OPEN.

Record 1531 adds the cancellation-preserving normal form for the actual
source inclusion.  Keeping outer, second-support, and reflected branches
together gives
`(E Q [E,M] + E [Q,M] E + [E,M] Q E) J = (E Q E M - M) J`,
using the formally proved `E J = J` and `Q J = J`.  This cancels the middle
noncommuting terms before any Schatten estimate and is the correct signed
block to pair with the prolate branch.  It introduces no energy estimate or
positivity; the source-compressed root/cancellation producer remains OPEN,
while the independent outer-pair HS split remains the NO-GO recorded in 1530.
The owning bridge also now exposes the complete identity
`[P,M] J = ((E Q E) M - M) J - [K_prol,M] J`,
so the next analytic consumer may target these two signed columns directly.
The paired square-sum consumer is also formal: summability of the two signed
columns after bounded ambient postcomposition and source-side precomposition
implies the full source-commutator square-sum.  This closes only the consumer
interface; the two physical energy premises remain OPEN.

Record 1532 discharges one of those two premises.  Since the source prolate
remainder is `A† A` and the all-scale factor `A` is square-summable, ideal
closure under bounded pre- and postcomposition proves the prolate commutator
column square-summable for every bounded physical `M,D,N`.  Thus the only
remaining B4 producer obligation at this interface is the signed
Hardy-sub-identity column `((E Q E) M - M) J`; the prolate leg is FORMAL and
WO-B remains OPEN solely on that Hardy column and its G8 readback.
The final reduction theorem packages this as one premise, so no separate
prolate estimate is needed in future physical-factor consumers.

Record 1533 gives the remaining Hardy column its exact two-defect normal form:
`((E Q E) M - M) J = -(I-E) M J - E (I-Q) E M J`.
The physical factor remains inside both terms and no projection commutation is
used.  The radial finite-window theorem does not yet instantiate this identity
for arbitrary actual `M`; the Fourier-gap defect is also unestimated.  This is
an object-level sharpening only, so WO-B stays OPEN.

Record 1534 adds the square-sum consumer for this split.  The two explicit
defect columns, after arbitrary bounded ambient/source factors, imply the
Hardy column square-sum.  Combined with the formal prolate-column result,
the physical B4 producer is now exactly the pair of defect estimates shown in
proof record 1534; no hidden third commutator estimate remains.

Record 1535 specializes the consumer to any source-composed radial factor:
`E M J = M J` makes the radial defect vanish exactly.  The complete forward
finite Euler transport satisfies this support identity, so its source
commutator column is reduced to the single Fourier-gap square-sum, with the
prolate commutator already formal from record 1532.  This is a formal
consumer bridge only; the physical visible-prime boundary factors still lack
the needed Fourier-gap estimate and WO-B remains OPEN.

Record 1536 rewrites the remaining Fourier-gap column exactly as a
Hardy–Titchmarsh radial tail:
`E (I-Q) E M J = E H (I-E) H E M J`.  Thus the next analytic producer can be
stated as a quantitative radial-tail estimate for the Hardy-transformed
physical column.  The identity is formal and does not supply that estimate;
WO-B remains OPEN.

Record 1567 executes preregistered order-of-battle item 6 on the ρ5
obligation (independent of WO-S and WO-B): the ρ5 gate is stated ONCE as the
named proposition
`g8R5EulerContentBridge` in `C1G8R5EulerContentBridgeTarget`, its right side
pinned to the committed `poleTerm - archimedeanTerm - finitePrimeSum` split
on the half-density square, its left side pinned to the four compiled
channels, and the canonical-family arithmetic row transported to read exactly
`finitePrimeSum owner.sourceTest.convolutionSquare` (same detector, same
prime set, zero estimate input).  The pinned ledger exposes the sign
mechanism: the visible prime-power sum occurs twice in the ambient prefix
ledger with opposite signs (row `arithmeticOperator` plus the definition
`sameObjectResidual := projectionResponse - arithmeticOperator`), so
row-by-row vanishing allocations are precluded and the producer must control
the combined rows.  The ρ5 obligation becomes a pinned-target statement; the
estimate itself, the source/ambient trace transport, and the P2 connector from
`sourceBandGramResponse_eq_soninFirstJet_sub_remainder` to the leakage limit
remain OPEN.  WO-S and WO-B statuses are unchanged.  RH not claimed.

Record 1574 transports the three named channels through committed cyclicity
(`C1G8R5LeakageChannelCycles`, try11 GREEN 3957 jobs, standard axioms): each
channel trace indexed on the source basis is restated on the BOUNDARY side -
response on the actual-band pair carrier, total on the common boundary
carrier (its sign carried as an operator `Neg` of the cycled endo), remainder
as the pair sum of the two.  The cycled operands are exactly the pair-leg
transports `data.left oL K`, `data.right oL K` living on the same carriers as
the 1492/1493/1495 boundary-leg machinery, which is the formal OUT-side
interface the rho5 combined-row producer must consume (this IN/OUT split).
Pure bookkeeping: no estimate, no sign premise, no component identification.
The same record adjudicates the Q-hM identity question of the 1573 B4 chain:
the actual `M_p` contains adjoint Euler transports, which are advances across
the log-radial boundary, so the fixed-scale radial self-adaptation shortcut
is blocked for the actual columns (paper mechanism note against committed
definitions, not a formal no-go); B4 keeps both 1534 defect premises pending
a scale-adapted `hM'` formalization or the honest both-columns estimate.
WO-S and WO-B statuses are unchanged.  RH not claimed.

Record 1569 then lands exactly that P2 connector:
`C1G8R5LeakageChannelPSplit` pins the 1480 limit operator as
`g8R5LeakageTotalChannel = g8R5LeakageRemainderChannel -
g8R5LeakageResponseChannel`, discharges all three diagonal summabilities by
`boundedSandwich` transports of the committed three-branch and Sonin pair
owners, and restates the proven limit as the difference of the two named
channel traces (try4 GREEN 3956 jobs, standard axioms, no new premises).
The ρ5 producer obligation is thereby anchored to NAMED channels: the prime
residual content must come out of the remainder-channel trace combination,
consistent with the 1567 dual-sign preclusion.  The estimates themselves,
the source/ambient transport, WO-S, and WO-B remain OPEN.  RH not claimed.

Record 1575 adjudicates the Q-hM question of the 1573/1574 chain from the
primitive translation convention (`GlobalLogCrossing.lean:145-150`:
`Translation b u (t) = u (t + b)`; carrier columns supported on
`[log lambda, ∞)`).  The four-factor ledger of the actual ambient factor
`M_p` (the `Bridge:74-79` witness) shows only the adjoint Euler transports
move support, each leaking leftward by its `log q`; the total leak is
`Lambda(p::S) = log prod_{q in p::S} q`.  Consequences for this map's
IN/OUT split: fixed-scale `hM` fails on the OUT side (1574's mechanism
re-confirmed with the exact value replacing the `lambda/p^k` placeholder),
the scale-adapted `hM'` holds as pure support identity but cannot feed the
scale-faithful 1535 shortcut consumer, and the radial defect leg becomes
explicitly STRIP-CONFINED: `D o (I - E) M_p J N` factors through
multiplication by the indicator of `[tau - Lambda, tau)`.  A
strip-confinement Lean brick (pure a.e. indicator arithmetic from
committed coeFn lemmas) is registered for the next formal wave; WO-S and
WO-B statuses are unchanged.  RH not claimed.

Record 1576 files the phase wave's pre-registered typed stop: the 1568 T2
entry condition never fired (negative-ray beta = 1/2 for every symbol decay,
modulation branch typed dead), so the multiplier-phase lever class {vdc,
root-symbol, modulation, prolate subtraction, exact hM} has no admitted
route to (star) or to the B4 gap column - a verdict on routes, NOT on the
gate (which stays OPEN).  The ordered AO re-pricing shows the almost-
orthogonality hope was level-mis-specified: (star) asks Hilbert-Schmidt
while Cotlar bounds operator norms, and both natural decompositions either
collapse to exact Pythagoras (frequency annuli: disjoint multipliers, cross
terms zero) or rename the same divergent off-diagonal sum (support annuli).
Consequences for the WO-B legs: B3's composite window becomes explicit -
committed kernel support data (`rootConvolution = cc20GlobalLogConvolution
involution.test`, BandTrace:36-39, plus bundle hsupp) and 1575's closed-form
shifts place `(I - E) C M_p J` inside a fixed compact window
[tau - Lambda_max - R, tau), with only the cheap half-line
support-propagation lemma uncommitted before the 1495/1496 assembly can
consume it; hradial is now a strip-restricted object (square-summability of
a strip-restricted composition - unpriced, outside both dead classes); and
the only live almost-orthogonality target is the visible-prime sum inside
hBoundary/rho5 at NUCLEAR level (unnamed, unregistered for spend).  WO-S
status unchanged; WO-B legs re-typed, not closed.  RH not claimed.

Record [1577](../proofs/1577_b3_composite_phantom_verdict_and_card_repricing.md)
audits that entry against committed source and CORRECTS it on B3. The
"composite window becomes explicit / one cheap support-propagation lemma
uncommitted" framing is a phantom: B3's radial OUT leg is already unconditional
for both physical boundary columns at
`C1G8R3CompositeBoundaryEnergy.lean:1147-1200` (`..._compositeRadialLeg_sourceBasis_normSq_summable`
and the `boundaryDagger`/postcomp twins), where the wide-radial support is
discharged INTERNALLY at the one-step shift `Real.log p` by
`..._wideRadialSupport`, the file contains zero `sorry`, and no consumer awaits
a `Lambda_max` composite window (workspace grep over `ConnesWeilRH/` finds
none). The reason is structural: the landed columns are one-step Schur objects
whose only support mover is the single adjoint transport at `p`, whereas 1575's
`Lambda(p::S) = log prod q` measures the FOUR-factor chain, whose consumer is
B4's `hradial` strip leg. B3's table row ("actual physical columns closed;
generic reduction formal, LANDED 1558/1561") is therefore RE-AFFIRMED, not
extended. Same record: B4's remaining obligation is TWO simultaneous premises
read verbatim from
`C1G8R3BoundaryOutputFactorizationBridge.lean:509-527` - `hradial` (support
side, strip-confined, unpriced) and `hgap` (Fourier side, the column the 1576
typed stop covers) - so `hradial` alone closes nothing and is DEFERRED rather
than funded. WO-S and WO-B statuses are unchanged; nothing is proved here, no
Lean is built. RH not claimed.

Record [1579](../proofs/1579_g8_survivors_adjudicated_hradial_priced_and_support_lemma_committed.md)
exhausts the 1576 section-4 survivor queue at paper level against committed
source. The item-1 prereq is a double phantom: the "not committed yet"
support-propagation lemma is `convolution_support_subset_add_Ioo`
(`CC20YoshidaConvolution.lean:386`, ten-plus callers, engine
`MeasureTheory.support_convolution_subset`), and 1495's exact translation
conjugation never required a shifted-half-line-union check. The item-2 object
`hradial` is PRICED CLOSED: the physical B4 chain
`D E H (I-E) H E M_p J` (record 1568 section 1) has NO root-kernel slot, while
both committed square-summability generics
(`C1G8R3CompositeBoundaryEnergy.lean:911` and `:1287`) hardwire
`rootConvolution owner` in the conclusion and draw all compactness from it -
:911 via the 1495/1496 window mechanism, :1287 via
`sourceProlateHilbertSchmidtFactor` plus the reflected B3 leg; strip
confinement contributes no singular-value content (law F29). Funding
`hradial` would be a new carrier-level compactness estimate, and 1577(ii)
caps it regardless. WO-S and WO-B statuses are unchanged; B4 remains open on
`hgap` inside the 1576 typed stop; nothing is proved here, no Lean is built.
RH not claimed.

Record 1592 changes the B4 consumer interface without changing the route
status: the exact wide-Hardy support premise can be replaced by the formal
decomposition `A = H E_w H A + (A - H E_w H A)`. The first term is handled by
the existing composite gap theorem; the remaining producer obligation is the
explicit Hardy-tail square-sum after the root-gap operator. This is FORMAL
consumer algebra, not an estimate for the actual visible-prime outputs.

Record [1595](../proofs/1595_gap_free_endpoint_mass_from_spectral_tail.md)
supplies the S3-side endpoint-mass reduction: convergence of the actual
endpoint diagonal values to zero makes every subunit threshold mass finite.
This is FORMAL bookkeeping; the Sonin spectral-tail convergence itself is
still open, and it does not alter the B4 WO-S / WO-B status.

Record [1597](../proofs/1597_hardy_tail_reflected_radial_normal_form.md)
proves the exact normalization of the approximate B4 tail as a Hardy-
transported radial complement. This identifies the next producer target with
the reflected radial chain, but supplies no estimate; B4 remains open.

Record [1597](../proofs/1597_hardy_tail_reflected_radial_normal_form.md)
proves the exact normalization of the approximate B4 tail as a Hardy-
transported radial complement. This identifies the next producer target with
the reflected radial chain, but supplies no estimate; B4 remains open.

Record [1594](../proofs/1594_approximate_hardy_boundary_consumer.md) wires that
approximate gap consumer into the full G8 visible-boundary energy ledger. The
boundary theorem now takes, per actual output, the radial support identity and
the explicit Hardy-tail square sum (plus the existing IN leg). This is FORMAL
consumer composition; the analytic tail producer remains open and the WO-S /
WO-B route statuses are unchanged.

Record 1612/1613 further specializes this interface to the actual source
column type.  The formal theorem
`wideHardySupport_sourceColumn_iff_wideFourierSupport` proves that the B4
Hardy premise is equivalent to the same-scale Fourier projection equality for
`A : sourceSoninCarrier λ →L Carrier`; record 1613 then exposes the B4 gap
consumer directly from that Fourier equality.  This is a formal consumer
rewiring, not an analytic producer: the actual Fourier-defect square-sum for
the visible-prime boundary columns, and the S3 source-compressed root energy,
remain OPEN.  Evidence: accepted build log `1613_fourier_gap_consumer_retry`.

**Status update (2026-09-18, source-kernel split):** record [1616](../proofs/1616_source_compressed_root_kernel_split.md)
formally expands the live S3 gate `J† C J` using the exact source identity
`P = E Q E − R`. The three terms containing the prolate remainder `R` are
now separated from the central Hardy-corner term `J† (E Q E) C (E Q E) J`.
This is a formal algebraic narrowing, not an energy estimate: the central
corner square-sum is still the sole S3 producer target, while the B4 Fourier
defect producer remains OPEN. Evidence: paired audit build log
`1616_source_compressed_kernel_split_retry13.log`.

**Status update (2026-09-18, one-sided source reduction):** record [1617](../proofs/1617_source_compressed_root_kernel_one_sided.md)
uses `J† P = J†` before expanding `P = E Q E − R`, giving the sharper exact
identity `J† C J = J† (E Q E) C J − J† R C J`. The first term is the
existing Hardy-compressed root-energy interface pulled back by the bounded
adjoint inclusion; the second is a pure prolate-remainder term. This removes
the unnecessary right Hardy corner from the active producer target. It is
still a formal reduction: the central energy estimate and B4 producer remain
OPEN. Evidence: paired audit build log
`1617_source_compressed_kernel_one_sided_retry3.log`.

**Status update (2026-09-18, wave preflight + strip brick + carrier bridge):**
route re-review [1618](../proofs/1618_route_rereview_s3_b4_carrier.md) found
the registered S3 brick already landed, so the S3 spend is zero and the
five-form equivalence table is filed as
[1620](../proofs/1620_s3_reduction_layer_complete.md): the open estimate is
one analytic statement in the equivalent forms ambient `P C P`, source gate
`J† C J`, source input `C J`, Hardy-compressed root `E Q E C J`, and source
projection `P C J` (`C1G8R3GateAmbientNormalForm.lean`, links 1–5). **S3
remains OPEN**; the guardrails (no Friedrichs gap, no ambient HS shortcut, no
`qw`-sign premise) are unchanged.

B4 side: [1619](../proofs/1619_strip_confinement_landed_signed_b4_target.md)
lands record 1575 section 3.3 as support algebra in
`ConnesWeilRH/Dev/C1G8R3StripConfinement.lean` (+ audit), nine declarations:
the radial defect of any wide-certified operator is the translated finite
strip projection on `[log λ − s, log λ)`, with additive scale composition and
no caller premise for the two committed physical columns at width exactly
`log p`. The signed corollary
`hardyColumn_radialDefect_eq_strip_of_wideHardySupport` shows that under the
wide Hardy certificate (the premise the 1612/1613 consumers take) the
unbounded reach of `1 − E_λ` of record [1599](../proofs/1599_b4_unbounded_reflected_tail_boundary.md)
collapses to that finite strip. This is support algebra only (law F29): no
decay, no Hilbert–Schmidt, no trace statement; the certificate for actual
columns and the `hgap` Fourier leg remain the open B4 producer. **WO-B
unchanged, B4 OPEN.**

Carrier side: [1621](../proofs/1621_carrier_eigenvector_bridge_and_t4_route.md)
machine-checks that carrier nonemptiness is exactly the existence of a
nonzero radial `±1` eigenvector of the committed Hardy–Titchmarsh involution
(`SoninCarrierEigenvectorBridge.lean` + audit, five declarations), and files
the paper-level half-phase computation `U H U⁻¹ = R` for
`U = F⁻¹ M_{m^{-1/2}} F`. The base obligation `archimedeanSoninCarrier_nontrivial`
is still a `def`, not a theorem (law F33), so records 1586–1589 stay
CONDITIONAL and the de Branges existence reading of
[1590](../proofs/1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md)
is unchanged; T4 of `docs/proofs/1003` remains the productive route.

Wave acceptance: `build-logs/1618_strip_confinement_carrier_bridge.log` — 4076
jobs, zero `error:`, zero `sorryAx`, 14 standard axiom prints, no warning in
the new modules. RH not claimed.

**Status update (2026-09-18, multiplier-conjugate wave; records 1622–1625).**
[1622](../proofs/1622_multiplier_conjugate_factorization_and_1621_erratum.md)
lands the factorization `H = R ∘L U_m` with `U_m = F ∘L M_m ∘L F⁻¹` for the
Hardy–Titchmarsh involution (`SoninCarrierMultiplierConjugate.lean` + audit,
ten declarations, standard axioms), together with the fixed/anti-fixed forms
`U_m u = ±R u` and the carrier characterization as radial `u` with `U_m u` in
the reflected radial subspace; it also carries the erratum withdrawing 1621's
"covariance not committed" caveat and its half-phase square root (the
covariance is `CCM24ArchimedeanCarrier.lean:863`, the factorization is free).
[1623](../proofs/1623_t4_prolate_attack_four_obligations_and_two_mismatches.md)
types the four T4 obligations (domain / spectral sign / carrier transport /
window restriction) against the source (PNAS 2022, PMC9295779, Corollary 2.2),
records that the tree's own "prolate" naming is the finite-S strict-angle
band-crossing layer and not the CCM prolate operator, and files two
mismatches: the one-sided committed carrier versus the paper's two-sided
Sonin space, and the fact that a bounded multiplier would force an empty
carrier. [1624](../proofs/1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md)
identifies the B4 wide certificate and the carrier base as one and the same
Toeplitz condition `P_+(e^{2πi c xi} m · R(F v)) = 0`: WO-B's producer premise
and the base of both WO legs are one analytic object, governed by the
multiplier's half-plane growth `(πx)^{2πy}` (paper-level, unformalized).
[1625](../proofs/1625_s3_form_selection_and_strip_density_bound.md) selects
form v `P ∘L C ∘L J` as the S3 attack surface (fewest layers, carrier-visible,
same Toeplitz object as 1624) and closes the StripDensity finiteness fork of
1589 §6 at the trivial bound `Tr(P M_Δ P) ≤ Λ` from the committed `P ≤ E` and
the committed indicator readback (brick specified; the missing layer is a
basis-to-measure trace identity). **WO-S/WO-B/B4 unchanged and OPEN; S3 OPEN
in form v; carrier base still a `def` (law F33); RH not claimed.**

Wave acceptance: `build-logs/1622_multiplier_conjugate.log` — 3322 jobs, zero
`error:`, zero `sorryAx`, ten standard axiom prints, no warning in the two new
modules.

**Status update (2026-09-18, infrastructure round; records 1626).**
[1626](../proofs/1626_infrastructure_verdict_toeplitz_form_and_scale_monotonicity.md)
lands the scale-monotonicity brick
(`Dev/SoninScaleMonotonicity.lean` + audit: `Radial`, `FourierSupport` and the
carrier are antitone in `lambda`, so carrier nonemptiness propagates downward
in the scale and triviality propagates upward — the base obligation is a
sharp-threshold statement) and closes the infrastructure question of 1623 §5:
everything on the critical path is already stateable in committed vocabulary
(no H² layer needed to *state*; the missing layer is needed only to *prove*).
It fixes the explicit symbol form `m(xi) = Gamma_R(1/2 - 2 pi I xi) /
Gamma_R(1/2 + 2 pi I xi)` with its zero/pole ledger, re-types the carrier base
as the de Branges-pattern obligation `W/A in H^2(C_+)`, `W/B in H^2(C_-)` for
one entire `W != 0`, records that `A` is not Hermite-Biehler (so the textbook
de Branges theory does not literally apply), and **withdraws the 1624 §5
"cheap scalar test"**: the symbol's argument has no limit at infinity, the
continuous-symbol index theory is unavailable, and the applicable criterion is
the Makarov-Poltoratski one for real-analytic unimodular symbols
(arXiv:1711.04511 §2.3), which lands back in model-space/uniqueness-set
territory. **Carrier base (now in `(T)`/de Branges form) OPEN; T4/B4/S3/WO
legs unchanged and OPEN; no witness; RH not claimed.**

Round acceptance: `build-logs/sonin_scale_monotonicity2.log` — 3319 jobs, zero
`error:`, zero `sorryAx`, five standard axiom prints, no warning in the two new
modules.

**Status update (2026-09-18, entire-`W` round; record 1627).**
[1627](../proofs/1627_entire_w_obligations_two_corrections.md) gives the
elementary face of the carrier base — `(T')`: one nonzero `g` with
`supp g ⊆ [0,∞)` and `supp (U_m g) ⊆ (−∞,0]`, i.e. exactly `V_arch(1) ≠ {0}`,
stated in committed vocabulary with no H² layer — and proves one obstruction:
**no witness can have finite exponential type.** Reason: `W/A ∈ H²(ℂ₊)` forces
(pointwise, via the weighted boundary `L²` bound plus subharmonicity) the
decay `|W(x)| ≲ e^{−π²|x|/2}`, and a finite-type entire function decaying
exponentially on `ℝ` has compactly supported transform that extends
analytically across the real axis, hence vanishes identically. So every
band-limited / Paley–Wiener / finite-type construction is excluded and the
witness must be of infinite type (the Γ-factor/prolate class). The record also
files two corrections: **(i)** the carrier is a *conjunction* of two half-line
support conditions on the same vector and is genuinely scale-dependent (in the
model `m = 1`, `V_arch(λ) ≠ {0}` exactly for `λ < 1`; no translation moves it
to `λ = 1`), so 1624 §4's "WO-B premise and carrier base are one analytic
object" is withdrawn in its equivalence form — they share the multiplier only;
**(ii)** a drafted closed form `A·B = √π/sin(π/4 − π²iz)` is **false**
(counterexample `Γ_ℝ(1/2)² = 7.4163 ≠ √(2π) = 2.5066`; the slip is
`Γ((1−s)/2) ≠ Γ(1−s/2)`), the correct elementary statements being
`A·B = π^{−1/2}Γ(1/4−πiz)Γ(1/4+πiz)` (so `1/(A B)` is entire with zeros at the
poles of `A` and `B`) and `Γ_ℝ(s)Γ_ℝ(−s) = −2π/(s sin(πs/2))` (verified at
`s = 1/2`). **Carrier base OPEN; T4/B4/S3/WO legs unchanged and OPEN; no
witness; RH not claimed.**

Round acceptance: no build (no new Lean this round); the standing brick is the
1626 scale-monotonicity module.

**Status update (2026-09-18, MP-criterion round; record 1628).**
[1628](../proofs/1628_mp_criterion_shortness_b4_scalar_form_transport_brick_ledger_erratum.md)
lands the **window-transport brick** (`Dev/SoninWindowTransport.lean` + audit:
`IsWindowWitness T u` and `carrier_nontrivial_of_window_witness` — any nonzero
window witness with vanishing `u` and `H u` outside `(-T,T)` witnesses the
one-sided carrier at every scale `λ ≤ e^{−T}`; this formalizes the direction of
the 1623 one-sided/two-sided mismatch: the tree's obligation is the *weaker*
relaxation of any bounded-window Sonin existence), and records three route
results: **(N5)** the Makarov–Poltoratski criterion's real form is a *shortness*
condition on a set `Σ(γ)` built from the argument (failure form
`Σ|I_n|²/(1+dist(0,I_n)²) = ∞`, Hartmann–Mitkovski arXiv:1511.08326 §8), with a
Beurling–Malliavin-density threshold form
`inf{a : Ker T_{conj(S)^a Θ} ≠ {0}} = D⁺_BM(Λ)`; our `m` is a **meromorphic
inner function** (MP's own class), its phase is computed to two terms
`γ(ξ) = −2πξlog|ξ| + 2πξ + (π/4)sgn(ξ) + O(1/|ξ|)`, `γ' = −2πlog|ξ| + O(1/|ξ|)`,
so the criterion's stated hypotheses (**γ' bounded below**, **γ of bounded
variation**) both FAIL and the obligation redirects to the single number
`D⁺_BM(Λ(m))` of the node sequence `Λ(m) = {γ ∈ πℤ}` (counting `≈ 4R log R`),
with both branches mapped to route consequences (small density ⟹ carrier
nonempty below the critical scale; infinite density ⟹ empty at every scale);
**(N6)** the classical Krasichkov–Tumarkin criterion independently confirms the
1627 finite-type obstruction, and no infinite-type construction is available;
**(B4)** the premise now has a single-column scalar form
`ξ ↦ e^{2πi(log λ'')ξ}m(ξ)ψ(ξ) ∈ H²(ℂ₊)` with `ψ = F⁻¹v`, and support algebra
provably cannot deliver it (the kernel `K = F⁻¹(m)` sits on `[0,∞)`, so the
*lower* edge of `U_m v` is controlled by the *upper* edge of `v`: B4's premise
is a cancellation, not a support condition). Also carries the **numerically
confirmed ledger erratum**: `|A(x+iy)| ≍ |x|^{πy−1/4}e^{−π²|x|/2}` and
`|m(x+iy)| ≍ |x|^{2πy}` (the `π^{−s/2}` prefactor cancels the `π` inside
Stirling's `(π|T|)^{σ−1/2}`; mpmath: `|m(5+0.3i)| = 20.796183` vs `|x|^{2πy} =
20.774349`, while `(πx)^{2πy} = 179.73508`; `|A(5)| = 1.8196985e−11` vs
`√2·5^{−1/4}e^{−π²·5/2} = 1.8196408e−11`). **Carrier base OPEN; T4/B4/S3/WO
legs unchanged and OPEN; no witness; RH not claimed.**

Round acceptance: `build-logs/sonin_window_transport.log` — recorded in the
1628 record; the 1626 monotonicity brick remains the standing accepted module.

---

**Status update (2026-09-19, conditional endpoint sign):** record
[1659](../proofs/1659_endpoint_limit_positive_trace_from_survivor_core.md) and
`Dev/C1G8R3EndpointPositiveTrace.lean` identify the endpoint limit operator
exactly as `F† ∘L F` with `F = C ∘L (I + N†) ∘L C ∘L J`.  Using the existing
`g8EndpointGate_iff_survivorCore` equivalence, the survivor-core premise gives
square-summable columns for `F`, so the endpoint ordinary trace is formally
nonnegative.  Thus the endpoint sign/readback is no longer an independent
producer obligation; S3 remains **OPEN** only at the source-compressed
survivor-core energy estimate.  This is conditional and does not claim RH.

**1629 note (navigation only).** The route map has been redrawn as
[043](043_route_map_to_rh_after_1629.md). This file's operator-bridge audit
stands unchanged; what changed is the base's status: the 1628 redirect to
`D⁺_BM(Λ(m))` is withdrawn as a class misapplication (law F40), the carrier's
Toeplitz form is now exact and model-checked (`m(−ξ)`, shift `ã = 4π log(1/λ)`),
and the base is recorded as a Hardy-only phenomenon (`H² \ N⁺`).

**Status update (2026-09-19, record 1702).** The named StripDensity
compression obligation is now discharged for every positive operator presented
as a Hilbert–Schmidt factor `A†A`: `Dev/StripDensityTraceLedger.lean`
proves the trace inequality for a self-adjoint contraction by factoring the
compressed operator as `(A P)†(A P)` and applying the committed
Hilbert–Schmidt precomposition bound. This is a formal partial closure of the
1625 basis-to-measure fork, not the general positive-operator theorem; WO-S,
WO-B, the source-projection energy estimate, and the carrier base remain OPEN.
Evidence: [1702](../proofs/1702_strip_density_hilbert_schmidt_compression_trace_lemma.md),
focused 2664-job build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-19, record 1703).** The theorem
`sourceCompressedRootAnnularGram_trace_re_le_sourceRootAnnularGram_trace_re`
now proves that the source-compressed annular Gram trace is bounded by the
ambient annular Gram trace.  It is the trace-level form of the contractivity of
the source-inclusion adjoint, using the exact column-energy identities and
their summability.  Therefore an ambient annular upper bound transports
directly to the compressed S3 consumer; the compressed trace is no longer an
independent analytic target.  The ambient annular bound, WO-S/WO-B, and the
source-projection root square-sum remain OPEN.  Evidence: [1703](../proofs/1703_source_compressed_annular_trace_dominated_by_ambient.md),
focused 3962-job build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1708).** The direct source-compressed
root decomposition now has a formal basis-energy reduction.  The theorem
`sourceCompressedRoot_prolateTerm_sourceBasis_normSq_summable` proves that
the prolate correction `J† R C J` is square-summable on every named source
basis, using the all-scale prolate Hilbert--Schmidt factor and bounded ideal
calculus.  The iff
`sourceCompressedRoot_squareSum_iff_hardyCorner_squareSum` reduces the S3
survivor obligation exactly to the Hardy corner
`J† (E Q E) C J`.  Thus the prolate correction is CLOSED; the Hardy-corner
carrier estimate remains OPEN.  This is FORMAL and does not claim RH.

**Status update (2026-09-20, record 1711).** The remaining annular output now
has an exact pointwise readback.  The theorem
`sourceRootAnnularOutputWindow_coeFn_eq_annulus_indicator` identifies the
output, almost everywhere, with the indicator of
`Icc (-n) n \ Icc (-N) N` multiplied by the same root-convolution output.
This closes the representation/readback step needed before a kernel-diagonal
estimate; it supplies no upper bound, summability, or sign.  The S3 Hardy
corner energy estimate therefore remains OPEN.  FORMAL evidence: record 1711
and the paired Audit leaf, focused 3963-job build, zero `error:` and
`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1716).** The existing formal theorem
`sourceRootCompletedBandRoot_not_hilbertSchmidt` is scoped to the ambient
`rootConvolution ∘L sourceBandProjection` complement channel. It does not
apply to the live S3 source-compressed target
`sourceSoninProjection ∘L rootConvolution ∘L sourceInclusion`. The distinction
is now recorded explicitly: the full ambient-HS shortcut is closed, but S3 is
not a no-go. The current producer remains a uniform annular Gram-trace upper
bound / equivalent pointwise kernel-diagonal estimate, consumed by
`sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound`.
FORMAL evidence: records 1708, 1711–1713, 1715–1716 and the cited Lean
declarations; no route status change.

**Status update (2026-09-20, record 1712).** The pointwise readback is now
lifted to the exact L2 energy identity
`sourceRootAnnularOutputWindow_normSq_eq_annulus_integral`: each annular
column norm squared equals the integral of the squared norm of the explicit
annulus-restricted root-convolution output.  This is the kernel-diagonal
representation needed by WO-S; it is still only an identity and proves no
uniform bound or summability.  The Hardy-corner energy estimate remains OPEN.
FORMAL evidence: paired Audit leaf, focused 3967-job build, zero `error:` and
`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1713).** Tonelli now formally exchanges
the nonnegative annular column-energy sum with the spatial lintegral:
`sourceRootAnnularOutputWindow_lintegral_tsum_eq_tsum_lintegral`.  The Lp
representatives provide the required a.e. measurability automatically.  Thus
the remaining S3 producer is isolated after the exchange as a pointwise
kernel-diagonal bound; no finite bound, summability, or sign has been assumed.
FORMAL evidence: paired Audit leaf, focused 3968-job build, zero `error:` and
`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1715).** The attempted full-translation
noncompactness shortcut is now formally audited and rejected. At unit scale,
`sourceSonin_nonzero_not_closed_under_all_right_translations` shows that a
source-carrier vector whose entire right-translated orbit remains in the
carrier must be zero: the Fourier-support projection is identity on the
carrier, its translated-orbit norm tends to zero, and translation is an
isometry. This removes the full-orbit obstruction as a proof of S3 failure;
it does not provide S3. The remaining producer is still the post-Tonelli
pointwise kernel-diagonal bound, possibly with finite-tail or cutoff structure.
FORMAL evidence: paired Audit leaf, focused 3285-job build, zero `error:` and
`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1717).** The shifted-Hardy consumer has
been audited against the live S3 operator.  The committed theorem
`doubledShiftHardyInteriorCompression_summable` concerns the defect block
`(I-P) K_b (I-P)`, while S3 is the source-compressed Hardy corner
`J† (E Q E) C J`.  The exact shifted conjugations and the exact prolate
decomposition do not supply an equality or bounded-ideal transfer between
these operators.  Therefore no S3 estimate is claimed from the shifted-Hardy
result.  After the formal annular readback and Tonelli exchange, the minimum
remaining producer is the post-exchange pointwise kernel-diagonal bound (or
an equivalent uniform annular trace bound).  This is a formal interface audit,
not a no-go theorem and does not change the healthy-CompactLog B5 route.
Evidence: [1717](../proofs/1717_shifted_hardy_not_s3_transfer_exact_kernel_diagonal_gap.md).

**Status update (2026-09-20, record 1718).** A Fourier-side audit confirms
that `rootConvolution` is already a Plancherel multiplier, but the source
Sonin projection currently exposes only its closed-subspace/projection
definition.  No committed theorem gives the diagonal density of
`C ∘ sourceSoninProjection ∘ C†` or an annular integrable majorant.  The next
new mathematical brick is therefore a source-Sonin density lemma with the
same healthy owner; ambient projection substitutions are out of route.  The
uniform annular trace bound remains the direct consumer target.
Evidence: [1718](../proofs/1718_fourier_side_source_sonin_density_lemma_is_the_new_s3_bone.md).

**Status update (2026-09-20, record 1719).** Existing formal decay now gives
the first usable sublemma for the source-Sonin density route:
`sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero`,
and hence source-Sonin projection decay on the selected translated orbit.
This is only qualitative.  The new minimal analytic target is a quantitative
tail-rate estimate for the compact root multiplier, sufficient for
`sum_n ||P_Sonin T_(-n) k_g||^2 < infinity` (or its continuous weighted
analogue).  That rate upgrade would feed the already-formal Tonelli and
annular-trace consumers; it is still OPEN.
Evidence: [1719](../proofs/1719_source_fourier_tail_decay_reduces_s3_density_to_quantitative_rate.md).

**Status update (2026-09-20, record 1720).** The first quantitative rate
brick is now formal: `fourier_norm_mul_sq_le_integral_norm_second_deriv`
proves quadratic Fourier decay from two integrable derivatives.  This is the
correct rate scale for square-summable unit-translation tails.  It does not
yet close S3 because the live source-Sonin root multiplier has not been shown
to satisfy the stated Sobolev hypotheses; the remaining bridge is now a
concrete weighted-L2/second-derivative statement rather than an unspecified
qualitative tail estimate.  FORMAL evidence: record 1720 and its paired Audit,
focused 2967-job build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1721).** The abstract quantitative
interface is now complete: a quadratic unit-translation decay bound implies
the required square-summable column tail via
`summable_normSq_of_quadratic_decay`.  This removes the rate bookkeeping from
the remaining S3 producer.  The unresolved obligation is solely the
operator-level bridge from the actual source-Sonin projected root to that
quadratic bound, or an equivalent integrable kernel diagonal; arbitrary L2
basis-vector smoothness is not assumed.  FORMAL evidence: record 1721,
paired Audit, focused 2967-job build, zero `error:`/`sorryAx`, standard axioms
only.
## 2026-09-20 operator-bridge audit (record 1722)

The existing `sourceActualBandFiniteEulerPairedResponse_isTraceClassAlong`
family was audited as a possible S3 producer. It is not one: that response
contains finite-Euler and detector factors and is controlled by the physical
boundary pair, whereas S3 is the column square-sum of
`sourceInclusion† * rootConvolution * sourceInclusion`. No committed theorem
identifies or bounds these operators. The exact remaining producer is the
uniform annular root-kernel diagonal bound exposed by the Tonelli and L2
readback modules. Record 1722 documents the evidence. Status: formal audit;
S3 remains open at this producer, with no route change.

**Status update (2026-09-20, record 1723):** the bookkeeping bridge is now
formal. `sourceRootAnnularOutputWindow_normSq_tsum_eq_kernelDiagonal_lintegral`
identifies the annular column square-sum with the pointwise kernel diagonal
integral by the existing L2 readback and Tonelli theorem. The remaining
producer is therefore exactly a cutoff-uniform integrable upper bound for
that diagonal; no basis regularity or finite-dimensional shortcut is allowed.

**Status update (2026-09-20, record 1724):** the next operator-level bridge
was audited against the committed Hardy definition. The Hardy--Titchmarsh
owner is currently only an L2 Fourier/reflection/scattering composition; the
tree has no theorem giving integrable first/second derivatives or a pointwise
kernel diagonal for the selected root input. Thus records 1720–1721 cannot
yet be applied to arbitrary source-carrier basis vectors. The preferred next
brick is concrete Hardy-transform regularity for the compact root input (or,
as a fallback, a direct integrable diagonal majorant). Evidence: record
1724; route unchanged.

**Status update (2026-09-20, record 1725):** the Schwartz-core part of the
regularity bridge is now formal. `fourier_norm_mul_sq_le_schwartz_second_deriv`
uses `SchwartzMap.derivCLM` to discharge the two integrable-derivative
hypotheses of the quadratic Fourier estimate, and
`summable_schwartz_fourier_normSq_on_unit_annuli` converts it to square
summability. This applies to an actual Schwartz representative, not
automatically to the L2 Hardy--Titchmarsh quotient or arbitrary source-carrier
basis vectors. S3 remains OPEN; the exact missing interface is the
identification/regularity of the selected Hardy output, or an independent
pointwise diagonal majorant. Evidence: formal record 1725, focused 2968-job
build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1726):** the Schwartz-core estimate is
now attached to the actual selected root. `rootConvolution_apply_schwartz`
identifies the root output on `u.toLp 2` with the concrete Schwartz
convolution by the involuted compact root, and the 1725 decay/summability
consumer applies to that output. This closes no arbitrary-basis or
Hardy-output step: S3 remains OPEN at the Hardy multiplier regularity or
direct diagonal-majorant interface. Evidence: formal record 1726, focused
3167-job build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1727):** the committed Gamma
archimedean factor and its scattering quotient now have formal first-order
real differentiability on the real frequency axis
(`differentiable_ccm24ArchimedeanFactor` and
`differentiable_ccm24ArchimedeanScatteringPhase`, together with the conjugate
inverse phase theorem). This removes the bare continuity gap in the multiplier
interface for both directions, but supplies no derivative-growth
bound and no Schwartz-multiplier theorem. The Hardy-output identification,
quantitative decay, and cutoff-uniform kernel-diagonal majorant remain OPEN;
S3 and the healthy CompactLog B5 route are unchanged. FORMAL evidence:
record 1727 and its paired Audit leaf, focused 2965-job build, zero
`error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1728):** the same module now proves the
exact real-frequency quotient derivative formula for the scattering phase,
using the real-linear conjugation equivalence and the nonvanishing Gamma
factor. This is a genuine algebraic bridge for any future derivative-growth
estimate; it does not assert such a bound and does not close the Hardy-output
or kernel-diagonal obligation. S3 remains OPEN. FORMAL evidence: record 1728,
focused 2964-job build, zero `error:`/`sorryAx`, standard axioms only.

**Status update (2026-09-20, record 1730):** the concrete critical Mellin
profile now has a formal exact second chain rule on the Schwartz core. The
second derivative is decomposed into the weighted first-derivative term, the
weighted second-derivative term, and the weighted profile term. This is the
correct input shape for the existing quadratic Fourier-tail consumer, but no
integrability majorant has yet been claimed. The Hardy-output identification
and S3 kernel-diagonal bound remain OPEN. FORMAL evidence: record 1730 and
its paired Audit leaf, focused 2967-job build, zero `error:`/`sorryAx`,
standard axioms only.

**Status update (2026-09-20, record 1732):** the second-derivative
integrability from 1731 now feeds the existing one-dimensional Sobolev
consumer. The concrete first-derivative critical Mellin profile is
differentiable with integrable derivative, so its classical Fourier transform
is formally in `MemLp 2`. This closes the concrete Schwartz-core Fourier-L2
consumer only; the arbitrary source-carrier Hardy-output transfer and the
uniform kernel-diagonal bound remain OPEN, so S3 is unchanged. FORMAL
evidence: record 1732 and its paired Audit leaf.

**Status update (2026-09-20, record 1731):** the concrete critical Mellin
profile now has a formally integrable explicit second-derivative formula on
the Schwartz core. The positive logarithmic tail uses the zeroth Schwartz
seminorm and the negative tail uses the third seminorm; existing profile and
chain-term integrability supplies the remaining summands. This is a formal
Sobolev input for the quadratic Fourier-tail consumer, but it still does not
identify the arbitrary source-carrier Hardy output with the concrete
Schwartz profile and therefore does not close S3. The source-carrier
regularity transfer or an independent kernel-diagonal majorant remains OPEN.
