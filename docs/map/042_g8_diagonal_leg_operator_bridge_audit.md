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
