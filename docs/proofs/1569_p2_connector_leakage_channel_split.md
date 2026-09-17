# 1569 — P2 connector brick: formal split of the leakage-channel limit

Date: 2026-09-17.

**Status: FORMAL.** Zero estimates, zero sign premises, zero RH content.
This brick executes the named follow-up of record 1567 §"P2 sub-limit split
status": it transports the committed band decomposition
`G = J1 - R` (`sourceBandGramResponse_eq_soninFirstJet_sub_remainder`) up to
the actual-cutoff leakage limit object of record 1480, pinning the P2
sub-limit as a NAMED channel trace. Consumer: the rho5 bridge target
(record 1567), whose leakage-square channel now has its prime-residual
content separated from its Sonin-jet content at the level of the proven
limit.

## Landed declarations

`ConnesWeilRH/Dev/C1G8R5LeakageChannelPSplit.lean` with paired
`...Audit` leaf, namespace `ConnesWeilRH.Dev`:

| declaration | content |
| --- | --- |
| `g8R5LeakageTotalChannel` | the record-1480 limit operator itself: `K† oL (-G†) oL K`, `K` the compressed global convolution |
| `g8R5LeakageRemainderChannel` | `K† oL R† oL K` — the P2 sub-limit channel (compressed prime-window residual) |
| `g8R5LeakageResponseChannel` | `K† oL J1† oL K` — the compressed Sonin first-jet channel |
| `g8R5LeakageChannel_eq_remainder_sub_response` | unconditional operator identity `total = remainder - response` (from `-(J1 - R)† = R† - J1†`) |
| `isTraceClassAlong_g8R5LeakageTotalChannel` | given the 1480 basis bundle: bounded sandwich of the committed `sourceThreeBranchSourcePairData` (its swap, times `(-1)`) owns the total channel's summable diagonal |
| `isTraceClassAlong_g8R5LeakageResponseChannel` | given bundle + `pairedBoundaryBasis`: sandwich of `sourceActualBandFiniteEulerSoninPairData.swap` |
| `isTraceClassAlong_g8R5LeakageRemainderChannel` | the sum of the two owned channels |
| `g8R5LeakageChannelTrace_split` | `ordinaryTraceAlong` total = trace(remainder) - trace(response), via `ordinaryTraceAlong_sub` |
| `tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff_p2Split` | restatement of the 1480 theorem: the SAME truncated channel converges, limit now written as the difference of the two named channel traces |

No new premises enter the restated limit: its hypothesis bundle is 1480's
basis bundle plus `pairedBoundaryBasis` (already a premise of the committed
remainder-pair machinery the split quotes). The `boundedSandwich` transport
(`Source/CC20Concrete/HilbertSchmidtIdeal.lean:566`) supplies all three
summability discharges; no fresh analysis lemma was needed anywhere.

## What this buys the rho5 program

The pinned bridge target (1567) reads `re(trace of the four-channel
endpoint-limit) = poleTerm - archimedeanTerm - finitePrimeSum`. This brick
locates WHERE the `finitePrimeSum` content can attach on the leakage side: it
must come out of the named remainder channel trace
`ordinaryTraceAlong sourceBasis (K† oL R† oL K)` minus (or combined with)
the response-channel trace, never from either one alone, consistent with the
1567 dual-sign consequence that rowwise-vanishing allocations are
structurally precluded. The two channel traces are now first-class named
objects with proven summability, so any future producer can be demanded to
target one of them by name.

## Boundary

This brick proves no bound on either channel trace and identifies neither
with a component of `qw`. The rho5 gate, (★), B4, WO-S/WO-B and the R4
wrapper all stay OPEN as in map 042. RH not claimed.

## Acceptance

try1 `1746_r5_leakage_psplit_try1.log`: 31 errors — the standing §7b
G8-open-union hazard (missing `CCM24FiniteSBandTrace`,
`CompactRootHalfLinePair`, `C1G8P1MetricChannels` opens) plus docstring/
`set_option` ordering. try2 `1747_..._try2.log`: three tactical failures
(`rw` direction into a hypothesis that lacks the pattern; missing local
`adjoint_sub` idiom; `(-1) • x = -x` simp-closure). try3
`1748_..._try3.log`: `ContinuousLinearMap.adjoint_sub` and
`neg_eq_neg_one_smul` unknown constants — replaced by the committed local
`ext_inner_right` idiom (precedent `C1G8R5AggregateExpansion.lean:134`) and
`simp`. try4 `1749_r5_leakage_psplit_try4.log` is GREEN: footer "Build
completed successfully (3956 jobs)", zero `^error:` lines, zero `sorryAx`,
and all nine audit lines print exactly
`[propext, Classical.choice, Quot.sound]`.
