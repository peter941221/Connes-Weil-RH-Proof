# 1500 — R2: the one readback identity and its itemized remainder ledger

**Status: RECON + PREREG (zero new Lean).** This record pins, once and for
all, the single identity that the G8 same-owner readback must satisfy, with
every remainder named and its status marked. It answers work-order step 3:
"将实际 G8 总迹、端点项、P2 残差和目标 `qw(g)` 放入一条精确恒等式，逐项列清余项".
No estimate is proved; RH is not claimed.

## 0. The endpoint is fixed

The readback contract consumes exactly one sequence — quoted from
`C1G8AdjointShearGram.lean:1016-1035`:

```text
readback_tendsto_qw :
  Tendsto (fun n => (ordinaryTraceAlong sourceBasis
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re
    - remainder n) atTop (𝓝 (C1SameOwnerWeil.qw owner.sourceTest))
```

Anything whose trace is *not* `(g8SourceCutoffPairData … n).traceProduct` along
`sourceBasis` is a different endpoint and does not count (this excludes, in
particular, the metric-coframe total trace of record 1486 from *being* the
endpoint; see §4). Set

```text
t_n := re⟨ordinaryTraceAlong sourceBasis
        (g8SourceCutoffPairData … n).traceProduct⟩ : ℝ.
```

## 1. The finite identity (FORMAL at every n)

The committed four-channel ledger
(`g8SourceCutoffPairData_ordinaryTrace_eq_fourChannelLedger`,
`C1G8AdjointShearGram.lean:1312-1345`, with the real-pairing lemma
`g8SourceCutoffCross_trace_add_adjointCross_eq_two_re`, `:1365-1376`) gives,
with all channels on the same `owner/lambda/family/globalBasis/sourceBasis`:

```text
(1)   t_n = b_n + 2·x_n + l_n                      for every n,
        b_n := re⟨tr (J† ∘L W_n† ∘L D ∘L W_n)⟩      (endpoint channel)
        x_n := re⟨tr (J† ∘L W_n† ∘L S ∘L D ∘L W_n)⟩ (cross channel)
        l_n := re⟨tr (J† ∘L W_n† ∘L S ∘L D ∘L S† ∘L W_n)⟩ (leakage channel)
```

where `W_n = fullBoundaryPositiveOperator owner.sourceTest (cutoffLower … n)
(cutoffUpper … n)`, `S = finiteEulerPulledObliqueShear lambda family`,
`D = detectorOperator owner`, `J = sourceInclusion lambda`
(`C1G8AdjointShearGram.lean:1069-1113`). The finite-prime family is the
canonical one (`g8CanonicalFamily`, record 012 §2), so the visible-prime
content of `S` is exactly the owner's; there is no owner or support mismatch
left in (1).

## 2. The limit layer

| Quantity | Limit object | Status |
| :-- | :-- | :-- |
| `x_n → X` | `re⟨tr ((J-cmp conv)† ∘L (−sourceBandGramResponse†) ∘L (J-cmp conv))⟩` — record 1479/1481 (`C1G8R3ActualCutoffCrossTraceLimit.lean:248`) | **FORMAL** |
| `l_n → L` | signed same-owner finite-Euler remainder response through the actual cutoff — record 1480 (`C1G8R3ActualCutoffSignedRemainderLimit.lean:45`); its `hfactor` discharges by `sourceProlateHilbertSchmidtFactor_summable_all_scales` | **FORMAL** |
| `b_n → B` | endpoint channel limit for `g8SourceCutoffPairData` | **OPEN** (candidate route: record 1478 strong limit + record 1476 strong-pair sandwich transfer) |
| `L`, `X` values | signed same-owner response values; **not known zero** | — |
| P2 residual | the visible-prime residual carried inside `S`; its separate limit is a sub-item of `L`'s limit object | **OPEN** as a separate named limit |

## 3. The gate — one identity, two open items

Assuming the three limits exist, (1) passes to the limit:

```text
(2)   lim t_n = B + 2·X + L.
```

The G4 contract is satisfied by the *exact* choice

```text
      r_n := (b_n − B) + 2·(x_n − X) + (l_n − L),
```

for which `t_n − r_n = B + 2·X + L` is constant, `remainder_tendsto_zero`
holds iff `b_n → B` (the other two are formal), and
`readback_tendsto_qw` holds **iff**

```text
(3)   B + 2·X + L = qw(owner.sourceTest).
```

Equations (2)+(3) are the complete readback identity. The itemized remainder
ledger:

```text
ρ1_n := t_n − (b_n + 2 x_n + l_n)          ≡ 0            FORMAL (exact, no asymptotics)
ρ2_n := 2 (x_n − X)                        → 0            FORMAL (1479/1481)
ρ3_n := l_n − L                            → 0            FORMAL (1480 + all-scale prolate summability)
ρ4_n := b_n − B                            → 0            OPEN   (endpoint trace limit)
ρ5   := (B + 2·X + L) − qw(g)              = 0 required   OPEN   (same-owner identification)
```

**The substantive gate is ρ5, not ρ2–ρ4.** Records 1479/1480/1481 already
show that the remainders *have* limits; nothing committed shows that the
*aggregate limit equals `qw(g)`*. ρ5 is a signed same-owner value identity —
it encodes the prime-power coefficient readback (the Euler content of `S` and
the P2 residual inside `L`), and it is exactly where the classical
explicit-formula difficulty lives. No amount of further convergence work
touches ρ5.

## 4. Endpoint routing of the energy work orders (WO-S/WO-B)

The survivor/boundary diagonal energies `hSurvivor`/`hBoundary` reduced by
records 1498/1499 feed the **metric term**
`g8PhysicalMetricCutoffOperator` (`C1G8P1MetricBoundary.lean:37`), which is
the P1 metric component of the *physical endpoint*, not `t_n` itself. The
committed transport into the endpoint is the identity
`g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq_g8_add_internal_sub_complement`
(`C1G8AdjointShearGram.lean:845-935`) and its metric split
`…_eq_metric_add_internal`: the physical endpoint pair data equals the readback
pair data plus an internal forward correction minus complement cross terms,
with `A = J ∘L C + D` decomposing the cutoff's left leg. Consequently:

```text
WO-S/WO-B energies → metric-term trace limit (1486, conditional)
                   → endpoint channel limit b_n → B   (ρ4 route, via 845-935)
                   → ρ5 identification → G4 → RH.
```

Any energy estimate that does not land in this chain is attached to the wrong
endpoint. This is the precise sense in which the two "leakage"-named objects
(the record-1497 source-Sonin leakage inside the coframe legs and the
four-channel `l_n`) are *not* thereby connected: they sit at different nodes
of the chain, and only (1) and the 845-935 identity connect nodes formally.

## 5. Immediate admissible work

1. **ρ4 brick (endpoint trace limit).** Prove `b_n → B` on the literal
   `g8SourceCutoffPairData` channel via record 1478's strong limit and record
   1476's fixed-HS-pair transfer; the limit statement itself (constancy of
   `t_n − r_n`) then becomes formal.
2. **ρ5 prereg.** State the same-owner identification (3) as one Lean theorem
   with the raw geometry inputs of record 1464 before attempting any estimate;
   if the only available input would be a `qw` sign, the route stops (typed
   circularity, record 012 stop rules).
3. **P2 sub-limit.** Split `L`'s limit object into the prime-window residual
   (P2) and the compressed response, so ρ5's Euler content is exposed term by
   term.
