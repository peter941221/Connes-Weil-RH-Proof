# 2268 — Producer-side wiring of the direct-product decay brick (Lean)

Date: 2026-09-30

Consumer: 2257's count-free consumer chain
(`C1RouteAItem5Arithmetic.a005_item5_terminal_count_free`) takes the
count-free bound shape `charge ≤ 4 · mult · B + knownError` with
`mult ≤ multProxy2248`, `B ≤ bUpper2243` as hypotheses; 2265 landed the
producer brick `laplaceAt_convolution_spectral_bound_of_strip` with its
strip hypothesis `hB` explicit; 2267 certified that hypothesis
numerically at the frozen constant on the centered strip. This record
wires the brick into the chain at the frozen constants in Lean.

Verdict: **the wiring module lands. `ConnesWeilRH/Dev/C1RouteAProducerWired.lean`
proves four theorems — the frozen dyadic shell bound, the frozen
shell-mass bound, the frozen high-shell tsum bound
`4 · spectralMultiplicityConstant · bUpper2243`, and the end-to-end
`a005_item5_producer_wired` — all axiom-clean
(`[propext, Classical.choice, Quot.sound]`), module + probe build at
3524 jobs. The end-to-end theorem reduces the chain to exactly four
inputs: the strip hypothesis `hstrip` (certified numerically by 2267),
the count-side `spectralMultiplicityConstant ≤ multProxy2248`, the L1
margin enclosure, and the non-tail charge and 2255 gap bounds.**

## Method

1. `directProduct_dyadic_shell_bound` — for a `CompactLogTest` pair
   `(b, c)` and any `ρ` in height shell `n + 1`, the frozen dyadic tail
   `‖L (b ⋆ c)(centeredXiCoordinate ρ)‖ ≤ bUpper2243 / (2^n)²`. Proof
   mirrors `exists_spectral_laplaceAt_dyadic_tail_bound` exactly (the
   shell lower bound `2^(n+1) ≤ |Im ρ|` via
   `pow_succ_le_of_dyadicShellIndex_eq_succ`, the `2^n` weakening, the
   `(2π)²` rescale), replacing the existential quadratic constant by
   the 2265 strip corollary at `B = bUpper2243`.
2. `directProduct_weightedZeroMeasure_shell_bound` — one exact dyadic
   shell of the weighted-zero mass is at most
   `spectralHeightMultiplicity (n + 1) · bUpper2243 / (2^n)²`, the
   frozen re-run of `exists_spectralHeightShell_weightedZeroMeasure_bound`
   with `F = b ⋆ c` and the concrete per-shell estimate.
3. `directProduct_highShell_tsum_bound` — the exact-owner high-shell
   weighted-zero tsum obeys the frozen budget
   `4 · spectralMultiplicityConstant · bUpper2243`; the geometric
   `3/4`-ratio assembly of `exists_weightedZeroMeasure_highShell_tsum_bound`
   is transcribed unchanged.
4. `a005_item5_producer_wired` — composes theorem 3 with
   `a005_item5_terminal_count_free` at `mult := spectralMultiplicityConstant`,
   `B := bUpper2243`, `charge := (high-shell tsum) + chargeRest`, giving
   `tsum + chargeRest + gap + eps0FullTail2249 < -qLo` from the four
   registered inputs.

## Signature of the end-to-end theorem

```text
theorem a005_item5_producer_wired
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c)
    (hmult : spectralMultiplicityConstant ≤ multProxy2248)
    {qLo gap chargeRest : Real}
    (hmargin : margin2249 ≤ -qLo)
    (hcharge : chargeRest ≤ knownError2109)
    (hgap : gap ≤ gapCharge2255) :
    (∑' n, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) +
      chargeRest + gap + eps0FullTail2249 < -qLo
```

with `FrozenStripHypothesis b c` abbreviating the 2265 `hB` shape at
`B = bUpper2243`.

## Axiom audit

```text
directProduct_dyadic_shell_bound              [propext, Classical.choice, Quot.sound]
directProduct_weightedZeroMeasure_shell_bound [propext, Classical.choice, Quot.sound]
directProduct_highShell_tsum_bound            [propext, Classical.choice, Quot.sound]
a005_item5_producer_wired                     [propext, Classical.choice, Quot.sound]
```

Build: `lake build ConnesWeilRH.Dev.C1RouteAProducerWired` clean at
3523 jobs; probe `C1RouteAProducerWiredProbe.lean` at 3524 jobs.

## Interpretation

- Before this record the chain had a producer lemma (2265) and a
  consumer (2257) that did not touch: the consumer's `hcharge` was an
  abstract bound, and the tsum it governs was never connected to the
  direct-product transform. The wiring places the *actual* high-shell
  weighted-zero tsum of `b ⋆ c` in the charge position, so the
  count-free budget `4 · mult · B` of the consumer is now fed by the
  2265 decay estimate through the same owner (no reindexing, no new
  measure).
- The three remaining hypotheses are exactly the registered residual
  obligations: `hmult` is the count-side constant comparison (2240/2248
  measured it bitwise in binary64; the Lean inequality is the count-side
  revival item), and `hmargin`/`hcharge-rest`/`hgap` are the analytic
  enclosure lanes (2249 L1 margin, 2109 known-error, 2255 gap charge).
- `hstrip` is the only producer-side input, and 2267 certifies it at
  artifact grade at the frozen constant — the producer gate is now a
  numeric obligation discharged (2267) plus a composition discharged
  (this record).

## Nonclaims

- `spectralMultiplicityConstant ≤ multProxy2248` is carried as a
  hypothesis, not proved here (the arithmetic needs the log bounds of
  the `xiGrowthFixedConstant` formula); the count side remains open;
- `hmargin` (2249), `hcharge`-rest (2109) and `hgap` (2255) are carried
  as hypotheses; nothing about the L1/charge/gap lanes changes;
- the module is a composition: it adds no new estimate beyond 2265 and
  no new numeric constant beyond the frozen 2243/2248 literals;
- `hstrip` is not proved in Lean; its numeric truth is the 2267
  artifact obligation, and no Lean-side ball certificate of the strip
  bound is claimed;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- module: `ConnesWeilRH/Dev/C1RouteAProducerWired.lean`;
- probe: `ConnesWeilRH/Dev/C1RouteAProducerWiredProbe.lean`;
- imports: `C1RouteADirectProductDecay` (2265),
  `C1RouteAWeightedZeroMeasure` (the 2201/2203 assembly),
  `C1RouteAItem5Arithmetic` (2257 consumer);
- predecessor records: `docs/proofs/2265_routea_weighted_zero_direct_product_decay_lean.md`,
  `docs/proofs/2257_routea_weighted_zero_count_free_lean.md`.