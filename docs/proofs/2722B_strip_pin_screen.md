# 2722B — Triangle-ladder pin screen at pipeline grade: NO-GO (scoped)

Verdict: the record-2722A IBP-bridge lane, priced through a triangle L1
ladder on the concrete row-B cardinal owners, misses all three wired
strip-envelope constants at pipeline grade — by 4.79e7 (quartic),
1.08e6 (quadratic), and 5.63e4 (contract, best order). This is a named,
reproducible no-go on the mechanism, not a lower bound on the true
derivatives. The three wired strip premises therefore must travel the
cancellation-preserving transport lane (rung 2722C).

Consumer and premise (binding-route audit):

- Consumer: `fourPointContradictionRowBWired2721C` (row B, gamma_2 =
  21.022039638771556, N = 5, n = 3) inside the reopen-motion premise
  list. Premise to remove: the three quantified strip hypotheses
  `hcontract`, `hquartic`, `hquadratic`.
- Rung plan (record 2722A task card): the bridge corollaries reduce
  each premise to one scalar pin `exp B * derivOrderL1 k f <= C`; this
  screen decides whether the pins are priceable at pipeline grade.
- Failure criterion (pre-registered in the script header): a pin that
  fails at every admissible ladder order is a scoped no-go freezing
  the triangle-ladder discharge for this owner class.

## 1. What is priced

For the record-1980/2720 model the strip functions are cardinal sums

    base.test(x)       = sum_z c_z P_z(D)[e^{z.} seed](x)   (8 targets)
    correction.test(x) = sum_z c_z P_z(D)[e^{z.} seed](x)   (56-node
                         owner, 3 active terms, values from 1980)

with `seed = f_tilde^{*10}` (support `[-10, 10]`, `B = 10`),
`SEED0 = 3^10 = 59049`, `c_z = y_z / (Q_z * SEED0)`, `Q_z = prod_{w!=z}
(w - z)`, `P_z(X) = prod_{w != z}(X - w)`, and the stored binary64 nodes
of the record-2720 row B (`Row_(CANDIDATES[1])`). The bridge-side L1
masses are bounded term-by-term (triangle over the sum):

    ||term_z^(K)||_1 <= e^{B |Re z|} sum_{j+p <= K+m}
                        C(K,j) |z|^{K-j} |alpha_p^{(z)}| S_{j+p},

`alpha_p` the coefficients of `prod (X + z - w)`, and the seed ladder

    S_q = ||seed^(q)||_1 <= min over 10-part compositions of q
          of prod 2^{k_i} D_{k_i}   (a_0 = ||f_tilde||_1 = 3),

`D_k` the record-2720 interval-certified table re-run in this same
process to depth 58 (`certified_D_table` with `K_MAX = 58`).

## 2. Reading (all three wired premises)

Wired constants: `q = 26/10^17`, `C4 = 61000000`, `C2 = 29000000`,
contract threshold `T = 64` (Lean defs, record 2721).

+----------------+-----------------+-----------------+-------------+--------+
| premise        | triangle pin    | wired constant  | ratio       | verdict|
+----------------+-----------------+-----------------+-------------+--------+
| hquartic (K=4) | 2.922167343e15  | 6.1e7 (C4)      | 4.7904383e7 | FAIL   |
| hquadratic(K=2)| 3.134006739e13  | 2.9e7 (C2)      | 1.0806920e6 | FAIL   |
| hcontract (min | 5.633e4 x best  | q*64^48 budget  | 5.6330e4    | FAIL   |
| over K in 0..51| budget at K=48) |                 |             |        |
+----------------+-----------------+-----------------+-------------+--------+

The contract ladder is a clean U-shape: the pin/budget ratio decreases
monotonically from K=0 (`2.537e27`) through K=15 (`6.32e18`), K=30
(`9.08e11`), K=40 (`2.59e7`), reaches its measured minimum `5.633e4`
at K=48, and is already rising again at K=50 (`8.80e4`) and K=51
(`1.567e5`). K=51 is the largest order the depth-58 certified ladder
can price (the base term needs derivative order K+7), so the measured
minimum 5.633e4 is the best triangle price on this ladder. At the
tail, after dividing by the 64 per order, the ratio still moves by
1.5-1.8x per order in the wrong direction (8.80e4/5.633e4,
1.567e5/8.80e4) against a certified-ladder step D_58/D_57 = 198.9;
deeper ladders are a tendency claim, not part of this measurement —
the verdict below is stated at the quantifier "every order priceable
on the depth-58 ladder".

Cross-reads (same-run reproduction anchors, instrument-laws 2bj/2573):

- Certified ladder entries D_1..D_12 agree with the committed record-
  2720 `D_table` to a maximum relative drift of 1.0887992267344172e-16.
- Owner invariants reproduce: `owner_cardinality = 56`,
  `base_target_count = 8`, `corr_active = 3`, `H = 24.02923323790201`,
  `radius = 87.0719873427753` (record-2720 row B).
- 2720's own internal ladder checks (`D_1 >= 2`, `D_2 >= 8`) pass.

## 3. Why the gap has this size (mechanism, not arithmetic luck)

The 2720 certified constants `C4_star = 6.052430e7` and `q_star_T64 =
2.5248e-16` are obtained from an interval envelope that dominates the
SAMPLED cardinal sum — the cancellation between the 8 (resp. 3 active)
cardinal terms is inside the certified object. The bridge-side pin
instead prices `exp B * ||f^(K)||_1`, and every triangle step sums
`|term_z|`: the relative loss is exactly the classic
`sum_z |term_z| / |sum_z term_z|` cancellation factor, here measured
between 6 and 8 orders of magnitude at the two decay constants. The
same blindness pattern is documented in the ledger for the L1
per-node split (AGENTS 2n) and for the cancellation-floor instruments
(AGENTS 2u): absolute-value majorants on multi-term cardinal sums
cannot reach cancellation-certified budgets, and no refinement of the
ladder changes that — the obstruction is structural.

## 4. Honest scope (sufficient-bound discipline)

Per the standing law that failed sufficient bounds are not lower bounds
on the actual object: this screen does NOT prove `||base.test^(4)||_1 >
e^{-B} * C4`. It proves that the triangle-ladder certification route —
any price that bounds the cardinal sum term-by-term with the seed
ladder `S_q` — misses the wired constants by the tabled factors on
this owner at pipeline grade. Records that reuse the 2722A corollaries
must therefore supply a genuinely different positive object (a
cancellation-preserving derivative or envelope estimate), not a deeper
D table.

## 5. Routing decision

- `NO-GO-TRIANGLE-LADDER-AT-PIPELINE-GRADE` is recorded for the three
  wired strip premises on the row-B owner class; the pin-discharge use
  of the 2722A bridge is frozen for this class (the bridge theorems
  themselves stay in the tree — they are sound, just not priceable
  here).
- The live route for `hcontract`/`hquartic`/`hquadratic` becomes rung
  2722C: transport the record-2720 certified envelope (a cancellation-
  preserving object by construction) into Lean as the wired hypotheses
  for the actual owner — which requires the owner identification
  between the pipeline cardinal and `laplaceAt base.test`/
  `laplaceAt correction.test` and the support facts from storedWidth
  data (clearing the record-2ay slab guard), plus a numeric tie
  checker against this artifact family.
- No wired hypothesis was removed this run; no producer GO; no RH
  claim; map-103 freeze unchanged (premise shrinking under the reopen
  motion, same doctrine as 2721B/C).

## 6. Reproduction

    python3 scripts/strip_pin_screen_2722b.py
    # wall 237.4 s, mpmath dps 60, CPython 3.13 (Windows-side reading
    # environment for this numeric instrument)
    # artifact: results/2722b_strip_pin_screen.json
    # smoke mode: STRIP_PIN_SMOKE=1 restricts the ladder to depth 12

Provenance hashes (script, artifact, and its two committed inputs) are
inside `results/2722b_strip_pin_screen.json` under `provenance`.
