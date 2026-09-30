# 2316 — NODE-VALUES-CERTIFIED: the 101 certified node values of the captured owner min-product, replayed bitwise and pinned below `stripGridMax2303`

Record 2313's consumer `frozenStripHypothesis_of_certified_nodes` asks, at
each of the 101 grid nodes `j/100`, `-50 <= j <= 50`, for

    min (stripSecondNorm (j/100) b * stripNorm (j/100) c)
        (stripSecondNorm (j/100) c * stripNorm (j/100) b) <= stripGridMax2303

with `stripNorm sigma f = ∫ e^(sigma x) ||f x|| dx`, plus the support bound
records 2314/2315 supply.  Record 2303 computed certified per-node uppers of
exactly this min-product (the `B_point` field of its 101 `grid_rows`) and
took their maximum for the Lean pin.  This record turns that table into a
first-class, re-verifiable input:

    2275 capture (base, corr vectors, bitwise vs 2267 operands)
      + 2238 panel law + 2234 inflation law + 2303 reduce expressions
      + the 101 committed directed-MPFR sigma files
      --------------------------------------------------------------
      101 certified node values B_point(j)  (bitwise replay, all rows)
      exact-rational directions: B_point(j) >= min product, <= pin
      --------------------------------------------------------------
      NODE-VALUES-CERTIFIED   (results/2316_node_values.json)

Verdict: **NODE-VALUES-CERTIFIED** — all 101 rows replay bitwise against the
committed reduce fields, every `B_point` is an exact-rational upper of the
certified min-product and at most the pinned `stripGridMax2303`, the live
numpy raw screen (the 2277 reproduction) is reproduced bitwise and every
certified min-product dominates it, and the binding node `sigma = -0.5`
clears the pin by 41974.272 ulp.  The value half of the owner bridge is now
a registered table.  No Lean certificate, no producer GO, no RH claim.

## The node values, defined

For the captured owner pair `(b, c)` — the record 2275 capture's coefficient
vectors over the shared corrected families `(a_f^2, theta_f)`, i.e. the
functions `correctedPhysical` of record 2315 with the captured vectors — the
node value at `sigma_j = j/100` is

    N_j = min(D2_b(sigma_j) * M_c(sigma_j), D2_c(sigma_j) * M_b(sigma_j)),

where `M_f = ∫ e^(sigma x) ||f||` and `D2_f = ∫ e^(sigma x) ||f''||`.
Record 2303 certifies, per node, the chain of uppers

    point (directed MPFR trapezoid, 240001 nodes)      p_q(sigma_j)
    panel (composite-EM, (dx^2/12)(2 rmax) ladder)     p_q + panel_q
    inflation (2237 radii x corrected ladder)          (p_q + panel_q)(1 + e_q)
    norms   certified uppers M_b, D2_b, M_c, D2_c
    channels c1 = D2_b M_c/(2 pi)^2, c2 = D2_c M_b/(2 pi)^2
    B_point = upward-rounded (2 pi)^2 * min(c1, c2)   >= N_j

and the Lean pin `stripGridMax2303 = 2644542.8515` was set above their
maximum `2644542.851480454`.  The modulation vector enters through the
ladder weights `|theta|^i` and the phase in the raw screen; the coefficient
vectors enter through the ladder weights `|c|`, the sigma-file quadrature
inputs (bitwise-linked here) and the live raw screen.  Both enter where the
capture is bitwise-anchored, exactly as recorded.

## What was verified (all green)

+----------------------------------------+----------------------------------------+
| check                                  | reading                                |
+----------------------------------------+----------------------------------------+
| capture vs 2267 operands               | families/base/corr bitwise equal       |
| sigma files                            | 101 present, indexed, nodes = 240001,  |
|                                        | bitwise equal to `grid_rows.point`     |
| assembly replay, 101 rows              | j, sigma, panel x4, infl x4, norms x4, |
|                                        | channels x2, min, binding, B_point     |
|                                        | all bitwise; mismatches = {}           |
| 2238 ladder replay                    | base and corr bitwise (envelope and    |
|                                        | recon copies)                          |
| rmax / dx / transfer / sup / margin    | bitwise replay of the artifact fields  |
| raw-check floats, `anchor_raw`         | bitwise replay (rel_max 7.2765792e0)   |
| live numpy raw screen                  | bitwise equal to committed recon rows  |
| exact directions                       | B_point >= min product and <= pin,     |
|                                        | certified min product >= live raw,     |
|                                        | 101 rows each, exact rationals         |
| cross-record pins                      | 2311 (PINNED-ENVELOPE-VERIFIED) and    |
|                                        | 2313 (PINNED-GRID-SAMPLING-VERIFIED)   |
|                                        | both consistent; arithmetic-file md5   |
|                                        | unchanged since 2312 (b3fb88c3...)     |
+----------------------------------------+----------------------------------------+

## Pins and readings

+----------------------------------------+----------------------------------------+
| quantity                               | value                                  |
+----------------------------------------+----------------------------------------+
| pin (Lean literal, parsed and guarded) | 2644542.8515                           |
| binding node                           | j = -50, sigma = -0.5, binding "a"     |
| max node value B_point                 | 2644542.851480454                      |
| pin margin at the binding node         | 1.9545793533325194e-05                 |
|                                        | = 41974.272 ulp of the render          |
| margin range over the 101 nodes        | 41974.272 ... 1.6956296617047196e+16   |
| worst raw ratio (min over nodes)       | 2.4661322656498452 at j = 0            |
| raw ratio rel_max                      | 7.2765792264717994 (replayed)          |
| continuum sup (max x transfer)         | 2823660.8460007603                     |
| frozen bUpper2243 / margin             | 9506275.102584327, 3.36664904924696x   |
+----------------------------------------+----------------------------------------+

The pin margin is the SAME ulp count quoted by the record 2311 pin artifact
(4.2e4 ulp): 2316 re-derives it per node instead of only at the maximum.

## Continuity (byte-frozen inputs)

+-----------------------------+----------------------------------------------+
| input                       | md5 / digest                                 |
+-----------------------------+----------------------------------------------+
| 2303 envelope artifact      | b7814e7376580766f9a039e87fee7300 (frozen     |
|                             | here for the first time)                     |
| 2303 recon artifact         | bcde28dd520ef975a36ec5574fd9e075             |
| 2275 capture (live file)    | d83ee0ffccdbf1b193cb7a9a065d5c82             |
| claimed vector md5s         | d461872e... (base), c37e16a9... (corr)       |
| 2267 operands               | c4f319db18352c6584fa0c23a3117ab1             |
| 101 sigma files (digest)    | 0cef0286d391522f03ab52e717bbe71f             |
| arithmetic pins file        | b3fb88c3dd1e2e289454193dfc000376             |
+-----------------------------+----------------------------------------------+

## Controls

+----------------------------------+--------------------------------------------+
| control                          | reading                                    |
+----------------------------------+--------------------------------------------+
| synthetic pin parse              | "12.345" round-trips                       |
| shifted pin rejected             | render - 1e-3 fails the direction          |
| one-ulp point mutation           | replay mismatch detected (has teeth)       |
| inflated raw screen rejected     | x2.5 at j = 0 (x2 is NOT enough: the       |
|                                  | certification price there is 2.466x)       |
| capture mutation rejected        | one-ulp family shift fails the anchor      |
+----------------------------------+--------------------------------------------+

The first-run control incident is itself a reading: the initial "doubled raw
rejected" premise was falsified by measurement (at `j = 0` the certified
value already exceeds twice the raw screen, ratio 2.466), and was replaced
by the x2.5 form above.  Control premises must accommodate the measured
certification price, not assume it.

## What this changes for the route

- The strip lane's owner-bridge residual is now exactly: (i) this node table
  (artifact grade, 101 values; max at the pin margin above), (ii) the Lean
  instantiation consuming it — the specialization of
  `frozenStripHypothesis_of_certified_nodes` to the packaged owner pair of
  record 2315, whose only remaining hypothesis is the 101-node bound.
- The 101 sigma files, the envelope artifact and the capture are now linked
  by live hashes and bitwise replay, so a future drift in any of them fails
  the check loudly.
- After the instantiation: the signed margin and the non-tail charge.  The
  selected-owner signed inequality remains the summit.

## Non-claims

- Artifact grade throughout: no Lean certificate of the strip integrals;
  the node values remain numeric inputs to the Lean consumer.
- The sigma point quadrature itself is not re-run; only its committed files
  are re-linked (index, node count, bitwise row equality) and its directions
  are re-checked (certified point >= raw).
- The 2303 reduction (pavement gate, coefficient radii, ladder) remains as
  recorded there; 2316 replays the assembly and the directions, not the
  analytic majorant proofs.
- No producer GO, no gate sign change, no RH claim.

## Provenance and reproduction

- Check: `scripts/routea_node_values_2316.py` (md5
  `1e4b9bc2bc6f7d3fe41c6fdce3ca9299`) -> `results/2316_node_values.json`
  (verdict NODE-VALUES-CERTIFIED, failures empty, md5
  `07d3f9e5f59b8daa4b398e4322694205`).
- Machinery replayed by import: `routea_weighted_zero_direct_product_outward_2234.py`
  (md5 `236afe90a759c54677931839cb99eb3d`) and
  `routea_weighted_zero_panel_dx2_2238.py` (md5
  `1c7cd24654acbc5401da162f7464f331`).
- Reproduction, from the repository root in the Linux verification
  environment:

      python3 scripts/routea_node_values_2316.py

  (the run writes `results/2316_node_values.json`; exit code 1 on any
  failure).

Next registered obligation: the Lean instantiation
`frozenStripHypothesis_of_certified_nodes` with the record 2315 packaged
owner pair, leaving the 101-node bound of this table as the single strip
hypothesis; then the signed margin and the non-tail charge.