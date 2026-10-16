# Record 2716: honest joint-acceptance repricing of the stored map-103 gate rows (G1 swing 1)

**Verdict: TWO-SIDED.**
(1) **PATTERN-FAMILY FREEZE CORE CONFIRMED AT HONEST CONSTANTS.** Every
registered-pattern gate row (C > 0, b > 0, det < 0; the map-103
DEAD_ON_CURRENT_FAMILY core) has multiplicity-honest A_n >= 37.2 even
under the record-2710 geometry — no lambda passes the record-2708
contract on any of the 16 pattern rows, at either geometry.
(2) **A NON-VERTEX n=3 CANDIDATE LANE OPENS ON THE STORED ROWS.** Under
the exact record-2708 section-5 reading (non-vertex D/B/C branches use
the gate parabola directly), the honest multiplicity factor
beta_s/m = 4*Cspec*(3/4)^s/m, and the record-2710 geometry d = 169/16,
**11 stored rows are honestly joint-compatible, 4 of them at n = 3** —
inside the G1 target index set — and **2 of those are P4-shell
admissible**: (gamma_1, N=4, n=3) and (gamma_3, N=5, n=3). At the old
geometry only n = 4 survives (7 rows): the 2710 geometry does not merely
buy margin here, it opens the n = 3 lane. **n = 2 is honestly dead at
the stored constants at both geometries** (min A_new = 9.67e7), so the
G1 witness index reduces to n = 3.

This is a candidate-lane identification, not a gate witness: the stored
rows are sampled B5-family measurements (P3 uncertified), and the freeze
of map 103 stands until the named complete-owner probe fires (Nonclaims).

## Task card (bounded-progress gate)

```text
consumer    riemannHypothesis_of_four_point_span_contradiction_producer,
            via the record-2708 contract P1-P5 + (G) + (T1)/(T2)
owner       the stored map-103 trial owners (gamma, N) of
            results/2033_gate_tail_pairing.json, all 35 rows
premise     PAIR-MISMATCH / no-paired-rows at unit-proxy grade: does any
            stored row satisfy joint acceptance under the EXACT 2708
            contract with beta_s/m priced (not the unit proxy)?
criterion   honest joint nonempty (gate set intersects the (R) tail ray)
            per row, with the gate BRANCH classified exactly
budget      paper arithmetic only (record-2709/2714 precedent): 50-dps
            evaluation of stored constants; no rig, no build, no owner
            change
stop        verdict recorded; any required constant missing -> gap
```

## Conventions (all from committed sources; script docstring carries the map)

Gate parabola per row: `G(lam) = D - (2b) lam + C lam^2` with
`det = C*D - b^2` (record 2032), hence `Delta = B^2 - 4 C D = -4*det`
exactly (never reconstructs D). Exact lambda > 0 gate sets by branch:

```text
C > 0, Delta < 0 : none            (registered pattern dies here)
C > 0, Delta >= 0: interval [L-, L+]
C < 0, Delta <= 0: all             (gate holds for every lambda > 0)
C < 0, Delta > 0 : rays (0, L-] U [L+, inf)
```

Tail, exact composed form (record 2708 section 4): (J) is
`4*Cspec*(3/4)^s * K^4 * (K^4+lam)^2 * (2 pi)^12 * (q^n C4 C2)^2
< m lam^2`, equivalent to (R) `A_n (1 + K^4/lam)^2 < 1` with

```text
A_n = 4*Cspec*(3/4)^s * K^4 * (2 pi)^12 * (q^n C4 C2)^2 / m,
Ltail_n = K^4 sqrt(A_n) / (1 - sqrt(A_n))     (0 < A_n < 1).
```

`Cspec = 128.65` (the proved bound; NOT multProxy2248 — the record-2714
anchor lesson), `m = 1` floor (larger m only helps), `q = 2^-14` stored,
geometries `K^4 = H^4` (stored) and `d = 169/16` (record 2710, strictly
smaller, asserted per row). The record-2354 sensitivity variant
`eps^2 = (3/2)A` is priced as `A_n -> (3/2) A_n`. P4 screen:
`2|Im rho| <= 2^(N+1)` (necessary condition, not the identification).

## Anchors (in-run, all green)

```text
a1  tau_q reproduced row-by-row at float order      max rel dev 0.0
a2  2709 new_proxy reproduced row-matched           max rel dev 8.8e-17
a3  gate_signs == (C>0 and b>0 and det<0)           all 35 rows
a4  recorded 2033 lambda_joint_rows (8) subset of   8 == 8 (equality)
    this script's exact unit-proxy joint set
a5  d < H^4 on every row                            asserted
```

Anchor a4 is the exactness control: the unit-proxy lane of this script
reproduces the record-2033 P5 screen EXACTLY (the 2033 finding
"LAMBDA-PAYS, 8 rows" is recovered as the unit-proxy joint set), so the
deltas below are attributable to the two honest changes alone
(beta_s/m priced; branch-exact gate reading).

## Results

**Table 1 — pattern rows (16 interval-branch rows) honestly dead.**

```text
+---------------------+-----------+--------------+--------------+
| pattern family      | rows      | min A_old    | min A_new    |
+---------------------+-----------+--------------+--------------+
| C>0, b>0, det<0     | 16        | 4.398e+06    | 37.198       |
+---------------------+-----------+--------------+--------------+
```

minimum at (gamma_3, N=5, n=3). A_n >= 1 kills (R) outright
(no lambda exists), so the gate interval is irrelevant: the
same-index pairing failure that freezes map 103 is CONFIRMED at honest
grade and both geometries.

**Table 2 — honest joint rows.**

```text
+---------------------------+------+--------+-----------------+
| lane                      | rows | n=3    | n=4             |
+---------------------------+------+--------+-----------------+
| old geometry (K^4 = H^4)  | 7    | 0      | 7 (rays)        |
| 2710 geometry (d = 169/16)| 11   | 4      | 7 (rays)        |
+---------------------------+------+--------+-----------------+
```

**Table 3 — the n = 3 rows at the 2710 geometry (the candidate lane).**

```text
+----------------+------+---------+-----------+----------+---------+---------+--------+
| owner          | n    | branch  | L+        | A_new    | Ltail   | P4      | 3/2    |
+----------------+------+---------+-----------+----------+---------+---------+--------+
| (14.1347, 4)   | 3    | rays    | 1381.5    | 3.68e-3  | 0.683   | OK      | joint  |
| (21.0220, 5)   | 3    | all     | ALL       | 3.60e-1  | 15.86   | OK      | joint  |
| (21.0220, 3)   | 3    | all     | ALL       | 5.42e-1  | 29.47   | fail    | joint  |
| (21.0220, 4)   | 3    | all     | ALL       | 4.37e-1  | 20.59   | fail    | joint  |
+----------------+------+---------+-----------+----------+---------+---------+--------+
```

The P4-admissible n=3 candidates, with their joint lambda intervals:

```text
(gamma_1, N=4, n=3):  gate lambda >= 1381.5 (ray) AND lambda > 0.683
                      -> joint lambda in [1381.5, inf)
(gamma_3, N=5, n=3):  gate everywhere AND lambda > 15.86
                      -> joint lambda in (15.86, inf)
```

All 11 honest-joint rows keep their joint under the record-2354
sensitivity variant eps^2 = (3/2)A.

**n = 2 is dead at the stored constants:** min A_new over the six n=2
rows is 9.674e7 (interval branch throughout); n=2 can only re-enter if
a changed owner/hypothesis produces a different row class, which this
pricing does not provide.

## Findings

1. **The honest repricing changes the stored-row verdict class.** The
   unit-proxy screen (record 2033) found 8 joint rows, one at n=3 —
   (gamma_1, N=4, n=3) — but at unit-proxy grade. Honest beta kills
   exactly that row at the old geometry (A_old = 30.13 > 1) and the
   record-2710 geometry revives it (A_new = 3.68e-3): the geometry
   record, priced under the exact contract, moves an n=3 row from
   dead to joint. The driver is the K^4 ratio H^4/d ~ 3759 plus the
   (K^4 + lambda)^2 factor at the row's stored lambda.

2. **The gate branch, not the constants, is what the era's screen
   missed.** All 11 honest-joint rows are non-vertex rows (16 rays + 3
   all across the 35). The record-2035 lock "n=4 row has no gate
   pattern" is true and untouched — these rows are not pattern rows —
   but the record-2708 contract section 5 admits non-vertex branches
   directly, and on them the gate set is unbounded above, so once
   A_n < 1 the joint is automatic. The binding quantity on this lane is
   A_n (the tail), and A_n at n=3 is dominated by q^6 = 2^-84 times the
   certified Cspec — the honest constants are strong enough.

3. **The reopen target is now named precisely.** AGENTS section 2
   reopens the frozen family only after "a named-hypothesis probe
   produces a complete-owner gate at or beyond the tail-closure index,
   or proves a q bound strong enough for the actual gate row and
   lambda." On the stored constants at the 2710 geometry the tail
   closes at n = 3; the probe is therefore: **a complete-owner gate
   certificate at (owner, n=3) with the C<0 branch** — i.e., the
   record-2708 P5 duty at n=3 — plus P2 (complete prefix), P3
   (certified C4/C2 at the chosen owner), P4 shell identification, and
   the G3 rho-quantifier. If that probe fires with the stored sign
   structure, the row lands inside the honest joint of Table 3.

4. **Remaining premise chain to a G1 witness (unchanged in kind,
   sharpened in index).** P2 source-zero prefix completeness (G2); P3
   certified C4/C2 — the stored values are sampled decay-grid
   measurements (G4-adjacent, per-rho re-certification, budget room to
   delta* = 1.0141e-16 per record 2714); P5 the actual complete-owner
   ICgate at n=3; P4 the shell identification (this record's flag is
   the necessary 2|Im rho| <= 2^(N+1) screen only); G3 the
   source-zero identity/quantifier. G5 (consumer integration) is
   closed (record 2715).

## Nonclaims

- No producer GO, no SourceRH, no RH claim, no map-103 reopening: the
  freeze stands until the named complete-owner n=3 probe fires. This
  record prices stored constants; it produces no owner fact.
- The stored rows are sampled B5-family measurements at sampled
  decay constants; "honestly joint" is a statement about those stored
  numbers under the exact contract, not about the complete owner.
- The P4 column is a necessary-condition screen, not the shell
  identification.
- A_n uses m = 1; the true multiplicity only helps. Cspec = 128.65 is
  the proved bound; no unproved constant is consumed.
- No new Lean module, no build, no measurement: paper arithmetic per
  the record-2709/2714 precedent.

## Evidence

- `scripts/g1_joint_acceptance_repricing_2716.py` (self-contained,
  50-dps mpmath, exact binary64 capture via Fraction, anchors a1-a5)
- `results/2716_g1_joint_acceptance_repricing.json` (35 rows, both
  geometries, sensitivity variant, survivor lists, source sha256)
- Inputs: `results/2033_gate_tail_pairing.json` (stored owners/rows,
  sha256 in artifact), `results/2709_high_shell_geometry_sensitivity.json`
  (a2 anchor), `docs/proofs/2708_joint_acceptance_contract.md` (the
  contract), `docs/proofs/2710_high_shell_geometry_verified.md`
  (d = 169/16), `docs/proofs/2714_nearline_collision_frontier.md`
  (Cspec convention, per-rho budget room),
  `docs/proofs/2715_consumer_integration_verified.md` (G5 closed).
