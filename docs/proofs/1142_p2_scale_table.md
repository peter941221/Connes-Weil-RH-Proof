# Record 1142 - P2 scalar-witness scale table (pre-brick B2 of map 005)

Date: 2026-09-05.

Status: feasibility datum, NUMERICAL/EXACT-DATA level (map 004 section 1
labels). This record proves no theorem and claims no sign. It prices the
admission wall of `no_stageB_budget_of_qw_negative` (record 1140) in the
committed exact data, correcting the sketch numbers of map
[`005`](../map/005_p2_scalar_witness_zero_configuration_design.md) section
2.2. Consumer: the healthy-`CompactLog` B5 chain via the P2 producer lines
S/B/C of map 005.

## 1. Operative margins (EXACT, committed data)

The margins consumed by `C1GateLevelTransferClasses` are `mu := -Q*.U`
with the committed exact rationals in
`C1WindowRationalIngestQ28/Q38/Q48.lean:39`:

```text
+------+----------------------------------------------+---------------------+
| data | committed U (exact rational)                 | mu = -U (decimal)   |
+------+----------------------------------------------+---------------------+
| q28  | -1231802638776891/1180591620717411303424     | 1.0433774196e-06    |
| q38  | -3669237615059765/302231454903657293676544   | 1.2140488872e-08    |
| q48  | -193419435787029/1208925819614629174706176   | 1.5999280737e-10    |
+------+----------------------------------------------+---------------------+
```

Note: these are the values the classes module actually imports. Tighter
one-off certificates exist in the 1112/1113 bundles (e.g. a -5.999e-11
(4,8) interval result), but they are NOT the wired margins; q28 carries
the largest margin and, per the record-1113 super-geometric decay, is the
only realistic window class for the witness's `hcert` field.

## 2. The hbudget floor at the pinned orbit (correction to 005 section 2.2)

The scalar budget of `P2ScalarOneWindowBudgetWitness.hbudget` is

```text
|log(4*pi) + gamma| * s0(defect)  +  Carch
  + N * log N * 2 * (s0 g.convSq + s0 W.convSq)  <=  epsilon <=  mu
```

with `N = ceil(exp(Bsupport)) + 1` and `Bsupport` a bound for BOTH square
supports. CORRECTION: map 005 section 2.2 used `Bsupport = n+2`; the
witness field `hgsquareSupp` bounds the SQUARE of the detector, which the
D1 construction places in `Ioo(-2(n+2), 2(n+2))` (record 1089 window
arithmetic). The class window W (radius 2) contributes `2a = 4`, so:

```text
+-------+--------+--------+--------+-----------+-------------+
| orbit | b=n+2  | Bsup   | N      | N*log N   | 2*N*log N   |
+-------+--------+--------+--------+-----------+-------------+
| n = 0 |   2    |   4    |   56   |  225.42   |   450.8     |
| n = 1 |   3    |   6    |  405   | 2431.57   |  4863.1     |
+-------+--------+--------+--------+-----------+-------------+
```

(`e^4 < 55` and `e^6 < 404` are one-line series facts; the table uses the
exact ceiling values. `log(4*pi) + gamma = 3.1082399118...`.) Smaller
`Bsupport` than the true square support is not available: the witness
must certify the actual supports.

### 2b. The orbit parameter is height-dependent (evidence-backed caveat)

The `n` of the pinned export is not free: it is produced by the
construction (`C1P2DefectControl.lean:583-636`), which cancels every
zero node in the closed ball `R = 2^(n0+1) + 2 + dist(2, rho)` around
`rho` before the detector data close, so the orbit support radius
`n + 2` must grow with the node ball. The record-1114b model
reconnaissance places the detector support radius `a_det` in `[10, 13]`
at the first zero. At those radii the floor is:

```text
a_det = 10:  Bsupport = 20,  N ~ e^20 ~ 4.9e8,   2 N log N ~ 1.9e10
             required scale  (q28)  ~ 5.4e-17
a_det = 13:  Bsupport = 26,  N ~ e^26 ~ 2.0e11,  2 N log N ~ 1.0e13
             required scale  (q28)  ~ 1.0e-19
```

The section-2 rows are therefore MECHANICAL LOWER BOUNDS at toy orbits;
the honest floor at the first zero is 17 to 19 orders below O(1)
seminorm scale, and it worsens with zero height (`n0` grows like
log2|Im rho|, and `dist(2, rho)` like |Im rho|). All section-3 and
section-4 conclusions survive a fortiori; the Line-S falsifier must
exhibit identity-level cancellation, and no cell of the table admits an
estimate route.

## 3. The two lenses on the admission wall

Lens 1 - per-unit seminorm requirement. For the prime side alone to fit
under `mu`, the uniform scale `s0 g.convSq + s0 W.convSq` must satisfy:

```text
+-------+----------+----------+----------+
| orbit |   q28    |   q38    |   q48    |
+-------+----------+----------+----------+
| n = 0 | 2.31e-09 | 2.69e-11 | 3.55e-13 |
| n = 1 | 2.15e-10 | 2.50e-12 | 3.29e-14 |
+-------+----------+----------+----------+
```

The squares are autocorrelations of O(1)-mass tests (the record-1116 twin
anchors the detector scale at f0 with GATE/f0 = +0.45698 at the true
delta = 0 configuration), so the true seminorm scale is O(1), not
1e-10..1e-14. GAP: about 9.7 orders at the best cell (n=1, q28), 13.5 at
(n=1, q48).

Lens 2 - required cancellation of the defect gate. In the assumed
off-line-zero world, `gate(defect) = gate(g) - gate(W) >= gate(g) + mu`
while the budget forces `|gate(defect)| <= epsilon <= mu`. The detection
mass (twin scale 0.457 * f0) must be cancelled to below 1e-6: about 5.7
orders minimum at q28 IF f0 = O(1), independent of any seminorm
bookkeeping.

Both lenses are the same wall seen from the budget side and the identity
side: the identity-level cancellation demanded by DR2 (map 005 section
2.1) is worth 6 to 13 orders of magnitude depending on the cell. No
estimate-based mechanism can span it; only an exact structural
cancellation (the defect's rho-channel absorbed by the window's Mellin
profile, Line S) or a genuine eigensystem sign (Line B) can even in
principle produce a proof whose hypothesis set is consistent.

## 4. Consequences for the attack lines

1. Class selection is forced: q28 (largest margin, 1.04e-6). q38/q48
   are 2 and 4+ orders worse; record 1113 shows margins decay
   super-geometrically past a = 4, so no larger class helps.
2. Orbit selection is NOT available as a lever: the export's `n` is
   construction-produced and height-dependent (section 2b); it cannot be
   tuned down to the toy rows. The floor must be priced at the true
   `n(rho)`, i.e. 17+ orders at the first zero.
3. Line S falsifier is now quantitative: a model decomposition of the
   defect (1116 twin, true delta = 0 nodes) must exhibit a cross-term
   channel of size ~0.457 * f0 cancelling the rho-channel EXACTLY (not
   to 1e-10; to identity level). Partial cancellation is invisible to
   the budget.
4. This table does NOT obstruct the route: in the RH-consistent world
   the witness is vacuous. It prices the proof burden of the only
   remaining producer shape and kills honest-envelope routes
   quantitatively (map 005 A4 is now a numeric statement, not a slogan).

## 5. Verification

All quantities are either committed exact rationals (section 1, read
from the named Lean files) or one-line exact-arithmetic evaluations
(section 2 ceilings; section 3 divisions reproduced with Python
`fractions.Fraction`, 30-decimal context). No rig, no probe, no verdict
selector; nothing here can gate a build.
