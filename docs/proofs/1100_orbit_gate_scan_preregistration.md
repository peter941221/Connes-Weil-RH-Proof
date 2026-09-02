# 1100 - the orbit-window semi-local gate scan (pre-registration)

Date: 2026-09-02.

Status: PRE-REGISTRATION, committed BEFORE the run.  This record prices the
record-1099 exit gate - `orbitWindowSemiLocalGate` - numerically over the
triple-vanishing subspace at the D1 orbit windows.  It extends the committed
record-1020 spectral rig with the visible-prime rows of
`C1SameOwnerWeil.finitePrimeSum`.  Consumer (map `004` section 2):
`sourceRH_of_orbitWindowSemiLocalGate`.  RH is not claimed; GATE 1 untouched;
evidence level NUMERICAL (map `004` section 1).  The probe is
`1100_orbit_gate_scan_probe.py`.

## 1. The quantity scanned

For a test `g` supported in `(-a, a)` with `a = n + 2` the D1 orbit radius
(`n >= 0`; the row `a = 1` is outside the family and is labeled
reconnaissance), and `F = g.convolutionSquare` the plain autocorrelation of
the profile (record-1086 pin), the gate functional is

```text
Q(g) = arch(F) + sum over prime powers q with log q < 2a of
       (Lambda(q) / sqrt(q)) * (F(log q) + F(-log q))
     = arch(F) + 2 * sum (Lambda(q)/sqrt(q)) * F(log q)      (F even)
```

with `arch` the record-1086 closed form
`(log 4pi + gamma) F(0) + int_0^oo [e^{y/2}(F(y)+F(-y)) - 2 F(0)] /
(e^y - e^{-y}) dy` plus the exact tail `F(0) log tanh(a)`.
`F(log q)` is BILINEAR in `g`, so the whole gate is a quadratic form; the
scan forms its K x K compression on the orthonormal null space of the three
moment rows `laplaceAt(g, s) = 0`, `s in {0, 1/2, 1}`, and reports the top
eigenvalue (the gate price), alongside the arch-only and prime-only tops.

## 2. Why this is the right price, and what it cannot do

If the top of `Q` over the vanishing subspace were `<= 0` at the pinned
orbit radius of a hypothetical off-line zero, then NO healthy detector could
exist for that zero (healthy detector data requires
`arch + finitePrimeSum > 0` via
`weilSquareSumPositive_iff_spectralWeilValue_neg`), contradicting the FORMAL
detector existence - so the scan prices the exact numerical viability of the
record-1099 exit.  The compression top is a MATRIX observation (law 34):
it is a lower bound on the continuum supremum, so a negative top is
evidence-only (the 1087 logical status) and can never close the gate; the
legendre-enveloped family IS C-infinity with compact support (a legal
`CompactLogTest` member), so a positive top is a witnessed direction of the
carrier up to the numerical rank decision, subject to the constraints
residual gate.  A positive direction need not be a detector (no detection
constraint, no positivity-field filter is imposed), so BOTH verdict branches
concern the sign theorem on all of `V`, not the detector subclass.

## 3. Gates (pre-registered, abort discipline as in 1097)

```text
+----------+----------------------------------------------------+---------+
| Gate     | Criterion                                          | Class   |
+----------+----------------------------------------------------+---------+
| G-arch-1 | ENVIRONMENT-DRIFT MEASUREMENT (re-registered       | MEASURE |
|          | 2026-09-02, see the amendment note below): the     |         |
|          | imported committed 1020 rig is run on the nine     |         |
|          | committed legendre anchor rows and its tops are    |         |
|          | RECORDED against the committed log values; the     |         |
|          | drift must stay <= 1e-4 abs (an order below the    |         |
|          | 1e-3 decision threshold).                          |         |
| G-arch-2 | SAME-ENVIRONMENT EQUIVALENCE: the adapted orbit    | ABORT   |
|          | class with primes OFF must reproduce the imported  |         |
|          | rig's tops on the same nine rows to <= 1e-12 abs   |         |
|          | (same interpreter, same libraries, shared static   |         |
|          | method - expected exact).                          |         |
| G-count  | Hard sieve anchors: a=1 -> 5 visible prime powers  | ABORT   |
|          | (2,3,4,5,7); a=2 -> 24 (through 53; 59 and 64      |         |
|          | excluded by log q < 4).                            |         |
| G-sym-t  | The prime matrix built from shifts {+log q} equals | ABORT   |
|          | the matrix from {-log q} transposed to 5e-6 abs    |         |
|          | (quadrature-level identity; catches sign/offset    |         |
|          | bugs, which would be O(1)).  AMENDED pre-run: the  |         |
|          | first draft said 1e-12 rel, impossible off-grid -  |         |
|          | the shift sums are O(step^2) quadratures, not      |         |
|          | reindexings.                                       |         |
| G-closed | Sine-family cross-check at a=2, K=8 (t=log 2,      | ABORT   |
|          | log 3): the analytic-shift route matches the       |         |
|          | closed-form overlap integral to 5e-6 abs on the    |         |
|          | fine grid (32001) AND the coarse-grid diff is      |         |
|          | 3x-6x larger (quadrature-order check).  AMENDED    |         |
|          | pre-run for the same reason as G-sym-t.            |         |
| G-row    | Per row: moment residual <= 1e-10 AND orthonorm.   | DISCARD |
|          | error <= 1e-10; invalid rows are discarded, the    |         |
|          | verdict consumes only valid rows; if ALL rows of   |         |
|          | one radius are invalid that radius is recorded     |         |
|          | unresolved (no abort).                             |         |
+----------+----------------------------------------------------+---------+
```

Noise floor: the certified record-1087 fidelity scale of the arch matrix
path is 5.6e-05 (first-cell sliver scale), so the positive-direction
threshold is set an order of magnitude above it.

### Amendment (2026-09-02, PRE-SCAN, after run1's pre-registered ABORT)

Run 1 (`build-logs/1100_gate_scan_run1.log`) fired the original G-arch-1
ABORT on its first anchor row: the fresh-uv environment
(numpy 2.5.2 / scipy 1.18.1) reproduces the committed legendre top at
r = 0.300, K = 8 as -1.09135266 against the committed log's -1.09132868
(gap 2.4e-05 vs the original 5e-8 gate).  Root cause: the committed log was
produced in an environment that no longer exists (the era venv is deleted),
and the committed probe's numerics are textually unchanged since
`ecdc1df` (verified by git diff against the 1087 batch `b83dec0`), so the
gap is library drift, at the same order as the certified 5.6e-05 matrix
fidelity scale and an order below the 1e-3 decision threshold.  No scan row
was consumed in run 1, so no verdict-selection bias exists.  Re-registration
replaces the unreachable log-reproduction equality by (a) the recorded
environment-drift measurement (G-arch-1, <= 1e-4) and (b) the
same-environment adapted-class-vs-rig equivalence (G-arch-2, <= 1e-12),
which is the certification this record actually needs: the adapted class
calls the imported rig's certified static method directly.  The scan has
not run yet at the time of this amendment.

Second pre-scan fix (same run sequence, still before any scan row was
consumed): run 5 fired G-closed because the first implementation compared
the null-COMBINATION route values against the closed-form values of the
RAW BASIS functions (C R C^T against R) - an O(1) category error with
shrink 1.00x, not a quadrature failure.  G-closed is corrected to compare
at the basis level (route vs closed form, the shift mechanism plus its
quadrature order) AND at the null level (route vs C R C^T, the
orthonormalization plumbing); tolerances unchanged.  G-sym-t passed at
1.4e-15 in the same run: the plus/minus comparison is an exact index
substitution, so no quadrature slack is involved.

## 4. Verdict mapping (pre-registered)

```text
any ABORT-class gate fails  -> ABORT: no verdict, no repo change.
H1 POSITIVE: some valid row has total top >= +1e-3
                            -> GATE-FAILS-ON-V at that radius (matrix
                               observation): the all-of-V sign theorem is
                               false there; any future sign proof must use
                               detector-class restrictions.
H2 NEGATIVE-PLATEAU: at EVERY radius in {1,2,3,4} all valid rows are < 0
   AND the K-sequence increments are geometric (last increment ratio
   >= 0.5) with geometric extrapolation < 0
                            -> GATE-ALIVE-EVIDENCE: numerical pricing only
                               (law 34); formal closure would additionally
                               need a certified spectral-gap upper bound.
else                        -> SPLIT: report the per-radius sign table as
                               the price of the gate; no route change.
```

No repo change is keyed to any branch except this record's own verdict
section; map updates, if any, will be made in a separate edit citing the
log, labeled NUMERICAL.

## 5. Verdict (appended after the run)

**SPLIT fired (per the section-4 mapping): the price table is reported, no
route change.**  But the run's decisive output is STRUCTURAL: the measured
total top is the quadrature sliver itself, identified below.

Provenance.  Six runs, all through the resource runner, acceptance by
flushed log.  Run 1 (`1100_gate_scan_run1.log`) fired the original G-arch-1
ABORT (environment drift 2.4e-05 vs the unreachable 5e-8 log-reproduction
gate; re-registered pre-scan, see the amendment).  Runs 2-4 crashed before
any gate could be consumed (probe implementation bugs: basis-evaluator
broadcast orientation, unstored coefficient handle, wrong accumulator
shape); run 5 passed G-arch-1/G-arch-2/G-count/G-sym-t and fired G-closed
on a comparison-level error (null combinations checked against raw-basis
closed forms; amended pre-scan).  Run 6 (`1100_gate_scan_run6.log`,
executed probe md5 `a6b252fe54114fa75d2e2393e83f3545`, numpy 2.5.2 /
scipy 1.18.1) passed every certification gate: G-arch-1 worst drift
2.773e-05 (recorded); G-arch-2 gap 0.00e+00 on all nine anchor rows;
G-count 5 and 24 terms exactly; G-sym-t 1.443e-15; G-closed basis level
plus null level <= 4.7e-09 with the 4x coarse/fine shrink.  One scan row
(a=4, K=32, legendre) was DISCARDED by the pre-registered row gate (moment
residual 1.7e-10 > 1e-10).

The scan (valid rows; total = arch + prime):

```text
+-----+---------+----+--------+------------+------------+-------------+
| a   | family  | K  | terms  | top_total  | top_arch   | top_prime   |
+-----+---------+----+--------+------------+------------+-------------+
| 1.0 | leg     | 32 | 5      | -0.000121  | +0.181078  | +1.422653   |
| 2.0 | leg     | 32 | 24     | -0.000231  | +0.919114  | +1.199244   |
| 3.0 | leg     | 32 | 98     | -0.000352  | +1.426876  | +0.920668   |
| 4.0 | leg     | 24 | 465    | -0.000483  | +1.868974  | +0.631891   |
| 1.0 | sine    | 20 | 5      | -0.000120  | +0.214820  | +1.301881   |
| 2.0 | sine    | 20 | 24     | -0.000239  | +0.956242  | +0.879140   |
+-----+---------+----+--------+------------+------------+-------------+
```

Anatomy: top_total is the sliver, not physics.  Every measured top equals
-(0.94..1.00) x step/2 with step = 2a/8000, across both families and all
four radii - the offset tracks the GRID, not the window.  Mechanism: the
arch body quadrature starts at the first correlation lag, missing the
[0, step] cell of area ~= step x F(0)/2; the polarization pairing
q(i+j) - q(i) - q(j) cancels this bias on OFF-diagonal entries (their
F(0) values are 2, 1, 1) but keeps -step/2 on every DIAGONAL entry
(F(0) = 1 on the orthonormal null space).  So the measured arch matrix is
the true one shifted by -(step/2) I, and the same shift rides on the
total top.  After removing it, the corrected tops are +2e-06 .. +3e-05 -
all INSIDE the certified record-1087 fidelity scale 5.6e-05 of this arch
path.  Consequences, honestly stated:

1. H1 did NOT fire: no positive direction at the +1e-3 threshold was
   witnessed at any orbit radius, and H2's negative plateau is NOT
   evidence either - the plateau IS the artifact.  The sign of the true
   top (~0 to within +-6e-5) is UNRESOLVED at this rig's resolution.
2. The price is PINNED at zero across the orbit radii: the visible
   prime-power mass grows from 5 to 465 terms from a = 1 to a = 4 while
   the achievable maximum of the gate functional stays at the sliver
   scale.  Nothing grows with radius.  (sine a in {3,4} was out of the
   row plan by design; legendre carries those radii.)
3. Next probe (named, NOT yet run): 1100b with a first-cell-corrected
   arch body (add the analytic leading cell step x F(0)/2, or integrate
   the closed-form integrand from 0), same gates, resolving the sign of
   the +-3e-5 residual.  Its verdict would be the first real sign
   reading of `orbitWindowSemiLocalGate` over V.

AGENTS 7c law (37) is banked from this run: a polarization-built
quadratic form inherits the body quadrature's first-cell sliver as an
IDENTITY shift -(step/2) I on its diagonal only; eigenvalues at that
scale are quadrature, not physics - diagnose by checking the measured
offset against step/2 across radii before reading any sign near zero.

RH unclaimed; GATE 1 untouched; map unchanged (SPLIT branch).
