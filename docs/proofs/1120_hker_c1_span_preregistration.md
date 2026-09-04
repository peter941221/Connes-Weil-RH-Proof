# 1120 - (c) Hker closed via C1 exact annihilation at span level: pre-registration

Date: 2026-09-04.  Status: PRE-REGISTRATION committed BEFORE any run.
Consumer: the class-certificate chain of record 1118.  After 1119 the
(a)+(b) chain has `Hbox` as its only analytic named hypothesis; the last
missing named slot is (c) `Hker` (1118 prereg section 1c: ker R_true vs
ker R_mid).  1118 pre-registered two mechanisms, tried IN ORDER:

    C1. Exact annihilation: for concrete coefficient vectors of window
        tests, verify R . c = 0 as rational identities (norm_num).
    C2. Drift bound: |R_true - R| entrywise inside a committed rational
        drift box + slack-margin argument (requires law-34 enclosures on
        the moment integrals).

This record invokes C1 - at SPAN level, which is strictly stronger than
the per-instance form 1118 named and cheaper to verify: ONE identity
`R * K = 0` (3x5 entries, 8-term sums) closes EVERY coefficient vector
c = K . y at once.  C2 is NOT invoked.

## 0. Ground truth verified before registration (read-only precheck)

Committed-data lineage, verified by reading the generators and one
read-only Fraction recomputation (the probe below re-verifies
independently as the registered falsifier):

  (i)  `1115_rational_ingestion_preprocess.py` rationalizes R
       entrywise from the cert bundle (`R = F(R_mid)`), then builds K as
       the EXACT-Fraction RREF nullspace basis of that rational R with
       the generation-time assertion `mm(R, K) == 0` (line 199) and
       `det(R R^T) != 0` (rank 3);
  (ii) precheck recomputation over all three classes q28/q38/q48:
       R*K = 0 EXACTLY; qchain R == F(cert R_mid) entrywise (1112 cert
       for (2,8)/(4,8), 1113 cert for (3,8)); pivots [0,1,2], free cols
       [3,4,5,6,7], so K carries the canonical I_5 block at the free
       columns; entry sizes ~122 digits (R) / ~275 digits (K) - the
       R*K identity is 15 entries x 8-term sums, norm_num-feasible at
       maxHeartbeats 2e9 (1119 landed heavier identities).

Consequence (the point of the record): ker R = im K for the committed
rational data, so the T-box domain condition `R.mulVec c = 0` is, for
the certificate, the DESIGN constraint "choose the Stage-B test with
c in span K" - not an analytic hypothesis.  What remains physical (the
TRUE moment table R_true annihilating the test only up to the arb
midpoint displacement) is exactly 1118's C2 slot; per the 1118 decision
rule it stays OUT of this chain - the Lean theorems consume c in ker R
directly - and is booked below as a named T2-side obligation, never
silently assumed.

## 1. What lands

### 1a. Probe `docs/proofs/1120_hker_probe.py` (exact Fractions only)

Per class q28/q38/q48, ALL checks must PASS before anything is emitted:
  0. R*K = 0 exact (independent recomputation from committed JSON);
  1. rank(R) = 3: det(R R^T) != 0 exact;
  2. lineage: qchain R == F(cert R_mid) entrywise (correct cert per
     class);
  3. K canonical form: I_5 block exactly at the free columns, pivot
     block = -A_rref rows (i.e. K = RREF nullspace basis, the identity
     the Lean norm_num will re-prove);
  4. full chain E*R = A_rref and A_rref*K = 0 exact;
  5. print entry digit sizes (Lean feasibility record).
Falsifier: any FAIL => no Lean emitted, report the class, fall back to
the 1118 C2 SKELETON in a NEW preregistration (no threshold weakening,
no silent partial credit).

### 1b. Lean `ConnesWeilRH/Dev/C1HkerSpan.lean`

  - generic `hkerC1_of_RK0 : R * K = 0 -> forall y, R.mulVec (K.mulVec y)
    = 0` (pure algebra: mulVec_mulVec + zero_mulVec);
  - per class q28/q38/q48: `RK0_q* : Q*.R * Q*.K = 0` (norm_num, exact
    rational, raised budget; per-entry fallback registered as in 1119
    if any entry cannot close at 2e9);
  - span discharge at BOTH headline levels, per class:
      `tbox_spanK_q*`: radius hypotheses hG/hM + y =>
        (K y).(Mt.(K y)) <= U * (K y).(Gt.(K y)) - via tbox_q* with the
        hker slot closed by hkerC1/RK0;
      `absolute_spanK_q*`: hrep (ICgate literally on the LHS) + hnorm +
        Hbox + y => ICgate <= -mu_q* - via absolute_true_q*.
  - audit module: `#print axioms` on every public declaration (allowed
    set exactly {propext, Classical.choice, Quot.sound}); G3 fidelity
    examples: tbox_spanK_q28 elaborates with the radius hypotheses and
    conclusion literally as in 1119's audit, absolute_spanK_q28 with
    LHS literally `ICgate w.convolutionSquare` and RHS `-mu_q28`.

## 2. Gates (registered BEFORE the build)

G1: focused `lake build` of the two new modules on the ext4 mirror;
    acceptance = "Build completed successfully" footer AND zero
    `^error:` lines.  G2: axiom sweep all exactly standard, zero sorry.
G3: the fidelity examples compile with the literal shapes above.
G4: staged-file hygiene grep 0 matches before every commit.

## 3. Falsifiers (no threshold weakening)

Probe FAIL => C1 inapplicable => new preregistration for the C2
skeleton (1118 decision rule; this record reports partial and stops).
Any RK0_q* norm_num entry failing at 2e9 => split per-entry before any
other change (1119 discipline).  No data value may be edited; the
committed Q*/K/data modules are read-only inputs.

## 4. Run protocol

Commit (prereg + probe) BEFORE the probe run; commit Lean BEFORE the
first build; one root-caused fix commit per failing build; post-run
addendum after G1-G4.  RH NOT claimed; no map change keyed.

## 5. T2 startup assessment (decision memo, user-requested)

Inventory of what a D1-pinned Stage-B instance (1117 s2) needs, and
what this record changes:

  +--------------------------------------------------------------+
  | input                         | status after 1120            |
  +-------------------------------+------------------------------+
  | (i) coefficients c in ker R   | FREE: any y, c = K.y; the    |
  |                               | hker slot is C1-discharged   |
  | (ii) Hnorm (c.G_true.c = 1)   | normalization convention of  |
  |                               | the representative; law-34   |
  |                               | side, bookkeeping only       |
  | (iii) hrep: GATE(g) =         | pure Lean algebra over the   |
  |       c.M_true.c (matrix      | abstract data (1117 linearity|
  |       representation)         | layer); NOT yet landed - the |
  |                               | natural NEXT Lean record     |
  | (iv) contraction decay of the | numeric work on the true     |
  |      real iterative correction| 13-node shape = the 1116c    |
  |                               | model-consumption contract   |
  +--------------------------------------------------------------+

Verdict: GO, sequenced as (iii) THEN (iv): land the matrix-
representation lemma as its own Lean record (no numerics, data
committed), while the concrete instance waits for the 1116c contract
(1116 twin measured GATE/f0 = +0.45698 at true delta = 0 with k=1
domination configuration-LOCAL - Stage A does essential work, so the
instance must consume the real per-node decay, not a model surrogate).
After (iii), the ABSOLUTE headline `ICgate <= -mu_a` holds on the
D1-pinned g modulo exactly ONE numeric input (iv).  Bookkeeping note:
(ii) scales y without changing the direction of any inequality (the
bound is homogeneous of degree 2 in c on both sides).
