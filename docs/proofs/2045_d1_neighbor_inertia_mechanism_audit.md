# 2045 — D1 neighbor-mechanism audit (arXiv 2608.13637) + projection-difference interface: PARTIAL-TRANSFER / COUNTING-ONLY, candidate IC-mechanism registered

Verdict: **PARTIAL-TRANSFER / COUNTING-ONLY**.  The 2026-08 neighbor
mechanism (rank-trace + Sylvester inertia on finite compressions of
Weil's Hermitian form, replacing the RH positivity premise) does **not**
transfer to the mainline obligation, and the audit says exactly why:
the neighbor machinery reads the **inertia (a count)** of a compression,
while the mainline obligation is the **sign (an evaluation)** of one
projection-difference pairing.  Index data cannot decide a single
vector's sign.  The transferable residue is registered as candidate
mechanism **IC (inertia-compression)** with kill conditions (section 4).

On the way, the exact interface between the corrected trace identity
(record 016) and compression/inertia language is derived and verified
in **exact rational arithmetic** (6/6 cases, status
PROJECTION-INERTIA-EXACT-PASS), producing two scoped no-gos:
**NO-GO-OPERATOR-SIGN** and **NO-GO-CORNER** (section 2), plus one
recorded false identity and its exact characterization (section 3).

Artifacts: `results/2045_projection_inertia_exact.json`; rig
`scripts/routea_projection_inertia_exact_2045.py` (WSL ext4 mirror,
`fractions.Fraction` only).  Literature level: arXiv (unrefereed).

## 1. What the neighbor paper does (as read, not re-derived)

arXiv:2608.13637, "More than two thirds of the zeta zeros are simple
and on the critical line" (2026-08-13; LLM-credited; ships a Lean 4
formalisation of Theorems A and B in its Appendix A; adversarial
multi-instance review per its own front matter).  Unconditional claims:
>= 2/3 of zeros (with multiplicity) simple and on the line in the
Montgomery-Taylor window (0.6725), >= 5/6 distinct (0.8362).

Abstract mechanism, verbatim: *"the Riemann hypothesis, classically
needed to read the zero side as a positive sum over real ordinates, is
replaced by a rank-trace inequality applied to a finite compression of
Weil's Hermitian form, with Sylvester's law of inertia handling off-line
pairs."*  Chain as cited by the paper: Montgomery 1973 -> Bombieri 2000
(negative index of truncations of W **counts off-line pairs**) ->
Aryan 2022 / BGSTB 2024 (unconditional second moments) ->
Goldston-Suriajaya 2025/26 -> Theorem A (inertia bound (Z)+(L)
replaces positivity).  Its own ceiling statement, verbatim:
*"Nothing in the method distinguishes between 'two thirds' and 'all'."*

Ledger note (added 2026-09-27 with the section-5 correction): the paper
was ALREADY in the project ledger with a deeper mechanism reading than
this section's - see records 1347 (authors: Alpoege--Furman; the A1
capacity exponent fused with the paper) and 1348 (the appendix
method-ceiling notes read the constants chain term by term: the ceiling
is exactly "3 - R(psi)", only tr and the HS second moment enter, "the
floor of the main block is never required", "the method cannot SEE
near-zero directions - it averages over them").

Structural read in mainline language:

```
neighbor (Z): count off-line pairs = negative index of a compression
neighbor (L): rank-trace + Sylvester inertia converts the count bound
neighbor (P): unconditional second-moment input (prime side)
mainline need: the SIGN of <theta_S(g), A theta_S(g)> for ONE owner
               vector, uniformly over hypothetical zeros (COVER)
```

Counting and signing are different layers: negative index > 0 says
*some* direction is negative, not that the owner's vector is.  Index
0 would imply the sign, but no input in the neighbor chain supplies
index 0 for the owner class (their extreme configuration is
rank P = 0, n_+(Q) <= N/2 - the opposite corner).  Hence COUNTING-ONLY.

## 2. Exact interface lemmas and the two scoped no-gos

At the record-016 interface: P a projection, H = 2P - 1, u unitary,
P_hat = u^*(1-P)u, T_S = u^*[H,u], Q := u^* P u = 1 - P_hat,
F_g = g^* g, theta_S(F_g) = |theta_S(g)><theta_S(g)|.  All statements
below are verified EXACTLY (rational arithmetic, no tolerance) in six
cases: 2x2 Pythagorean rotations t = 1/2, 1, 2; rational quaternion
3x3 rotations (involution; e1-axis) with P of rank 1 and 2.

```
L1  T_S = u^* H u - H = 2(Q - P)
L2  W_S(F_g) = -(1/2) Tr(theta_S(F_g) T_S) = Tr(theta_S(F_g)(P - Q))
    => QW(g,g) = <theta_S(g), (P - Q) theta_S(g)> + Pole_lambda(g)   [016 (3)]
    (row-gate normalization of record 1931: ICgate = -qw reads with -A)
L4  D(F_g) = (1/2) Tr(theta_S(F_g)(T_S - P T_S P))
           = Tr(theta_S(F_g)(Q - P Q P));
    with P = diag(1_k, 0): Q - PQP = [[0, B],[B^T, C]], B = Q[0:k, k:],
    C = Q[k:, k:], Q = u^* P u  -> INDEFINITE iff B != 0 iff [P, Q] != 0
L5  QW + D = Tr(theta_S(F_g) P P_hat P) = PositiveTrace >= 0   [016 (6),(7)]
    and the (016 (5)) form of D coincides with the L4 form
```

Engine identity for A := P - Q (one line, exact, e.g. expand both sides):

```
(2Q - 1) A = 2QP - P - Q = -A (2P - 1),
equivalently the classical anti-identity (2P - 1) A (2Q - 1) = -A.
```

Consequences (all verified exactly):

1. **spec(A) = -spec(A).**  Given Ax = lambda x, lambda != 0, the pair
   u0 = (2P-1)x, v0 = (2Q-1)x satisfies A u0 = -lambda v0, A v0 =
   -lambda u0, so A(u0+v0) = -lambda (u0+v0); the degenerate case
   u0 + v0 = 0 forces Px = (1+lambda)x/2, Qx = (1-lambda)x/2 and then
   Ax = lambda x *is* the -lambda eigenvector.  Sample verification:
   for t = 1/2, x = (3,1), lambda = 4/5 gives w = u0 + v0 =
   (6/5, -18/5) and A w = -(4/5) w exactly.
2. **A >= 0 <=> A = 0 <=> A <= 0 <=> [P, u] = 0.**  (A >= 0 puts
   spec(A) in [0, inf); symmetry puts it in (-inf, 0]; a self-adjoint
   operator with spectrum {0} is 0.)  **NO-GO-OPERATOR-SIGN**: no
   mechanism can prove the owner obligation by proving P - Q >= 0:
   for any owner whose semilocal phase u_S does not commute with the
   cutoff P, A is indefinite with balanced +/- inertia - and
   [P, u_S] = 0 would make W_S = 0, i.e. empty.  The mainline
   obligation is irreducibly a **vector-compression** statement: the
   sign of the pairing for the SPECIFIC theta_S(g), with A itself
   indefinite.  (This is the operator-level form of the admissible
   non-split mechanism classes of AGENTS section 2.)
3. **NO-GO-CORNER**: D is the pairing of theta_S(F_g) with
   Q - PQP, whose block form is [[0, B],[B^T, C]] in the P-split.
   For x = (x1, x2): <x, (Q-PQP)x> = 2<B x2, x1> + <C x2, x2>, and x1
   is free, so the corner is indefinite whenever B != 0 (i.e. whenever
   [P, Q] != 0, the only live case).  No sign of D follows from the
   block structure alone; corner-inertia arguments are dead as a class.

Exact sample rows (QW = Tr(theta(P-Q)), D = Tr(theta(Q-PQP)),
PT = QW + D, with PSD rational theta):

```
+------------+-----------------------+------+------+------+-----------+
| case       | A (display)           |  QW  |  D   |  PT  | neg wit   |
+------------+-----------------------+------+------+------+-----------+
| 2x2 t=1/2  | [[16,12],[12,-16]]/25 | 24/25| 8/25 | 32/25| [-12,7]   |
| 2x2 t=1    | diag(1,-1)            |   0  |   2  |   2  | [-11,-12] |
| 3x3 rank1  | 2x2 block + 0         |  -   |  -   |  -   | found     |
| 3x3 r2 rot | 2x2 block + 0         |  -   |  -   |  -   | found     |
+------------+-----------------------+------+------+------+-----------+
| 3x3 r2 inv | A = 0 (degenerate)    |   0  |   0  |   0  | n/a       |
+------------+-----------------------+------+------+------+-----------+
```

(3x3 entries elided to the witness column: every REQUIRED check passes
in all six cases; the degenerate branch verifies u commutes with P and
QW = D = PT = 0.)  Note 2x2 t = 1 shows QW = 0 with A != 0: even a
nontrivial rotation can have a vanishing owner pairing - the sign is
genuinely a property of the vector, not of the operator.

## 3. One recorded false identity (found by the exact rig)

The tempting conjugation claim **u^* A u = -A is FALSE in general**.
The rig caught it on the first run (t = 1/2: u^T A u = [[-16,-12],
[-12,16]]/25 + ... != -A).  Exact characterization, measured 6/6:

```
u^* A u = -A  <=>  u^2 P = P u^2
```

(expand U = u^* P u: u^* A u = Q - (u^2)^* P u^2, which equals Q - P
iff u^2 commutes with P).  True exactly in the three involution cases
(u^2 = 1) and false in the genuinely rotating ones.  The correct engine
is the two-sided identity of section 2; the false one is retained in
the artifact as `L3_uT_A_u_eq_negA_general` with the diagnostic pair
(`L3_u2_P_commute`) so the failure mode cannot silently return.

## 4. Registered candidate mechanism IC (inertia-compression), unpriced

```
IC: prove  neg-index( A restricted to V ) = 0  where
    A = P - Q and V = range(theta_S(g))  (the owner image space),
    via a rank-trace inequality + Sylvester inertia - the neighbor
    toolkit - on the OWNER OBJECT rather than on the zero-counting
    compression.
```

Status: PROJECT CANDIDATE, no measurements, no pricing.  RETIRED
UNPRICED by record 2049 (kill condition 3 fires on the record-1348
evidence; see also the section-5 correction).  Note A|_V is
the compression of an indefinite operator (no-go 2 of section 2), so
any IC proof must use V-specific structure; A's global negative inertia
is exactly half its rank (spectrum symmetry, item 1 above), which is
why a pure-inertia input cannot suffice.

Kill conditions, frozen:

1. If the required rank-trace input is equivalent to qw >= 0 in
   disguise (an F82-style sign-conserving split), IC is dead on
   arrival - check by reduction before any pricing.
2. If the required bound is a phase-Toeplitz smallness statement, IC
   re-derives the closed epsilon-gap lane (laws F48-F58) - retire it
   without new work.
3. IC needs an input of second-moment type (the neighbor's (P));
   the owner class has no unconditional mean-value theorem for
   theta_S(g) on record.  If no input source exists, IC is an empty
   shell and dies unpriced.  (The neighbor's input structure is read
   exactly in record 1348 section 1: Lemma 3.2 consumes tr and the
   Hilbert-Schmidt second moment only; that is the moment shape IC
   would need on the owner space, and the project's own moment-floor
   lane 1347/1348/1349 measures the corresponding gap.)
4. Toolkit availability (to check, not checked here): von Neumann
   trace inequality and Sylvester inertia directions are mathlib
   bricks per the neighbor's appendix; verify presence in the
   project's pinned mathlib v4.30 before any Lean-side use.

## 5. Ledger changes made by this record

- CORRECTION (2026-09-27, same day, after a full-repo `git grep`): the
  earlier claim that the neighbor paper was absent from the ledger is
  **FALSE and withdrawn**.  `git grep -l '2608\.13637'` returns nine
  pre-existing ledger files, earliest 2026-09-12: `1344` (the s3b
  method-ceiling branch), `1347` (A1 capacity exponent, fused with the
  paper), `1348` (deep-ladder prereg AND the appendix method-ceiling
  notes), `1349` (A1b verdict), `1354`, `1405`, plus `docs/map/README.md`
  and `route/000_rh_mainline/README.md`.  Record `1348` section 1 had
  already read the mechanism exactly (ceiling = "3 - R(psi)"; only tr
  and the HS second moment enter; the main-block floor is never
  required) and section 2 had measured the project's own moment-floor
  gap (gamma = 0.3355).  What in THIS record is new and stands: the
  exact record-016 interface lemmas, the engine identity, the two
  no-gos, the recorded false identity, and the exact rig.  What does
  NOT stand: this record's literature-novelty framing and the IC
  registration as a fresh mechanism - IC is the already-open question
  `1344` s3b / `1348`, and its kill condition 3 fires on the `1348`
  evidence.  Adjudicated in record 2049.
- (Withdrawn bullet, kept for the audit trail: "the neighbor mechanism
  is now IN the project ledger (it was absent; grep ... returned
  nothing before this record)".)
- Bombieri's negative-index fact (negative index of truncations of W
  counts off-line pairs) is recorded as the counting-layer partner of
  the project's own sign obligation - the same pyramid, different
  layer.
- COVER is untouched: the neighbor result is a density statement
  (>= 2/3), the mainline needs every hypothetical zero (exception-free
  uniformity, map 107).  Nothing here changes the COVER obligation.

## 6. Scope and non-claims

- The neighbor paper's numbers are NOT re-derived here; its chain is
  cited as arXiv claims, community verification unconfirmed; treat as
  to-be-re-derived literature, not as project evidence.
- The interface lemmas are exact ALGEBRA (toy matrices, rational
  arithmetic) - the rearrangement of committed record-016 statements
  plus the engine identity.  No owner measurement was made; no
  analytic input; no Lean.
- The two no-gos are scoped to the stated hypotheses (P projection,
  u unitary, the 016 interface) and to their mechanism classes.
- Not a producer theorem.  Not RH.  Route statuses are unchanged (D
  stays CLOSED by F82; the record-2039 section-4 direct-defect-
  negativity shape remains open, now with the counting/signing
  distinction attached).