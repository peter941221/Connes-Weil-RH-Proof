# 1111 - E0 promoted to Lean: the S-lemma top-bound bridge (pre-registration)

Date: 2026-09-03 (night).

Status: PRE-REGISTRATION, committed BEFORE the Lean build. User gate
OPENED this session ("可以Lean" 2026-09-03); 1105 authorized the
direction, 1108/1109/1110 named it next #3 for three records.

WHAT E0 IS (verbatim provenance): prompt-006 plan entry E0 ("Finsler
乘子证书", reply ledger 006 section Q4) - search multipliers NU so
the pencil T(NU) = U*G - M - (R^T NU + NU^T R) is PSD on the
truncated basis, needing NO K-inverse. 1105 authorized
re-registering E0 as the SOS-identity certificate; records
1108/1109/1110 then PROVED EXACTLY THAT E0's linear-algebra core
WORKS as a certificate machine (T(NU*) PSD with f(NU*) = the
constrained top: exact trust-region duality, no mu-sign surgery).
This record promotes that core to a formal Lean bridge - the
INGESTION TEMPLATE for every future certified number.

## 1. What is formalized (and what is NOT)

Formalized, in ConnesWeilRH/Dev/E0SlemmaBridge.lean + paired Audit:

  (1) `sLemmaPencil` (n x n, entries in R): U • G - M -
      (R^T * NU + NU^T * R), shapes R : m x n, NU : m x n (the
      1109 convention - R^T*NU and NU^T*R both n x n).

  (2) HEADLINE `isTopBound_of_psd`:
      if the pencil is PSD (Matrix.IsPosSemidef) then
      `isTopBound U G M R`, i.e. for EVERY c with R.mulVec c = 0:
          dotProduct c (M.mulVec c) <= U * dotProduct c (G.mulVec c).
      This is the exact implication 1108-1110 USE: on the kernel the
      NU term contributes ZERO to the quadratic form
      (c^T R^T NU c = <Rc, NU c> = 0), so ANY multiplier that makes
      the pencil PSD carries the whole bound - the same fact that
      kept 1108's conclusion alive through its erratum.
      G-positive-definiteness is NOT needed for the implication
      (registered as a hypothesis-free lemma on purpose).

  (3) `ratio_le_of_psd`: the Rayleigh-quotient form for G > 0
      (c^T M c / c^T G c <= U when Rc = 0, c^T G c > 0) - the
      literal sentence "certified top <= U" of the float-domain
      records.

  (4) TOY INGESTION EVIDENCE: one explicit numeric witness
      (n = 2, m = 1, R = ![![0,1]], M = !![0,1],[1,0]], G = I,
      U = 0, NU = ![![-1,0]] so the pencil is EXACTLY 0 - PSD by
      the zero matrix) with the bound discharged by norm Numeral-
      level tactics. Proves the template accepts closed data; the
      real data ingestion is NOT this record (see 2).

NOT formalized (scope discipline):

  - NO concrete G/M/R from 1108/1109/1110 (transcendental float
    data - needs 1112's rational enclosures first);
  - NO function-space statement (the c -> sum c_k phi_k map, the
    window class, the Q-F2 gap = I-C, record 1114 fronts it);
  - NO gate Prop discharge, NO eigenvalue/sSup statements
    (isTopBound is the sSup-free restatement - sup bookkeeping
    deferred to the day it is consumed);
  - NO claim that the toy is a window class; RH unclaimed; map
    unchanged; README untouched.

## 2. Verdict mapping (literal, law 42)

  GREEN:  lake build of both modules finishes with the footer
          "Build completed successfully" AND zero ^error: lines
          AND the Audit module's #print axioms shows exactly the
          three standard axioms on every declaration AND
          sorryAx count 0 in the logs.
  RED:    any of the above fails; fixes registered before retry
          (1101 procedure); no threshold semantics here - build
          acceptance is binary evidence from the log (WSL toolbox
          rule: log not exit code).

Escalation ladder if Mathlib's IsPosSemidef API fights: unfold to
the ∀ x, 0 <= ∑ i, x i * mulVec ... elementwise form (the toy and
headline both live in that form); the theorem statements are the
contract, tactic routes are free.

## 3. What this brick buys for the map

  - 1112's design target becomes precise: produce RATIONAL entry
    enclosures [lo, hi] for (G, M, R, NU, U) at (2,8) and (4,8)
    whose interval pencil is PSD - then a future ingestion brick
    proves IsPosSemidef for the MIDPOINT rationals by
    rational Cholesky inside Lean (native_decide is viable only at
    small n and modest denominators - a registered open question,
    not an assumption);
  - 1114 (I-C) inherits a formal consumer: whatever function-space
    statement is eventually needed must conclude `isTopBound` on
    coordinates to plug into (2).

## 4. Environment

Windows tree source of truth; build-only WSL ext4 mirror; focused
targeted build via scripts/run_resource_aware_task.sh
(lake build ConnesWeilRH.Dev.E0SlemmaBridge
ConnesWeilRH.Dev.E0SlemmaBridgeAudit); log local (gitignored);
numbers and statements live in this doc's post-run addendum.

## 5. Post-run addendum (2026-09-03 night) - VERDICT: GREEN

HEAD of pre-run commit: 47e55db. Final build (run 6):
"Build completed successfully (1772 jobs)", ZERO error lines, ZERO
warnings attributable to the new modules, and all three public
declarations print exactly [propext, Classical.choice, Quot.sound]
(sorryAx count 0):

    isTopBound_of_psd   (headline bridge)
    ratio_le_of_psd     (Rayleigh-quotient form, G > 0)
    ingestion_toy       (closed-data witness, pencil exactly 0)

Realized-vs-registered notes (literal):

- the PSD predicate landed on Mathlib's REALIZED name
  `Matrix.PosSemidef` (section 1 wrote "Matrix.IsPosSemidef" - the
  4.30 API spells the predicate PosSemidef with
  posSemidef_iff_dotProduct_mulVec as the quadratic-form bridge;
  same contract, name corrected by evidence);
- the algebra came out as: expand the quadratic form IN PLACE in
  the working hypothesis (sub/add/smul_mulVec +
  dotProduct_sub/add/smul), kill each multiplier term via the
  identity  c.T*(A*NU)*v c = (R*vc) .T (NU*vc)  (orientation fix:
  Mathlib's mulVec_mulVec folds, does not split - rewrite with
  the arrow reversed), then rw hc, zero_dotProduct, and linarith;
- G-positive-definiteness never entered the headline proof (as
  registered: the implication is hypothesis-free in G); the toy
  needed one explicit-argument fix (NU is invisible in the goal,
  provided with (NU := ...) by the caller).

Run ledger (build iterations, zero semantic changes after run 2's
design note):

- run 1  RED: bad import name (Data.Matrix.Notation -> Basic).
- run 2  RED: mulVec_mulVec orientation + nonexistent
         smul_mulVec_assoc + a target-matching hexp design that
         overshot (vecMul atom rewrites); in-place restructure.
- run 3  RED: last mile - U .T (scalar) needed smul_eq_mul and the
         duplicate zero_dotProduct rw missed (all-occurrences
         rewrite had already closed both).
- run 4  GREEN (1772 jobs); runs 5-6: warning hygiene only
         (unused simp args / dead norm_num removed - linter
         honesty, law 39 direction: proofs tightened to what they
         actually use, no threshold semantics touched).

What 1112 inherits (concretely): the ingestion contract is
`(sLemmaPencil U G M R NU).PosSemidef` over (Fin 8) rational data -
1112 must emit (G, M, R, NU, U) as rationals with an interval-
provable PSD pencil; a future ingestion brick then closes
PosSemidef on the midpoint data (via diagonal Cholesky evidence -
`PosSemidef.of_dotProduct_mulVec_nonneg` + rational sum-of-squares,
or native_decide at modest denominators - registered OPEN, not
assumed).  The I-C statement (1114) must conclude `isTopBound` on
coordinates to plug in.

RH unclaimed; no gate Prop discharged; map unchanged; README
untouched.
