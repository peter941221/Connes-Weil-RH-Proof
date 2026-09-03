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
