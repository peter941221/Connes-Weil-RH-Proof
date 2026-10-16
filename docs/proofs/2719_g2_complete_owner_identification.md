# Record 2719: G2 complete-owner identification at the n = 3 candidate balls

**Verdict: G2 IDENTIFICATION GREEN — THE STORED OWNER IS THE COMPLETE
OWNER (zero-set side).  NO RE-MEASUREMENT IS NEEDED.**  The stored
record-1980 known-zero lists at both candidate balls are certified equal
to the complete source-zero sets in the closed formal balls:

```text
+----------------+-----+------------+--------+------+---------+---------+----------+
| row            |  N  | R (formal) | window | known| exact   | margins | pins     |
|                |     |            | T+/Tc  | list | phase   | in / out| worst    |
+----------------+-----+------------+--------+------+---------+---------+----------+
| (14.1347,4)    |  4  | 48.208904  | 62.344 | 14+5 | 14 / 5  | 1.139 / | 7.8e-15  |
|                |     |            | 34.074 |  =19 | res 0.0 | 2.769   | 28 evals |
| (21.0220,5)    |  5  | 87.071987  | 108.094| 33+15| 33 / 15 | 0.925 / | 2.2e-14  |
|                |     |            | 66.050 |  =48 | res 0.0 | 1.030   | 66 evals |
+----------------+-----+------------+--------+------+---------+---------+----------+
```

Both rows carry the full fifteen-check identification discipline with
zero failed checks.  Because NOTHING was missing from the stored lists,
the record-2718 gate sign certificates were computed at the complete
owner all along: the "re-measurement on the complete owner" obligation
is a NO-OP, and rung (ii) of the named map-103 reopen probe closes at
model grade.

## Task card (bounded-progress gate)

```text
consumer    riemannHypothesis_of_four_point_span_contradiction_producer,
            via the record-2708 contract P2 duty (the finite-set ->
            shell-prefix identification, "still required" per the
            contract) -- rung (ii) of the named map-103 reopen probe
owner       the ACTUAL source-zero set in the closed formal balls
            B(rho_i, R_i); source zeros = nontrivial zeros (the lane's
            committed completed-source convention; orbit and
            healthy-target pins are separate construction nodes)
premise     the stored 1980 known lists (mpmath zetazero + per-point
            conjugate membership, "mirrors the metric owner") were
            enumerated but never identified with the complete ball
            zero set; record 2718's certificates are conditioned on
            that identification
criterion   E0-E9 below, all green per row => identification; any
            missing zero => OWNER-GAP-FOUND => re-measurement swing
budget      one WSL run: 45 s wall (phase walks to t = 108.1 at step
            0.02, Hardy-Z scans, zetazero walk, 94 pin evaluations)
stop        verdict recorded (this record)
```

## The identification discipline (all values in-run)

```text
E0  stored-metadata anchor  radius bitwise == stored 2032 fields
                            (48.208904068660146 / 87.0719873427753);
                            known counts == 19 / 48; owner cardinality
                            == 27 / 56; the independent zetazero walk
                            reproduces the op list ELEMENTWISE (bitwise
                            complex equality)
E1  pin-zero-ness           |zeta(1/2 +- i gamma_k)| < 1e-10 at dps 60
                            for every listed ordinate, BOTH signs,
                            evaluated directly: worst 7.79e-15 (row A,
                            28 evals) and 2.17e-14 (row B, 66 evals)
E2  exact upper count       N(T+) = (theta + Phi)/pi by the unwrapped
                            critical-line phase (record-2245 method):
                            14.0 / 33.0, residual EXACTLY 0.0
E3  exact conjugate count   N(Tc) = 5.0 / 15.0, residual EXACTLY 0.0
E4  independent enumeration Hardy-Z sign-change scan (no zero table):
                            14 / 33 ordinates, paired set agreement
E5  Trudgian uppers         2014: 17 >= 14 and 7 >= 5 (row A); 36 >= 33
                            and 18 >= 15 (row B); validity T >= e; the
                            2012 variant co-reads 16/7 and 35/17
E6  Platt-Trudgian scope    every ball point has |Im| <= Im(rho) + R
                            <= 108.09 + 1.5 << 3e12: ALL in-ball source
                            zeros are on the critical line and SIMPLE
                            (single vanishing factors suffice for P2)
E7  ball-edge margins       nearest included 1.139 / 0.925 INSIDE the
                            sphere; nearest excluded 2.769 / 1.030
                            OUTSIDE (bar 1e-6): the loop's 1e-10
                            membership pad is inert by 6+ orders
E8  environment audit       zetazero(4) gap 3.1e-19 vs the true
                            30.424876125859513210; the 1994 spurious
                            pin 27.67032193035704 carries |zeta| =
                            2.845 -> correctly rejected by E1 semantics
E9  owner separation        min pairwise separation 0.05 (= |rho -
                            gamma_1|), 5e4 x the pad; owner arithmetic
                            closes exactly: 19+4+8-4 = 27 and
                            48+4+8-4 = 56 (four orbit/target
                            coincidences deduped), matching the stored
                            cardinalities
```

The window geometry is delta-corrected (the record-2245 template used
the crude |Im z - gamma| <= R window): with delta = |Re(rho) - 1/2| =
0.05, the exact critical-line windows are T+ = Im(rho) +
sqrt(R^2 - delta^2) and Tc = sqrt(R^2 - delta^2) - Im(rho).  Both balls
reach BELOW the real axis (T- = -34.07 / -66.05), which is why the
conjugate membership matters here and did not at the record-2245 rows.

## Reading

1. **The named probe's two rungs are both closed at model grade.**
   Rung (i): the four gate sign certificates (record 2718).  Rung (ii):
   the complete-owner identification (this record) -- and the
   re-measurement clause dissolves, because a complete identification
   with zero gaps means the stored channels WERE the complete-owner
   channels.  The percent-grade flip budgets (record 2717), the
   forward-error rig (record 2718), and the zero-set completeness
   (here) together form the complete-owner gate certificate at the two
   candidate rows.

2. **What still separates this from a map-103 reopen motion is the
   Lean-formal side, not new numerics.**  The P2 identification in
   Lean (finite set -> shell prefix S_s), the P3 certified C4/C2 strip
   decay constants (still sampled from the record-2033 height grid),
   P4's shell inequalities as Lean facts, and the Lean absorption of
   the 2717/2718/2719 constants.  The freeze remains in place; this
   record does not reopen the family and does not claim the reopen
   clause fired -- it establishes that the probe's numeric content is
   complete.

3. **The 1994 kill-list corruption is confirmed confined.**  The
   record-1980 owner builder used mpmath zetazero (never the GAMMAS
   kill list), the E8 audit re-confirms both the true gamma_4 and the
   spurious pin's rejection, and the record-2245 impact note's scoping
   ("no Lean statement is affected") is re-validated at the candidate
   owners.

4. **The Platt-Trudgian simplicity import does double duty.**  Beyond
   on-line-ness (which collapses the in-ball zero set to the
   critical-line enumeration), simplicity of every in-ball zero is what
   makes P2's single vanishing factor per zero sufficient -- the
   convolution square's transform vanishes to order one at each node
   factor, matching order-one zeros.

## Nonclaims

- Cited-import + numeric certificate at MODEL grade: Trudgian 2014/2012
  and Platt-Trudgian 2021 are external theorems registered numerically
  (first in record 2245, re-registered here), not Lean facts.
- The owner-model constants (the rho binary64 floats, the
  formal-radius convention) are the stored record-1980 model constants;
  the identification speaks of the model balls.
- The Lean-side finite-set -> shell-prefix identification is NOT done
  here; P3 (certified C4/C2) and P4 (shell inequalities in Lean) are
  open; the freeze stands.
- No producer GO, no gate sign change, no SourceRH, no RH claim.

## Evidence

- `scripts/g2_complete_owner_id_2719.py` (imports the committed 1980
  owner builder and the record-2245 count-brick machinery verbatim;
  writes the artifact; `__main__` guarded)
- `results/2719_g2_complete_owner_id.json` (both rows: geometry, exact
  phase counts with residuals, Hardy-Z lists, Trudgian tables, edge
  margins, 94 pin evaluations, environment audits, failed-check lists;
  module sha256s)
- `results/2719_g2_run.log` (the run log)
- Inputs: `scripts/fourpoint_actual_owner_1980.py` (the owner builder),
  `scripts/routea_weighted_zero_owner_count_brick_2245.py` (phase /
  Hardy-Z / Trudgian machinery), `results/2032_gate_row_search.json`
  (stored row metadata anchoring E0),
  `docs/proofs/2718_gate_sign_rig.md` (the certificate this completes),
  `docs/proofs/2717_p5_n3_probe.md` (flip budgets),
  `docs/proofs/2708_joint_acceptance_contract.md` (the P2 duty).
