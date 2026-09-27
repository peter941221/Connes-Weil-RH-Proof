# 2049 — IC kill-condition check (first pass): ledger correction, mathlib toolkit evidence, IC retired unpriced

Verdict: **IC-RETIRED-UNPRICED / LEDGER-CORRECTION-REGISTERED**.  The
first pass over the four frozen kill conditions of record 2045 section 4
found one correction (the neighbor paper was ALREADY in the ledger, more
deeply read than record 2045 claimed - withdrawn in place) and one
kill-condition firing: IC's required input has no source on record and
the question it restates is an OPEN LANE already registered as 1344 s3b.
Toolchain condition 4 resolves cheaply: six of the seven bricks the
neighbor paper needs are present in the pinned mathlib, and the seventh
(the named von Neumann trace inequality) is a four-line assembly of
three present bricks.  No probe; no Lean.  Artifact:
`results/2049_mathlib_brick_check.json`; tool
`scripts/mathlib_brick_check_2049.py`.

## 1. The correction (record 2045 section 5)

Record 2045 claimed the neighbor mechanism (arXiv:2608.13637) was absent
from the project ledger.  It was not.  `git grep -l '2608\.13637'`
returns nine tracked files before 2045, earliest 2026-09-12:

```
+-------------+--------------------------------------------------------+
| record      | what it already says about the paper                   |
+-------------+--------------------------------------------------------+
| 1344        | s3b method-ceiling branch: "the 2608.13637 method      |
|             | ceiling" adjudicated BEFORE digits (lines 151/170)     |
| 1347        | authors (Alpoege-Furman), Lean-4 verified, "proof      |
|             | discovered by Claude"; A1 capacity exponent fused      |
|             | with the paper; asks "why does compression top out     |
|             | at a proportion?"                                      |
| 1348        | deep-ladder prereg AND the appendix "method-ceiling    |
|             | notes": the ceiling is exactly "3 - R(psi)"; Lemma     |
|             | 3.2 consumes tr and the HS second moment ONLY; "the    |
|             | floor of the main block is never required"; "the       |
|             | method cannot SEE near-zero directions - it averages   |
|             | over them"                                             |
| 1349        | A1b deep-ladder VERDICT (CRITICAL-PINNING)             |
| 1354, 1405  | later preregs citing the paper                         |
| map/README, | the map and the route-000 navigational text also       |
| route/000   | mention it                                             |
+-------------+--------------------------------------------------------+
```

Record 2045's section 5 now carries the correction inline (the false
novelty claim is withdrawn, the withdrawn text kept for the audit
trail); what survives from 2045 unchanged: the exact record-016
interface lemmas, the engine identity, NO-GO-OPERATOR-SIGN,
NO-GO-CORNER, the recorded false identity, and the exact rational rig.
What does not survive: the literature-novelty framing and the IC
registration as a fresh mechanism (section 4 below).

Root cause, stated for the rules file: the earlier grep was run over a
subtree with unanchored/too-narrow patterns; a full-repo `git grep` on
the bare arXiv id returns nine files.  The instrument lesson is
registered in record 2050.

## 2. What 1348 already established (so 2049 does not duplicate it)

- The ceiling is a MOMENT constant: only the first and second spectral
  moments of the compression enter; the main-block floor is never used;
  this is the mechanical meaning of "proportion, not ALL".
- The project's own moment-floor gap was measured on the committed A1
  ladder: mean ~ m^-0.6528, lambda_min ~ m^-0.9884, gap exponent
  gamma ~ 0.3355, spectrum flat (participation ~ 1.03 of full
  dimension); the conjectural target form is
  lambda_min >= c_eps m^(-1/3-eps) mean.
- Rails: their G~ acts on the height-sample space, the project's G_m on
  the test-net space; the contrast is a statement about method
  FAMILIES, not a theorem connecting the two matrices.

## 3. Kill condition 4 resolved: toolchain evidence

Pinned toolchain: `leanprover/lean4:v4.30.0`, mathlib rev
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, tree
`.lake/packages/mathlib/Mathlib` (8000+ files, single-pass scan).

```
+--------------------------------------+---------+-----------------------------------------+
| brick                                | verdict | evidence (file:line)                    |
+--------------------------------------+---------+-----------------------------------------+
| sylvester_inertia_uniqueness         | PRESENT | QuadraticForm/Signature.lean:120,132    |
| sylvester_inertia_existence          | PRESENT | QuadraticForm/Real.lean:16,66           |
| birkhoff_von_neumann                 | PRESENT | Analysis/Convex/Birkhoff.lean:152,170   |
| rearrangement_inequality             | PRESENT | Algebra/Order/Rearrangement.lean:70,116 |
| hermitian_trace_eq_sum_eigenvalues   | PRESENT | InnerProductSpace/Trace.lean:39,44 AND  |
|                                      |         | Analysis/Matrix/Spectrum.lean:237       |
| singular_values_api                  | PRESENT | InnerProductSpace/SingularValues.lean   |
| von_neumann_trace_inequality (NAMED) | ABSENT  | no trace_mul_le / trace-singularValues  |
|                                      |         | inequality anywhere in the tree         |
+--------------------------------------+---------+-----------------------------------------+
```

Reading: the neighbor's claimed bricks are half-present-and-half-
assemblable.  Sylvester's law of inertia is present in BOTH halves (as
congruence invariance of the inertia indices of real quadratic forms -
`QuadraticMap.Equivalent.sigPos_eq`/`sigNeg_eq` - and as the existence
of the +-1 weighted normal form).  The named von Neumann trace
inequality is absent, but the HERMITIAN case (the only case the IC
mechanism needs, A = P - Q being a difference of projections) is a short
assembly of present bricks:

```
tr(AB) = sum_ij alpha_i beta_j |<u_i, v_j>|^2      [spectral bases of
                                                    Hermitian A, B]
       <= sum_ij |alpha_i| |beta_j| p_ij           [p doubly stochastic]
       <= sum_i |alpha_i| |beta_i| = sum_i sigma_i(A) sigma_i(B)
                       [Birkhoff: p = convex combination of permutation
                        matrices; rearrangement: aligned pairing
                        maximizes]
```

so condition 4 does NOT kill IC; it makes the Lean side cheap (one new
proof of a textbook lemma, four steps, all ingredients present).

## 4. Kill condition 3 FIRES: no input source on record

The frozen rule (2045 s4): "IC needs an input of second-moment type ...
If no input source exists, IC is an empty shell and dies unpriced."

Audit of the ledger, 2026-09-27:

- The neighbor's own inputs are read exactly in 1348 s1: the zero side
  consumes rank-trace bookkeeping (tr, HS second moment) and the prime
  side consumes the Montgomery-Vaughan mean value of the window
  functional; the ceiling is the moment constant 3 - R(psi).
- The ledger's unconditional second-moment material lives in other
  lanes: the A1 capacity lane (1347/1348/1349) and the tail layer
  (1913 Hardy tail moment decay, 1738 joint symbol and tail sampling).
  None of them is an unconditional mean-value theorem for theta_S(g) on
  the owner class.
- `theta_S` and second-moment vocabulary co-occur in exactly ONE
  document before this record: record 2045 itself (the registration
  being audited).

Therefore kill condition 3 fires and **IC is retired unpriced**.  The
reopen condition is sharp and named: produce a SECOND-MOMENT input for
theta_S(g) on the owner class (an unconditional mean-value statement
for the owner image), or show that such an input follows from an
existing lane.  Absent that, IC is a restatement of an already-open
question (below) and must not consume desk time.

## 5. Relation to the existing lanes (no double counting)

IC as registered in 2045 is the open question of record 1344 s3b - "why
does the compression method top out at a proportion?" - restated in
016 language, and the project's quantitative version of it is the
moment-floor gap of 1348 s2 (gamma ~ 0.3355).  The desk item therefore
stays in the A1/moment-floor lane; the IC registration is closed rather
than parked, because two registrations of one question invite
double-counting.

## 6. Ledger changes and non-claims

- Record 2045 section 5 corrected in place (correction dated and the
  withdrawn text kept); section 4 status updated to RETIRED UNPRICED.
- `docs/map/README.md` batch block: the neighbor-mechanism entry now
  points at 1344/1347/1348/1349 and at this record's adjudication.
- New instrument: `scripts/mathlib_brick_check_2049.py` (single-pass,
  boundary-anchored patterns, ASCII-safe printing) with artifact
  `results/2049_mathlib_brick_check.json` - reusable for any future
  Lean-side plan that rests on "mathlib has X".
- Non-claims: no mathlib build was run; the brick rows are SOURCE
  reads at the pinned rev (the tool greps the tree).  The von Neumann
  assembly is sketched, not formalized.  No probe digits, no Lean, no
  producer theorem, not RH.  The neighbor paper's own numbers are not
  re-derived here (that remains record 1348's reading plus its rails).