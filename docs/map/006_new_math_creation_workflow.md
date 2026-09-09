# 1227 - New-math creation workflow (NM loop)

Date: 2026-09-09.

Status: PROCESS AUTHORITY, binding for every new-math campaign opened from
this record onward. This record proves no new RH theorem, claims no sign,
and registers no candidate survival. RH is not claimed.

Map role: supporting process record under the binding ruling
[`003`](003_b1_b5_minimal_exit_route_selection.md). It establishes the
creation loop that complements the project's audit-and-falsify loop
(records 1043-1226). It changes no route selection, no endpoint authority,
and no frozen route; it opens an idea-generation mode with its own
registered gates. The companion preregistration (workflow establishment +
first sweep round) is record
[`1227`](../proofs/1227_nm_loop_workflow_and_sweep_preregistration.md).

## 0. Why a creation workflow is needed now

Records 1043-1226 built a complete audit-and-falsify machine: every route
was preregistered before its runs (law 42), every numerical claim stayed
MODEL-labeled until certified (law 65), and every dead end carries a
committed file:line witness. That machine has now spent the enumerated
attack lines inside the imported framework:

```text
+--------------------------------------------------+----------------------------+
| Line                                             | Terminal status            |
+--------------------------------------------------+----------------------------+
| B5 producer campaign (budget-only, bare stage-3) | refuted/frozen 1140-1211   |
| Line B (Bombieri finite positive owner)          | frozen by explicit         |
|                                                  | directive (records         |
|                                                  | 1147-1196)                 |
| Route-1 prime-free reference (5x no-go)          | closed 1197-1209           |
| Signed-tail recon, exit (a)                      | formally dead, record      |
|                                                  | 1226 (K1, committed as     |
|                                                  | A1/A1b)                    |
| Cand-B entrywise campaign                        | withdrawn, record 1225     |
|                                                  | section 2 (target has no   |
|                                                  | witness)                   |
| Moving projection family (B5 Stage A/B)          | FP response RANK-3         |
|                                                  | non-separable, record      |
|                                                  | 1224 sec. 3f/3g;           |
|                                                  | instrument check running   |
|                                                  | (record 1225 sec. 4)       |
+--------------------------------------------------+----------------------------+
```

The record 1226 route ruling leaves the UNIVERSAL NON-BUNDLED CONTRACT
shape (projection-side `L4`, Bombieri-side `A4`) as the only surviving
producer shape, and the gate `0 <= qw g` is RH-equivalent by design
(records 1124/1140). Progress from here requires a new positivity
mechanism, not more labor on enumerated routes. The bottleneck has shifted
from verification to idea supply. This document registers the loop by
which new mechanisms are generated, screened, dry-fired, and promoted.

## 1. Why a creation loop is viable here

Three project assets that historical RH attempts generally lacked:

```text
+---------------------------+------------------------------------------------+
| Asset                     | Effect on the creation loop                    |
+---------------------------+------------------------------------------------+
| The no-go ledger (~30     | Compresses the search space into a corridor:   |
| formalized obstructions,  | a candidate mechanism is screened against      |
| records 1140-1226, each   | known necessary conditions (section 3) in      |
| with a committed witness) | hours instead of rediscovering an obstruction  |
|                           | in campaign-weeks.                             |
+---------------------------+------------------------------------------------+
| Machine verification      | A guessed identity or inequality builds the    |
| (Lean + law-34 certified  | same day; the convince-the-community           |
| numerics + axiom audits)  | bottleneck is replaced by an axiom audit.      |
+---------------------------+------------------------------------------------+
| MODEL rigs (1212/1213/    | Ideas dry-fire numerically at law-65 status    |
| 1225 twins + the          | against a committed positive control before    |
| calibrated positive       | any Lean investment.                           |
| control, record 1225      |                                                |
| sec. 4)                   |                                                |
+---------------------------+------------------------------------------------+
```

Honest constraints, registered so no round forgets them:

- The gate is RH-equivalent: any mechanism that passes the full loop IS a
  proof of RH. The loop raises the screening rate; it does not raise the
  base rate of ideas.
- The framework (CC20/Yoshida selected test family) was imported, not
  generated here; mechanisms outside its analytic idiom must be translated
  into explicit-formula language before the screen can judge them.
- The external-AI directive (2026-09-03) stands: beat 1 is literature
  retrieval, never dialogue.

## 2. The loop

```text
   (1) SWEEP            (2) SCREEN           (3) PROTOTYPE         (4) PREREG
  literature      --->  shape filter    --->  MODEL dry-fire   --->  campaign
  + corpus              (paper-only:          (positive control     record
  mining                U1-U4 + the           first, then           (Stage-0
  (read-only,           route-specific        detector)             audit +
  queries registered)   spec)                                       law 42)
```

### Beat 1 - SWEEP

Input: the corridor spec (section 3). Activity: retrieve candidate
mechanisms from arXiv, Mathlib, the project corpus, and the citation
closure of the imported framework. Output: registry rows (section 4).
The query set and the inclusion rule are preregistered per round - law 42
applies to the sweep protocol itself. Kill rule: none; the sweep is
additive. Absence of includable hits is recorded as EMPTY-WITH-QUERIES,
which is itself evidence.

### Beat 2 - SCREEN

Input: registry rows. Activity: apply the universal spec U1-U4, then the
route-specific spec of the targeted route, to each candidate as a
paper-only exercise. Every candidate leaves the screen as SCREENED-DEAD,
SCREENED-LIVE, or NEEDS-ANALYSIS, each with a one-line mechanism reason.
Budget: hours per candidate. A screen that exceeds one day is itself a
finding - the candidate is too vague to screen - and is parked as
NEEDS-ANALYSIS with the blocking question named. Output: survivors plus
kill-ledger rows (section 5).

### Beat 3 - PROTOTYPE

Input: screen survivors. Activity: build the cheapest numerical twin
(law 65, MODEL status). Order is mandatory: reproduce the committed
positive control (root-supported triple-vanishing test, ground truth
`qw = +1.895768e-02`) inside its registered band FIRST - instrument
fidelity before any detector claim, the record 1225 sec. 4 lesson - and
only then fire at the detector instance. Output: MATCH/MISMATCH. Verdict
reading: a control MISMATCH kills the instrument, not the candidate; a
detector MISMATCH kills the candidate's numerical form but leaves its
analytic question open.

### Beat 4 - PREREG

Input: prototype survivors. Activity: a record-1225-style Stage-0
target-satisfiability audit from committed sources FIRST - the
conjunction the campaign would have to satisfy is checked for witness
possibility before any construction spend. Then the full preregistration:
declarations, falsifiers, branches, budget. Output: a numbered campaign
record. The Stage-0 audit can terminate a campaign in the same window
(record 1226 precedent: a planned one-week recon was discharged from
committed sources in hours).

## 3. Corridor spec

### Universal (any mechanism, any route)

```text
+-----+-------------------------------------------------------------+---------------------------+
| ID  | Necessary condition                                         | Committed source          |
+-----+-------------------------------------------------------------+---------------------------+
| U1  | Satisfiability-first: the target conjunction must admit a   | record 1225 sec. 1        |
|     | witness by audit before construction. A target that carries | (C1B5TargetSatisfiability |
|     | both signs on one test is dead on arrival.                  | .lean:63-88)              |
+-----+-------------------------------------------------------------+---------------------------+
| U2  | Shape criterion: a producer bundled with healthiness on the | record 1226 sec. 2-3      |
|     | same g and carrying an unconditional `producer => 0 <= qw   | (C1AggregateSocket        |
|     | g` is formally empty. Surviving shapes: universal           | Satisfiability.lean,      |
|     | non-bundled contracts (L4/A4), or positivity by             | A1/A1b/A2/A4)             |
|     | construction on the triple-vanishing class.                 |                           |
+-----+-------------------------------------------------------------+---------------------------+
| U3  | Identity-level readback: positivity must arrive by          | records 1212/1213         |
|     | construction (per-n positive operators + exact trace        | (verdict H2), 1223        |
|     | identities + limit-of-nonnegatives), never by a             | sec. 3.1 (Fork B),        |
|     | main-term-vs-tail estimation contest.                       | 1226 C1                   |
+-----+-------------------------------------------------------------+---------------------------+
| U4  | Instrument calibration: a numerical prototype must          | record 1225 sec. 4 and    |
|     | reproduce the committed positive control inside its         | addendum A8 (C4 replay    |
|     | registered band before it may speak about the detector.     | rel 1.64e-07)             |
+-----+-------------------------------------------------------------+---------------------------+
```

### Route-specific (moving-operator-family route)

```text
+-----+-------------------------------------------------------------+---------------------------+
| ID  | Necessary condition                                         | Committed source          |
+-----+-------------------------------------------------------------+---------------------------+
| S1  | Per-n operator positivity by construction, not estimation.  | record 1226 C1            |
+-----+-------------------------------------------------------------+---------------------------+
| S2  | Counterterm INSIDE the kernel: P~_n = C~_n^* K~_n C~_n      | record 1223 sec. 3.1      |
|     | form; external subtraction of a divergent bulk is formally  | (Fork B ruling; Fork A    |
|     | dead (it breaks limit-of-nonnegatives).                     | dead)                     |
+-----+-------------------------------------------------------------+---------------------------+
| S3  | The kernel carries two interfering geometric modes; rank-1  | record 1224 sec. 3f/3g    |
|     | and affine corrections are formally excluded.               | (RANK-3 sealed)           |
+-----+-------------------------------------------------------------+---------------------------+
| S4  | Trace readback Re Tr(P~_n) -> qw g at identity level in n,  | records 1212/1213         |
|     | not inequality level.                                       |                           |
+-----+-------------------------------------------------------------+---------------------------+
| S5  | The response family is not fixed/n-frozen: a bounded trace  | record 1211 (cofinality   |
|     | against a frozen kernel fires the obstruction.              | obstruction)              |
+-----+-------------------------------------------------------------+---------------------------+
```

A candidate aimed at a different route derives its own route-specific
spec the same way: from that route's no-go ledger, not from taste.

## 4. Candidate-mechanism registry (living)

Seed categories registered by record 1227. Status vocabulary: SEEDED ->
SWEEPED -> SCREENED-DEAD / SCREENED-LIVE / NEEDS-ANALYSIS -> PROTOTYPED ->
PREREGGED. Only a sweep round's own committed preregistration (or
amendment) may add seeds.

```text
+-----+--------------------------------+--------------------------------------+----------+
| id  | category                       | claimed positivity mechanism         | status   |
+-----+--------------------------------+--------------------------------------+----------+
| M1  | Pick/Nevanlinna (Herglotz)     | positive-measure representation of   | SWEEPED  |
|     |                                | functions positive on a half-plane   |          |
+-----+--------------------------------+--------------------------------------+----------+
| M2  | complete monotonicity /        | CM <=> Laplace transform of a        | SWEEPED  |
|     | Bernstein                      | positive measure (Bernstein's        |          |
|     |                                | theorem)                               |          |
+-----+--------------------------------+--------------------------------------+----------+
| M3  | total positivity / Schoenberg  | variation-diminishing kernels;       | SWEEPED  |
|     |                                | real-zero entire functions           |          |
+-----+--------------------------------+--------------------------------------+----------+
| M4  | de Branges entire-function     | Hilbert-space positivity; a named    | SWEEPED  |
|     | spaces                         | RH program                             |          |
+-----+--------------------------------+--------------------------------------+----------+
| M5  | Lee-Yang / circle theorems     | positivity => zeros on the critical  | SWEEPED  |
|     |                                | line (zero-repulsion idiom)          |          |
+-----+--------------------------------+--------------------------------------+----------+
| M6  | Bombieri quadratic form        | finite weighted Hermitian form =     | COMMITTED|
|     | (in-project)                   | K*-Gram norm square, unconditional   | engine;  |
|     |                                | in (t > 0, gamma, z)                 | A4 re-   |
|     |                                | (C1BombieriFiniteQuadraticBridge     | entry    |
|     |                                | .lean:75-84); re-enters only through | only     |
|     |                                | the universal A4 shape (record 1226  |          |
|     |                                | C3)                                  |          |
+-----+--------------------------------+--------------------------------------+----------+
```

Sweep-round rows are appended below the seed table by each round's
committed addendum, with fields: reference (title + arXiv id or URL),
one-line mechanism, corridor-spec contact (which of U1-U4 / S1-S5 the
mechanism addresses or threatens), status.

### Round 1 (record 1227, 2026-09-09)

Branch YIELD: four of the five queried categories produced includable
rows; M2 ended EMPTY-WITH-QUERIES (queries retained in the record 1227
preregistration section 2). A SWEEPED row is retrieval output, not an
endorsement; screening (beat 2) is a registered follow-up record.

```text
+-------+---------------------+--------------------------------------------+---------------------------+
| row   | reference           | mechanism (one line)                       | corridor contact          |
+-------+---------------------+--------------------------------------------+---------------------------+
| R1.1  | arXiv:2108.04807    | truncated Hankel-matrix positivity           | U3, S1: finite-matrix     |
|       | Bickel-Pascoe-      | conditions built from power-series           | positivity by             |
|       | Sargent, "Zero-free | coefficients at each real point =>           | construction; Hankel      |
|       | regions near a      | zero-free regions near the line; a family    | family is the closest     |
|       | line"               | of relaxations of RH                         | published relative of     |
|       |                     |                                            | the M6 engine             |
+-------+---------------------+--------------------------------------------+---------------------------+
| R3.1  | arXiv:2007.12889    | Schoenberg total positivity and its          | U3: structural            |
|       | "Schoenberg's       | Laguerre-Polya connection for zeta-related   | positivity <=> real-      |
|       | theory of totally   | kernels (review)                             | zero entire functions     |
|       | positive functions  |                                            |                           |
|       | and the Riemann     |                                            |                           |
|       | zeta function"      |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R3.2  | arXiv:2602.20313    | Polya-frequency order of the de Bruijn-      | U3; S5-adjacent: the      |
|       | "On the Polya       | Newman kernel K(u) = Phi(|u|) (Feb 2026);    | DN deformation is a       |
|       | frequency order of  | RH <=> Lambda <= 0 deformation context       | moving kernel family      |
|       | the de Bruijn-      |                                            |                           |
|       | Newman kernel"      |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R4.1  | arXiv:2301.00421    | completion of C_c^inf(R) under the Weil-     | U3; direction is RH =>    |
|       | Suzuki, "On the     | distribution hermitian form; positive        | positivity (converse is   |
|       | Hilbert space       | definite UNDER RH (v3 2025)                  | the gate shape); map-004  |
|       | derived from the    |                                            | endpoint-interface        |
|       | Weil distribution"  |                                            | caution at screen         |
+-------+---------------------+--------------------------------------------+---------------------------+
| R4.2  | arXiv:2301.05779    | Li coefficients realized as norms in a       | U3: positivity by         |
|       | "Li coefficients    | de Branges-type model space; norm            | construction (norms);     |
|       | as norms of         | nonnegativity yields a necessary condition   | bridge to the Li-         |
|       | functions in a      | for RH                                       | criterion seed (M8        |
|       | model space"        |                                            | candidate)                |
+-------+---------------------+--------------------------------------------+---------------------------+
| R4.3  | arXiv:1204.1827     | canonical system of differential equations   | S2/S5-adjacent: operator  |
|       | "A canonical system | whose de Branges space is built from zeta    | families generated by a   |
|       | of differential     | data                                         | differential system       |
|       | equations arising   |                                            |                           |
|       | from the ..."       |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R4.4  | arXiv:2209.04658    | the screw line of zeta generates a de        | U3                        |
|       | "The screw line of  | Branges space H(E) isomorphic to a model     |                           |
|       | the Riemann zeta-   | space                                        |                           |
|       | function and its    |                                            |                           |
|       | applications"       |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R4.5  | arXiv:2012.11121    | chains of reproducing-kernel Hilbert spaces  | S5-adjacent: an indexed   |
|       | "Chains of          | controlled by a first-order system           | chain of spaces is a      |
|       | reproducing kernel  |                                            | moving-family idiom       |
|       | Hilbert spaces ..." |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R5.1  | arXiv:2411.16777    | Lee-Yang theorem + Fisher zeros locate the   | U2 context: circle-       |
|       | "Equivalence        | partner function's zeros on the critical     | theorem transfer of a     |
|       | between the zero    | line; equivalence of zero distributions      | positivity property       |
|       | distributions ..."  |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| R5.2  | arXiv:2211.16680    | new van Dantzig pairs (xi, eta) both real-   | U3                        |
|       | "A new class of     | rooted via the Lee-Yang property             |                           |
|       | solutions to the    |                                            |                           |
|       | van Dantzig         |                                            |                           |
|       | problem ..."        |                                            |                           |
+-------+---------------------+--------------------------------------------+---------------------------+
| M2    | EMPTY-WITH-QUERIES  | no complete-monotonicity/Bernstein hit       | round-2 refinement        |
|       | (round 1)           | passed the inclusion rule                    | candidates listed in      |
|       |                     |                                            | record 1227 sec. 7        |
+-------+---------------------+--------------------------------------------+---------------------------+
```

Retrieval log (NOT registry material, recorded for honesty and round-2
planning): arXiv:2502.04962 (lecture notes - rejected at the inclusion
rule), arXiv:2404.07832 (de Branges extremal-problem application, not a
program), arXiv:1705.06222 and arXiv:1910.14368 (Polya-Hilbert /
scaling-Hamiltonian spectral programs - named RH programs found in
round-1 retrieval but outside the seed categories, logged as a possible
round-2 seed), arXiv:2602.04022 (Feb 2026 survey - map context only).

## 5. Kill-ledger format

One row per death, appended where the candidate died:

```text
date | candidate id | beat (2/3/4) | one-line mechanism reason | evidence pointer
```

Same function as the project's dead-route archive: nothing is
re-litigated without new committed evidence.

## 6. Discipline carried over

1. Law 42: the sweep protocol, every screen amendment, every prototype
   gate, and every campaign is committed before its run or build.
2. Law 65: every number the loop produces is a MODEL twin until Lean
   certification.
3. Stage-0 gate: no campaign-week is spent before the target-
   satisfiability audit.
4. Kill accounting: every death takes a kill-ledger row in the same
   commit that records it.
5. Promotion criteria: a candidate reaches beat 4 only with (a) a
   SCREENED-LIVE row naming its corridor-spec contact points, (b) a
   control-MATCH prototype, and (c) a Stage-0 audit that finds its
   target conjunction witness-consistent.

## 7. What this record does NOT change

The running record 1225 sec. 4 positive-control probe is untouched; its
verdict still governs the L4 numerical campaign. The `L4`/`A4` universal
contracts remain re-point markers, not campaigns (record 1226 sec. 8
ruling 3). E2/1219 stays SUSPENDED (record 1223). Line B stays frozen
(records 1147-1196); seed M6 consumes its committed engine read-only.
The external-AI directive (2026-09-03) is unchanged.

RH is not claimed.
