# 1227 - NM loop establishment and Stage-1 sweep round 1 (preregistration)

Date: 2026-09-09.

Status: PREREGISTERED before any sweep run (law 42). RH is not claimed.

Authority: Peter's 2026-09-09 directive to open the new-math loop, to
establish the creation workflow as a new map document, and to begin
execution in the same window. The workflow itself lives in map document
[`006`](../map/006_new_math_creation_workflow.md); this record registers
the establishment commit and the protocol of the first sweep round, so
that the round's queries and inclusion rule are committed before any
retrieval runs.

Relation to the running probe: verdict-independent. The corridor spec the
sweep screens against is already committed (records 1211/1212/1213/1223/
1224/1225/1226); nothing in this record consumes any number the record
1225 sec. 4 probe has not yet produced, and the probe continues to run
untouched.

## 1. Deliverable 1 - workflow establishment (committed with this prereg)

Map document 006: the four-beat NM loop (SWEEP / SCREEN / PROTOTYPE /
PREREG), the corridor spec (universal U1-U4; moving-family route-specific
S1-S5; each condition with its committed source), the seed candidate
registry M1-M6, the kill-ledger format, and the promotion criteria. The
map README authority table and reading order are synchronized in the same
commit (live-update rule), and the freeze card's Allowed Work list gains
the read-only NM-loop item. No route authority changes; no frozen route
is touched; no Lean file is created or edited by this deliverable.

## 2. Deliverable 2 - Stage-1 sweep round 1 (protocol registered here; run only after this commit)

Scope: READ-ONLY. No Lean build, no numerics run, no edit to any frozen
module, no external-AI dialogue (the 2026-09-03 directive stands);
literature retrieval only (arXiv search primary, web search secondary
for named programs).

Queries, registered per seed category:

```text
M1  arXiv: "Pick function" / "Nevanlinna" AND ("Riemann zeta" OR
    "Riemann hypothesis"); positivity context required by the inclusion
    rule below
M2  arXiv: "complete monotonicity" AND ("Riemann hypothesis" OR "Weil
    explicit formula" OR "Riemann xi")
M3  arXiv: ("total positivity" OR "Polya frequency") AND ("Riemann" OR
    "zeta zeros")
M4  arXiv + web: "de Branges" AND "Riemann hypothesis"
M5  arXiv: "Lee-Yang" AND ("Riemann zeta" OR "zeta zeros" OR "critical
    line")
M6  corpus-internal: no external query. The registry row cites the
    committed unconditional engine (C1BombieriFiniteQuadraticBridge
    .lean:75-84) and its A4 universal re-entry shape (record 1226 C3).
```

Extension seeds (M7 Nyman-Beurling/Baez-Duarte Gram positivity, M8 Li's
criterion, M9 Burnol explicit-formula Hilbert spaces) may be added ONLY
by a committed amendment to this section before their queries run
(law 42); they are listed here as named possibilities, not as registered
round-1 queries.

Inclusion rule: a reference enters the registry iff (a) it states a
positivity mechanism in an explicit-formula / Weil-positivity context
relevant to the gate `0 <= qw g`, or (b) it is a named RH program built
on the seed mechanism. Anything else stays in the round's retrieval
output and is not registry material.

Registry-row fields: reference (title + arXiv id or URL), one-line
mechanism, corridor-spec contact (which of U1-U4 / S1-S5 the mechanism
addresses or threatens), status SEEDED -> SWEEPED.

Absence handling: a category with no includable hit records
EMPTY-WITH-QUERIES with its queries retained; absence is evidence and is
reported as such, not silently dropped.

## 3. Deliverable 3 - round-1 addendum

Registry rows appended to map 006 section 4, and a round-1 yield summary
appended to this record as section 7, in the same window. The usual
outbound hygiene check applies before any push (no local paths, no
private-workflow artifact names in public text).

## 4. Falsifiers and branches

F1 (tooling falsifier): a query fails at the retrieval layer (not at the
inclusion rule). Remedy: one retry; a persistent failure records
TOOL-FAILURE for that category, which is NOT an EMPTY finding and must be
re-run in a later round.

Branches:

- YIELD: at least one category produces includable rows. The round-1
  addendum lists them; screening (beat 2) of any survivor is a
  registered follow-up record, not part of this record.
- THIN: every category ends EMPTY-WITH-QUERIES or TOOL-FAILURE. A
  query-broadening amendment (which may activate the extension seeds
  M7-M9) is committed before round 2.

## 5. Budget

One window, read-only. No Lean build time, no numerical run time, no
interaction with the running probe.

## 6. What this record does NOT claim

No candidate survival claim of any kind - a SWEEPED row is retrieval
output, not an endorsement. No route ruling. No witness of L4, A4, or any
contract. No interaction with the record 1225 probe verdict, the E2/1219
suspension, or the Line-B freeze. Every quoted number (e.g. the control
ground truth +1.895768e-02) remains a MODEL twin under law 65.

## 7. Post-run addendum: round-1 yield

Branch: YIELD. The registered queries ran as committed (arXiv retrieval,
one pass per category; no tool failure - F1 did not fire). Ten includable
rows landed in map 006 section 4: M1 one row, M3 two rows, M4 five rows,
M5 two rows. M2 = EMPTY-WITH-QUERIES (no complete-monotonicity/Bernstein
hit passed the inclusion rule; the query is retained for round 2). M6
unchanged (corpus-internal engine, no external query).

Three borderline hits were adjudicated by abstract retrieval before the
registry decision, inclusion rule applied strictly:

- arXiv:2301.00421 (Suzuki, "On the Hilbert space derived from the Weil
  distribution", v3 2025): ADOPTED. The completion of C_c^inf(R) under
  the Weil-distribution hermitian form, positive definite UNDER RH - the
  project's home explicit-formula idiom. The conditional direction is
  recorded honestly (RH => positivity; the gate needs the converse
  transfer), and the map-004 endpoint-interface caution applies at
  screen time.
- arXiv:2108.04807 (Bickel-Pascoe-Sargent, "Zero-free regions near a
  line"): ADOPTED. Truncated Hankel-matrix positivity conditions built
  from power-series coefficients yield zero-free regions near the line -
  a family of relaxations of RH. Finite-matrix positivity by
  construction; structurally the closest published relative of the M6
  unconditional engine.
- arXiv:2502.04962 (Pedersen, "Special Functions from a Complex
  Viewpoint"): REJECTED. Mini-course lecture notes: neither a named RH
  program nor a new mechanism.

Round-2 amendment candidates (NOT registered; each needs a committed
amendment to section 2 before its queries run, law 42): M2 refinements
("Laguerre-Polya class" + xi function; "Bernstein function" + zeta);
extension seeds M7 (Nyman-Beurling/Baez-Duarte Gram-matrix positivity -
note the R1.1 Hankel adjacency), M8 (Li's criterion - note R4.2 already
bridges to it), M9 (Burnol explicit-formula Hilbert spaces); and a
possible M10 (spectral interpretation: Polya-Hilbert operators
arXiv:1705.06222, scaling Hamiltonian arXiv:1910.14368 - named programs
found in round-1 retrieval but outside the seed categories, therefore
logged, not registered).

Next beat: screening (beat 2) of the ten SWEEPED rows against U1-U4
(plus S1-S5 for rows aimed at the moving-operator route) is a registered
follow-up record; it is paper-only and consumes no instrument time. No
candidate survival is claimed by this record. The record 1225 sec. 4
probe continued running untouched throughout the sweep.

RH is not claimed.
