# Record 1341 — B0: the moving-family wall dissolves — the general contract IS the scalar gate, and the gate is SourceRH in both directions

Date: 2026-09-11.
Status: READ-ONLY PAPER AUDIT (beat B0 of record 1340 section 6; no Lean
brick, no numerics, no Source change, nothing self-authorized). B0 was
specified as: write the concrete HT-/Mellin-conjugated window pair
specification, then run the map-006/U1 Stage-0 audit against the record-1340
wall. The audit answers the question BEFORE the specification was needed,
and the answer reorganizes the lane. RH is not claimed.

## 1. The two facts that did the dissolving

**Fact R4 (generalization trivializes the family space).** Record 1340
finding R1 observed that the canonical obligation is the family-GENERAL
`PositiveTraceOperatorLimitFamily`
(`ConnesWeilRH/Dev/C1PositiveTraceLimitBridge.lean:79-93`), whose
`traceOperator : Nat -> H -L[ℂ]-> H` is free DATA. Push that observation
to its end: for a FIXED carrier basis `b` and test `g`,

```text
  Nonempty (PositiveTraceOperatorLimitFamily b g)   <=>   0 <= C1SameOwnerWeil.qw g
```

- (=>) the committed bridge `qw_nonnegative_of_positiveTraceOperatorLimitFamily`
  (same file; the limit-of-nonnegatives engine).
- (<=) two lines: if `c := qw g >= 0`, take the CONSTANT family
  `traceOperator n := c • rankOne v v` with any fixed nonzero
  `v : cc20GlobalLogCrossingL2` (e.g. the class of the indicator of
  `[0,1]`); rank-one => trace class along `b` with `trace = c`,
  `(c • rankOne v v).IsPositive` holds termwise for `c >= 0`,
  `remainder := 0`, and the readback is the constant sequence at `c`.

No contract field requires window growth, cutoff structure, or any relation
to `cutoffProjectionOperator` - those live in the PINNED structure
`ProjectionCutoffLimitContracts`
(`C1Stage3ProjectionOperatorFamily.lean:182-223`), i.e. the general contract
with `traceOperator` glued to the static family. Consequence: **every wall
theorem of record 1340 section 2 (plain-window emptiness, fixed-response
1211, bounded-moving-response cofinality 616-627) is an artifact of the
PINNING and constrains nothing in the general contract.** There is no
"moving family engineering" left to do: family-shopping is closed, because
the family exists iff the scalar is nonnegative.

**Fact R5 (the scalar gate is SourceRH in BOTH directions, internally).**
The forward direction is committed architecture: `hsign` feeds the capstone
`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg`
(`C1HealthyYoshidaSpectralNegativity.lean:585-610`). The REVERSE direction -
`¬ SourceRH` REFUTES the gate - is also fully committed, in two committed
pieces used inside that very capstone proof:

```text
  hdetector  : rho off the line (right rep) -> exists g, HealthyYoshida
               DetectorData rho g            [exists_rightOfCriticalXiZero_
               of_re_ne_half + detector machine, cited :594-598]
  hg.vanishesOnF : the detector g IS in the triple-vanishing class
               (CC20VanishesOn {0, 1/2, 1}, CC20RHExit.lean:21-24,28-31)
  L1         : HealthyYoshidaDetectorData rho g -> Weil value of the square
               is STRICTLY NEGATIVE            [weilSquareSumPositive_iff_
               spectralWeilValue_neg, C1HealthyYoshidaDetector.lean:182-200]
```

and the scalar identification `qw g = spectralWeilValue g.convolutionSquare`
is the centerTwo bridge (`C1CenterTwoCriterionBridge.lean:28`; Gate-2a
`psi F = spectralWeilValue F` is the explicit-formula Prop,
`C1SpectralWeil.lean:591-604`). Therefore, propositionally:

```text
  [forall vanishing g: 0 <= qw g]   ->   SourceRH      [capstone, committed]
  not SourceRH                      ->   exists vanishing g: qw g < 0   [above 3 lines]
```

i.e. the surviving obligation of the WHOLE post-1339 campaign (L4 = L4' =
hsign, and A4 through the same capstone) is not "like" `SourceRH`: it is
internally equivalent to it. The record-1225 reading "hproducer is
`SourceRH` in disguise" (map 007 section 1) extends verbatim to the
repaired universal premise: the quantifier repair moved the contradiction
out of the PREMISE shape, but the premise content remains exactly the
theorem. That is not a defect of the architecture - the capstone direction
was always meant to be that hard - but it is decisive for lane choice:
**there is no weaker operator-theoretic shadow of RH left on this surface.**

## 2. Classical anchor (external evidence, per the evidence rule)

The equivalence R5 is the formalized form of the classical Weil positivity
criterion: RH is equivalent to nonnegativity of the explicit-formula
quadratic form on the class of test data with the vanishing/moment
conditions. Anchors: Davenport-Erdos 1936 (Duke Math. J. I, the two-sided
form positivity criterion); Weil 1952 (sur les "formules explicites", the
distribution form - the campaign's own `psi`/`poleTerm` naming); Li 1997
(the countable shadow: coefficient positivity for the moment vanishing
conditions); current survey statement: "Weil's remarkable equivalence: the
Riemann Hypothesis is equivalent to the positivity of certain quadratic
forms" (arXiv:2602.04022v1, 2026-02, section on Weil's criterion; also the
standard reference on the Riemann-hypothesis page, "Weil's criterion").
The campaign's triple-vanishing set {0, 1/2, 1} in Mellin coordinates is
the repo-owner form of the classical moment-vanishing side conditions;
the `1/2` member is the centerTwo symmetry point that makes the same-owner
square unique. Nothing here is newly proved; the anchor's role is to show
R5 is not an artifact of the pinning - the equivalence is the mathematics.

## 3. What this kills, what it leaves

```text
+-----------------------------+-------------------------------------------+
| surface                     | status after B0                           |
+-----------------------------+-------------------------------------------+
| moving-window design cycle  | DEAD BY DISSOLUTION (R4): no family choice|
| (Fork B as originally       | adds strength over 0 <= qw(g). The HT/    |
| conceived in 1223-1225)     | Mellin window hint cannot help: it      |
|                             | optimizes the pinned family the general   |
|                             | contract does not require.                |
| 1340 sec. 2 wall            | family-specific artifacts, retained as  |
|                             | history, no longer load-bearing.          |
| R4'/R5 as theorems          | NOT committed (paper only). A brick     |
|                             | fixing both equivalences is worthwhile    |
|                             | housekeeping (beat B0b): it closes      |
|                             | family-shopping formally.                 |
| construction-level proof of | THE only live content: every future     |
| 0 <= qw on the vanishing    | candidate (de Branges/Burnol Sonine     |
| class                       | spaces, Suzuki's Weil-form completion,  |
|                             | truncated-Hankel positivity) must be a  |
|                             | CONSTRUCTION (C1 discipline), and by    |
|                             | R5 succeeds iff RH.                     |
+-----------------------------+-------------------------------------------+
```

The honest strategic reading: the campaign has spent its numerics and much
of its formal architecture discovering, instance by instance (1226 sockets,
1329 twins, 1334-1339 carriers, 1340 families), that no weakening of
`SourceRH` exists at the positivity surface. The surviving program is
exactly the classical one - find the positivity construction that Weil's
criterion guarantees exists but nobody has produced - now inside a proof
assistant with hard construction-only discipline. That is a legitimate
campaign shape (it is what de Branges programs look like), but its expected
value is the expected value of a new attack on RH itself, and the owner
decision (1341 sec. 5) is where the effort goes, not whether the gate is
weaker than RH: it is not.

## 4. Registry collision (companion lane, re-scoring note)

Two map-006 sweep-round-1 rows are ON this surface, not merely adjacent:

- **R4.1** (Suzuki, arXiv:2301.00421v3): completion of `C_c^infinity(R)`
  under the Weil hermitian form, "positive definite UNDER RH; the converse
  is the gate" - the published phrasing of R4/R5 verbatim modulo the
  form-vs-distribution dictionary.
- **R1.1** (Bickel-Pascoe-Sargent truncated-Hankel, arXiv:2108.04807):
  the countable-shadow variant (Li's criterion family) of the same gate.

Screen note for the companion lane: R4.1's gate direction is exactly the
campaign's open half; its RH direction is the classical sum-of-squares
(= R5's committed reverse + the uncommitted forward classical half,
`SpectralSummable` per-zero terms becoming squared moduli on the line -
check what the repo's centerTwo machinery already proves under
`B.onLine`-style hypotheses before calling it uncommitted).

## 5. Executable residue (registered, NONE executed)

```text
B0a micro-falsifier probe (one small prereg, law 42): the triple-vanishing
    PRIME-FREE class (support subset (-log 2, log 2) makes
    finitePrimeSum = 0 COMMITTED, C1SameOwnerWeil.lean:167-189, so
    qw = pole - arch = explicit point-value + one integral per g).
    A found g with qw(g) < 0 and machine-verified vanishing refutes the
    gate (R5) => closes the entire positivity surface cheaply and formally.
    Under RH nothing exists to find (classical anchor): expected outcome
    NO-FIRE; the cost is one half-day. One-shot discipline per A9 style:
    one grid, one verdict, no ladder.
B0b equivalence brick (~1 batch): commit R4 (both directions) and the R5
    forward pairing as `positiveTraceFamily_iff_qw_nonneg` +
    `not_sourceRH_of_exists_vanishing_negative_qw` (or the contrapositive
    already in the capstone - the brick's value is CLOSING family-shopping
    in code). Feasibility check done at record time: the repo's
    `IsTraceClassAlong` is just diagonal-series summability
    (`Source/CC20Concrete/PositiveTrace.lean:37-40`), and the rank-one
    diagonal is the Bessel-square series `c * |inner (basis i) v|^2`
    (summable, sum = c * normSq v, ordinary Mathlib), so the brick needs
    NO dependency on the open 1331 G3 kernel-trace package. Low risk,
    no new mathematics.
B0c R4.1 translation audit (map-006 beat 2, companion lane): the
    Suzuki completion vs the repo's `psi`-form dictionary, paper record.
B0d owner decision: continue the RH-level construction campaign (de
    Branges/Sonine geometry inside Lean), or freeze the gate and spend
    capacity where the campaign has comparative advantage.
```

## 6. What this record does NOT establish

No Lean theorem, no numeric datum, no proof or disproof of RH or of the
gate; no claim that a positivity construction is feasible (R5 says it is
feasible exactly when RH is true); no reopening of anything frozen; the
classical anchors are cited, not reproved; the vanishing-class membership
of the off-line detector (`hg.vanishesOnF`) is read from the committed
capstone usage, not re-audited here. RH is not claimed.
