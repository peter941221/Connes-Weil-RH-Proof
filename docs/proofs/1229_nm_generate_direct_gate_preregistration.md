# 1229 - NM Beat 0: direct-gate generation round G1 preregistration

Date: 2026-09-09.

Status: PREREGISTRATION.  This is a paper-only Generation Card and
adversarial identity audit, registered before any new Lean declaration,
numerical run, or candidate survival claim.  RH is not claimed.

Authority: map record [`006`](../map/006_new_math_creation_workflow.md), Beat
0, after record [`1228`](1228_nm_round1_prior_art_translation_preregistration.md)
closed its ten literature rows as `NO-YIELD`.  The consumer remains binding
route ruling [`003`](../map/003_b1_b5_minimal_exit_route_selection.md): the
healthy-`CompactLog`, selected-detector semi-local B5 exit.  This record does
not reopen B1, Line B, a normalized owner, exact prime-free reference matching,
or an absolute defect/tail budget.

## 1. Generation Card G1

```text
candidate/id  G1: finite-visible-prime Schur-complement identity

TARGET EQUATION
  ICgate (g.convolutionSquare) <= 0
  for the same formal orbit g = g(rho) and its finite visible-prime owner;
  this is the direct P2 gate consumed by the existing same-owner B5 exit.

NOVEL MOVE
  Do not cancel the complete finite-prime residual by matching to a prime-free
  reference (formally wrong-sign), and do not bound its absolute size.  Seek
  instead an exact block decomposition in which the signed visible-prime
  vector is retained and eliminated by a Schur complement against a positive
  Archimedean/zero-configuration block.

SIGN SOURCE
  Positivity of the block Gram kernel and a proved Schur-complement inequality,
  with the rho-dependent node relations entering the off-diagonal block.

CHEAP FALSIFIER
  Restrict the claimed identity to one visible prime-power and the lowest
  nontrivial block rank.  A sign-indefinite Schur complement, a missing
  rho-dependent off-diagonal identity, or reduction to the known direct gate
  tautology kills G1 before formalization.
```

## 2. Exact screen obligation

The paper audit must produce all of the following, or classify G1
`NEEDS-ANALYSIS` without opening Lean:

```text
G1.1  A concrete vector b_g indexed by the actual finite visible prime powers,
      and a concrete Hermitian block matrix
        [ A_rho  B_rho ]
        [ B_rho* C_rho ]
      on one named space.

G1.2  An exact same-owner identity relating ICgate(g.square), not merely an
      estimate, to that block quadratic form plus an explicitly signed
      remainder.

G1.3  A rho-specific derivation of the required block relation from the
      detector's node/detection equations; generic triple vanishing alone is
      insufficient.

G1.4  A proof that the Schur complement is nonnegative/controlled without
      assuming qw >= 0, SourceRH, an equivalent spectral sign, or a hidden
      same-g positive data field.

G1.5  A literal one-prime/lowest-rank falsifier calculation whose hypotheses
      are consequences of G1.1--G1.4, not arbitrary free matrix entries.
```

The initial identity sources are the committed exact residual and direct-gate
interfaces of map record 005 (records 1198--1206 therein), not a new reference
owner.  A block matrix introduced only after replacing the residual by an
unknown sign assumption fails G1.2/G1.4 and is dead.

## 3. Parallel incubator cards (not campaigns)

`G2`: a rank-at-least-three moving finite-part trace identity with an internal
counterterm and exact same-owner readback.  It is parked pending the registered
1225 positive-control verdict; no work opens it while that instrument gate is
running.

`G3`: an explicit Herglotz/de Branges convention bridge from a positive measure
or model-space norm to the same `CompactLog` finite-prime `ICgate`.  It is
parked because 1228 found no source with this translation; it may resume only
with a primary-source lemma that names both sides of the bridge.

## 4. Branches

```text
IDENTITY: G1.1--G1.5 all have concrete, noncircular statements.
          Next: separate SCREEN-CARD, then a Lean interface brick.

TAUTOLOGY: the proposed identity reduces to ICgate(g.square) <= 0 itself,
           or hides it as a Schur-complement premise.
          Next: SCREENED-DEAD, kill-ledger row; do not prototype.

MISSING-BRIDGE: no rho-specific block relation reaches the finite primes.
          Next: NEEDS-ANALYSIS; no Lean or numeric work.
```

Budget: one paper-only identity audit.  No number is produced and no route
status changes.

RH is not claimed.

## 5. Post-run addendum: G1 identity audit

Evidence level: FORMAL interface audit plus PROJECT-CANDIDATE analysis.

`G1.2` has a genuine general identity, but it is weaker than G1 needs:
`gate_qform_span` in `C1GateMatrixRepresentation.lean:392-396` writes
`ICgate((spanObj w y).convolutionSquare)` as the quadratic form of
`gateMatrix w`.  It supplies neither a finite-visible-prime coordinate vector
nor a sign.  Choosing a span that contains the actual orbit detector does not
repair that absence.

The strongest natural Gram specialization is formally ruled out.  The theorem
`not_negGateMatrix_posSemidef_of_healthyDetector_span` in
`C1P2BilateralProfileExit.lean:171-194` proves that, whenever `spanObj w y =
g` is healthy, the universal certificate `(-gateMatrix w).PosSemidef` is
false.  This covers the naive plan “represent the selected detector in a
finite span and prove the whole gate matrix negative semidefinite.”  It is not
a missing estimate: its conclusion would directly force the refuted direct
gate sign.

The same obstruction appears for a reference/defect rewrite: the exact
identity `defectGate_singleton_eq_sub` is committed in
`C1T2Assembly.lean:211-214`, while
`signedDefectGateResidual_iff_detectorGate_nonpos` in
`C1P2BilateralProfileExit.lean:135-143` proves that the standard signed
reference residual is logically equivalent to the direct gate itself.  Thus a
Schur complement obtained only by repackaging that identity is a `TAUTOLOGY`,
not a new producer.

Verdict: the universal finite-span Gram branch of G1 is `SCREENED-DEAD`
(FORMAL-FAMILY-SPECIFIC no-go).  The proposed genuinely detector-specific
block branch is `NEEDS-ANALYSIS`, not live: no current theorem supplies
G1.1/G1.3, namely a rho-dependent off-diagonal relation from the orbit node
equations to the actual finite visible-prime coordinates.  No false death is
recorded for that unformed branch, and no Lean or numerical work is opened.

The next admissible move is to await the already-running 1225 control verdict
before deciding whether parked G2 can be unparked.  G3 remains parked under
the NO-YIELD literature result of record 1228.

RH is not claimed.
