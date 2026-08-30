# 1065 - S2 pair owner: root commutator legality under one prolate-factor HS contract

Date: 2026-08-31. Follows 1063 (F1' crux verdict, active-order decomposition) and
record 1064 (semilocal second-support chain green; thm-3/thm-4). This record pins the
S2 owner shape BEFORE Lean edits. Target brick:
`ConnesWeilRH/Dev/C1ProlateRootCommutatorPairOwner.lean` (+ paired audit leaf, house
style). No numeric probe is a proof here; no F1' closure is claimed until both S1 and
the new contract below are discharged by producers.

## 0. Operational verdict up front

```text
(1) S2 CLOSES UNDER EXACTLY ONE NEW NAMED ANALYTIC CONTRACT.
    The owner for cc20Commutator(C, K_S) = C oL K_S - K_S oL C is built from a base
    pair data D0 whose legs are the bounded prolate-remainder factor
        F_K := targetProlateRemainderFactor unitSoninScale family
              = Q_S oL (E - R_S)                      Dev C1Prolate:81-84
    with K_S = F_K^dagger oL F_K (existing theorem, Dev C1Prolate:88-92).  Two
    boundedSandwich transports put the root on each side; l2Sum + smulRight(-1)
    forms the signed difference.  The only new obligation is
        S2-FK-HS := Summable fun i => |F_K (globalBasis i)|^2 .

(2) NO ROOT SELF-ADJOINTNESS IS ASSUMED.
    C never appears as a Hilbert--Schmidt leg: it enters only as a bounded
    sandwich dressing, whose precomposition preserves leg summability via the
    existing summable_normSq_precomp (HilbertSchmidtIdeal.lean:56).  Neither
    term of the commutator is related to the other by adjoint unless C = C^dagger,
    which is exactly what this shape avoids requiring.

(3) THE SEMILOCAL CHAIN IS THE ESTIMATE ROUTE, NOT A LEGALITY INPUT.
    thm-4 (targetRootSecondSupportCommutatorBranch_eq_reflectedRoot) rewrites the
    second-support branch as E oL HT oL [E,B] oL HT oL E with B compact; that feeds
    size/decay estimates for ledger branch 2.  The legality owner below uses none of
    the HT machinery: trace legality needs one factorization, estimates need the
    four branches.

(4) GO: write the brick this round.  Expected axiom set is the standard-3 set;
    the paired audit leaf verifies via #print axioms before any state promotion.
```

## 1. The consumption interface (what S2 asks for, pinned)

The S2 obligation and its pair-data reduction already live in
`ConnesWeilRH/Dev/C1ProlateResponseTraceLegalityUnitScale.lean`:

```text
targetProlateDetectorRootCommutatorRemainder owner family
  = C^dagger oL cc20Commutator(C, K_S)                 Dev C1Prolate:226-231
S2 := IsTraceClassAlong globalBasis (that operator)    Dev C1Prolate:234-239

_of_pairData ... (pairData : BasisHilbertSchmidtPairData (G := G) globalBasis)
  (hpair : pairData.traceProduct = cc20Commutator(C, K_S))
  => S2                                                Dev C1Prolate:243-262
```

The consumption proof is `boundedSandwich_isTraceClassAlong` with left dressing
`C^dagger` and right dressing identity; no cyclic trace is used.  The capstone then
reads F1' = S1 + S2 (Dev C1Prolate:370-381).

So the brick's algebraic goal is a single equation:

```text
T_P := pairData.traceProduct  ==  cc20Commutator(C, K_S)
     ==  C oL K_S - K_S oL C        (cc20Commutator A W = A.comp W - W.comp A,
                                     ThreeBranchCommutatorLedger.lean:27-29)
```

## 2. Why the two-sided sandwich shape is forced (options table)

Candidate owner shapes for `C oL K_S - K_S oL C`, with their walls:

| Option | Shape | Wall / extra contracts needed |
|--------|-------|-------------------------------|
| A: single oriented difference | X - X^dagger, X := C oL K_S | (X)^dagger = K_S C^dagger, not K_S C.  Needs root self-adjointness C = C^dagger as a NEW assumption or lemma.  Rejected: hides an analytic fact inside the owner shape. |
| B: four-product l2Sum over the expanded ledger terms CEQE / CR / EQEC / RC | each product as its own pair data | The two R-terms (CR, RC) force the bare star projection R to be a Hilbert--Schmidt leg (infinite rank; no existing fact grants leg status).  Wall unless we add a windowing contract per term. |
| C: regroup [C,M] - [R,C], M := E Q_S E | oriented differences of CM and RC | Branch A is ownable from the F2 compression data (trace product E Q_S E); branch B still hits the bare-R wall.  Partial only. |
| D: TWO-SIDED SANDWICH l2Sum (ADOPTED) | l2Sum(D1, D2.smulRight(-1)); D_i = boundedSandwich of one base data D0 | Exactly one new contract (S2-FK-HS).  C is always a bounded dressing.  No self-adjointness. |

Option D works because K_S itself factors as F_K^dagger F_K with F_K BOUNDED
(windowed projection composition, Dev C1Prolate:78-92): the base data owns K_S as a
positive square, and the two-sided transport moves the root to either side without
ever making it a leg.  The precedent for `l2Sum(a, b.smulRight (-1))` as a signed
difference owner is `compressionDifferencePairData` (Dev C1Prolate:409-424).

## 3. Owner construction (exact Lean chain)

All names below are the planned declarations in the new brick leaf.  Machinery
references are committed, green (build4):

```text
summable_normSq_precomp            HilbertSchmidtIdeal.lean:56
smulRight / smulRight_traceProduct_eq  HilbertSchmidtIdeal.lean:403/415
l2Sum     / l2Sum_traceProduct_eq_add  HilbertSchmidtIdeal.lean:461/492
boundedSandwich / boundedSandwich_traceProduct_eq  HilbertSchmidtIdeal.lean:566/583
```

```text
(0) Contract (the single new analytic obligation, owner-free):
    def targetProlateRemainderFactorSummable (family) {nu} (globalBasis) : Prop :=
      Summable fun i => |targetProlateRemainderFactor unitSoninScale family
                         (globalBasis i)|^2

(1) Base square data:
    def targetProlateRemainderSquarePairData ... :
        BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
      left = right = F_K ;  leg proofs = the S2-FK-HS contract twice.
    theorem ..._traceProduct_eq : T_D0 = K_S
      by unfold; exact targetProlateRemainderFactor_adjoint_comp_self (C1Prolate:88).

(2) Left-side transport (root on the left of K_S):
    def targetProlateRootLeftRemainderPairData :=
        D0.boundedSandwich globalBasis C identity
    theorem ..._traceProduct_eq : T = C oL K_S
      by rw [boundedSandwich_traceProduct_eq, (1)]; simp only [comp_id].

(3) Right-side transport (root on the right of K_S):
    def targetProlateRemainderRightRootPairData :=
        D0.boundedSandwich globalBasis identity C
    theorem ..._traceProduct_eq : T = K_S oL C  (same closing).

(4) Signed difference owner:
    def targetProlateRootCommutatorPairData :
        BasisHilbertSchmidtPairData (G := WithLp 2 (finiteSCarrier x finiteSCarrier)) globalBasis :=
      D1.l2Sum (D2.smulRight (-1))
    theorem ..._traceProduct_eq : T_P = cc20Commutator(C, K_S)     [CRUX EQUATION]
      proof plan (LANDED GREEN build #3, 2026-08-31):
        unfold targetProlateRootCommutatorPairData
        rw l2Sum_traceProduct_eq_add
           smulRight_traceProduct_eq   -- scalar (-1 : C)
           (2), (3)                    -- down to X + (-1 : C) • Y  vs  X - Y
        simp only [sub_eq_add_neg, neg_one_smul, cc20Commutator]
      Note: cc20Commutator must be listed explicitly in the simp set (named
      defs are not auto-unfolded); precedent at
      CCM24FiniteSCommonBoundaryPair.lean:1751.  The P def itself needed a
      fully-qualified explicit smulRight call (implicit dot on a parenthesized
      receiver failing - AGENTS 7b).
      Precedent for the closing tactic:
      CCM24FiniteSProlateCommutatorTraceBound.lean:70-83 (the source-side sibling
      owner with the identical l2Sum + smulRight(-1) shape closes exactly this way);
      neg_one_smul is also used at
      CCM24FiniteSGatePhysicalNormalizedAnomalyTrace.lean:254.  Probe discipline
      remains the fallback if the module build goes red on this step.

(5) S2 closure:
    theorem targetProlateDetectorRootCommutatorTraceLegality_of_remainderFactorSummable
        (globalBasis) (factorBasis : HilbertBasis k C (WithLp 2 (finiteSCarrier x finiteSCarrier)))
        (owner family) (hFK : S2-FK-HS) : S2 := by
      apply _of_pairData ... (4's data) ; exact (4)'s equation.

(6) F1' corollary:
    theorem targetProlateRemainderDetectorWeightedTraceLegality_of_bothSummable
        (owner family) {nu} (globalBasis)
        (hS1 : S1 contract, C1Prolate:177-182) (hFK : S2-FK-HS) : F1' := by
      have hcomm := (5) with the supplied product factorBasis ;
      exact capstone ... hS1 hcomm        (C1Prolate:370-381).
```

Product-basis wiring note: owner P lives over `WithLp 2 (finiteSCarrier x finiteSCarrier)`,
so steps (5)-(6) carry an explicit `factorBasis` argument, exactly as `_of_pairData`
already does.  Exhibiting such a basis is a pure existence-side detail at discharge
time; it is NOT an analytic obligation and is not counted in the contract ledger.

## 4. Contract ledger after this record (F1' state)

| Obligation | Statement | Status | Producer route |
|------------|-----------|--------|----------------|
| S1 | Summable of |(F_K oL C)(basis i)|^2 | named contract, producer pending (unchanged by this record) | owner-dependent; source-side mirror decay estimates under reconnaissance |
| S2-FK-HS (NEW) | Summable of |F_K(basis i)|^2 | named contract introduced here | owner-free finite-S prolate-factor HS fact; likely shares a producer with S1 (equivalent if the root is unitary on the carrier - NOT promoted, no such lemma exists yet) |
| F2 (target/source compression) | two Summable contracts for Q oL E factors | named contracts, unchanged | estimate route only; not consumed by this owner |

No positivity, remainder sign, or RH-facing statement is asserted.  The owner proves
summability of the named-basis diagonal series via Cauchy--Schwarz on HS legs (the
existing `traceProduct_isTraceClassAlong` machinery); it says nothing about size.

## 5. Brick spec and build plan

Files:
- `ConnesWeilRH/Dev/C1ProlateRootCommutatorPairOwner.lean` — declarations (0)-(6) above,
  imports mirroring C1ProlateResponseTraceLegalityUnitScale plus that Dev leaf itself;
  namespace ConnesWeilRH.Source.C1ProlateRootCommutatorPairOwner.
- `ConnesWeilRH/Dev/C1ProlateRootCommutatorPairOwnerAudit.lean` — #check + #print axioms
  for every new declaration (contract def, four pair-data defs, five theorems).

Build ladder (AGENTS 7a): copy both files to /home/peter/rh/ConnesWeilRH/Dev/, remove
stale .o/.olean for the two modules, then `flock ... lake build <both modules>` and
accept on LOG evidence only: "Build completed successfully", zero `error:` lines,
zero sorryAx.  The step-(4) crux closer now has an in-repo precedent (see above), so
the standalone probe is a fallback rather than a first step.

Go/no-go: GO.  Every algebraic input AND both closing tactics are committed and green.
