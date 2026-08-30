# 1066 - F1' single-contract reduction: S1 is the bounded-precomposition shadow of S2-FK-HS

Date: 2026-08-31. Follows 1065 (S2 pair owner; two-contract corollary) and
1063 (F1 crux verdict; raw F1 retired as a proof target). This record pins the
algebraic relation between the two remaining F1' contracts BEFORE Lean edits:
S1 follows from S2-FK-HS in one line of committed machinery, and S2-FK-HS is
termwise identical to the retired raw-F1 series. Target brick:
`ConnesWeilRH/Dev/C1ProlateSingleContractReduction.lean` (+ paired audit leaf,
house style). No numeric probe is a proof here; no PRODUCTION (production) of any
summability fact is claimed.

## 0. Operational verdict up front

```text
(1) F1' AT UNIT SCALE COLLAPSES TO EXACTLY ONE NAMED ANALYTIC CONTRACT.
    S1 := Summable fun i => |F_K oL C (globalBasis i)|^2 is the bounded-
    PREcomposition shadow of S2-FK-HS := Summable fun i => |F_K (globalBasis i)|^2:
    one line of committed-green summable_normSq_precomp
    (HilbertSchmidtIdeal.lean:56-77) with all three basis arguments = globalBasis,
    operator := F_K, bounded := C.  No owner dependence, no new axioms.

(2) THE COLLAPSED CONTRACT IS TERMWISE THE RETIRED RAW F1 SERIES.
    The diagonal identity deleted at d1dfae1 (git 74b8cbb diff):
        ((|F_K e_i|^2 : R) : C) = <e_i, K_S e_i>
    so S2-FK-HS <-> IsTraceClassAlong globalBasis K_S by Summable.congr /
    .norm / of_norm.  The one contract left to produce is exactly the series
    that record 1063 numerically flagged for {2,3,5}: nonmeet principal-angle
    mass growing ~ xi_max^0.4 over four octaves (10.21/15.18/20.88/28.28).

(3) THE 1063 TENSION RESOLVES AS "GUARD INHERITED, NOT VERDICT".
    The probe measured SUM_{j >= jstar} lambda_j(M) of M = E Q_S E; K_S is the
    DEF M - R_S (CCM24FiniteSProjectionTrace.lean:161-166), so in finite dims
        Tr(K_S)_model = nonmeet mass + meet residual,
    and the probe hit the dominant term through two unproved bridges (meet-
    residual control; grid -> continuum basis).  Raw-F1 falsification was never
    a formal negation of S2-FK-HS.  Next probe (record 1067 candidate): measure
    |F_K_model|_HS^2 = Tr(M - R_S) DIRECTLY in the same rig, closing the meet-
    residual bridge before scheduling an analytic producer.

(4) GO: write the brick this round; expected axiom set is standard-3 on all
    four declarations, verified by the paired audit leaf before state promotion.
```

## 1. The two contracts and their composition (pinned verbatim)

```text
S2-FK-HS   Dev C1ProlateRootCommutatorPairOwner:67-71
def targetProlateRemainderFactorSummable (family) {nu} (globalBasis) : Prop :=
  Summable fun i => |targetProlateRemainderFactor unitSoninScale family
                     (globalBasis i)|^2

S1         Dev C1ProlateResponseTraceLegalityUnitScale:177-182
def targetProlateDetectorRightSmoothingFactorSummable owner family {nu} globalBasis : Prop :=
  Summable fun i => |targetProlateDetectorRightSmoothingFactor owner family
                     (globalBasis i)|^2

A oL C     Dev C1Prolate:142-146   targetProlateDetectorRightSmoothingFactor
                               = targetProlateRemainderFactor unitSoninScale family
                                 oL rootConvolution owner
F_K        Dev C1Prolate:81-85     targetProlateRemainderFactor lambda family
                               = Q_S oL (E - R_S)           (bounded; windowed projections)
K_S = F†F  Dev C1Prolate:88-92     _adjoint_comp_self
capstone   Dev C1Prolate:370-381   F1' := S1 + S2-legality
                               (of_rightSmoothing_and_rootCommutator)
corollary  brick 1065 :202-214     F1' := S1 + S2-FK-HS
                               (of_rightSmoothing_and_remainderFactorSummable)
```

where the S2-legality operand `targetProlateDetectorRootCommutatorTraceLegality`
(Dev C1Prolate:234-239) is closed by brick 1065's pair owner from S2-FK-HS alone
(brick 1065 :186-198).

## 2. The reduction, exactly

### 2.1 S1 follows from S2-FK-HS: precomposition, not postcomposition

Committed machinery (HilbertSchmidtIdeal.lean:53-77; the `omit [CompleteSpace ...] in`
block at :33 covers it, so no completeness instance is needed):

```text
theorem summable_normSq_precomp {ι κ ν : Type*}
    (sourceBasis : HilbertBasis ι C H) (targetBasis : HilbertBasis κ C G)
    (newSourceBasis : HilbertBasis ν C K)
    (operator : H ->L[C] G) (bounded : K ->L[C] H)
    (hoperator : Summable fun i => |operator (sourceBasis i)|^2) :
    Summable fun k => |(operator oL bounded) (newSourceBasis k)|^2
```

Instantiation:

| argument          | value                                          | why                                                        |
|-------------------|------------------------------------------------|------------------------------------------------------------|
| sourceBasis / targetBasis / newSourceBasis | globalBasis, three times | H = G = K = finiteSCarrier; one basis serves all three roles |
| operator          | F_K : Op                                       | the HS-leg factor; hfactor IS its series (contract def)     |
| bounded           | C = rootConvolution owner : Op                 | typed `Op` at Dev C1Prolate:279; bounded sandwich dressing  |

S1's factor (Dev C1Prolate:145-146) is `F_K oL C` — PREcomposition of F_K by the
bounded map C.  The sibling postcomp lemma (:36-51) would give `C oL F_K`, the wrong
operator order; choosing it silently changes the operator while keeping the proof
shape identical, which is why this record pins the choice explicitly.

```text
S2-FK-HS -- Summable |F_K e_i|^2 --------+
                                         \
                                          v   summable_normSq_precomp (one line)
                                         S1 -- Summable |(F_K oL C) e_i|^2 -->
```

### 2.2 S2-FK-HS is termwise the raw-F1 series: the iff

The retired diagonal identity, verbatim proof from git 74b8cbb under its record-1063
factor name (the last rewrite's lemma verified present in the pinned mathlib tree at
Analysis/InnerProductSpace/Basic.lean:213):

```text
theorem targetProlateRemainderFactor_unit_diagonal_eq_targetRemainder ... :
    ((|F_K (globalBasis i)|^2 : R) : C) =
      inner C (globalBasis i) (targetProlateRemainder unitSoninScale family (globalBasis i)) := by
  have hsq := targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family
  rw [← hsq, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
```

The iff then closes with committed machinery only:

- direction B (IsTraceClassAlong -> S2-FK-HS): VERBATIM the retired `_unit_summable`
  closing — `htrace.norm`, pointwise congr via `Complex.norm_of_nonneg`
  (Analysis/Complex/Norm.lean:106) + `sq_nonneg`.
- direction A (S2-FK-HS -> IsTraceClassAlong): `h.congr (fun i => (hpointwise i).symm)`
  gives summability of the diagonal MODULUS, then `Summable.of_norm`
  (Analysis/Normed/Group/InfiniteSum.lean:186) drops the norm.  This is the only step
  without an in-repo precedent; its sole new lemma was verified present before writing.

## 3. Identification chain: what is Lean-proven vs model-level (the 1063 tension)

| step | statement | status | where pinned |
|------|-----------|--------|--------------|
| K_S = M - R_S, with M := E Q_S E | definitional | LEAN DEF | CCM24FiniteSProjectionTrace.lean:161-166 |
| F_K bounded; K_S = F†F | proven theorem | LEAN | Dev C1Prolate:81-92 |
| eigenvalues of M are squared principal angles between range(E) and range(Q_S) | finite-dim linear algebra, stated in the probe doc | MODEL | 1063 §1; probe :93-97 (M = ED@HT@ED@HT@ED) |
| Tr(K_S)_model = SUM_nonmeet lambda(M) + meet residual | follows from K_S = M - R_S in finite dims; NOT yet a Lean lemma | BRIDGE 1 (open) | this record §3 |
| probe statistic == SUM_nonmeet lambda(M) | `nonmeet_sum` splits at first gap > 0.02, sums the rest (> 1e-12) | MODEL (exact by construction) | probe :104-110; 1063 §3 table |
| grid spectrum -> continuum named-basis series | discretization fidelity of the eigvalsh rig | BRIDGE 2 (open) | 1063 §1 reservation: the probe "does NOT identify the principal-angle statistic with Lean's named-basis IsTraceClassAlong" |

Conclusion: the {2,3,5} growth sits in a term that dominates `Tr(K_S)_model`.  If
bridge 1 holds with sub-growth meet residual and bridge 2 is faithful, S2-FK-HS dies
for that family exactly as raw F1 did.  That is why record 1067 should measure
`|F_K_model|_HS^2 = Tr(M - R_S)` directly — building `R_S_model` per the Gram-corrected
meet at CCM24FiniteSProjectionTrace.lean:145-152 in the same rig — rather than
re-measure the nonmeet mass alone, which leaves bridge 1 open.

## 4. Contract ledger after this record (F1' state)

| Obligation | Statement | Status after 1066 | Producer route |
|------------|-----------|-------------------|----------------|
| S2-FK-HS (THE single contract) | Summable of \|F_K(basis i)\|^2; termwise = the raw F1 series | open; inherits the 1063 operational guard ({2,3,5} ~ xi^0.4 growth); record-1067 probe planned before scheduling a producer | analytic production only — no owner machinery remains in the chain |
| S1 | Summable of \|(F_K oL C)(basis i)\|^2 | DERIVED: follows from S2-FK-HS via summable_normSq_precomp (new theorem, one line) | none needed once S2-FK-HS is produced |
| S2 (commutator legality) | IsTraceClassAlong of the C-dagger root-commutator remainder | closed by brick 1065's pair owner from S2-FK-HS (committed green, build #3) | — |
| F1' | IsTraceClassAlong of D oL K_S along globalBasis | follows from S2-FK-HS ALONE via the new single-contract corollary — CONDITIONAL; no production claimed | consumes the top row once produced |
| F2 (compression factors) | two Summable contracts for Q oL E at unit scale | unchanged | estimate route only; not consumed by this leaf |

## 5. Brick spec and build #4 plan

Files:
- `ConnesWeilRH/Dev/C1ProlateSingleContractReduction.lean` — the four declarations below,
  imports mirroring brick 1065 plus explicit `CC20Concrete.HilbertSchmidtIdeal` /
  `CC20Concrete.PositiveTrace` (for summable_normSq_precomp and IsTraceClassAlong);
  namespace ConnesWeilRH.Source.C1ProlateSingleContractReduction; the open block mirrors
  brick 1065 plus its sibling Dev namespace.
- `ConnesWeilRH/Dev/C1ProlateSingleContractReductionAudit.lean` — #check + #print axioms
  for all four declarations (expect standard-3: propext, Classical.choice, Quot.sound).

Declarations (exact statements):

```text
(0) targetProlateRemainderFactor_unit_diagonal_eq_targetRemainder     [§2.2 verbatim]
(1) targetProlateDetectorRightSmoothingFactorSummable_of_remainderFactorSummable
      {nu} owner family globalBasis (hfactor : S2-FK-HS) : S1
    proof: unfold the two S1 defs; exact summable_normSq_precomp
           globalBasis globalBasis globalBasis F_K C hfactor        [one line]
(2) targetProlateRemainderFactorSummable_iff_unitIsTraceClassAlong
      {nu} globalBasis family : S2-FK-HS <-> IsTraceClassAlong globalBasis K_S
    proof: rw [IsTraceClassAlong, contract]; shared pointwise helper via (0);
           direction B verbatim from the retired _unit_summable closing;
           direction A via .congr + Summable.of_norm
(3) targetProlateRemainderDetectorWeightedTraceLegality_of_remainderFactorSummable
      {nu kappa} globalBasis factorBasis owner family (hfactor : S2-FK-HS) : F1'
    proof: have hright := (1); exact brick 1065's two-contract corollary with
           hright, hfactor                                     [two lines]
```

Build ladder (AGENTS 7a). Mirror decision made by olean probe at build time: the NTFS
mirror holds brick-1065 oleans from build #3 (2026-08-31_05:14) while the ext4 home has
the source but no olean for that module — so BUILD #4 RUNS ON THE NTFS MIRROR
(`/mnt/c/Projects/Connes-Weil-RH-Proof`), where the two new sources already exist at the
canonical Windows paths; wave = exactly the two new modules.  `flock /tmp/lake.lock
lake build <both module names>`, full output to a log file, acceptance on LOG EVIDENCE
only: "Build completed successfully", zero `error:` lines, zero sorryAx for these
modules (exit codes lie across the wsl boundary).

Go/no-go: GO.  Every algebraic input AND both closing routes are committed and green;
the only novel step is declaration (2)'s direction A, whose sole new lemma was verified
present in the pinned mathlib tree before writing.

## 6. Build #4 outcome (post-build addendum)

GREEN on the second attempt. First run red with a single error at the brick's final
`exact`: record-1065's corollary name was split across two source lines, and Lean read
the first line as the complete identifier `targetProlateRemainderDetectorWeightedTraceLegality_`
(unknown) - identifiers do not continue across newlines (hazard banked in AGENTS 7b).
Joined onto one line; rebuilt.

Acceptance evidence (WSL log, warm NTFS mirror): footer "Build completed successfully
(3201 jobs)", zero `error:` lines, zero sorryAx, all four declarations on exactly
[propext, Classical.choice, Quot.sound]; olean mtimes confirm re-elaboration of both new
modules. A parallel duplicate invocation against the same log file was killed before it
could interleave (bash truncates the redirect target at setup time even while blocked on
flock - also banked in AGENTS 7a).
