# Accepted-Source Decision Evidence Matrix

Date: 2026-06-28

Status:

```text
decision evidence matrix ready
accepted-source certification: open
Lean status: not touched
```

## Purpose

This matrix gives a referee one table for the nine accepted-source decisions.

It does not accept any row. It records:

```text
decision record
source anchors
project evidence
minimum acceptance evidence
named rejection
route consequence
```

A row becomes accepted-source only after the matching decision record receives
an external referee decision, accepted independent proof, or Lean theorem with
axiom audit.

## Dependency Order

```text
1. CCM24 source interface
        |
        v
2. CCM25 source interface
        |
        v
3. CC20 trace source interface
        |
        v
4. S2-B1 trace-scale no-missing-bulk theorem
        |
        +-----------------------------+
        |                             |
        v                             v
5. sign/defect classification     6. restricted-to-full scalar bridge
        |                             |
        +-------------+---------------+
                      |
                      v
7. final sign bridge
                      |
                      v
8. CC20 finite-vanishing exit
                      |
                      v
9. RH definition bridge
```

The order is not cosmetic. Later rows consume object, support, sign, and limit
choices from earlier rows.

## Decision Matrix

| order | row | decision record | source anchors | project evidence | acceptance evidence required | rejection names | route consequence if rejected |
|---:|---|---|---|---|---|---|---|
| 1 | CCM24 fixed-S source interface | `docs/audits/ccm24-source-interface-referee-decision-record.md` | `mainc2m24fine.tex:237-253,761-823,846-852,983-1003,1050-1060` | `docs/audits/ccm24-source-interface-accepted-source-packet.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md`; `docs/proofs/ccm24-support-window-transport-discharge.md` | reviewer accepts one finite `S`, one support window `I`, one `V_S=M_S U_S`, one bounded comparison class, one Sonin comparison, and no automatic post-`Q` transport | `FixedSModelMismatch(S)`, `SupportWindowDrift(S,I,g)`, `BoundedComparisonClassMismatch(S)`, `AutomaticPostQTransportImport(S,I,g)` | route loses the common fixed-S coordinate before trace read-off |
| 2 | CCM25 Weil-form source interface | `docs/audits/ccm25-source-interface-referee-decision-record.md` | `mc2arXiv.tex:400-428,445-470,496-540,266-272,302-303` | `docs/audits/ccm25-source-interface-accepted-source-packet.md`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | reviewer accepts `QW(g,g)=Psi(F_g)`, `QW_lambda` as restriction, finite-prime atoms, pole normalization, and no spectral input | `QWObjectMismatch(g,F_g)`, `QWLambdaRestrictionMismatch(lambda,g,F_g)`, `FinitePrimeAtomMismatch(lambda,g,n)`, `PoleNormalizationMismatch(lambda,g)`, `SpectralShortcutImport` | route cannot identify the positive trace with the restricted Weil scalar or pass to `QW(g,g)` |
| 3 | CC20 trace source interface | `docs/audits/cc20-trace-source-interface-referee-decision-record.md` | `weil-compo.tex:378-387,448-464,2014-2030,2106-2121,2131-2165` | `docs/audits/cc20-trace-source-interface-accepted-source-packet.md`; `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md`; `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | reviewer accepts Hilbert-Schmidt, trace-class square, cyclic trace moves, support-square trace, Mellin convention, and local signs for the same test | `TraceLegalityBeforePositivityFailure(g)`, `CyclicTraceMoveWithoutIdealWitness(g)`, `SupportSquareScalarMismatch(g)`, `MellinHalfDensityMismatch(F_g)`, `CC20LocalSignMismatch(F_g)` | route cannot use positive trace or feed CC20 Proposition C.1 |
| 4 | S2-B1 trace-scale no-missing-bulk theorem | `docs/audits/s2-b1-trace-scale-referee-decision-record.md` | combined CCM24, CCM25, and CC20 anchors above | `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md`; `docs/proofs/trace-scale-compatibility-proof-package.md`; source-interface packets | reviewer accepts `PositiveTrace = QW_lambda + Rank + Pole + CdefRemainder` with no `BulkScaleTerm` and no hidden finite-part subtraction | `BulkScaleTerm_(S,I,lambda,g)`, `HiddenFinitePartSubtraction_(S,I,lambda,g)`, `TraceScaleConventionMismatch_(S,I,lambda,g)`, `QWLambdaReadOffMismatch_(S,I,lambda,g)`, `CdefDoesNotDominateRemainder_(S,I,lambda,g,J)` | route stops at positive-trace read-off |
| 5 | Rows 1-7 sign/defect classification | `docs/audits/sign-defect-referee-decision-record.md` | `weil-compo.tex:710-719,747-761,875-878,1132-1140,1196-1199,1267-1270,1338-1360,2168-2250`; CCM24 transport anchors | `docs/audits/sign-defect-accepted-source-packet.md`; `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md`; `docs/proofs/sonin-prolate-defect-referee-discharge.md`; `docs/audits/semilocal-fourth-defect-ledger.md` | reviewer accepts source orientation, fixed-S post-`Q` transport, projection-defect split, rank/pole ledger, endpoint-strip `Cdef`, and no hidden positive defect | `CC20PostQSourceTermMissing(g)`, `FixedSTransportObjectDrift(S,I,lambda,g,F_g)`, `EndpointStripCdefMismatch(S,I,lambda,g,F_g,J)`, `SemilocalFourthDefect_(S,I,lambda,g,F_g,J)` | route cannot pass from finite-lambda positive trace to the lower bound for `QW_lambda` |
| 6 | restricted-to-full scalar bridge | `docs/audits/restricted-to-full-referee-decision-record.md` | `mc2arXiv.tex:400-428,464-470,496-540,266-272,302-303` | `docs/audits/restricted-to-full-accepted-source-packet.md`; `docs/audits/restricted-to-full-qw-source-readiness-audit.md`; `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | reviewer accepts eventual fixed-test equality `QW_lambda(g,g)=QW(g,g)` from restriction definition, support containment, and finite-prime stabilization | `QWLambdaRestrictionMismatch(lambda,g,F_g)`, `FixedTestSupportFailure(lambda,g)`, `FinitePrimeSupportStabilizationFailure(lambda,g,F_g)`, `SpectralShortcutImport`, `EvenSectorAssumptionImport` | route has only a finite-lambda lower bound and cannot reach global `QW(g,g)` |
| 7 | final CCM25-to-CC20 sign bridge | `docs/audits/final-sign-referee-decision-record.md` | `mc2arXiv.tex:445-470,530-540`; `weil-compo.tex:2131-2165,2072-2085` | `docs/audits/final-sign-accepted-source-packet.md`; `docs/proofs/final-sign-bridge-proof-package.md`; `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | reviewer accepts `QW(g,g)=-sum_v W_v(F_g)` and `QW(g,g)>=0 -> sum_v W_v(F_g)<=0` for the same `F_g` | `FinalSignMismatch(g,F_g)`, `QWCC20TestMismatch(g,F_g)`, `PsiExpansionSignMismatch(F_g)`, `FinitePrimeSignMismatch(F_g)`, `PoleSignMismatch(F_g)`, `InequalityDirectionMismatch(g,F_g)` | route cannot feed CC20's nonpositive Weil inequality |
| 8 | CC20 finite-vanishing exit | `docs/audits/cc20-exit-referee-decision-record.md` | `weil-compo.tex:2014-2030,2072-2085,2131-2165` | `docs/audits/cc20-exit-accepted-source-packet.md`; `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md`; `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | reviewer accepts Proposition C.1 with `F={0,1/2,1}`, route vanishing to CC20 Mellin vanishing, and the source RH conclusion | `CC20FiniteSetSideConditionFailure`, `MellinVanishingMismatch(F_g)`, `CC20SignInputMismatch(F_g)`, `UniformityRequirementMismatch`, `PropositionC1StatementMismatch` | route cannot derive the source RH conclusion |
| 9 | source RH to standard RH bridge | `docs/audits/rh-definition-referee-decision-record.md` | `weil-compo.tex:2072-2085`; `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-168` | `docs/audits/rh-definition-accepted-source-packet.md`; `docs/proofs/rh-definition-bridge-proof-package.md`; `docs/proofs/rh-definition-bridge-theorem-contract.md`; `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | reviewer or Lean accepts zeta equality, zero transport, negative-even exclusion, pole exclusion, critical-line equality, and standard RH target | `SourceZetaStandardZetaMismatch`, `ZeroPredicateMismatch`, `NegativeEvenExclusionMismatch`, `PoleExclusionMismatch`, `CriticalLineMismatch`, `ProjectLocalRHTargetLeak` | route may prove only a source-local RH phrase, not the standard RH predicate |

## Minimum Accepted-Source Evidence

For each row, the decision record must contain:

```text
verdict:
  accepted as stated
  or accepted after listed correction

accepted theorem statement:
  exact statement, not a paraphrase

accepted hypotheses:
  source hypotheses and route bridge hypotheses

accepted object bridges:
  same g, same F_g, same S/I/lambda where applicable

accepted sign bridges:
  local signs, pole signs, and inequality direction where applicable

accepted limit order:
  finite-lambda, fixed-test, or no-limit claim as required

non-importable shortcuts checked:
  spectral convergence, determinant convergence, even-sector assumption,
  route-local density, or project-local RH name

remaining caveats:
  none that weaken the row below the theorem candidate
```

If the decision uses a Lean theorem, attach the theorem name and the
`#print axioms` output. The remaining axioms must be only approved source
interfaces plus Mathlib/kernel foundations.

## Current Judgment

| question | answer |
|---|---|
| Does this matrix accept any row? | no |
| Does every accepted-source packet have a decision record? | yes |
| Does every decision record have a named rejection path? | yes |
| Has any accepted-source verdict been received? | no |
| Is S2-B1 still the first hostile-review row? | yes |
| Did this pass touch Lean? | no |

This matrix makes the external accepted-source review executable. It does not
replace the external decisions.
