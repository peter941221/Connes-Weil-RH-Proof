# Restricted-To-Full Referee Decision Record

Date opened: 2026-06-28

Status:

```text
decision record opened
verdict: pending external decision
accepted-source certification: open
Lean status: not touched
```

## Packet Under Review

```text
packet file:
  docs/audits/restricted-to-full-accepted-source-packet.md

row group:
  fixed-test restricted-to-full scalar bridge

theorem candidate:
  RestrictedToFullQWAcceptedTheorem(g,F_g)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether the CCM25 restriction definition and the
fixed-test support bridges prove:

```text
exists lambda0,
forall lambda >= lambda0,
  QW_lambda(g,g) = QW(g,g).
```

This is an eventual scalar equality for one fixed test. It is not a spectral
limit theorem.

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/restricted-to-full-accepted-source-packet.md` | primary packet |
| `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | source-readiness audit for the CCM25 restriction-definition path |
| `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | route-evidence bridge package |
| `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` | theorem-contract target |
| `docs/audits/ccm25-source-interface-referee-decision-record.md` | CCM25 source-interface prerequisite |
| `docs/audits/ccm24-source-interface-referee-decision-record.md` | support/window prerequisite |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| the `g` in `QW_lambda` and `QW` is one source test | common-test packages | pending |
| `supp(g)` lies in the restricted interval for all large `lambda` | CCM24 source-interface and support packages | pending |
| `F_g` gives the same visible finite-prime atoms in restricted and full formulas | finite-prime normalization packages | pending |
| CCM25 defines `QW_lambda` as a restriction of `QW` | restricted-to-full source-readiness audit | pending |
| pole and archimedean conventions agree between restricted and full forms | CCM25 and final-sign packets | pending |
| no finite-operator spectral convergence, determinant convergence, numerical eigenvalue convergence, or even-sector assumption enters | source-import and second-opinion audits | pending |

## Decision Block

External reviewer or formal proof must fill this block.

```text
verdict:
  pending

accepted theorem statement:
  pending

accepted hypotheses:
  pending

accepted object bridges:
  pending

accepted sign bridges:
  pending

accepted limit order:
  pending

non-importable shortcuts checked:
  pending

remaining caveats:
  pending
```

## Rejection Names

If the reviewer rejects the restricted-to-full row, use the most precise
obstruction name:

```text
QWLambdaRestrictionMismatch(lambda,g,F_g)
FixedTestSupportFailure(lambda,g)
FinitePrimeSupportStabilizationFailure(lambda,g,F_g)
PoleArchimedeanConventionDrift(lambda,g)
SpectralShortcutImport
EvenSectorAssumptionImport
```

## Current Judgment

| question | answer |
|---|---|
| Has the restricted-to-full row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the restricted-to-full accepted-source decision. It does not
decide it.
