# CCM25 Source-Interface Referee Decision Record

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
  docs/audits/ccm25-source-interface-accepted-source-packet.md

row group:
  CCM25 Weil-form source interface

theorem candidates:
  CCM25QWDefinitionTheorem(g,F_g)
  CCM25PsiSignExpansionTheorem(F_g)
  CCM25QWLambdaFormulaTheorem(lambda,g,F_g)
  CCM25FinitePrimeTermTheorem(lambda,g,n)
  CCM25VisiblePrimeSupportTheorem(lambda,F_g)
  CCM25PoleNormalizationTheorem(lambda,g)
  CCM25NoSpectralInputForScalarRoute

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem Bundle To Decide

The reviewer must decide whether CCM25 supplies the exact Weil-form source
interface used by the route:

```text
QW(g,g) = Psi(F_g)
F_g = g^* * g
QW_lambda is the source restriction of QW for the same test
restricted finite-prime terms are source Lambda(n)<g|T(n)g> atoms
global and restricted supports use the same visible prime-power atoms
source pole terms sit inside the CCM25 formula with the accepted sign
```

The reviewer must also confirm the scalar route boundary:

```text
the route does not import finite-operator spectral convergence,
determinant convergence, numerical eigenvalue convergence,
or the even-sector minimum-eigenvector assumption.
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/ccm25-source-interface-accepted-source-packet.md` | primary packet |
| `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | global `QW` and `Psi` project package |
| `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | restricted `QW_lambda` and pole project package |
| `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | finite-prime atom theorem targets |
| `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | restriction-definition path audit |
| `docs/audits/source-reread-v0.2.md` | source-line map |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| `QW(g,g)=Psi(F_g)` uses the same `F_g=g^* * g` | `QW`/`Psi` package | pending |
| `Psi` expansion owns finite-prime, archimedean, and pole signs | final sign spine and source-interface packet | pending |
| `QW_lambda` is a restriction-definition scalar, not a spectral approximation | restricted source-readiness audit | pending |
| restricted finite-prime atoms use source `Lambda(n)<g|T(n)g>` | finite-prime theorem contract | pending |
| global and restricted support sets use the same visible source atoms for fixed `F_g` | finite-prime support package | pending |
| pole normalization is not double-counted against route `PoleJetExtra` | restricted `QW_lambda` package | pending |
| no spectral convergence, determinant convergence, or even-sector assumption enters the scalar route | source-import and second-opinion audits | pending |

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

If the reviewer rejects the CCM25 source-interface row, use the most precise
obstruction name:

```text
QWObjectMismatch(g,F_g)
PsiSignExpansionMismatch(F_g)
QWLambdaRestrictionMismatch(lambda,g,F_g)
FinitePrimeAtomMismatch(lambda,g,n)
VisiblePrimeSupportMismatch(lambda,F_g)
PoleNormalizationMismatch(lambda,g)
SpectralShortcutImport
EvenSectorAssumptionImport
```

## Current Judgment

| question | answer |
|---|---|
| Has the CCM25 source-interface row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the CCM25 source-interface decision. It does not decide it.
