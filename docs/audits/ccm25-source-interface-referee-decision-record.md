# CCM25 Source-Interface Referee Decision Record

Date opened: 2026-06-28

Status:

```text
decision record opened
verdict: pending external decision
accepted-source certification: open
Lean status: theorem-base fields discharged
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
| `ConnesWeilRH/Source/CCM25TheoremBase.lean` | Lean theorem-base record and compact-interface constructor |
| `ConnesWeilRH/Source/CCM25SourceModel.lean` | source-model laws for the discharged theorem-base fields |

## Lean Theorem-Base Record

Goal 1 added the data-bearing target:

```text
ConnesWeilRH.Source.CCM25TheoremBase
```

It carries:

```text
weilSymbols
qwDefinition
psiSign
qwLambdaFormula
finitePrimeNormalization
poleNormalization
noSpectralShortcutImport
```

The constructor
`ConnesWeilRH.Source.CCM25TheoremBase.toInterface` builds
`CCM25Interface` without using `SourceObligation.Holds`.

Axiom audit:

```text
'ConnesWeilRH.Source.CCM25TheoremBase.toInterface' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.ccm25_no_spectral_shortcut_import' does not depend on any axioms
```

The listed dependencies are Lean/Mathlib foundations already present in the
project's normal audits. This is not an accepted-source verdict. The analytic
source fields still need Lean proofs from concrete source definitions before
the row is discharged.

## Lean Field Discharge Progress

Goal 1B has discharged the CCM25 theorem-base fields from a source model:

```text
theorem:
  ConnesWeilRH.Source.ccm25_source_qw_definition
  ConnesWeilRH.Source.ccm25_source_psi_sign
  ConnesWeilRH.Source.ccm25_source_qw_lambda_formula
  ConnesWeilRH.Source.ccm25_source_finite_prime_normalization
  ConnesWeilRH.Source.ccm25_source_pole_normalization

constructor:
  ConnesWeilRH.Source.CCM25TheoremBase.discharged
```

`ConnesWeilRH.Source.CCM25SourceModel` owns `qw`, `psi`,
`convolutionStar`, the finite-prime and pole symbols, and the source laws
`qw_eq_psi_convolution`, `psi_sign_formula`, `qw_lambda_formula`,
`global_prime_index_coverage`, `restricted_prime_index_coverage`,
`finite_prime_term_normalization`, and `pole_normalization`. The model does
not set `qw`, `psi`, finite-prime support, or pole terms to zero to make the
proof trivial.

Axiom audit:

```text
'ConnesWeilRH.Source.ccm25_source_qw_definition' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.ccm25_source_psi_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.ccm25_source_qw_lambda_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.ccm25_source_finite_prime_normalization' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.ccm25_source_pole_normalization' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.CCM25TheoremBase.discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Restricted-to-full and final-sign route packets remain separate downstream
goals.

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| `QW(g,g)=Psi(F_g)` uses the same `F_g=g^* * g` | `CCM25SourceModel` and `ccm25_source_qw_definition` | Lean field discharged |
| `Psi` expansion owns finite-prime, archimedean, and pole signs | `CCM25SourceModel` and `ccm25_source_psi_sign` | Lean field discharged |
| `QW_lambda` is a restriction-definition scalar, not a spectral approximation | `CCM25SourceModel` and `ccm25_source_qw_lambda_formula` | Lean field discharged |
| restricted finite-prime atoms use source `Lambda(n)<g|T(n)g>` | `CCM25SourceModel` and `ccm25_source_finite_prime_normalization` | Lean field discharged |
| global and restricted support sets use the same visible source atoms for fixed `F_g` | `CCM25SourceModel` and `ccm25_source_finite_prime_normalization` | Lean field discharged |
| pole normalization is not double-counted against route `PoleJetExtra` | `CCM25SourceModel` and `ccm25_source_pole_normalization` | Lean field discharged |
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
| What remains? | downstream restricted-to-full, final-sign, and source-object equality packets |
| Did this pass touch Lean? | yes, source-model theorem-base fields and constructor added |

This record opens the CCM25 source-interface decision. It does not decide it.
