# Connes-Weil RH Proof

This repository records a source-conditional Connes-Weil route toward the
Riemann Hypothesis and a Lean scaffold for checking the route interfaces.

The repository does not claim a completed proof of RH. It does not claim
journal acceptance, Clay acceptance, community acceptance, external referee
certification, or a completed Lean proof. The current artifact is a detailed
route with local proof packages and a Lean interface layer that keeps the
remaining analytic inputs visible.

## Current Status

```text
route-evidence composition: closed at local proof-package level
local pre-Lean proof-package matrix: complete
accepted-source certification: open
external referee certification: open
Lean route theorem: certificate-conditional
Lean source-object interface hardening: active
unconditional Lean RH theorem: open
public proof status: source-conditional
```

Here `closed` means that every row needed by the route has a named local
proof-package or audit artifact. It does not mean that an outside referee has
accepted the analytic row, that a source paper contains the exact imported
theorem in the required form, or that Lean has proved the row from first
principles.

The current Lean theorem has the conditional shape:

```lean
structure RouteCertificate (inputs : RouteInputs) where
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  ...
```

So the Lean route currently proves:

```text
RouteCertificate inputs -> Mathlib RiemannHypothesis
```

It does not yet prove:

```text
theorem final_rh : _root_.RiemannHypothesis
```

The current Lean work is replacing broad certificate fields by source-object
backed constructions and package-owned projections. The remaining hard route
inputs are still explicit.

## Short Verdict

The route is a conditional composition theorem:

```text
If the named CCM24, CCM25, and CC20 source-facing rows hold with the
normalizations used here, then the fixed-S positive-trace route gives RH.
```

The route does not import RH. It also does not import the CCM25 finite-operator
spectral convergence program, determinant convergence, or numerical eigenvalue
convergence. It uses a fixed-test scalar restriction bridge:

```text
QW_lambda(g,g) = QW(g,g)
```

for the same fixed source test once the support and finite-prime atoms have
stabilized inside the restricted window.

The route fails if any one of the following checks fails:

```text
1. The positive trace has an untracked bulk term outside QW_lambda, rank, pole,
   and endpoint-strip Cdef.

2. The Rows 1-7 sign/defect classification misses a fourth positive defect.

3. The fixed-test restricted-to-full bridge secretly imports spectral,
   determinant, or eigenvalue convergence.

4. The final sign bridge has the wrong sign or changes the test object.

5. The CC20 source RH conclusion does not transport to Mathlib's
   _root_.RiemannHypothesis.
```

## Primary Sources

| source | arXiv | role in the route |
|---|---|---|
| Connes-Consani-Moscovici 2024 | https://arxiv.org/abs/2310.18423 | fixed-`S` semilocal Hilbert model, support transport, Fourier compatibility, Sonin comparison |
| Connes-Consani-Moscovici 2025 | https://arxiv.org/abs/2511.22755 | Weil form `QW`, restricted form `QW_lambda`, pole normalization, finite-prime normalization |
| Connes-Consani 2020 | https://arxiv.org/abs/2006.13771 | archimedean support-square trace, trace legality, Mellin convention, finite-vanishing RH criterion |

Important source and certification files:

```text
docs/audits/source-reread-v0.2.md
docs/audits/source-import-legitimacy-audit.md
docs/audits/source-interface-discharge-completion-audit.md
docs/audits/unconditional-rh-gap-ledger.md
docs/audits/pre-lean-completion-audit.md
docs/audits/accepted-source-certification-audit.md
docs/audits/accepted-source-theorem-upgrade-ledger.md
docs/audits/accepted-source-packet-completion-audit.md
docs/audits/accepted-source-certification-status-board.md
docs/audits/accepted-source-decision-evidence-matrix.md
```

## Evidence Classes

Reviewers should separate four levels of evidence.

| class | meaning | current status |
|---|---|---|
| Source line located | A cited source file contains the object, formula, or theorem shape. | many rows |
| Project proof package | This repository gives a manuscript-level derivation from cited source inputs. | all local route rows |
| Accepted-source row | A source theorem, external referee, independent proof, or Lean theorem accepts the exact statement and hypotheses. | open |
| Lean theorem | Lean proves the row and `#print axioms` leaves only approved source interfaces and kernel foundations. | open for analytic rows |

The repository reaches the second class for the full route. It does not yet
reach accepted-source or full Lean theorem strength for the source-facing
analytic rows.

## Proof Route

The proof route is:

```text
fixed test g
        |
        v
F_g = g^* * g
        |
        v
choose fixed S, support window I, and lambda for this g
        |
        v
PositiveTrace_(S,lambda)(g) >= 0
        |
        v
PositiveTrace
  =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + R_(S,I,lambda,J)(g)
        |
        v
triple vanishing kills Rank and PoleJetExtra
        |
        v
|R_(S,I,lambda,J)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
        |
        v
Cdef_(S,I,lambda,J)(g) -> 0
        |
        v
QW_lambda(g,g) = QW(g,g) for lambda large enough
        |
        v
QW(g,g) >= 0
        |
        v
QW(g,g) = - sum_v W_v(F_g)
        |
        v
sum_v W_v(F_g) <= 0
        |
        v
Connes-Consani finite-vanishing criterion
        |
        v
Mathlib _root_.RiemannHypothesis
```

The finite set `S` may depend on the fixed test `g`. The route uses `S` only as
an auxiliary witness for that fixed test. After the restricted-to-full bridge,
the output is the global scalar `QW(g,g)`, and the final sign bridge gives the
CC20 global Weil sum for the same `F_g`.

The support window `I` is the fixed support window, or interval, used to localize
the chosen test. It is not a new target object.

## Object-Matching Requirement

The route only works if the following data remain the same throughout the
positive trace, read-off, restricted-to-full bridge, final sign bridge, and RH
exit:

```text
same g
same F_g = g^* * g
same finite set S
same support window I
same lambda
same half-density convention
same sign convention
same pole normalization
same finite-prime support
```

Lean now enforces part of this discipline by making downstream bridges consume
fields from the same source-backed package rather than independent propositions
with matching-looking names.

## Current Lean Interface Progress

The Lean scaffold is under:

```text
ConnesWeilRH/
ConnesWeilRH.lean
lakefile.toml
lean-toolchain
```

The current source-object layer reaches the route-certificate boundary.

The following constructors and records are now part of the interface-hardening
path:

```text
RouteInputs.ofExpandedSourcePackage
SourceBackedFixedSTest.ofExpandedSourcePackage
SourceTraceReadOffData.ofExpandedSourcePackage
route_certificate_of_expanded_source_package
ExpandedSourceFixedSTestFrontEnd
ExpandedSourceTraceReadOffFrontEnd
ExpandedSourceRouteCertificateFrontEnd
```

The current expanded route-certificate front end concentrates the hard route
inputs in:

```text
SourceSignDefectClassification
RestrictedToFullQWBridgeContract
FinalSignBridgeContract
```

The trace front end still carries the full and restricted trace-to-QW read-off
bridges as explicit inputs. These are not yet Lean proofs from analytic first
principles.

Recent Lean hardening moved several authority points into source-owned package
layers:

| area | current Lean hardening | boundary |
|---|---|---|
| RH definition bridge | source-RH to Mathlib-RH transport goes through `RHDefinitionBridge.source_rh_to_mathlib_rh` | does not prove the CC20 source criterion |
| CC20 finite-vanishing package | the compact criterion projects from the source-owned finite-vanishing package | does not prove Proposition C.1 from first principles |
| CCM25 finite-prime support | fixed-lambda exact support projects from the CCM25 concrete arithmetic package | does not prove the CCM25 analytic source formula |
| CCM25 common atoms | global and restricted finite-prime evaluator sums share the same common atoms | does not construct the analytic evaluator |
| fixed-test scalar read-off | package-owned theorems express `QW_lambda = QW` from common-atom read-offs and archimedean/pole balance | does not prove the analytic archimedean/pole balance |
| restricted-to-full guard | `RestrictedToFullAllowedInputRows` lists the allowed evidence and excludes spectral, determinant, and numerical eigenvalue imports | does not prove restricted-to-full analytically |

For Lean interface changes, the current verification pattern is:

```text
lake build ConnesWeilRH
#print axioms for changed constructors and final_connes_weil_rh
```

The latest recorded `#print axioms` checks for these interface-hardening rows
reported only:

```text
propext
Classical.choice
Quot.sound
```

Those are kernel/Mathlib foundations. They do not make the route unconditional,
because the remaining hard analytic inputs are still certificate fields or
source-package fields.

## Mathematical Gates

### Gate 1: Trace-Scale Compatibility

The positive trace, support-square trace, CC20 no-defect trace, and CCM25
restricted form must represent the same finite-lambda scalar.

The route must rule out a missing source-owned term such as:

```text
Bulk_(S,lambda)(g,g) ~ C log(lambda) ||g||^2
```

outside:

```text
QW_lambda
Rank
PoleJetExtra
endpoint-strip Cdef
```

Relevant files:

```text
docs/audits/trace-scale-compatibility-audit.md
docs/audits/trace-scale-compatibility-discharge-attempt.md
docs/audits/trace-scale-source-term-ledger.md
docs/proofs/trace-scale-compatibility-theorem-contract.md
docs/proofs/trace-scale-compatibility-proof-package.md
```

### Gate 2: Sign/Defect Classification

The route cannot use positive trace to infer `QW_lambda(g,g) >= 0` directly.
It needs the defect ledger:

```text
PositiveTrace
  =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + R_(S,I,lambda,J)(g)
```

with:

```text
|R_(S,I,lambda,J)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
```

The sign/defect bridge is split into seven rows:

```text
Row 1: source remainder object and sign
Row 2: source remainder after Q
Row 3: fixed-S transport into the CCM24/Sonin/window coordinate
Row 4: projection-defect normal form
Row 5: no-strip rank/pole identification
Row 6: endpoint-strip Cdef domination
Row 7: no hidden positive defect outside Cdef
```

Relevant files:

```text
docs/audits/sign-defect-blocker-audit.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/audits/sign-defect-accepted-source-packet.md
docs/audits/sign-defect-referee-decision-record.md
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

### Gate 3: Ledger Killing

The route imposes triple vanishing:

```text
hat g(0) = hat g(+i/2) = hat g(-i/2) = 0
```

This kills:

```text
Rank_(S,I)(g)
PoleJetExtra_(S,I)(g)
```

At finite lambda the route obtains:

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
```

This is weaker than finite-lambda positivity. The route needs fixed-test
exhaustion before it obtains full Weil positivity.

Relevant files:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

### Gate 4: Fixed-Test Exhaustion And Restricted-To-Full

For fixed `g`, `S`, `I`, and `J`, the endpoint-strip remainder must vanish:

```text
Cdef_(S,I,lambda,J)(g) -> 0
```

The restricted form must then agree with the full form:

```text
QW_lambda(g,g) = QW(g,g)
```

The current route excludes these replacement inputs:

```text
finite-operator spectral convergence
determinant convergence
numerical eigenvalue convergence
even-sector minimum-eigenvector assumption
```

The Lean guard `RestrictedToFullAllowedInputRows` lists the permitted evidence:

```text
common tuple
fixed-test support threshold
prime-power atom stabilization
finite-prime stabilization
exact finite-prime support
restriction rows
finite-prime evaluator sum equality
archimedean/pole stability
archimedean contribution balance
no-spectral-convergence witness
lower-bound evidence
```

Relevant files:

```text
docs/audits/restricted-to-full-qw-source-readiness-audit.md
docs/audits/restricted-to-full-accepted-source-packet.md
docs/audits/restricted-to-full-referee-decision-record.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

### Gate 5: CCM25 Finite-Prime Normalization

The finite-prime contribution must use the same source test and the same
prime-power atoms in the global and restricted formulas.

The pointwise local atom is:

```text
Lambda(n) * <g | T(n) g>
```

The minus sign belongs to the surrounding `Psi` or `QW_lambda` formula. It must
not be absorbed into the pointwise atom and then subtracted again.

The Lean package layer now exposes exact support and common-atom read-offs from
the same CCM25 concrete arithmetic package. This reduces object drift, but it
does not prove the CCM25 analytic source formula.

Relevant files:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/audits/ccm25-source-interface-accepted-source-packet.md
docs/audits/ccm25-source-interface-referee-decision-record.md
```

### Gate 6: Final Sign Bridge

The final sign bridge must prove:

```text
QW(g,g) = - sum_v W_v(F_g)
```

Then:

```text
QW(g,g) >= 0
        |
        v
sum_v W_v(F_g) <= 0
```

This is the CC20 inequality direction needed for the finite-vanishing exit.

Relevant files:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/final-sign-bridge-proof-package.md
docs/audits/final-sign-accepted-source-packet.md
docs/audits/final-sign-referee-decision-record.md
```

### Gate 7: CC20 Finite-Vanishing Exit And RH Definition

The final finite vanishing set is:

```text
F = {0, 1/2, 1}
```

The triple vanishing matches this set under the CC20 Mellin convention:

```text
s = 1/2 - i t

t = 0     -> s = 1/2
t = +i/2  -> s = 1
t = -i/2  -> s = 0
```

The final Lean target is Mathlib's canonical:

```text
_root_.RiemannHypothesis
```

The bridge must match:

```text
same zeta function
same non-trivial-zero predicate
same pole exclusion
same negative-even trivial-zero exclusion
same critical-line condition s.re = 1/2
```

Relevant files:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
docs/proofs/rh-definition-bridge-spine-discharge.md
docs/proofs/rh-definition-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-proof-package.md
docs/proofs/source-conditional-rh-route-closure-proof-package.md
docs/audits/rh-definition-accepted-source-packet.md
docs/audits/rh-definition-referee-decision-record.md
```

## Accepted-Source Review State

Every source-facing row now has a review packet or theorem-decision record.
None is marked accepted-source.

Review packets and decision records:

```text
docs/audits/ccm24-source-interface-accepted-source-packet.md
docs/audits/ccm24-source-interface-referee-decision-record.md
docs/audits/ccm25-source-interface-accepted-source-packet.md
docs/audits/ccm25-source-interface-referee-decision-record.md
docs/audits/cc20-trace-source-interface-accepted-source-packet.md
docs/audits/cc20-trace-source-interface-referee-decision-record.md
docs/audits/trace-scale-source-term-ledger.md
docs/audits/s2-b1-trace-scale-referee-decision-record.md
docs/audits/sign-defect-accepted-source-packet.md
docs/audits/sign-defect-referee-decision-record.md
docs/audits/restricted-to-full-accepted-source-packet.md
docs/audits/restricted-to-full-referee-decision-record.md
docs/audits/final-sign-accepted-source-packet.md
docs/audits/final-sign-referee-decision-record.md
docs/audits/cc20-exit-accepted-source-packet.md
docs/audits/cc20-exit-referee-decision-record.md
docs/audits/rh-definition-accepted-source-packet.md
docs/audits/rh-definition-referee-decision-record.md
```

Accepted responses should use one of these verdicts:

```text
accepted as stated
accepted after listed correction
rejected for listed obstruction
requires formalization before judgment
```

## Falsification Tests For Reviewers

| test | failure mechanism | first file to inspect |
|---|---|---|
| trace scale | `Tr(A^*A)` contains a lambda-growing bulk term outside rank, pole, and endpoint-strip `Cdef` | `docs/proofs/trace-scale-compatibility-proof-package.md` |
| source convention | the no-defect source trace uses a finite-part convention that loses trace positivity | `docs/proofs/trace-scale-compatibility-theorem-contract.md` |
| spectral shortcut | `QW_lambda -> QW` uses finite-operator spectra, determinant convergence, or numerical eigenvalues | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| fourth defect | fixed-S semilocal transport creates a source term outside Rows 1-7 | `docs/audits/semilocal-fourth-defect-ledger.md` |
| finite-prime normalization | a prime-power atom is omitted, duplicated, or assigned the wrong `Lambda(n)<g|T(n)g>` term | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| dynamic `S(g)` | the fixed-S read-off returns an `S`-local scalar instead of global `QW(g,g)` | `docs/audits/s-local-global-quantifier-audit.md` |
| final sign | `QW(g,g)` equals the CC20 Weil sum with the wrong sign or for a different test object | `docs/proofs/final-sign-bridge-proof-package.md` |
| RH definition | the source zero predicate does not match Mathlib's zeta, exclusions, and critical-line target | `docs/proofs/rh-definition-bridge-proof-package.md` |

A reviewer should reject the route if one test fails with a source-backed
counterexample.

## Non-Importable Shortcuts

These claims must not enter the route as accepted inputs.

| shortcut | status in this route |
|---|---|
| CCM25 finite-operator spectral convergence to zeta zeros | not used |
| determinant convergence toward Xi | not used |
| numerical eigenvalue convergence | not used |
| even-sector minimum-eigenvector assumption | not used |
| replacing positive trace by `S_lambda theta_S(g)` | rejected unless a new trace-scale theorem is proved |
| automatic harmless Sonin/prolate defect | replaced by Rows 1-7 |
| automatic CCM24 transport for post-`Q` derivative, boundary, and tail terms | replaced by Row 3 subcontracts |
| source statement ending in "RH" equals Mathlib RH by name | replaced by the RH definition bridge |

## Repository Layout

```text
ConnesWeilRH/
  Segmented Lean scaffold for the Connes-Weil route.

docs/audits/
  Source rereads, blocker audits, accepted-source packets, and theorem-decision
  records.

docs/proofs/
  Project proof packages and theorem contracts.

docs/manuscripts/
  Paper-facing manuscript drafts.

formalization/
  Lean readiness and interface planning notes.
```

## Verification Commands

For Lean route work:

```text
lake build ConnesWeilRH
```

For hygiene:

```text
git diff --check
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"
rg -n "allGood|everything|complete|exitWorks" ConnesWeilRH docs -g "*.lean" -g "*.md"
```

Before treating a Lean theorem as a proof artifact:

```text
#print axioms <theorem_name>
```

The remaining axioms must be exactly the approved source interfaces plus
Lean/Mathlib foundations.

## Current Boundary

The current repository is ready for outside mathematical review as
source-conditional route evidence. It is not an accepted-source certificate, a
completed Lean proof, or a public proof of RH.
