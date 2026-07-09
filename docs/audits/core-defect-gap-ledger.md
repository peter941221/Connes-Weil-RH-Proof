# Core Defect Gap Ledger

Status: battle ledger for the three hard steps behind the fixed-S
Connes-Weil positive trace route.

This file does not certify RH. It extracts the three proof packages behind the
fixed-S positive trace route and records their current route-evidence status.

## Result

The three battle packages are now written at route-evidence level and are
integrated into the manuscript's `Three-Battle Integrated Gate`.

The newer hard-blocker audit is:

```text
docs/audits/sign-defect-blocker-audit.md
```

It treats the hostile sign/defect objection as closed only at route-evidence
level until an accepted import or formal theorem proves that every non-ledger
Sonin/prolate defect produced by the fixed-S read-off lies in the
endpoint-strip `Cdef` class and that no hidden positive defect remains.

The theorem contract for that exact target is:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
```

The discharge ledger for that contract is:

```text
docs/audits/sonin-prolate-defect-discharge-ledger.md
```

It splits the hard blocker into seven rows: source remainder object, source
remainder after `Q`, fixed-S Sonin transport, projection-defect normal form,
rank/pole identification, endpoint-strip `Cdef` domination, and the final
no-hidden-positive-defect equality.

Rows 1 and 2 now have a source-orientation theorem contract:

```text
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
```

That contract fixes the CC20 signs `W_infty=L-D` and `W_infty=S-E`; it does
not prove the later fixed-S endpoint-strip `Cdef` bridge.

Row 3 now has a fixed-S transport theorem contract:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
```

That contract states the next import/proof target:
`CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g)`. It only transports
the CC20 `D circ Q` / `E circ Q` bulk and boundary pieces into the same
fixed-S CCM24/Sonin/window coordinate. It does not classify them as rank, pole,
or endpoint-strip `Cdef`; those are later rows.

After the restricted lower bound is obtained, the restricted-to-full step is
separately guarded by:

```text
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
```

Those files require the CCM25 restriction definition to compose with the common
test, fixed window, and finite-prime support contracts. They explicitly reject
finite-operator spectral convergence or determinant convergence as a substitute
for fixed-test scalar equality.

The source-readiness audit for the contract is:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md
```

It finds relevant CC20 local and CCM24 semilocal ingredients, but no direct
source theorem proving that the transported prolate/Sonin defect is exactly
rank, pole, or endpoint-strip `Cdef`.

The imported exploration note `docs/ConnesWeilPositivity.md` contains the right
local targets for the next attack. It also contains status labels such as
`paper-closed` and `closed at route-paper level`. Those labels are not proof
evidence. They mark route-note confidence and must be replaced by theorem
statements, source citations, and referee-checkable proofs.

The current proof packages perform that replacement:

```text
docs/proofs/battle-1-test-quotient-proof-package.md
docs/proofs/rank-repair-finite-normal-form.md
docs/proofs/semilocal-q-compact-form.md
docs/proofs/fixed-s-no-defect-compact-form-read-off.md
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

```text
positive fixed-S trace
        |
        v
source trace operator identification
        |
        v
fixed-S support-square transport
        |
        v
CCM25 QW_lambda read-off
        |
        v
Cdef exhaustion
        |
        v
no-hidden-positive-defect equality
        |
        v
restricted-to-full QW bridge
        |
        v
triple-killed Weil positivity
```

## Evidence Boundary

| item | evidence | status |
|---|---|---|
| README states the key public spine as `Positive trace = QW_lambda` plus ledgers and `Cdef` | `README.md:69`, `README.md:160-172` | route claim to audit |
| README uses fixed-test exhaustion through `Cdef_(S_A,I,lambda,J)(g) -> 0` | `README.md:253` | route claim to audit |
| Manuscript states that Theorem 1 reads the positive trace as CCM-normalized `QW_lambda` plus ledgers | `docs/manuscripts/connes-weil-rh-proof-draft.md:1303-1306` | route claim to audit |
| Manuscript says the Lean formalization is not yet a full proof of RH | `docs/manuscripts/connes-weil-rh-proof-draft.md:1642-1643` | boundary statement |
| Exploration note starts from an unclosed route | `docs/ConnesWeilPositivity.md:20`, `docs/ConnesWeilPositivity.md:35-37` | caution |
| Exploration note later marks the fixed-S transport package as route-note closed | `docs/ConnesWeilPositivity.md:147192-147196`, `147258-147263` | proof sketch, not certificate |
| CC20 says the Weil distribution and Sonin trace differ by a prolate-spheroidal term that must be controlled | arXiv:2006.13771 abstract, https://arxiv.org/abs/2006.13771 | external warning |
| CCM25 says rigorous spectral convergence as `N, lambda -> infinity` would establish RH | arXiv:2511.22755 abstract, https://arxiv.org/abs/2511.22755 | external warning |

## Battle 1. Test And Quotient Compatibility

Target name:

```text
TestAndQuotientCompatibility(S,I,lambda)
```

Source in the exploration note:

```text
docs/ConnesWeilPositivity.md:143121-143132
```

Focused audit:

```text
docs/audits/battle-1-test-quotient-compatibility.md
```

The theorem must prove that the test used in the Connes trace formula and the
test used in the route are the same mathematical object after all convention
changes.

### Required Statement

For every admissible compactly supported test `g`, with

```text
F_g = g^* * g,
```

define the Connes source test `h` in the same half-density convention used by
CCM25. Then:

```text
Trace(R_Lambda U(h))
```

has CCM main term:

```text
QW_lambda(g,g),
```

and the quotient directions removed in the Connes source construction match
exactly the route's rank and pole ledgers.

### Proof Obligations

| obligation | what must be shown | current evidence |
|---|---|---|
| half-density conversion | `h` is the source-side test attached to `F_g`, with no hidden conjugation or Mellin-sign change | `docs/ConnesWeilPositivity.md:143102-143105` |
| quotient conversion | source quotient/radical directions are exactly the zero-mode and Tate pole channels | `docs/ConnesWeilPositivity.md:143106-143109` |
| ledger match | zero-mode goes to `Rank_(S,I)(g)` and Tate directions go to `PoleJetExtra_(S,I)(g)` | `docs/ConnesWeilPositivity.md:143124-143131` |
| failure check | a mismatch in `h/F_g` or in quotient/radical directions kills the route | `docs/ConnesWeilPositivity.md:143144-143150` |

### Acceptance Test

A proof of Battle 1 must give a displayed chain:

```text
g
  -> F_g = g^* * g
  -> h in Connes source convention
  -> Trace(R_Lambda U(h))
  -> QW_lambda(g,g) + rank/pole source channels
```

Every arrow must cite either a source formula or a project lemma. A proof that
only names `TestAndQuotientCompatibility` does not pass.

## Battle 2. Fixed-S Quantized Support-Square Transport

Target name:

```text
FixedSQuantizedSupportSquareTransport(S,I,lambda)
```

Source in the exploration note:

```text
docs/ConnesWeilPositivity.md:147051-147115
```

Focused audit:

```text
docs/audits/battle-2-fixed-s-support-square-transport.md
```

Proof package:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
```

This is the hardest direct bridge from the positive Hilbert trace to the
Weil-form read-off.

### Required Statement

In the canonical fixed-S model `V_S=M_S U_S`, prove that the theta-smoothed
support-square trace satisfies:

```text
Tr(theta_S(g)^*
   P_(S,G) P_hat_(S,G) P_(S,G)
   theta_S(g))

=

Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

+ Rank_(S,I)(g)
+ PoleJetExtra_(S,I)(g)
+ CdefRemainder_(S,I,lambda)(g),
```

with:

```text
|CdefRemainder_(S,I,lambda)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

### Proof Obligations

| obligation | what must be shown | current evidence |
|---|---|---|
| projection transport | fixed-S support and Fourier-support projections are the transported source projections | `docs/ConnesWeilPositivity.md:147119-147129` |
| phase pullback | `P_hat_(S,G)` is the pulled-back Fourier projection with phase `u_S` | `docs/ConnesWeilPositivity.md:147131-147140` |
| no-defect source identity | the archimedean identity `P P_hat P = -P(1/2)u_infty^(-1)d^-u_infty P` transfers only after tracking defects | `docs/ConnesWeilPositivity.md:147155-147170` |
| defect classification | every model-change mismatch contains an `M_S` or `M_S^*` commutator and enters `Cdef` | `docs/ConnesWeilPositivity.md:147178-147182` |
| trace legality | theta smoothing makes all trace moves ordinary trace-class or leaves them in the source regularized trace convention | `docs/ConnesWeilPositivity.md:147184-147187` |

### Rejection Criterion

The proof fails if it uses:

```text
same quantized-calculus expansion
```

as a substitute for showing that `V_S`, `M_S`, `M_S^*`, support projections,
Fourier projections, and theta smoothing preserve the trace identity modulo
only rank, pole, and endpoint-strip `Cdef` terms.

## Battle 3. Cdef Norm And Fixed-Test Exhaustion

Target names:

```text
CdefNormFormula(S,I,lambda,J)
CdefConsistencyAudit(S,I,lambda,J)
FixedTestCdefExhaustion(S_A,I,g)
```

Source in the exploration note:

```text
docs/ConnesWeilPositivity.md:146790-146918
```

Proof package:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
```

Focused audit:

```text
docs/audits/battle-3-cdef-exhaustion.md
```

This battle must turn the endpoint-strip remainder into a normed quantity with
a proved limit for fixed `g` and fixed finite prime set `S_A`.

### Required Definition

For fixed finite `S`, support interval `I`, cutoff `lambda`, and graph order
`J`, define:

```text
Cdef_(S,I,lambda,J)(g)
  :=
sum_(alpha in R_(S,I,lambda,J))
  || theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^* ||_1

+

sum_(beta in Q R_(S,I,lambda,J))
  |BoundaryStripTrace_beta(g)|.
```

Here every `alpha` is an endpoint-strip normal-form term and every
`BoundaryStripTrace_beta` still contains at least one endpoint-strip factor
before boundary evaluation.

### Required Estimate

Prove:

```text
Cdef_(S,I,lambda,J)(g)
  <=
C'_(S,I,J)(g) Cdef_graph_(S,I,lambda,J')(g),
```

then prove:

```text
Cdef_graph_(S_A,I,lambda,J')(g) -> 0
```

for fixed `g`, fixed `I`, and fixed `S_A`. Since `C'_(S_A,I,J)(g)` is fixed in
that limit, this gives:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

### Proof Obligations

| obligation | what must be shown | current evidence |
|---|---|---|
| finite endpoint-strip normal form | commutator defects expand into finitely many strip terms for fixed `S,I,J` | `docs/ConnesWeilPositivity.md:146802-146816` |
| trace-norm control | every endpoint-strip term is trace-class with the displayed norm bound | `docs/ConnesWeilPositivity.md:146821-146842` |
| `Q` stability | applying `Q` keeps a strip factor before every boundary evaluation | `docs/ConnesWeilPositivity.md:146831-146834` |
| graph/prolate comparison | trace-norm `Cdef` is bounded by fixed constant times graph/prolate `Cdef_graph` | `docs/ConnesWeilPositivity.md:146836-146842` |
| fixed-test exhaustion | graph/prolate `Cdef_graph` tends to zero with `g` and `S_A` fixed | `docs/ConnesWeilPositivity.md:146893-146903` |

## Three-Battle Completion Gate

The three battles count as passed only when the manuscript contains:

| gate | required artifact |
|---|---|
| Battle 1 | a proof of `TestAndQuotientCompatibility` with explicit half-density and quotient/radical maps |
| Battle 2 | a proof of `FixedSQuantizedSupportSquareTransport` that expands every model-change mismatch into rank, pole, or endpoint-strip `Cdef` |
| Battle 3 | a normed `Cdef` definition, a trace-norm estimate, and a fixed-test exhaustion proof |
| Lean audit | symbolic `Prop` bridges replaced or refined so the final route cannot accept arbitrary proof fields for the three battle targets |
| source audit | every external theorem used in the three battles cited by arXiv identifier, formula number, or source line |

The three mathematical battle gates now pass at route-evidence level. The
correct public status remains:

```text
source-conditional route manuscript,
not a Clay/journal/Lean proof certificate.
```
