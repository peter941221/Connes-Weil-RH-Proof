# Connes-Weil RH Proof

This repository contains a source-conditional Connes-Weil route to the Riemann
Hypothesis.

The main manuscript is:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md
```

Current status:

```text
route-evidence composition: closed
accepted-source certification: open
Lean proof status: open
external certification: open
public proof status: source-conditional
```

This repository does not claim journal acceptance, Clay acceptance, community
acceptance, or completed Lean verification. It presents a route whose outside
analytic inputs stay explicit.

## Primary Sources

| source | arXiv | role in the route |
|---|---|---|
| Connes--Consani--Moscovici 2024 | https://arxiv.org/abs/2310.18423 | fixed-`S` semilocal Hilbert model, support transport, Fourier compatibility, Sonin comparison |
| Connes--Consani--Moscovici 2025 | https://arxiv.org/abs/2511.22755 | Weil form `QW`, restricted form `QW_lambda`, pole and finite-prime normalizations |
| Connes--Consani 2020 | https://arxiv.org/abs/2006.13771 | archimedean support-square trace, trace-class legality, Mellin convention, finite-vanishing RH criterion |

The source-line map lives in:

```text
docs/audits/source-reread-v0.2.md
```

The external-review checklist lives in:

```text
docs/audits/accepted-source-certification-audit.md
```

## Conditional Claim

Assume the cited CCM24, CCM25, and CC20 source inputs in the normalizations
recorded by the manuscript and audits. Then the fixed-`S` Connes-Weil positive
compression route gives the Riemann Hypothesis.

The proof does not import RH as an assumption. It imports source theorem
interfaces and uses project proof packages to connect one fixed test object
through the trace, Weil-form, and RH-exit layers.

## Proof Spine

```text
  One compact test g
        |
        v
  F_g = g^* * g
        |
        v
  +--------------------------------------------------+
  | CCM24 fixed-S coordinate                         |
  | V_S = M_S U_S                                    |
  | one support window, one Fourier window           |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | CC20 trace legality                              |
  | Hilbert-Schmidt -> trace-class -> cyclicity      |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Positive fixed-S trace                           |
  | Tr(A_(S,lambda,g)^* A_(S,lambda,g)) >= 0         |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Source read-off                                  |
  | positive trace = QW_lambda(g,g)                  |
  |                  + rank ledger                   |
  |                  + pole ledger                   |
  |                  + endpoint-strip Cdef remainder |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Triple vanishing                                 |
  | hat g(0)=hat g(i/2)=hat g(-i/2)=0                |
  | kills rank and pole ledgers                      |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Fixed-test exhaustion                            |
  | Cdef(lambda,g) -> 0                              |
  | QW_lambda(g,g) = QW(g,g) for fixed g             |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Final sign bridge                                |
  | QW(g,g) = - sum_v W_v(F_g)                       |
  | QW(g,g) >= 0 -> sum_v W_v(F_g) <= 0              |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | CC20 Proposition C.1                             |
  | finite vanishing set F={0,1/2,1}                 |
  +--------------------------------------------------+
        |
        v
  Mathlib-style Riemann Hypothesis target
```

## Core Objects

Fix a finite set `S` of places containing the archimedean place. CCM24 supplies
the semilocal transform:

```text
V_S = M_S U_S.
```

For `lambda > 1`, the route uses the transported projection:

```text
P_(S,G)(lambda) = V_S P_S(lambda) V_S^(-1).
```

For a compactly supported test function `g`, set:

```text
F_g = g^* * g.
```

The route uses only admissible tuples:

```text
supp(g) subset I,
I subset [lambda^(-1), lambda],
S contains every finite prime visible to F_g.
```

This condition keeps the positive trace, the restricted Weil form, and the
endpoint-strip exhaustion on the same test object.

## Positive Trace And Read-Off

The positive operator is:

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

After the Hilbert-Schmidt and trace-class gates:

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
  >= 0.
```

The route then proves the read-off:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda)(g),

|R_(S,I,lambda)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The sign/defect bridge is the main project-owned obstruction. It now has a
referee-facing proof chain:

```text
Rows 1-2:
  CC20 source remainder object, sign orientation, and post-Q image.

Rows 3-7:
  fixed-S post-Q transport,
  projection-defect split,
  rank/pole identification,
  endpoint-strip Cdef domination,
  no hidden positive defect.
```

Relevant files:

```text
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
docs/audits/sign-defect-blocker-audit.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
```

## Killing The Ledgers

The route imposes:

```text
hat g(0) = hat g(+i/2) = hat g(-i/2) = 0.
```

Then:

```text
Rank_(S,I)(g) = 0,
PoleJetExtra_(S,I)(g) = 0.
```

The positive trace identity gives:

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The proof sends `lambda` to infinity while keeping `g`, `I`, and the finite
prime visibility set fixed. The finite-prime support stabilizes because `F_g`
has compact support, and:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

The fixed-test bridge then gives:

```text
QW(g,g) >= 0.
```

This step does not import finite-operator spectral convergence or determinant
convergence. It uses the CCM25 restriction definition for the same fixed test
object.

Relevant files:

```text
docs/audits/restricted-to-full-qw-source-readiness-audit.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

## Final Sign And RH Exit

CCM25 uses:

```text
QW(f,g) = Psi(f^* * g).
```

The final sign bridge proves at route-evidence level:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Therefore:

```text
QW(g,g) >= 0
        |
        v
sum_v W_v(F_g) <= 0.
```

That is the inequality direction needed for CC20 Proposition C.1.

The final finite vanishing set is:

```text
F = {0, 1/2, 1}.
```

The triple vanishing above matches this set under the CC20 Mellin convention:

```text
s = 1/2 - i t

t = 0     -> s = 1/2
t = +i/2  -> s = 1
t = -i/2  -> s = 0
```

The route also records the bridge from the CC20 source RH conclusion to
Mathlib's `_root_.RiemannHypothesis`, including zeta equality, zero transport,
negative-even exclusion, pole exclusion, and the critical-line equation
`s.re = 1/2`.

Relevant files:

```text
docs/proofs/final-sign-bridge-proof-package.md
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
docs/proofs/rh-definition-bridge-proof-package.md
docs/proofs/source-conditional-rh-route-closure-proof-package.md
```

## External Review Targets

The useful external review is row-by-row. The main questions are:

| row | question |
|---|---|
| CCM24 fixed-S model | Do the CCM24 source hypotheses give the exact `V_S`, support window, Fourier window, bounded comparison, and Sonin comparison used here? |
| CCM25 Weil objects | Do `QW`, `Psi`, `QW_lambda`, pole terms, finite-prime terms, and signs match the route test object? |
| CC20 trace legality | Do the Hilbert-Schmidt, trace-class, cyclicity, Mellin, and sign conventions apply to this transported source object? |
| sign/defect bridge | Does the Rows 1-7 proof chain classify every CC20 post-`Q` remainder term as killed rank/pole ledger or endpoint-strip `Cdef`? |
| restricted-to-full bridge | Does fixed-test `QW_lambda(g,g)=QW(g,g)` follow from restriction-definition and support stabilization, without spectral convergence? |
| final sign bridge | Does `QW(g,g)=-sum_v W_v(F_g)` have the right sign for CC20 Proposition C.1? |
| RH definition bridge | Does the CC20 source conclusion match Mathlib's canonical RH predicate? |

Use this checklist:

```text
docs/audits/accepted-source-certification-audit.md
```

## Lean Status

The repository has a segmented Lean scaffold:

```text
ConnesWeilRH.lean
ConnesWeilRH/
lakefile.toml
lean-toolchain
```

Current route target:

```text
lake build ConnesWeilRH
```

The Lean scaffold separates source theorem interfaces from project-owned route
lemmas. It remains source-conditional until the CCM24, CCM25, and CC20 source
interfaces are replaced by formal source-paper proofs or accepted imported
theorems.

Before treating any Lean theorem as a proof artifact, run:

```text
#print axioms <theorem_name>
```

The remaining axioms must be exactly the approved source interfaces plus
Mathlib/kernel foundations.

## Repository Layout

```text
docs/
  audits/
    accepted-source-certification-audit.md
    source-reread-v0.2.md
    source-import-legitimacy-audit.md
    sign-defect-blocker-audit.md
  manuscripts/
    connes-weil-rh-proof-draft.md
  proofs/
    source-conditional-rh-route-closure-proof-package.md
    cc20-source-remainder-rows1-2-referee-discharge.md
    sonin-prolate-defect-referee-discharge.md

ConnesWeilRH/
  Segmented Lean route scaffold.

formalization/
  Lean readiness and interface planning notes.
```

## Verification

For manuscript and audit hygiene:

```text
git diff --check
rg -n "task-marker|fix-marker|proof-sketch|named-gap" docs
rg -n "[^\x00-\x7F]" docs
```

For Lean route work, build the segmented target from the Linux-side Lean
worktree:

```text
lake build ConnesWeilRH
```

The current repository state is ready for outside mathematical review as
source-conditional route evidence. It is not yet an accepted-source or Lean
certificate.
