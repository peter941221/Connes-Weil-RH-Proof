# Trace Scale Compatibility Audit

Date: 2026-06-28

Status:

```text
B1 project proof-package coverage: closed
Lean status: not started
public proof status: not upgraded
```

## Question

This audit checks the first external-review blocker:

```text
Does the ordinary positive trace

  Tr(A_(S,lambda,g)^* A_(S,lambda,g))

have the same scalar normalization and lambda-asymptotic scale as the
restricted CCM read-off

  QW_lambda(g,g) + Rank_(S,I)(g) + PoleJetExtra_(S,I)(g)
    + R_(S,I,lambda)(g),

with no missing divergent bulk term and no hidden finite-part subtraction?
```

This is a separate question from trace-class legality. A proof can define the
ordinary trace and justify cyclic moves without yet proving that the ordinary
positive trace, the support-square trace, the no-defect source trace, and the
CCM25 restricted quadratic form all represent the same finite-lambda scalar at
the same scale.

## Current Judgment

The current repository now discharges trace-scale compatibility at project
proof-package level.

The route has documents for trace legality and for the positive-trace read-off.
Those documents name the right chain:

```text
ordinary positive trace
  -> support-square trace
  -> no-defect source trace
  -> CCM25 QW_lambda read-off.
```

They do not yet supply a standalone theorem that rules out the scale mismatch
raised by the external critique:

```text
ordinary positive trace grows with lambda
        |
        v
finite-part or no-defect read-off stays bounded after ledger killing
```

The proof package does not give accepted-source, referee, or Lean
certification. It records a route-evidence answer: within the current fixed-S
calculus, every term outside `QW_lambda` is named as rank, pole, or
endpoint-strip `Cdef`.

## Evidence From The Repository

| object | repository evidence | current meaning | B1 risk |
|---|---|---|---|
| `PositiveTrace^G_(S,lambda)(g)` | `README.md:237-251` defines `A_(S,lambda,g)=P_hat P theta_S(g)` and `PositiveTrace=Tr(A^*A)>=0`. `docs/manuscripts/connes-weil-rh-proof-draft.md:648-659` says `A` is Hilbert-Schmidt and `A^*A` is trace-class. | Ordinary trace-class positive trace. | The documents justify existence and nonnegativity, but they do not state the lambda-asymptotic size of this trace. |
| support-square trace | `docs/manuscripts/connes-weil-rh-proof-draft.md:675-677` rewrites positive trace as `Tr(theta_S(g)^* P P_hat P theta_S(g))`. | Ordinary trace after cyclic legality. | The route needs this equality to preserve the scalar normalization, not only trace-class legality. |
| support-square-to-defect split | `docs/manuscripts/connes-weil-rh-proof-draft.md:680-710` splits `P P_hat P` into a quantized differential main term, no-strip boundary terms, and projection-order defects. | Route decomposition before CCM read-off. | The split must account for every lambda-scale contribution. A missing bulk term would invalidate the later `Cdef -> 0` use. |
| no-defect source trace | `docs/manuscripts/connes-weil-rh-proof-draft.md:720-724` keeps the archimedean no-defect summand under the Connes--Consani regularized trace convention. | Source convention for the no-defect summand. | The route must prove that any regularized or finite-part convention matches the ordinary positive trace after all named ledgers and remainders are extracted. |
| `QW_lambda(g,g)` | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002` displays the restricted CCM25 formula. `docs/manuscripts/connes-weil-rh-proof-draft.md:1027-1033` asserts the no-defect trace equals `QW_lambda(g,g)`. | Restricted Weil quadratic form after source read-off. | The equality must include the same scalar normalization and cutoff convention as the positive trace. |
| read-off equality | `README.md:282-297` states `PositiveTrace = QW_lambda + Rank + PoleJetExtra + R` and `|R| <= C Cdef`. | Main finite-lambda route identity. | B1 asks whether this identity still holds after checking trace scale, finite-part subtraction, and ordinary-vs-regularized trace conventions. |
| fixed-test limit | `README.md:369-382` requires `Cdef -> 0` and then `QW_lambda(g,g)=QW(g,g)` for large lambda. | Final passage from restricted to full scalar for fixed `g`. | If the positive trace has a divergent bulk not present in `QW_lambda + ledgers + Cdef`, then `R` cannot tend to zero. |
| existing trace contract | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:351-372` requires exact operator, Hilbert-Schmidt gate, trace-class square, cyclic ledger, support-square formula, no-defect trace, and bounded comparison. | Import target for trace legality and read-off order. | The checklist does not yet include an explicit trace-scale/asymptotic compatibility row. |

## Why Trace Legality Is Not Enough

Trace legality proves that a trace expression is meaningful:

```text
operator identity
  -> Hilbert-Schmidt gate
  -> trace-class square
  -> legal cyclic moves
```

B1 asks for a stronger statement:

```text
ordinary trace scalar
  =
source no-defect scalar
  +
all named ledgers
  +
endpoint-strip Cdef remainder

and every term has the displayed lambda-scale.
```

The difference matters because the route later kills the ledgers and sends
`Cdef` to zero. That limit step only works if no divergent ordinary-trace
component has been hidden inside a regularized convention or dropped as a
finite-part subtraction.

## Required Discharge

A future proof package or accepted source import should add a theorem with this
shape:

```text
TraceScaleCompatibility(S,I,lambda,g):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    + Rank_(S,I)(g)
    + PoleJetExtra_(S,I)(g)
    + R_(S,I,lambda)(g)

and:

  R_(S,I,lambda)(g)
    is exactly the endpoint-strip Cdef-controlled remainder,

  no additional bulk finite-part subtraction is used,

  every ordinary-vs-regularized trace conversion occurs in the named source
  no-defect summand or in one of the named ledgers.
```

The theorem must also record one of the following lambda-scale outcomes:

| outcome | meaning |
|---|---|
| bounded positive trace | prove the ordinary positive trace stays on the same scale as `QW_lambda + ledgers + Cdef` for fixed `g` |
| exact cancellation | identify the divergent part and prove it cancels inside named ledgers or the no-defect source convention before the `Cdef -> 0` limit |
| accepted finite-part identity | cite a source theorem that states the ordinary positive trace read-off equals the finite-part CCM scalar with the same normalizations |

Without one of these outcomes, the route cannot use nonnegativity of
`PositiveTrace` to conclude `QW(g,g) >= 0`.

The theorem target is now stated in:

```text
docs/proofs/trace-scale-compatibility-theorem-contract.md
```

The project proof package is:

```text
docs/proofs/trace-scale-compatibility-proof-package.md
```

The first discharge attempt is recorded in:

```text
docs/audits/trace-scale-compatibility-discharge-attempt.md
```

## Next Attack

The next mathematical step should be narrow:

```text
PositiveTrace scale audit
        |
        v
support-square trace normalization
        |
        v
no-defect source trace convention
        |
        v
CCM25 QW_lambda scalar read-off
```

The next pass should attack B2, the Sonin-projection repair direction, then B3,
the semilocal fourth-defect issue.
