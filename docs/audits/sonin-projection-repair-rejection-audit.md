# Sonin Projection Repair Rejection Audit

Date: 2026-06-28

Status:

```text
B2 repair path: rejected for the current route
current positive trace definition: unchanged
Lean status: not started
```

## Question

The first external opinion raised a natural repair attempt for B1:

```text
replace the positive trace

  Tr((P_hat P theta_S(g))^* (P_hat P theta_S(g)))

by a Sonin-projection trace such as

  Tr(S_lambda theta_S(F_g)).
```

The proposed repair aims to avoid possible ordinary-trace scale growth. The
same opinion warns that the Sonin projection can trivialize in the
`lambda -> infinity` limit and force a false conclusion such as
`QW(g,g)=0`.

## Verdict

The repair path is rejected for this route.

The current route keeps the positive scalar:

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g),

PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g)).
```

Evidence:

```text
README.md:237-251
docs/manuscripts/connes-weil-rh-proof-draft.md:648-659
docs/manuscripts/connes-weil-rh-proof-draft.md:951-963
docs/proofs/trace-scale-compatibility-proof-package.md:114-151
```

The route uses Sonin comparison only as part of fixed-window transport and
defect analysis. It does not define the positive trace by replacing `A^*A`
with `S_lambda theta_S(F_g)`.

## Why The Repair Is Invalid As A Shortcut

The current route needs a positive scalar and a read-off scalar on the same
scale:

```text
positive scalar
        |
        v
QW_lambda(g,g) + rank + pole + Cdef
```

A Sonin-projection replacement would have to prove the same contract:

```text
TraceScaleCompatibilityContract(S,I,lambda,g,F_g,J).
```

Without that contract, the repair only moves the B1 problem:

```text
ordinary-trace scale mismatch
        |
        v
Sonin-trace scale mismatch or trivial limit
```

If the Sonin projection tends strongly to zero in the chosen exhaustion, the
positive scalar tends to zero for bounded test data. Then a read-off of the
form:

```text
SoninTrace_lambda(g)
  =
QW_lambda(g,g) + o(1)
```

would force:

```text
QW(g,g)=0
```

for all triple-vanishing tests. The Weil quadratic form is not expected to
vanish identically on that class. Such a repair would therefore need a new
normalization, a new finite-part theorem, or a new nontrivial read-off
identity. None is part of the current route.

## Current Route Use Of Sonin Objects

| Sonin-related object | route role | not allowed as |
|---|---|---|
| CCM24 fixed-window Sonin comparison | transports fixed source windows and supports Cdef exhaustion | a replacement definition for positive trace |
| CC20 Sonin/prolate remainder | source defect object that must be classified | a harmless error by name |
| `CC20PostQRemainderFixedSSoninTransport` | moves the source post-`Q` remainder into the same fixed-S coordinate | automatic proof that all defects vanish |
| `SoninProlateDefectEqualsEndpointStripCdef` | theorem target for rank/pole/Cdef classification | a shortcut around trace-scale compatibility |

Evidence:

```text
docs/proofs/ccm24-support-window-transport-discharge.md
docs/audits/sonin-prolate-defect-source-readiness-audit.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
```

## Acceptance Rule For Any Future Replacement

Any future proposal that replaces the current positive trace must prove all of
the following before it can enter the route:

| requirement | reason |
|---|---|
| ordinary or normalized scalar definition | the proof must say which trace notion supplies positivity |
| positivity after normalization | finite-part subtraction may destroy `Tr(A^*A) >= 0` |
| same-scale read-off | the replacement scalar must equal `QW_lambda + ledgers + Cdef` at finite `lambda` |
| nontrivial limit | the replacement scalar must not force `QW(g,g)=0` for all tests |
| compatibility with B3/B4 | the replacement must still classify defects and return to the same global `QW(g,g)` |

The current repository supplies this same-scale route for the existing
ordinary positive trace at project proof-package level:

```text
docs/proofs/trace-scale-compatibility-proof-package.md
```

It supplies no equivalent theorem for a replacement Sonin-projection trace.

## Current Decision

| question | answer |
|---|---|
| Does B2 show a direct flaw in the current positive trace definition? | no |
| Does B2 block a proposed shortcut repair? | yes |
| Does the current route replace `A^*A` by `S_lambda theta_S(F_g)`? | no |
| What must happen if someone proposes that replacement later? | prove a new trace-scale compatibility theorem first |

B2 is closed as a rejected repair path. The next external-opinion target is
B3: semilocal fourth-defect risk.
