# CCM24 Source-Interface Referee Decision Record

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
  docs/audits/ccm24-source-interface-accepted-source-packet.md

row group:
  CCM24 fixed-S source interface

theorem candidates:
  CCM24FixedSModelTheorem(S)
  CCM24WindowTransportTheorem(S,I,g)
  CCM24BoundedComparisonTheorem(S)
  CCM24FixedWindowSoninComparison(S,I,g)
  CCM24NoAutomaticPostQTransport

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem Bundle To Decide

The reviewer must decide whether CCM24 supplies the exact fixed-S source
interface used by the route:

```text
one finite place set S,
one source support window I,
one common source test g,
one convolution square F_g = g^* * g,
one semilocal coordinate V_S = M_S U_S,
one support and Fourier-support transport chain,
one bounded comparison map preserving the later operator class,
one fixed-window Sonin comparison for the same S, I, and g.
```

The reviewer must also confirm the negative boundary:

```text
CCM24 does not automatically transport CC20 post-Q derivative,
boundary, or series-tail terms into the route fixed-S coordinate.
```

Those post-Q terms remain governed by the sign/defect packet.

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/ccm24-source-interface-accepted-source-packet.md` | primary packet |
| `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | fixed-S model and bounded comparison project package |
| `docs/proofs/ccm24-support-window-transport-discharge.md` | support/window and Sonin comparison project package |
| `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` | non-automatic post-Q transport audit |
| `docs/audits/source-reread-v0.2.md` | source-line map |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| fixed-S Hilbert model uses one finite set `S` | source-interface packet, fixed-S model row | pending |
| `U_S`, `M_S`, and `V_S=M_S U_S` match the route coordinate | semilocal object package | pending |
| support and Fourier support stay in one source window `I` | support-window package | pending |
| convolution support for `F_g=g^* * g` uses the same test `g` | source-test and support-window packages | pending |
| bounded comparison preserves the operator class used by trace and `Cdef` estimates | semilocal object package | pending |
| Sonin comparison keeps `S`, `I`, and `g` fixed | support-window package | pending |
| no post-Q derivative, boundary, or tail term is treated as automatic CCM24 transport | post-Q obstruction audit | pending |

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
  not applicable at this row except transport orientation

accepted limit order:
  pending

non-importable shortcuts checked:
  pending

remaining caveats:
  pending
```

## Rejection Names

If the reviewer rejects the CCM24 source-interface row, use the most precise
obstruction name:

```text
FixedSModelMismatch(S)
SupportWindowDrift(S,I,g)
FourierWindowDrift(S,I,g)
BoundedComparisonClassMismatch(S)
SoninComparisonObjectDrift(S,I,g)
AutomaticPostQTransportImport(S,I,g)
```

## Current Judgment

| question | answer |
|---|---|
| Has the CCM24 source-interface row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the CCM24 source-interface decision. It does not decide it.
