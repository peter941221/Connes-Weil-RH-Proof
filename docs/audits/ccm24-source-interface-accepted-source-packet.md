# CCM24 Source-Interface Accepted-Source Packet

Date: 2026-06-28

Status:

```text
CCM24 accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the CCM24 source-interface theorem candidates used by the
route before the positive trace, `QW_lambda` read-off, and endpoint-strip `Cdef`
exhaustion meet.

The packet fixes one source-backed semilocal model:

```text
S                 finite place set
I                 source support window
g                 common source test
F_g = g^* * g     common convolution square
V_S = M_S U_S     common fixed-S coordinate
```

The route may not change these objects between support transport, trace
read-off, and `Cdef` exhaustion.

## Source Anchors

| source | anchors | role |
|---|---|---|
| canonical fixed-S model | `mainc2m24fine.tex:237-253,786-804` | `U_S`, `M_S`, `V_S=M_S U_S`, and Fourier grading |
| support transport | `mainc2m24fine.tex:761-771` | support movement through the semilocal transform |
| bounded comparison | `mainc2m24fine.tex:806-823` | bounded comparison map and inverse |
| non-automatic transport warning | `mainc2m24fine.tex:846-852` | warning that multiplication and derivative structures do not commute by default |
| Fourier support transport | `mainc2m24fine.tex:983-1003` | Fourier-side support window |
| Sonin comparison | `mainc2m24fine.tex:1050-1060` | fixed-window Sonin comparison used by exhaustion |

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| fixed-S model | `CCM24FixedSModelTheorem(S)` | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | confirm the Hilbert model, `U_S`, `M_S`, `V_S`, and grading use the same finite set `S` |
| support window | `CCM24WindowTransportTheorem(S,I,g)` | `docs/proofs/ccm24-support-window-transport-discharge.md` | confirm source support, Fourier support, and convolution-square support move through one window `I` |
| bounded comparison | `CCM24BoundedComparisonTheorem(S)` | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | confirm the comparison map preserves the operator class needed for trace and `Cdef` estimates |
| fixed-window Sonin comparison | `CCM24FixedWindowSoninComparison(S,I,g)` | `docs/proofs/ccm24-support-window-transport-discharge.md` | confirm the Sonin comparison keeps `S`, `I`, `g`, and the graph/order budget fixed |
| no automatic post-`Q` transport | `CCM24NoAutomaticPostQTransport` | `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` | confirm derivative, boundary, and tail transport need the separate Row 3 packet |

## Rejection Conditions

A reviewer should reject this source-interface row if one of these conditions
occurs:

```text
1. the trace read-off and Cdef exhaustion use different fixed-S models;
2. support and Fourier support use different windows;
3. the comparison map does not preserve the trace or graph class used later;
4. Sonin comparison changes the source test or finite place set;
5. a proof treats post-Q derivative, boundary, or tail transport as automatic.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make CCM24 accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of the model, support, comparison, and Sonin hypotheses |
| Did this pass touch Lean? | no |

The CCM24 packet now gives reviewers a single place to certify the fixed-S
model before checking trace-scale, sign/defect, and restricted-to-full packets.
