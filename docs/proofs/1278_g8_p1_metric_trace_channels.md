# 1278 — G8 P1 ordinary-trace metric channel ledger

Date: 2026-09-10.

Status: FORMAL Lean fact. This record supplies no finite-prime equality, limit,
sign, `qw` readback, or RH claim.

Using the four-channel operator identity of record 1276 and the channel-local
Hilbert--Schmidt owners of record 1277, Lean now proves on the same source
basis the scalar identity

```text
Tr(C_n^* E^* W_g E C_n)
 = Tr(SS_n) + Tr(SB_n) + Tr(BS_n) + Tr(BB_n).
```

The result is an exact finite-cutoff ordinary-trace ledger. It is the legal
entry point for a future aggregate Euler comparison and keeps the cutoff,
owner, scale, detector, and family in every summand. No channel is identified
with the finite prime-power scalar yet.

Verification: `1278_g8_p1_metric_trace_channels.log`, green owning/Audit build
(3925 jobs), zero `error:`/`sorryAx`, standard three axioms only.
