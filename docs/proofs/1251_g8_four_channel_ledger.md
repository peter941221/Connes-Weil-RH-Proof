# Proof 1251 — the G8 finite-window four-channel ledger

Status: FORMAL-FOUR-CHANNEL-LEDGER (Lean), 2026-09-10.

On the same source owner and with the existing test-owned cutoff factor, the
G8 trace product is now split exactly into four concrete operators:

```text
T_G8 = T_base + T_cross + T_adjointCross + T_leakage.
```

Each term keeps the source inclusion, cutoff factor, detector, and oblique
shear in its literal order.  The identity is obtained by expanding
`(I + N_S^*)^* W_g (I + N_S^*)` before taking any trace; no cyclic trace move,
external subtraction, or owner change is used.  The basis-independent channel
operators are separate from the basis data, so the ledger can later receive
channel-specific trace/readback lemmas without duplicating the carrier.

This closes the structural finite-window ledger only.  It does not identify
any channel trace with `qw`, prove the L4 projection-limit contract, or prove
the A4 finite-visible-prime sign inequality.

Audit evidence: `/home/peter/rh/build-logs/1251_g8_four_channel_ledger_retry8.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
