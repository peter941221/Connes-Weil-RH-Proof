# G8 P1 diagonal channel positivity

Date: 2026-09-11.

The import-facing leaf `C1G8P1DiagonalChannelPositivity` proves that every
same-leg literal metric channel has the form `C† W C`, with the fixed
detector `W` in the middle, and is therefore positive on the same
`CompactLog` owner. Thus the two diagonal terms in the four-channel ledger
are formally positive; only the mixed channels can carry a sign.

This is a FORMAL P1 positivity consumer, not a finite-prime readback or a
detector-weighted cancellation theorem. Metric-to-radial transport, finite
metric trace equality, P2 remainder/sign, and P3 remain open.

Evidence: `1486_g8_p1_diagonal_channel_positivity.log`, owning and audit
targets green (3926 jobs), zero `error:`/`sorryAx`; the audited declaration
uses exactly `[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
