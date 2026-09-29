# 2211 — Transcendental forward-error allowance price

Date: 2026-09-29

This probe prices the exponent-evaluation allowance on the correction binding
row (node 2) at the full-owner `NSEG=1100` rule. It uses the project AMP
pattern for a rounded exponent argument, `8u |z| a`, together with the
`16u` term-operation allowance, applied to the absolute GL and Simpson term
sums. The vector-level GL-minus-S cancellation is retained in the value term.

```text
exponent-argument smear             2.4377393e-8
exp/term operation                  2.1685483e-10
total transcendental allowance      2.4594248e-8
```

Together with the 2209 vector bound and 2210 rounding allowance, the combined
correction price is `6.2550323e-5`. The transcendental allowance is only about
`0.04%` of that total; Simpson's fourth-order remainder remains binding.

Status: `TRANSCENDENTAL-ALLOWANCE-PRICED / OUTWARD-LEMMA-OPEN`.

The AMP calculation is a forward-error price, not yet a formal interval proof
of the transcendental library calls. Complete-owner transfer and the producer
gate remain open. No RH claim follows.

