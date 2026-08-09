# 918 (A-lane, verdict) — Mellin carrier free-standing certificate probe, axiom-clean

Status: **probe build-verified**.  `MellinCertificateProbe.lean` builds 2950 green;
`mellin_squareLaw` and `vonMangoldt_two_pos` depend only on
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no new `axiom`.

## What this is

A-lane L657's skeleton slot (`CommonFinitePrimeArithmeticSourceData W`) is typed
against `W : WeilFormSymbols`, whose every function field sits on
`TestFunction` (Schwartz).  The genuine Mellin carrier
(`MellinProductCarrier.Test = ℝ → ℂ`, log-coordinate) cannot fill that slot
without a total `LegacyTestEquiv.decode` into `TestFunction` — the noted wall in
`docs/proofs/setup/design-parallel-source-model-consensus.md`.

Per final-route decision (`free-standing Mellin certificate`), this probe records
the two honest facts the Mellin route actually owns:

1. **`mellin_squareLaw`**: `Mellin(f ⋆ f) = Mellin f · Mellin f` — a corollary of
   the already-proved axiom-clean `MellinProductCarrier.mellinConvolutionProductLaw`
   (backed by `MellinConvolutionIdentity.mellin_log_convolution_product`).
   This is the multiplicative core a genuine finite-prime certificate needs, and
   it is real on the Mellin carrier.
2. **`vonMangoldt_two_pos`**: `Λ(2) = log 2 > 0`, the per-prime weight seed.

## Why this is not "filling L657"

`WeilFormSymbols` pins every arithmetic field to `TestFunction`; the Mellin
carrier is a different space.  Making the Mellin carrier feed L657 requires the
`decode` total map the consensus doc already marks dead.  So the Mellin route
closes as a **parallel, free-standing certificate lattice**, demonstrated on the
log-carrier, without claiming the skeleton's ADB slot.

## Honest scope

This is a small, build-verified first step of the free-standing Mellin chain,
parallel to what `ConcreteP1SupportProbe` did for the concrete carrier.  It does
*not* reduce the skeleton's 4️⃣ axiom count.  RH still not claimed.

## Next real increment

1. Build the per-point `valueAt`/`finitePrimeTerm` structure on the Mellin
   carrier (mirroring the concrete carrier's), so a full certificate record
   (exact index set `{2}`) exists on ℓ Mellin — the honest parallel of
   `ConcreteP1SupportProbe`.
2. Or pivot the remaining skeleton roots through the Hilbert closed route
   (916/917) which already carries an axiom-clean closed gate.