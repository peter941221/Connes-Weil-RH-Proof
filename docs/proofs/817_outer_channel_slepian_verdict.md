# Proof-717 / Gate-3U: the hard bone — outer channel survives the EXACT prolate (Slepian) carrier

Date: 2026-08-06
Status: new-math verdict — the last escape in 816 is numerically closed.  The
outer channel `(I−R)∘D` does **not** vanish on the *exact* prolate/Slepian
carrier, and its leakage does not decay as the Slepian band narrows.  Combined
with 815/816, all tested carriers now show a non-decaying outer leak; the gate
stays open only for the genuinely-arithmetic finite-S structure.
Branch: `proof/gate3u-completed-readout`
RELATED: `815_rh_route_conditional_boundary.md`, `816_outer_channel_nonzero_numeric.md`

## 1. Why this probe exists (the honest gap 816 left open)

816 pushed Gate-3U's outer channel `(I−R)∘D` on broad and band-limited carriers,
all non-zero.  Its explicit caveat was that those band-limited functions were
*smooth-bump / Gaussian-windowed-sinc* — **approximate** prolate functions, not
the exact prolate spheroidal wave functions that would generate the true Sonin
space.  The remaining hope was:

```
D |_{sourceSoninCarrier} ⊆ range(R)   ⟺   (I−R)∘D·u = 0 on the true prolate carrier
```

This probe removes that caveat by putting the **actual Slepian sequences**
(discrete prolate spheroidal sequences, `scipy.signal.windows.dpss`) on the
carrier — the genuine maximal-concentration band-limited functions — and asks
whether `(I−R)∘D` cancels on them.

## 2. First, a Lean grounding: what "the prolate carrier" even is in this repo

Before trusting any Slepian number, the target subspace must be pinned. The
repo does **not** define explicit prolate spheroidal wave functions. The whole
"prolate trace reduction" is an *abstract operator construction*
(`Source/CC20Concrete/ProlateTraceReduction.lean`):

```
supportComplementProjection U = cc20PositiveHalfLineProjection
                                  − cc20TransportedSoninProjection U
prolateFactor U      = cc20TransportedHalfLineProjection U ∘L supportComplementProjection U
cc20TransportedSoninClosedSubspace U =
    cc20PositiveHalfLineClosedRange ⊓ cc20TransportedHalfLineClosedRange U
```

and `cc20PositiveHalfLine = Set.Ici 0` is a **spatial / log half-line**
(`GlobalLogSoninProjection.lean:26,153-163`).  So the Sonin carrier here is the
intersection of two *spatial* (support) ranges — radial ∩ transported-radial —
which is the classically-prolate-type "max concentration on a support interval"
object. The Slepian sequences below are the mathematically-correct concrete
instantiations of that idea: band-limited AND maximally concentrated on a radial
interval. (Nothing is *from* the repo's own objects — it's the object the escape
theorems name.)

## 3. Result (fidelity-guarded): the outer leak survives the exact prolate carrier

`817_outer_channel_slepian_probe.py` mirrors 815/816: `D = T⁺(A G⁻¹ A⁺)` on the
carrier span `A = (T·J)` (radial columns of `T`), `G = A⁺A`; then applies `D` to
Slepian columns `u` cut to radial support and reports the fraction of `‖D u‖`
lying under `log λ` = `(I−R)` leakage.  Slepian window `M` scaled by time-band
bandwidth `NW`:

```
logλ=0.0      {2}       {2,3}       {2,3,5}
 NW=2:    0.279        0.406       0.418
 NW=4:    0.279        0.388       0.411
 NW=8:    0.349        0.336       0.442

logλ=1.0    {2}       {2,3}       {2,3,5}
 NW=2:    0.283        0.408       0.430
 NW=4:    0.284        0.395       0.429
 NW=8:    0.355        0.343       0.456
```

Reading the table: as the Slepian band narrows (`NW` down) at fixed primes and
`log λ`, the leakage **stays 0.28–0.46** — it never heads to 0.  It barely moves
between `NW=2` and `NW=4`, and the small `NW=8` rise is just the lower-order
Slepian columns whose energy reaches across the boundary (mild, not a vanishing
trend).  So the exact-prolate carrier does **not** rescue Gate-3U's outer
channel.  The hard bone did not break here.

## 4. Honest scope — this is numeric, not a Lean refutation

Strictly, this closes the smooth-approximation gap 816 flagged, nothing more:

- It replaces 816's *approximate* prolate functions with the *exact* Slepian
  band-limited family — the honest caveat is now discharged for the 
  **band-limited** half of the Sonin carrier.
- It is **not** a proof. The repo has only the abstract star-projection
  reduction; the exact prolate basis is not constructively realized in Lean
  source. So we cannot *verify* the carrier is a Lean object; we verify the
  *object class* 816 named.

That means the current business status is unchanged but better levered: RH in
this repo is conditional on the single open identity, and each real carrier
added (816 broad, 816 band-limited, 817 exact-Slepian) yields a positive outer
leak with no decay. The  gate stays **numerically non-closed** on every carrier
implemented so far.

## 5. Closing line

**817 verdict:** the exact prolate (Slepian) transfer of 816's remaining hope
failed. The outer channel survives band-limiting → the whole remaining low-
probability escape is the genuinely-orthogonal finite-S arithmetic-prime
structure (not the toy 2,3,5), or a fully-exact prolate/PSWF formalization that
does not live in this repo today.

> Discipline: numeric falsification of the band-limited outer-channel estimate,
> not a Lean refutation and not a proof of RH. It discharges 816's explicit
> caveat by testing the exact (Slepian) prolate object it named.