# Proof-717 / Gate-3U: 822 — the exact transported-Sonin frame is where the outer channel leaks MOST (route-b negative)

Date: 2026-08-06
Status: route-b negative — measured the outer channel on the **exact
transported-Sonin frame** (the analytic object the repo's `maps_sonin_intersection`
theorem names), not a generic grid intersection.  The leak is **larger here than
on any plain carrier** (0.39–0.56).  So the transported-Sonin frame—the one
analytic object 815/818/819 thought might be special—is exactly where the outer
channel does NOT vanish.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/815_rh_route_conditional_boundary.md`, `817`, `818`, `819`, `820`, `821`

## 1. The route-(b) object (why this is the right frame)

The repo **proves** that the finite Euler transport `T` sends the source Sonin
intersection EXACTLY onto the target: 
`T(source-radial ∩ source-FourierSupport) = radial ∩ target-FourierSupport`
(`CCM24FiniteEulerSoninTransport.lean:69-77`).  So the correct basis of the
gate's Sonin space is **T applied to real band-limited radial functions** — the
TRANSPORTED prolate/Sonin frame.  815/818/819 called this "not a grid number";
we build it *explicitly* instead of intersecting subspaces (which 818/819 showed
degenerates):

```
frame_k = T . (exact Slepian column cut to radial support)      # transported Sonin
```

## 2. Result — the largest leak seen anywhere

```
transport-Sonin outer leak (I−R)∘D on frame_k:
   logλ=0        logλ=1
  {2}       0.392         0.392
  {3}       0.369         0.369
  {5}       0.330         0.330
  {2,3}     0.51          0.51
  {2,3,5}   0.56          0.56
  {7,11}    0.380         0.380
  {2,5,7}   0.53          0.53
```

Compare with plain/radial/Slepian channels from prior probes: those were
~0.28 ({2}), ~0.38 ({2,3}), ~0.41 ({2,3,5}).  On the transported-Sonin frame the
same families rise to 0.38/0.51/0.56.  The leak is logλ-identical (0 and 1) and
is the **maximum** observed in the whole probe family.

## 3. Why this is the decisive route-(b) negative

- The transported-Sonin frame `T·(Slepian functions)` IS the object the theorem
  `maps_sonin_intersection` declares to be the correct transported frame.  So
  we did not choose a toy: we transported the exact source-Sonin functions and
  measured on them.
- The result is the opposite direction from what the gate needed: instead of
  `(I−R)∘D` vanishing on the source/transported Sonin, it is LARGEST there.
- logλ-invariance (identical at 0 and 1) rules out a cutoff artifact.

## 4. Verdict

```
Route (b) — exact transported-Sonin/prolate transport — does NOT close Gate-3U:
  the outer channel is largest (0.38–0.56) on the very frame the transport
  theory names as the Sonin image.  No transported-Sonin or pure prolate frame
  makes (I−R)∘D vanish; the leak is pushed, if anything, largest there.
```

This is numeric (not Lean, not RH).  It binds route (b) at the level we can
reach: building the exact transported frame explicitly does not remove the outer
leak — it maximizes it.

## 5. The consolidated gate status (through 822)

| # | channel/scale probe | result |
|---|---------------------|--------|
| 815 | simple radial | non-zero |
| 816 | band-limited | non-zero |
| 817 | exact Slepian | non-zero |
| 818/819 | numeric R0 (grid) | degenerates/unreachable |
| 820 | Sobolev/decay scale | flat, no decay |
| 821 | real arithmetic primes | non-zero all |
| 822 | transported-Sonin frame | LARGEST leak (0.38–0.56) |

Every reachable analytic and arithmetic carrier shows the outer channel
non-zero; the inner (band/second) remains unreachable by grid.  The next
genuine step is the full infinite/critical-line RH-scale object or a full
analytic prolate-transport proof — both beyond numeric reach.