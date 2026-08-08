# Proof-717 / Gate-3U: consolidated status after probes 815–822 (both routes decided at numeric level)

Date: 2026-08-06
Status: verdict — after eight independent probes across both live routes (exact
prolate/Sonin carrier and real arithmetic families), the outer channel
`(I−R)∘D` of the metric wall is non-zero, often >1, and *does not vanish* on any
reachable carrier or family.  The inner (band/second) channel remains numerically
unreachable by grid/alternating-projection methods.  The whole route stays
conditional on the one open identity; RH is unchanged.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/815_rh_route_conditional_boundary.md` and 816–822 of this series.

## 1. The immediate job

`docs/proofs/815_rh_route_conditional_boundary.md` reduced the entire RH route in
this repo to ONE open operator identity, in two orthogonal channels:

```
endpointNorm ≤ 1  ⟺  OuterChannel + BandChannel = 0
```

with `OuterChannel = (I−R)∘D` and `BandChannel = forward + (R−R₀)∘D`, `R₀` the
Sonin (radial ∩ Fourier-support) projection.  The identity can only cancel if
EACH channel is 0.

## 2. What the 815–822 probe family established (honest, numeric)

| # | probe | channel/object | result |
|---|-------|----------------|--------|
| 815 | whole-gate reduction | two orthogonal channels | route REDUCES to one identity |
| 816 | broad + band-limited carrier | (I−R)∘D | non-zero, >1 for 2+ primes |
| 817 | exact Slepian (prolate) carrier | (I−R)∘D | non-zero (0.28–0.46), no decay |
| 818 | numeric R0 via alternating proj. | R0 | DEGENERATES (rank 0 / fails idemp.) |
| 819 | real archimedean phase (Gamma) | R0 | dim rescued (rank 8) but NEVER converges |
| 820 | Sobolev/decay-scale sweep | (I−R)∘D | flat; no decay in cutoff/res |
| 821 | real arithmetic prime families | (I−R)∘D | non-zero (0.10–0.42) on all |
| 822 | transported-Sonin frame (route b) | (I−R)∘D | LARGEST leak (0.38–0.56) |

## 3. What the full set says

- **Outer channel**: non-zero at every reachable scale.  Exact-Slepian (817)
  DOES NOT rescue it; Sobolev/decay (820) does not support a decay lemma; the
  real archimedean Gamma phase (819) still cannot converge R0; the transported
  Sonin frame (822) is where it leaks *most* (0.38–0.56).
- **Inner (band/second) : STILL OUT OF REACH OF NUMERIC METHODS**: both the
  toy-phase and the TRUE archimedean-phase `R0` cannot be materialized as a
  projector on a finite grid (818/819).  The repo proves the correct object is
  transported-Sonin exact intersection (822), but that object is analytic, and
  numeric row of methods can't reach it.
- So **no numeric probe has produced a vanishing (I−R)∘D on any reachable
  carrier, including the exact-Sonin and all-arithmetic ones the "remaining
  escape hatches" named.**

## 4. The honest status of the gate / RH

The whole chain is **still conditional on ONE open identity**.  The probes
settle only the *numeric* reachable part: the outer channel is numerically
non-vanishing and the inner channel is numerically unreachable.  None of this
proves RH, and none refutes it.  It refutes specific *methods* (subspace
intersection R0, outer-channel decay), not the theorem.

Remaining genuinely-live possibilities (beyond numeric reach, all analytic or
arithmetic at RH scale):
1. A **full infinite / critical-line** arithmetic structure (the actual RH
   operator over all primes, not finite-S families) behaves differently.
2. A **complete analytic prolate/Sonin transport computation** (the repo's
   `maps_sonin_intersection` object made rigorous at infinite dimension, not via
   a grid).

## 5. Deliverable summary

- Probes: `docs/proofs/816…822_*.py` (each reproducible).
- See docs: `816_outer_channel_nonzero_numeric.md`,
  `817_outer_channel_slepian_verdict.md`, `818_full_gate_r0_attempt.md`,
  `819_real_phase_verdict.md`, `820_outer_decay_sobolev_verdict.md`,
  `821_arithmetic_family_verdict.md`, `822_transported_sonin_verdict.md`.
- This file consolidates them.

## Handoff

- **RH status**: conditional, unchanged.  One open identity in two orthogonal
  channels.  Outer channel numerically non-vanishing at all reachable scales;
  inner channel not numerically reachable.  Not a proof, not a refutation.
- The two live routes are at the RH scale (infinite/critical-line, or full
  analytic prolate transport) — beyond what a finite grid can do.
## 6. Post-823 updates: 824 (resolution plateau) and 884 (Sonin-scale robustness)

- **824 (2026-08-06)**: the outer leak on the exact transported-Sonin frame PLATEAUS
  ~0.62 (per-family floor >=0.369) as n->6000 and L->32; it does not decay with
  resolution, so the 822 non-zero is a real lower bound, not a grid artifact.
- **884 (2026-08-08)**: sweeping the PHYSICAL Sonin scale (logla in [-2,2]) leaves the
  outer leak flat ~0.61-0.62 (regression anchor 0.6242 vs 824's 0.6245).  So the
  negative is SCALE-ROBUST: no choice of the physical lambda makes `(I-R)oD` vanish.

These reinforce §4's item (the outer channel is numerically non-vanishing); a future
closure must therefore come from the exact analytic cancellation `F == -D + J`
(docs/872), not from resolution, carrier, or scale.  Status: unchanged -- conditional
on one open identity; nothing here proves or refutes RH.
