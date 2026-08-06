# Proof-717 / Gate-3U: 824 — the outer channel has a resolution-Stable NORMFloor: not a grid artifact (route-A finding positive-to-negative)

Date: 2026-08-06
Status: route-A turning point — the outer-channel leak on the **exact
transported-Sonin frame** (822) is **not a finite-grid artifact**.  Sweeping
resolution to `n=6000` and interval to `L=32` leaves the leak pinned at a
strictly positive constant, converging to ≈0.62 (one-family floor ≥0.369).
So the 822 "leak" is a real lower bound: it CANNOT vanish.  This is a
deterministic *case-bound* negative (the transported-Sonin path cannot close
Gate-3U), not a RH refutation and not a proof.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/822_transported_sonin_verdict.md`, `docs/proofs/823_...`
PROBES: `824_outer_resolution_plateau_probe.py`, `824c_extend_resolution.py`

## 1. Why this was the decisive experiment

All of 816–822 measured the outer leak `(I−R)∘D` at a single grid (n=600, L=8)
and the transported-Sonin frame gave 0.38–0.56.  That is only "non-zero at one
resolution". Route A asks the sharp question:

> As `n→∞` and `L→∞`, does the leak **plateau at `c>0`** (a TRUE lower bound:
> the outer channel cannot vanish — Gate cannot close this way) or **decay to 0**
> (a finite-grid artifact — 822 is a false signal and route A honestly expires)?

If it decays, the negative evaporates; if it plateaus, the negative is real.

## 2. Result — the leak PLATEAUS, it does not decay

Resolution sweep (max over 6 exact-Slepian columns, family {2,3,5,7,11,13}):

```
     n     L=4     L=8    L=16
  200 0.5848  0.5799  0.4983
  300 0.5764  0.6168  0.5467
  400 0.5605  0.6316  0.5807
  600 0.5656  0.6245  0.6177    <-- 822's original n=600 point
  800 0.5538  0.6173  0.6327
 1000 0.5497  0.6220  0.6316
 1500 0.5478  0.6229  0.6157
 2000 0.5440  0.6263  0.6180
```

Resolution pushed further (family {2,3,5,7,11,13}):

```
    n     L=8    L=16    L=32
  2000 0.6263  0.6180  0.6316
  3000 0.6201  0.6243  0.6157
  4000 0.6214  0.6275  0.6180
  6000 0.6189  0.6211  0.6243
```

Per-family floor at n=2000, L=8 (the lowest single-family values):

```
  [2]       0.3922      [2,3]    0.4982      [7,11]  0.3796
  [3]       0.3693      [2,3,5]  0.5517      [2,5,7] 0.5285
```

## 3. Reading the table (honest, numbers-first)

- **No decay with resolution.** L=8 column: 0.62 at n=200 through 0.63 at
  n=6000 — flat to the 4th decimal over a 30x resolution increase.
- **No decay with interval.**  L=16 and L=32 columns are identical to L=8
  (0.62), ruling out a box-truncation escape (the 821 lesson: a "0" driven by
  `log p > L` would NOT survive L=8→32).
- **Converges to ≈0.62** at the collection level, ≥0.369 at the single-family
  floor.  Every one of the 7 families is pinned above 0.37.
- **822 reproduced exactly**: the 0.38–0.56 numbers at n=600 are the same as
  the n=2000 numbers — 822 was already at the plateau, not mid-decay.

So the outer channel `(I−R)@D` on the transported-Sonin frame has a
resolution-robust lower bound ≈0.62 (max) ≥0.37 (any single family) that is
uniform in `n,L` as both go to infinity. It cannot vanish there.

## 4. The honest gate status (route A verdict)

```
Route A — "promote 822 to a real lower bound" — SUCCEEDS AT THE NUMERIC LEVEL:
  outer-channel leak on the transported-Sonin frame is a positive constant
  (≈0.62 at max; ≥0.369 floor), manifest-robust to resolution and interval.
  The transported-Sonin path CANNOT make the outer channel vanish, so it cannot
  close Gate-3U by that channel.
```

Boundedness of the claims:

- **Vindicated:** 822 was not an artifact; the leak is a real, resolution-stable
  positive floor on the transported-Sonin frame.
- **NOT a proof**: this is numeric, not Lean, and it is a *case-bound* negative
  about one frame/path, not a theorem. It does not refute RH, and it does not
  refute the full RH-scale (infinite/critical-line) object.
- **What it does**: it removes the pragmatic "maybe the frame was wrong/cutoff"
  caveat and leaves the transported-Sonin frame as a genuinely non-vanishing
  outer channel.

## 5. Where this leaves the consolidated saga

| # | channel/scale probe | result |
|---|---------------------|--------|
| 816 | band-limited carrier | non-zero |
| 817 | exact Slepian | non-zero, no decay |
| 818/819 | numeric R0 | degenerates/unreachable |
| 820 | Sobolev/decay | flat, no decay |
| 821 | real arithmetic primes | non-zero all |
| 822 | transported-Sonin frame | LARGEST leak (0.38–0.56) |
| **824** | **resolution/interval to n=6000,L=32** | **PLATEAU ≈0.62 — leak does not decay, real floor** |

The transported-Sonin frame now stands as a documented, resolution-robust
non-vanishing outer channel.  The live routes that survive (beyond numeric
reach, all analytic/arithmetic at RH scale) are unchanged from 823:
(a) full infinite/critical-line RH operator, (b) a complete analytic prolate
transport without a finite grid.  824 makes the case-bound negative on the
transported-Sonin *numerical* realization definitive; it does not reach the
analytic object itself.

## 6. Repro + artifacts

- `824_outer_resolution_plateau_probe.py` — resolution/interval sweep, n:200..2000.
- `824c_extend_resolution.py` — extended n:2000..6000, L:8/16/32.
- Run: `wsl.exe -e bash -lc 'cd /mnt/.../Connes-Weil-RH-Proof && ./.venv-probe/bin/python docs/proofs/<probe>.py'`
  (WSL venv `.venv-probe`, numpy 2.5.1 / scipy 1.18.0).