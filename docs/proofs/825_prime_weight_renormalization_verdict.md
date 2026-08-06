# Proof-717 / Gate-3U: 825 — per-prime weight renormalization does NOT close the outer channel (idea A, numeric)

Date: 2026-08-06
Status: idea-A numeric NEGATIVE.  Giving each prime factor a relative weight
`w_p` in the finite-Euler transport factor moves the outer-channel leak
`(I−R)∘D` monotonically and only toward a TRIVIAL zero (as $w_p\to 0$ the whole
transport $T\to I$, the operator turns off).  There is no finite, non-trivial
$\alpha$ at which the leak vanishes while the operator stays genuinely active.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/822_transported_sonin_verdict.md`, `docs/proofs/823_...`,
`docs/proofs/824_outer_resolution_plateau_verdict.md`
PROBE: `825_prime_weight_renormalization_probe.py`

## 1. The hypothesis (idea A)

824 showed the outer-channel leak $(I-R)\circ D$ on the transported-Sonin frame
is a resolution-stable floor ($\approx 0.62$, single-family $\ge 0.369$).  Idea A
asked a sharp, falsifiable question:

> The metric coframe $D = H\cdot J\cdot G^{-1}$ is built under a particular
> Gram/inner product.  If the "correct" normalization multiplies each prime's
> transport factor $(I - p^{-1/2}shift_{-\log p})$ by a per-prime relative
> strength $w_p$, can the outer channel be made to vanish at a NON-trivial
> configuration (operator still genuinely active), rather than only as $T\to I$?

## 2. Why a per-prime weight is the only honest knob

The leak is a ratio $\|(D-I)u_{\text{under}}\|/\|Du\|$, so multiplying *all* of
$D$ by a common scalar leaves it invariant. To perturb the projection $D$ at all
you must deform the **relative** strength of the prime factors, i.e. put a weight
on each transport step:

$$
T_w = \prod_p \big(I - w_p\, p^{-1/2}\,\mathrm{shift}_{-\log p}\big),\qquad w_p=p^{-\alpha}.
$$

The identity guard is $w_p=1$, which must reproduce 824 exactly (it did).

## 3. Result — guard passes, scan is a clean monotone tail, no finite critical point

Identity guard (family, n=600, L=8):

| family | probe 825 $w_p=1$ | 824 floor |
|--------|-------------------|-----------|
| `[2]` | 0.3922 | 0.39 |
| `[2,3,5]` | 0.5628 | 0.55 |
| `all6` | 0.6245 | 0.62 |

The weight scan (family `all6`) is monotone decreasing in $\alpha$:

```
  alpha    leak
   -1.0    0.3669      (heavier small primes -> leaks MORE)
   -0.5    0.6083
    0.0    0.6245      <- 824 baseline
   +0.5    0.5075
   +1.0    0.3665
   +2.0    0.1813
   +3.0    0.0900
   +4.0    0.0447
   +5.0    0.0222     (-> 0, trivially, as T -> I)
```

Resolution guard at the strongest damping (a=3): n=600,1200,2000 all give
0.0897–0.0900 — flat, so 0.09 is a genuine spectral value, not a box artifact.
But it is the spectral value of a *degenerating* operator.

## 4. Reading (honest)

- **The leak has no finite-$\alpha$ critical point.**  It falls monotonically as
  $w_p$ damps the transport, and only reaches ~0 as $\alpha\to\infty$ where each
  `p^{-1/2}\cdot p^{-\alpha}=p^{-1/2-\alpha}\to0`, i.e. the transport factor
  collapses to the identity and the "outer channel" is vacuous. This is the
  TRIVIAL zero of $T\to I$, not a normalization discovery.
- **The wrong direction is informative**: $\alpha=-1$ (emphasizing small primes by
  an extra factor $p^{+1}$ relative) raises the leak for `[2]`/`[2,3]` and leaves
  `all6` near its baseline — small primes are where the outer channel is robustly
  active, and no weight on them removes it.
- **Conclusion**: within the metric-coframe formulation, no per-prime
  renormalization of the transport factor produces a non-trivial vanishing outer
  channel. The 824 non-zero outer channel survives the only scalar-deformation
  degree of freedom this reduction exposes. Idea A is, at the numeric level, dead.

## 5. Bound on this claim

- Numeric only (numpy/scipy on a uniform log-t grid, WSL venv), NOT a Lean proof
  and NOT a RH refutation.
- It kills the per-prime-weight deformation of the *same* coframe; it does not
  touch the two genuinely-live routes that 823/824 leave open:
  (a) the full infinite/critical-line RH operator, (b) a complete analytic
  prolate/Sonin transport without a finite grid.
- If a future construction rewrites $D$ on a genuinely different operator algebra
  (not a re-weighting of the same transport factors), this probe does not see it.

## 6. Repro

- `docs/proofs/825_prime_weight_renormalization_probe.py`
- Run: `wsl.exe -e bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && ./.venv-probe/bin/python docs/proofs/825_prime_weight_renormalization_probe.py'`
  (WSL venv `.venv-probe`, numpy 2.5.1 / scipy 1.18.0).