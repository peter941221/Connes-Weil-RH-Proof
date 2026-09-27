# 2043 — Route A interval chain, link L2: L2-WIDTH-FAIL (uniform panels)

Verdict: **L2-WIDTH-FAIL**.  The preregistered record-2041 interval
certificate chain dies at its first link as specified: on the one-copy
G8-H owner (rho = 0.6 + 40.9187190121475 i, scale 0.88, support 9.504,
book 1647 prime powers), the kernel-side projected total width of the
per-panel interval enclosure exceeds |Q| at every registered dxi, by a
factor 32-139.  The S1 sub-task (interval representation of the
archimedean sigma) is settled positively on the way: 4/4 anchors
contained with width ~2.5e-14.

Owner and instrument are the committed record-2037 state; verdict rules
were frozen in the rig header before the run.  Artifact:
`results/2043_interval_kernel_width.json`.  Rig:
`scripts/routea_interval_kernel_2043.py` (WSL ext4 mirror, mpmath iv
dps 20).

## 1. Readings

```
+--------+--------+-----------+------------------+----------+--------------------+
|  dxi   | panels | width_mean| projected width  | /abs(Q)  | float Q (midpoint) |
+--------+--------+-----------+------------------+----------+--------------------+
| 0.05   |  1600  |  569.087  | 1.5411e22        |  138.7x  | -1.095352e20       |
| 0.02   |  4000  |  254.658  | 6.8984e21        |   62.1x  | -1.109682e20       |
| 0.01   |  8000  |  129.429  | 3.5062e21        |   31.6x  | -1.110921e20       |
+--------+--------+-----------+------------------+----------+--------------------+
```

abs(Q) = 1.1111e20 is the committed record-2037 q_h1.  The float
midpoint references converge to it (0.15% at dxi 0.01), so the width,
not the value, is the defect.

Width per panel is xi-flat: width_max/width_mean = 1.25, 1.47, 1.47.
The scaling width_mean/dxi is 12733 (0.02) vs 12943 (0.01), stable to
1.7%: the ladder is in the LINEAR regime, and the coefficient is the
independent-sum constant

```
sum_{k in book} (2 Lambda(k)/sqrt(k)) * 2 pi log k  ~  1.29e4,
```

with saturation (per-term cos width capped at 2) visible only at
dxi 0.05, where log k >= 2/(2 pi dxi) = 6.37 (k >= 581).  The
archimedean sigma panel contributes ~2.5e-14, thirteen orders below the
oscillatory book: the width is 100% the prime-power channel.

## 2. S1 settled: interval sigma

sigma(u) = log pi - Re psi(1/4 - i u/2) in the 8-shift Stirling form,
rectangular complex interval arithmetic, even powers only:

```
psi(w) = log w - 1/(2w) - sum_{n=1..6} B_{2n}/(2n w^{2n}) + R,
|R| <= (1/12)/8.25^14 = 3.97e-15.
```

Anchors (interval contains committed float r59.rig.sigma_vec):

```
+-------+-----------------------------+-----------------------+-----------+
|   u   | interval                    | float committed       | contained |
+-------+-----------------------------+-----------------------+-----------+
| 0     | [5.3721834192256415, ...66] | 5.372183419225654     | yes       |
| 2 pi  | [0.0010601801741625, ..875] | 0.0010601801741747    | yes       |
| 20 pi | [-2.3025745382361817, ..73] | -2.3025745382361693   | yes       |
| 80 pi | [-3.6888787944689985, ..36] | -3.6888787944689874   | yes       |
+-------+-----------------------------+-----------------------+-----------+
```

This component is reusable by any future interval work on the
archimedean channel.

## 3. Why the chain dies, and the only registered reopen

Interval quadrature widths add over panels; the oscillatory book forces
per-panel width ~ 1.29e4 * dxi.  Reaching the 10% budget (projected
width < 1e19) needs dxi ~ 2.9e-5, i.e. 2.8e6 uniform panels (~18 h at
the measured 23 ms/panel), with L3 and L1 forced onto the same grid.
That is the 2038 certificate-complexity wall again, now measured
directly instead of estimated.

The preregistered chain is dead as specified (uniform panels).  The
named reopen is a certificate-TYPE change at L2/L3, not a refinement:

- panel-local analytic integration of the oscillatory factor
  (quadrature by parts: integrate cos(2 pi xi log k) against a per-panel
  linear model of g, turning the per-term width from
  O(w_k dxi) into O(w_k (2 pi log k)^2 dxi^2)-type algebraic decay), or
- adaptive subdivision clustered where g concentrates (p^2 poles at the
  counterpart ordinates +-40.9), which trades the xi-flat width for the
  measured imbalance of integral g.

Both must be priced by a dedicated probe before any reopen; neither is
registered as live by this record.

## 4. Instrument notes (three defects found and fixed during the run)

1. The first sigma implementation ran the Bernoulli ladder over ALL
   powers 1/w^n instead of even powers 1/w^{2n}: the interval sat above
   the float anchors by 8.76e-3 at u = 0, shrinking like 1/u^2.  The
   4/4 anchor failure caught it before any reading was taken; the
   difference 1/(12*8.25) - 1/(12*8.25^2) = 8.76e-3 identifies the
   mechanism exactly.  Preregistered anchors are what made the rig
   self-checking.
2. A plain mpf on the LEFT of an ivmpf operand makes the mpf context
   try to convert a nonzero-width interval and raises
   "can only create mpf from zero-width interval" (mpmath ctx_mp.py
   _convert_fallback).  Coefficients must live inside the iv context.
3. `routea_g8h_basis_comparison_2037.py` executed its measurement at
   module level, so every import re-measured and re-wrote the committed
   2037 artifact in the mirror (observed: q_h1 drift 1.07e-9 relative).
   The rig now carries an `if __name__ == "__main__"` guard and the
   mirror artifact was restored from the committed bytes (md5 verified).

## 5. Scope and non-claims

- Verdict covers the one-copy G8-H owner, the registered uniform ladder
  (dxi 0.05/0.02/0.01 on [-40, 40]), and the independent-sum per-panel
  enclosure.  It does not price the quadrature-by-parts redesign.
- The kernel-side projection uses the committed float g; L1/L3 slack is
  not counted (this is a lower bound on the achievable total width).
- No full-line tail (L4), no coefficient enclosure, no Lean.
- Not a producer theorem.  Not RH.  Route A remains at its 2038 no-go
  with this as the measured price of its registered reopen.
