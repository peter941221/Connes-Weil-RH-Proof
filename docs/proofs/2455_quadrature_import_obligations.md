# 2455 - Quadrature import obligations decomposed; grid priced; attachment architecture open

Date: 2026-10-02.

Verdict in one line: the quadrature import (the seam between the
pointwise 2454 node norms and the four external endpoint constants of
the 2343 strip bridge) is decomposed into four named obligations, and
the pricing screen on the certified 2342 artifact fixes the binding
constraint - the correction second-derivative channel is 81.2% panel
term, so no usable grid coarsening exists (floor ~98,035 nodes; 60,001
nodes overshoots the frozen pin by 2.56x) and any Lean-side import
design must work at the 10^5-panel scale.

## Consumer interface (read from source, not from memory)

`FrozenStripHypothesis b c` (`C1RouteAProducerWired.lean`) is:

  forall sigma in [-1/2, 1/2],
    min (stripSecondNorm sigma b.test * stripNorm sigma c.test)
        (stripSecondNorm sigma c.test * stripNorm sigma b.test)
      <= bUpper2243        -- = 5289085703/2000 = 2644542.8515

`frozenStripHypothesis_of_owner_endpoint_bounds`
(`C1RouteAEndpointStrip.lean`) discharges it from four endpoint
hypotheses at sigma = -+1/2, universal in the coefficient vectors:

  stripNorm (±1/2) (correctedPhysical baseCoefficients modulations)
    <= baseNormUpper2343          -- 2.7790943782
  stripSecondNorm (±1/2) (base ..)  <= baseSecondUpper2343   -- 9044.9434472
  stripNorm (±1/2) (correction ..)  <= correctionNormUpper2343  -- 231.2642026141
  stripSecondNorm (±1/2) (correction ..) <= correctionSecondUpper2343
                                                -- 666472.585392

These four Lean constants are outward roundings of 2342's certified
endpoint maxima B0, B2, C0, C2.  `stripNorm sigma f = integral
exp(sigma x) * |f x|` is an integral over the whole line (`C1RouteA
DirectProductDecay.lean`), so the missing objects are INTEGRAL bounds,
not point bounds - the 2454 node norms N are pointwise and do not feed
this consumer directly (wording corrected in the 2454 record).

## What 2342 certified externally

For the 2338-repaired ideal source (coefficient_owner field =
"2338 exact analytic finite-node solution rectangles"), on the exact
rational uniform grid x_j = -R + 2Rj/(N-1), N = 120001,
R = 2076918743413931058457251756481/316912650057057350374175801344
(~6.5536): per channel and k in {0, 2}, the point trapezoid sum of
exp(sigma x_j)|F^(k)(x_j)| plus the one-sided chord panel

  panel = (h^2/12)(2R) exp(|sigma| R) (m_(k+2) + 2|sigma| m_(k+1)
          + sigma^2 m_k),   h = 2R/(N-1),

with m_j the analytic sup bounds on |F^(j)|, gives endpoint maxima
B0 = 2.77909437816447..., B2 = 9044.94344717920...,
C0 = 231.26420261406076..., C2 = 666472.5853917701..., min product
1852190.2152630097 <= pin (ratio 0.7004).  All external Arb/Acb
arithmetic; nothing imported into Lean.

## Pricing screen (this record; results/2455_quadrature_import_screen.json)

Recomputing the min-product exactly from the artifact's raw endpoint
intervals reproduces the published product to relative 1e-12 (the
published fraction is built from dyadic-rounded exported endpoints, so
bitwise fraction equality is not the right cross-check; the screen's
first draft used equality and correctly failed itself).  Panel terms
scale as h^2 under coarsening f = (N-1)/(N'-1):

```
+---------+------------+--------------+--------+
|   nodes | min-product | ratio-to-pin | verdict |
+---------+------------+--------------+--------+
|   60001 | 6762639.11 |       2.5572 | break   |
|   80001 | 3886697.38 |       1.4697 | break   |
|  100001 | 2550523.87 |       0.9644 | fits    |
|  110001 | 2151500.25 |       0.8136 | fits    |
|  120001 | 1852190.22 |       0.7004 | 2342    |
+---------+------------+--------------+--------+
```

Panel shares at full N: base S0 3.3%, correction S2 **81.2%**.  Max
h-coarsening 1.2240 => node floor ~98,035.  The screen is diagnostic:
no new numerics, no capture data, no producer.

## Obligation ledger

- W-A (generic Lean analysis): the one-sided trapezoid panel error
  theorem - for g >= 0 continuous with bounded second derivative on a
  panel, the integral is at most the trapezoid plus
  sup|g''| (panel length)^3 / 12 - stated for the weighted integrand
  exp(sigma x)|F^(k)(x)| and proved once, function-independent.  No
  owner data.  Cleanest Mathlib route: integral form of Taylor with
  integral remainder, or Hermite-Hadamard refinement.
- W-B (small-scalar import): endpoint integral uppers (or point sums
  and panels separately), the m_j sup bounds, R and h, as exact
  rational literals.  Trivial mechanically; the same 2453/2454 pin
  discipline applies.
- W-C (attachment - the cost center): connect the m_j/panel bounds to
  the ACTUAL correctedPhysical function.  Two architectures:
  (i) per-panel data import - 10^5 panel hulls as literals; at the
  node floor this means ~10^5 x 4 channel-k objects plus a Lean-side
  summation that the rfl-peel/norm_num machinery cannot evaluate;
  infeasible at the 2453 per-theorem grade.
  (ii) analytic per-family envelope (recommended target): lift the
  2454 hull machinery from point boxes to rational-panel interval
  boxes - exp monotonicity and cos/sin range lemmas over a rational
  panel are proved once, the per-family factor boxes over a panel are
  computed in Lean from the panel endpoints, the COMPLEX SUM is
  composed before the modulus (A7 cancellation-blindness law: no
  per-family triangle), and one generic theorem covers all panels by
  array indexing.  O(1) theorems + O(10^5) computed data, the only
  candidate that fits the 10^5 scale.
- W-D (ownership alignment - blocker for constants): 2342's constants
  are certified for the 2338 repaired analytic coefficients; the
  2452-2454 import lane bounds the 2275 capture binary64 vectors.
  The 2343 consumer is universal in coefficients, so the import target
  vector must be settled by the owner chain (2342 next-steps 1-2 stay
  binding) before a producer can discharge the four hypotheses for the
  downstream owner.

## Scope

Decomposition and pricing only.  No Lean module, no strip norm
discharged, no quadrature imported, no producer GO, no RH claim.  The
next record should be the W-A panel-error theorem (generic, no data)
and a micro-experiment for the W-C panel-envelope shape at 2-3 panels,
before any grid-scale commitment.

Evidence:

- `scripts/routea_quadrature_screen_2455.py`
- `results/2455_quadrature_import_screen.json`
- `results/2342_direct_ideal_strip.json` (source artifact)
- `ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean` (consumer, read)
- `ConnesWeilRH/Dev/C1RouteAProducerWired.lean` (hypothesis def, read)
