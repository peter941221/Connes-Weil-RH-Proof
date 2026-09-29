# 2242 — Certified zero count Z = 0 for the four channel functions

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **certified**. Directed 256-bit MPFR interval paving certifies
`h_k(x) != 0` on the whole open interval `(-a30, a30)` for all four channel
functions (base/corr x M0/D2), with zero failing boxes in every channel;
the only zeros on the closed interval are the boundary points `+-a30`,
where the contact is flat. This retires the last open item of the 2238
composite-EM lever: the panel allowance becomes
`(dx^2/12)(2 a_max) M_k(sigma)` with `N_risk = 0` (priced in record 2243).

## What is certified, region by region

The channels are exactly the 2234 `node_bounds` functions on the committed
construction (`results/2234_build_cache.npz`, families and coefficients
rebuilt): `h_0 = F` and `h_2 = F''` for both the base and the corrected
coefficient vector. Region decomposition of `(-a30, a30)`:

```text
[-a29, a29]      paved, box by box          8780..21219 boxes per channel
(a29, a30)       analytic edge arc          single active family a30
(-a30, -a29)     analytic edge arc          same, mirrored
{+-a30}          zeros, flat contact        h_k(+-a30) = 0, all one-sided
                                            derivatives 0 (phi extension)
```

`a29 = 2.32`, `a30 = 2.5600000000000005` (the two largest family supports;
on the arcs only the family `(a30, theta = -39.25244858548658)` is active,
so the summations collapse to a single term). No gaps: the pavement covers
the closed `[-a29, a29]`, the arcs are open and covered analytically, and
the two endpoints are exactly the boundary zeros.

## The pavement

Method: per box, a natural interval extension evaluated in directed 256-bit
MPFR (`RNDD`/`RNDU`); a box passes iff at least one of the four coordinate
intervals (re, im of the hull) excludes zero; the final hull is expanded by
32 ulp (`mpfr_nextbelow`/`mpfr_nextabove`) to absorb the RNDN rounding of
the stored constants; the reported floor is the RNDD square root of
`dr^2 + di^2`, a certified lower bound of `min |h_k|` over the box.

```text
channel   boxes  pass-first  bisections  depth  min floor                 time
base_M0    8780       8702          40      2   1.2760421464680534e-63   13.1 s
base_D2    9247       8859         236      4   5.587411531104226e-58    21.9 s
corr_M0   21219       7321       13364      7   2.4240105139404953e-59   77.0 s
corr_D2   12500       7308        4509      5   1.0615649871831736e-53   53.3 s
```

All `n_failures = 0`. Every channel's floor box is
`[-2.32, -2.3199249487652582]`, the `a = 2.32` phi-tail zone at the
pavement edge (the smallest local values are the phi decay, not zero
candidates). The bisection counts are the dip neighborhoods (the 2238 scan
dips `2.487e-12` / `4.920e-09` live here) plus the edge zone; the bulk
passes at depth 0.

Evaluator hygiene (the two facts that make the hulls tight enough):

```text
e1^2 + e2 = (2K/a^2) G2(q) q^-4,   G2(q) = 2K - (2K+4) q + 3 q^2
```

removes the catastrophic `e1^2` / `e2` cancellation from the k=2 symbol
before intervalization, and every phi-carrying piece is bounded by its
monotone sup form (for `q < K/m`, `phi/q^m` is increasing in `q`, so the
sup sits at the box's `q_hi`), so no hull blows up at a family-edge
breakpoint.

Controls (`results/2242_smoke.json`, 33 boxes per channel): directed
containment `worst_rel_viol = 0.0` on all four channels (the interval hull
contains the binary64 evaluation everywhere under directed rounding), and
the factored-symbol identity holds at relative max `4.929745680884792e-15`
at `(a, theta) = (1.6800000000000002, 0.27159999999999984)`.

## The edge arcs

On `(a29, a30)` and its mirror, `H = c30 phi e^{i theta x} B(q)` with
`B = 1` (k=0) or `B_2` (k=2), and `phi = exp(-K/q) > 0` strictly on the
open arc (`q > 0` there, including arbitrary slivers at `+-a30`).

k=0: `H != 0` iff `c30 != 0`; both coefficient vectors qualify —
`c30_base = (-10219581129.919819, -715718458.5063183)`,
`c30_corr = (-187554128800042.1, -52652975480084.484)`.

k=2: `B2_re(q) = (2K/a30^2) G2(q) q^-4 - theta^2` is decreasing in `q` on
`(0, q29]` (`G2'(q) = 6q - (2K+4) < 0`; `q^-4` decreasing), so the arc
infimum sits at the arc's largest `q`, `q29 = q(u = a29/a30)`:

```text
q29_upper                0.17871093750000044
G2(q29) >=               48.65831279754636
q29^-4  >=               980.3823131338909
B2_re  >=                435200.11369115417   > 0
```

(the bound is deflated by `(1 - 2^-200)` to absorb constant rounding; the
artifact field `B2_re_lower_bound` carries the value above). Hence `B2_re`
does not vanish on the arc and `h_2 != 0` there. This is why the pavement
may stop at `+-a29`: the outer slivers — exactly where the float64 arrays
report the `~5e-314` denormal candidates at `x = +-2.5079` — are disposed
of analytically, not sampled.

## What this closes and what it does not

Closed: the certified zero count `Z = 0` gate of the 2238 composite-EM
lever, for all four channels, with the boundary zeros flat (so the
telescoped composite identity carries no kink term at `+-a_max` either).
With this certificate the panel allowance is
`panel_cem = (dx^2/12)(2 a_max) M_k(sigma)`, priced in record 2243.

Not closed / nonclaims:

- the pavement certifies per-box non-vanishing through outward interval
  hulls; it is not a sampling scan (the float64 arrays size the boxes
  only, and every acceptance decision is made in directed 256-bit MPFR
  with the 32-ulp hull inflation);
- the edge-arc certificate is the analytic single-family bound above, not
  an interval statement;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_zero_count_certificate_2242.py`
  (modes `smoke`, `pave_<channel>`, `edge`, `reduce`);
- artifacts: `results/2242_smoke.json`,
  `results/2242_pave_{base_M0,base_D2,corr_M0,corr_D2}.json`,
  `results/2242_edge.json`, `results/2242_zero_count_certificate.json`;
- MPFR: `libmpfr.so.6` via ctypes, 256-bit precision, directed rounding;
- construction: `results/2234_build_cache.npz` (local-only).