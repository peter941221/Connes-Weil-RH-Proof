# Record 2300: coefficient and physical-coordinate bridge price

## Result

The old binary64 polynomial construction and panel geometry do not clear
the sampled partial-bridge price gate: combined with interpolation, the
finest-grid majorant reads 45840350.9992, or 4.5840351 times budget. This
is a scoped price failure, not a lower bound on actual error.

A distinct, incomplete alternative has a lower partial price: regenerate
the polynomial coefficients from interval enclosures of the ideal nodes,
round those coefficients to binary64, and retain ideal panel geometry.
That partial candidate reads 287848.3442 = 0.02878483 times budget. It is
not an implemented complete evaluator; phase, moment and accumulation
errors have not been charged. Its diagnostic uses old-candidate sampled
magnitudes, not a certified magnitude enclosure for the alternative.

Evidence: `results/2300_carrier_coefficient_bridge_price.json` and
`scripts/routea_carrier_coefficient_bridge_price_2300.py`.

```text
partial transform error radius     | base          | correction
-----------------------------------+---------------+---------------
old coefficient construction       | 1.38502257e-12| 2.17023140e-9
old physical panel geometry        | 5.01153357e-12| 8.07732452e-9
regenerated coefficient cast only  | 2.25246744e-15| 3.61773492e-12
```

## Objects and derivation

An arithmetic bridge compares the exact object intended by a formula with
the exact real values represented by the stored floating-point output.
Here it compares the ideal 768:6 polynomial with the polynomial actually
produced by binary64 node generation, envelope evaluation and Chebyshev
fitting. No error estimate for the fitting library is assumed: the stored
coefficients are lifted exactly and compared against independently generated
ideal coefficient intervals.

Degree-six Lobatto nodes have the exact forms +/-1, +/-sqrt(3)/2, +/-1/2
and 0. The degree-six discrete cosine interpolation matrix is assembled
from this twelve-value cosine clock and integer Chebyshev power coefficients.
This bypasses the float least-squares fit. Bump envelopes are evaluated on
directed intervals at the ideal physical nodes, with the exact square of
each stored width as the support radius. Outside support the value is zero;
near a flat edge a nonzero exp(-1000) cap bounds even smaller exponentials
without pretending underflow gives an exact zero.

Let d_k be the complex difference of the kth power coefficient and r the
ideal panel half-length. The coefficient contribution is at most
r sum_k 2 |d_k|/(k+1), because the integral of |t|^k on [-1,1] is 2/(k+1).
This prices exact integration of the stored polynomial at ideal geometry.

For the geometry comparison, let delta_r and delta_c be the absolute
half-length and centre differences. Let S be the sum of the stored power
coefficient magnitudes and W = 80 pi + |theta|, which bounds the carrier's
shifted angular frequency throughout [-40,40]. The additional radius is
2 delta_r S + 2 r min(2, W(delta_c+delta_r)) S. The first term charges the
integration scale; the second charges the phase displacement, using
|exp(i x)-exp(i y)| <= min(2, |x-y|). Complex carrier differences are bounded
before triangle summation; full complex modulus is retained.

## Controls and remaining work

Eight controls pass: the exact cosine clock, every monomial through degree
six, independent bump evaluation on both sides of support, the coefficient
L1 bound against independent integration, complex cast errors, panel/grid
ledger sums, provenance, and rejection of mismatched profiles.

One design-time reference failed at an exactly known rational cosine:
high-precision cos(pi/3) landed about 3.6e-102 below 1/2, outside the exact
singleton interval. The reference now uses exact identities for the rational
clock values and independent high-precision evaluation only for irrational
values. No coefficient enclosure or acceptance bound was loosened.

The run verifies record-2299 source provenance and refuses any profile other
than 768:6. Stored coefficient and geometry bounds apply to exact integration
of those polynomials only. They do not enclose the executable's floating
moments, exponentials or final accumulation. Full-window propagation remains
sampled; infinite tail, selected-owner bridge and hgap remain open.

The next named construction is an evaluator using regenerated coefficients
and higher-precision physical coordinates, with separately priced phase,
moment and accumulation arithmetic. It must retain this captured owner and
the full kernel. Increasing panels alone cannot remove the observed geometry
price floor, so another node-count campaign is not the recommended next move.
