# Record 2298: full-window uniform-radius propagation screen

## Result

The current 192:6 interpolation-only uniform-radius majorant does not pass the
sampled finite-window budget. Its finest-grid reading is 1.99965140007206e10,
or 1999.6514 times the 1e7 budget. This is a method-sizing failure, not a
lower bound on the true error and not an analytic no-go. It explains why
record 2297's small origin-cell floor was insufficient.

Evidence: `results/2298_carrier_full_window_propagation_screen.json`, generated
by `scripts/routea_carrier_full_window_propagation_screen_2298.py`. All three
grids retain the same 30-family coefficients and all 41136 prime powers.
The same-candidate signed integral reproduces record 2296 bitwise on each grid.

```text
xi step   | sampled majorant | ratio to 1e7 | same-candidate drift
----------+------------------+--------------+---------------------
0.020     | 1.9985625866e10   | 1998.5626    | 0
0.010     | 1.9995445130e10   | 1999.5445    | 0
0.005     | 1.9996514001e10   | 1999.6514    | 0
```

## What is being priced and why

The functional multiplies a signed kernel, a squared polynomial magnitude,
and the squared magnitudes of two complex transforms. A uniform radius is
the same allowed transform error at every frequency. It is simple but can
overcharge frequencies where the true error is smaller.

Let b and c be the candidate base and correction magnitudes, and E and F
their interpolation-only error radii. Set d_b = 2 b E + E^2 and
d_c = 2 c F + F^2. If these radii bound the respective errors, the absolute
product deviation is at most b^2 d_c + c^2 d_b + d_b d_c. This is the
elementary expansion of the two squared magnitudes, including their product
error; omitting the product would lose the E^2 F^2 term at b=c=0.

The screen multiplies this expression by the absolute full kernel and the
full complex polynomial magnitude squared, then applies a sampled trapezoid
on [-40,40]. It uses record 2297's upper radius endpoints, rounded upward
once to binary64. Subsequent arithmetic and integration are diagnostic,
not directed rounding or continuous enclosure.

At step 0.005 the price decomposes as follows:

```text
term                       | sampled charge | role
---------------------------+----------------+------------------------------
b^2 d_c                    | 1.98779617e10  | correction-error channel
c^2 d_b                    | 1.18552184e8   | base-error channel
d_b d_c                    | 1.09781180e2   | product of the error charges
---------------------------+----------------+------------------------------
total                      | 1.99965140e10  | 1999.65 times budget
```

The correction-error channel carries about 99.4% of this majorant. Thus the
binding price is not the quartic origin floor: it is propagation against the
nonzero transforms elsewhere in the window. The sampled peak is near xi=-3.605.
Record 2296's same-grid direct absolute difference is only 3.28105767e5 on
this grid. The difference between the two numbers measures conservatism of
this chosen majorant and its interpolation radii, not an inconsistency.

## Controls and limitations

Six controls in `scripts/routea_carrier_full_window_propagation_selftest_2298.py`
cover complex perturbations, the zero-amplitude quartic floor, monotonicity,
negative-input rejection, upward radius conversion, and artifact ledger and
source hashes. The zero-radius case and both one-channel-only cases are
included. Source provenance is checked before reusing the 2297 artifact.

No stored-evaluator arithmetic bridge is supplied. The ideal-polynomial
interpolation radius cannot automatically enclose floating node generation,
coefficient conversion or shifted-moment evaluation. Sampled magnitudes,
kernel evaluations and trapezoids are not certified continuous integrals.
Neither hgap nor the infinite tail nor actual selected-owner readback closes.

## Next decision

Do not spend arithmetic-certification effort on the current 192:6 uniform
propagation price. Change a named hypothesis before repricing: either increase
the panel count with the seventh-derivative remainder target, or preserve
frequency-dependent/correlated error information. This is not a global freeze
on uniform radii or carrier interpolation.

With unchanged derivative bounds, a per-panel radius costs r^8 and the number
of panels grows as 1/r, so the summed interpolation charge scales as r^7.
Doubling panels would predict a 128-fold radius decrease; quadrupling predicts
16384-fold. These are planning estimates, not measured gains: the derivative
enclosures and full functional propagation must both be repriced. A 768-panel
degree-six probe is therefore a named, falsifiable next test, rather than an
unmotivated node-count increase. Acceptance requires a full-window method
price below budget with independent derivative and owner controls, before any
continuous-integral or arithmetic certificate is attempted.
