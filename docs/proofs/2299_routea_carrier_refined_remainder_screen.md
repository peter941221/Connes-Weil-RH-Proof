# Record 2299: measured 768:6 interpolation-method price

## Result

The named 768-panel degree-six profile clears the sampled full-window
interpolation-only price gate. The finest-grid price is 271761.36522066034,
or 0.02717614 times the 1e7 budget. This is a candidate method price, not
a continuous-integral certificate or a hgap supplier.

Evidence: `results/2299_carrier_refined_remainder_screen.json` and
`scripts/routea_carrier_refined_remainder_screen_2299.py`.

```text
profile | base interpolation radius | correction radius | finest-grid budget ratio
--------+---------------------------+-------------------+-------------------------
192:6   | 2.43880724e-9             | 4.50084236e-6      | 1999.6514
768:6   | 3.36711709e-14            | 6.11635156e-11     |    0.02717614
```

The full-window price gain is 73581.15, measured in the same run. The
previous summed r^7 scaling predicted only 16384 for fourfold refinement
with fixed derivative bounds. The stronger measured gain reflects tighter
derivative enclosures as well as smaller panels; it is not an extrapolated
asymptotic claim.

## Controls and method

The run first recomputes the complete 192:6 derivative panel ledger and
requires exact equality with record 2297. It then reprices the seventh/eighth
derivatives on 768 panels, with two subcells per panel and the same flat-edge
machinery. Both complex channels and all 30 captured families are retained.
No coefficients are re-solved or owner hypotheses changed.

On each of the 0.02/0.01/0.005 frequency grids, the same run reconstructs
both profiles, retains all 41136 prime powers, and reproduces the record-2298
baseline majorant bitwise. Refined budget ratios are 0.02716133 / 0.02717468 /
0.02717614. Seven controls cover signed-versus-absolute kernel conventions,
zero-radius algebra, upward endpoint conversion, predecessor reproduction,
panel sums, all grid gates and source hashes.

The two candidate polynomials differ by a sampled absolute functional
integral of 335717.7569 on the finest grid. This is a comparison of candidates,
not an independent evaluation of the true interpolation error.

## Boundary of the result

The interpolation prices refer to the ideal envelope polynomials. Stored
support radii, panel coordinates, Lobatto nodes, computed coefficients,
oscillatory moments, phases and accumulation still require arithmetic
bridges. A successful sampled price does not establish continuous-frequency
quadrature, infinite tails or actual selected-owner readback. Certificate
and hgap flags remain false.

The next decision is whether the stored evaluator's arithmetic fits the
remaining budget. Record 2300 addresses its coefficient and geometry parts;
the interpolation gate alone is not a reason to claim the whole path passed.
