# Route A record 2199: coefficient-error budget

The direct-product candidate from 2197 has a large correction coefficient, so
this screen adds a worst-case relative coefficient perturbation envelope to the
physical-support mass bound. It is a measured sensitivity screen, not an
interval solve.

At `sigma = 1`, the baseline direct masses were
`base_M0 = 2.0033`, `base_D2 = 6688.58`, `corr_M0 = 913.447`, and
`corr_D2 = 1.52614e6`. The resulting high-shell budget ratio was
`0.00220320` of the candidate signed margin.

The perturbation scan returned:

```text
relative coefficient error    budget / margin
1e-8                           0.00220320
1e-6                           0.00220337
1e-4                           0.00222093
1e-3                           0.00238287
```

Thus even a deliberately large `10^-3` relative coefficient perturbation does
not consume the available headroom in this model. The large coefficient is a
required charge in the eventual enclosure, but it is not currently the
binding screen term. The next live enclosure target is physical-grid/
trapezoid error plus complete-owner transfer.

The heavy probe completed with exit 0:
`results/20260929_weighted_zero_coefficient_error_budget_2199.log`.
