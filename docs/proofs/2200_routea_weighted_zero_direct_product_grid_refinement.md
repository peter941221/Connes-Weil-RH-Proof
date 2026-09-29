# Route A record 2200: direct-product physical-grid refinement

The live owner-local direct-product mechanism from 2197 was recomputed with
the coefficient path held fixed at quadrature order `m=6400` and physical
support grids of `30001, 60001, 120001, 240001` nodes.

The direct-product `C_upper` values were:

```text
30001: 77444.1439708785       relative to finest: -1.996e-10
60001: 77444.14398633518      relative to finest: -9.437e-15
120001: 77444.14398633596     relative to finest:  6.661e-16
240001: 77444.14398633591
```

The base/correction mass and second-derivative mass entries were stable to
roughly 12--15 digits. Thus the physical trapezoid/grid refinement is not the
binding measured term in the candidate direct-product budget.

This remains a measured candidate-owner control, not an outward enclosure or
complete-owner result. The heavy probe completed with exit 0:
`results/20260929_weighted_zero_direct_product_grid_refinement_2200.log`.
The remaining live work is intervalizing the physical functions and solve
error, then transferring from the candidate owner to the complete owner.
