# 1201 - Route 1 prime-free reference has the wrong sign

Date: 2026-09-06.

Status: formal route-1 no-go for this candidate shape. RH is not claimed.

For healthy detector data, let `W` be a reference whose convolution square is
supported in `(-log 2, log 2)`. If the bilateral profiles of the detector and
`W` match on the visible prime-log set, the finite-prime sum of the detector
vanishes. The healthy detector already has `qw g < 0`; the exact Weil
decomposition therefore forces

```text
0 < archimedeanTerm g.convolutionSquare.
```

Since `p2AggregateValue g = -qw g` on the triple-vanishing owner, the proposed
aggregate is then strictly positive. Thus exact matching to a prime-free
reference, including the `narrowArchRoot` candidate shape, cannot produce the
desired aggregate inequality. A viable Route 1 construction must preserve a
signed finite-prime residual (or supply a different Archimedean comparison);
this record does not rule out the residual consumer from record 1199.

Evidence: `archimedeanTerm_pos_of_healthyDetector_and_visibleProfileMatch_to_primeFreeReference`
in `C1P2BilateralProfile`, audited by `C1P2BilateralProfileAudit`.
The focused build `p2-primefree-negative.log` completed successfully with
3660 jobs, standard axioms only, and no `sorryAx`.
