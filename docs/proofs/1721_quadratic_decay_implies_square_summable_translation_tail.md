# 1721 — Quadratic decay now feeds the discrete tail consumer

Record 1720 supplied the pointwise Fourier rate but did not yet state the
discrete summability conversion.  The new theorem
`summable_normSq_of_quadratic_decay` proves that a sequence bounded by
`C * (n + 1)^(-2)` has a summable squared norm.

It uses the shifted real p-series with exponent `-2` and the elementary
comparison from the fourth-power square to the second-power majorant.
Together with record 1720, this closes the abstract rate-to-summability
interface required by the translated Hardy-tail consumer.

The remaining analytic bridge is explicit: establish such a quadratic bound
for the actual source-Sonin projected root columns, or prove an equivalent
operator kernel bound.  No regularity of arbitrary L2 basis vectors is assumed.

Evidence: `C1G8R3HardyTailRate.lean` and its paired Audit; focused build log
1721 completed successfully (2967 jobs), with zero `error:` and no `sorryAx`;
the Audit reports only the three standard axioms.
