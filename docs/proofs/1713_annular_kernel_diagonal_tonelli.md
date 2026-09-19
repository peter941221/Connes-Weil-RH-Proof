# 1713 — Tonelli bridge for the annular kernel diagonal

Date: 2026-09-20

Status: formal bridge, not an RH result.

The theorem
`sourceRootAnnularOutputWindow_lintegral_tsum_eq_tsum_lintegral` proves the
Tonelli exchange for the nonnegative squared-enorm functions of the annular
source-root columns.  The required a.e. measurability is supplied directly by
the Lp representatives; no finiteness assumption is used in the exchange.

Together with records 1711 and 1712, this gives the exact chain

```text
annular column trace
  = sum of column L2 energies
  = integral of the post-exchange pointwise kernel diagonal.
```

The last equality is only a representation.  The still-open S3 producer must
bound that kernel diagonal uniformly in the expanding annulus on the actual
healthy carrier.  No positivity, carrier witness, SourceRH, or RH conclusion
is supplied here.

Verification: focused build of the theorem and paired Audit leaf completed
successfully in 3968 jobs, with zero `error:` lines and zero `sorryAx`.  The
Audit declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
