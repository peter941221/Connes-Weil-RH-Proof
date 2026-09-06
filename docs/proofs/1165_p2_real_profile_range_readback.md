# Record 1165 — P2 real-profile finite-range readback

Date: 2026-09-06

## Result

For a convolution square supported in `(-B,B)`,
`finitePrimeSum` is exactly the explicit finite-range sum

```text
Σ n < ceil(exp B)+1  Λ(n)/√n · 2·Re(g²(log n)).
```

The theorem
`finitePrimeSum_convolutionSquare_eq_two_re_weighted_sum_range_of_support`
combines the support-controlled prime-sum range lemma with the Hermitian
profile identity.

The focused owner/audit build completed successfully in 3660 jobs, with no
`error:` lines or `sorryAx`; all audited declarations use only the three
standard axioms.

## Route meaning

This is the concrete finite arithmetic interface for the pinned detector's
future semi-local estimate.  It is a readback only: the range sum's sign and
the P2/RH conclusion remain OPEN.
