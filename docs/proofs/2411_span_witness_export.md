# 2411 — retain directed span witnesses

Date: 2026-10-02.

The 2407 replay retained only the four parent-reduced integral totals.  That
was insufficient for the audited finite-span consumer: the 39 directed span
upper values were computed inside each worker but discarded before the JSON
artifact was written.

`routea_nodal_interval_fullgrid_2359.py` now retains
`directed_term_binary64_roundup_span_integrals`, obtained by applying the same
256-bit MPFR `RNDU` multiplication by `dx` to each ordered span witness.  The
calculation is unchanged; this is a certificate-data retention change, not a
numerical conclusion.

The Linux MPFR 1001-node control passed with one span (the configured span
length exceeds the control grid), and the retained span value agrees with the
parent total to the displayed precision.  The 776611-node artifact must be
replayed under the new source hash before it can be used; the result remains
non-Lean data until pointwise mathematical-term dominance is established.
