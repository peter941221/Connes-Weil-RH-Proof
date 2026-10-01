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
parent total to the displayed precision.  The 776611-node replay under the
new source hash also completed: its independent readback found 39 finite
nonnegative witnesses with the expected `38×20001+16573` lengths and matching
source hashes.  The exact sum of serialized span floats differs slightly
from the parent-reduction total in some channels because the two `dx`
accumulation orders differ; both are retained and must not be conflated.  The
result remains non-Lean data until pointwise mathematical-term dominance is
established.
