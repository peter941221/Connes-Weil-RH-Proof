# 1723 — Exact annular kernel-diagonal mass identity

Date: 2026-09-20

Consumer: healthy `CompactLog` B5, S3 source-Sonin square-summability.

The new leaf `C1G8R3AnnularKernelDiagonalMass.lean` proves, for every
admissible outer cutoff and every countable Hilbert basis of the source-Sonin
carrier, the exact identity

`ofReal (sum_i ||annularOutput(e_i)||^2)`
`= integral_t (sum_i ||annularOutput(e_i)(t)||_e^2)`.

The proof combines the existing L2 norm readback with the Tonelli exchange.
It does not assume finite dimension, basis smoothness, or a trace-class
operator. The paired Audit leaf reports only the three standard axioms.

This closes the bookkeeping interface and leaves one genuine S3 producer:
an integrable, cutoff-uniform upper bound for the displayed pointwise kernel
diagonal. The theorem is not itself that bound and does not claim RH.

Evidence: focused build log `1723_annular_kernel_diagonal_mass_v4.log`,
3969 jobs, success footer, zero `error:` and zero `sorryAx`.
