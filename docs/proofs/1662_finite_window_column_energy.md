# 1662 — finite-window column energy is individually summable

## Formal result

For every selected owner, source scale, and integer window radius `n` large
enough to contain the compact support of the selected root test, the actual
finite-window approximation

`J† P_n C J`

has square-summable columns on every named source basis.  The proof factors
the window through the compact continuous-kernel operator
`fullBoundaryRootFactor`, then uses bounded zero extension and bounded source
adjoint postcomposition.  The support-radius hypothesis supplies the exact
identification with the global convolution window.

The same file retains the reverse-limit theorem: a radius-independent bound
on finite-set sums of these columns implies the full source-compressed
survivor-core square-sum.

Focused audit build: 3962/3962, zero errors, zero `sorryAx`, and only
`[propext, Classical.choice, Quot.sound]`.

## Mathematical boundary

This closes the individual finite-window legality, but not the uniform bound.
The remaining producer is precisely the collective radial-tail estimate as
the output window expands.  No RH conclusion is claimed.
