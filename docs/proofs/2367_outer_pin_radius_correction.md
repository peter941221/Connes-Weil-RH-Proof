# 2367 - Outer-pin correction for stored endpoints

日期：2026-10-02。

The 2366 replay caught a genuine boundary mismatch: binary64
`np.linspace(-radius, radius, 240001)` uses the stored float radius
`6.553600000000003`, while the exact Lean owner radius is slightly smaller.
Therefore the actual endpoints cannot be certified in
`[-storedWidth 4², storedWidth 4²]`. They are, however, inside the existing
exact outer pin `[-stripRadius2303, stripRadius2303]`, with
`stripRadius2303 = 6.5536001`.

The owner coordinate bridge was generalized to an arbitrary radius and uses
the global `ownerDerivativeBudget2350` bounds, so it can consume this outer
pin without weakening or falsifying the exact owner support statement. The
finite replay records this correction explicitly; it does not certify
integration or import the node data into Lean.

Status: `OUTER_PIN_CORRECTED_ANALYTIC_BRIDGE`; producer GO: `false`.
