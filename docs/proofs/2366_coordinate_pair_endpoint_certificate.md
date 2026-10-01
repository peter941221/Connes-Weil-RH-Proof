# 2366 - Coordinate-pair endpoint certificate replay

日期：2026-10-02。

The stored-vs-affine coordinate obligation for the 2359 grid is now replayed
independently with exact `Fraction` arithmetic after reading the stored
binary64 `np.linspace` values. The exact affine points lie in the exact owner
window `[-storedWidth 4², storedWidth 4²]`; the stored endpoints exceed that
window by binary64 radius roundoff, so the stored points are certified against
the existing outer pin `[-stripRadius2303, stripRadius2303]` instead. All
240001 stored points lie in that outer window. The replay also records the
number of nonidentical coordinates and the maximum exact displacement used by
the endpoint-reduced owner bridge.

This is a finite Python replay, not a Lean theorem, not a directed integral
certificate, and not a producer GO. Its purpose is to settle the named
endpoint/window and displacement input before attempting numerical
accumulation and trapezoid certification.

Status: `COORDINATE_PAIR_ENDPOINT_CERTIFICATE_REPLAY_WITH_OUTER_PIN`; producer GO: `false`.
