# 2279 - Direct oscillatory quadrature trust-horizon screen

Date: 2026-09-30

Result: replacing FFT with composite Gauss-Legendre direct integration does not yet produce a trusted tail. With xi from 40 to 200, order 64 to 128 changes the signed result by 4.618x, and order 128 to 256 changes it by 10.307x. A separate high-order run from 512 to 1024 changes it by 4.583x on xi from 40 to 100. The method is marked DIRECT-GL-TAIL-UNTRUSTED.

The corrected width-a^2 owner uses convolution support 13.1072 and 41136 prime-power terms. The integration forms the physical profiles first, applies exp(y/2), then directly evaluates the oscillatory transform at each xi. It does not reuse the legacy 52-term kernel.

The low-order signed readings are large and unstable; the high-order readings fall near 1e-25 but remain unstable. This is the expected cancellation-floor pattern: increasing quadrature order changes the result by several times instead of converging. No finite-range reading is used as an infinite-tail bound.

Decision: direct composite Gauss-Legendre in its current unscaled floating implementation is rejected as a certificate path. The next implementation needs cancellation-aware interval quadrature, a transformed variable that resolves the oscillation, or a certified oscillatory remainder formula. hgap remains explicit.

No Lean source or manifest-bound producer source changed. Four focused controls pass, in addition to the previous 56 controls. No producer GO or RH claim is made.
