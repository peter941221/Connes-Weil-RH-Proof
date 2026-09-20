# 1789 — Actual Archimedean factor second derivative

Date: 2026-09-21

## Result

`hasDerivAt_deriv_ccm24ArchimedeanFactor` proves the real-frequency second
derivative interface for the concrete CCM24 Archimedean factor. The formula
is obtained by differentiating the exact first-derivative factorization and
using the GammaR logarithmic-derivative interface.

The proof retains the actual factor owner and uses only the product rule; it
does not introduce an inverse or an unproved asymptotic estimate.

## Verification and scope

The focused paired build completed successfully in 3554 jobs. The Audit
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

This is a formal second-order factor interface. It does not yet prove the
full scattering-product W2,1 estimate, the S3 kernel-diagonal majorant,
detector-specific semi-local positivity, or RH. No priority claim is made.
