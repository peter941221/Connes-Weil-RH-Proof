# 1785 — Archimedean factor logarithmic derivative

Date: 2026-09-21

## Result

The declaration `hasDerivAt_ccm24ArchimedeanFactor_logDeriv` proves the
real-frequency derivative of the concrete CCM24 archimedean factor. Its
derivative is the real-frequency chain factor multiplied by the previously
read-back GammaR logarithmic derivative and by the factor itself.

The proof establishes differentiability of GammaR on the line with positive
real part from the nonvanishing of its reciprocal, then composes with the
critical-line affine parameterization. The paired Audit module reports only
`propext`, `Classical.choice`, and `Quot.sound`; the build has no `sorryAx`.

## Status and scope

This is formal interface evidence for the scattering-phase product. It does
not prove the weighted W2,1 estimate, the detector-specific S3 inequality,
or RH. It is a project derivation built on the existing GammaR identity and
the project digamma readback; no priority claim is made by this record.
