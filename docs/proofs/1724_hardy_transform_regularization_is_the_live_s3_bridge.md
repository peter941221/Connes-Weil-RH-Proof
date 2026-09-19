# 1724 — The live S3 bridge is Hardy-transform regularity

Date: 2026-09-20

Consumer: healthy `CompactLog` B5, S3 annular root-kernel diagonal bound.

## Audit result

The committed definition of `ccm24ArchimedeanHardyTitchmarsh` is the L2
composition `Fourier -> spectral reflection -> scattering multiplier ->
inverse Fourier`. The surrounding theorems prove involutivity,
self-adjointness, and unitary transport of the half-line projection. They do
not prove that this operator maps the selected compact root input into a
function with integrable first or second derivative, nor do they provide a
pointwise kernel diagonal.

Therefore the quadratic Fourier-decay theorem from records 1720–1721 cannot
yet be applied to the actual source-Sonin root. Applying it to arbitrary
source-carrier basis vectors would be invalid: those vectors are only L2
objects.

## Exact next theorem

The shortest live producer is one of these two equivalent interface forms:

1. a concrete weighted-L2/second-derivative estimate for the Hardy transform
   of the compact root input, strong enough to invoke quadratic decay; or
2. a direct integrable majorant for the diagonal of
   `rootConvolution * sourceInclusion * sourceInclusion† * rootConvolution†`
   after the annular output cutoff.

The first is preferable because the decay-to-summability and kernel-diagonal
consumers are already formal. No theorem is claimed in this record; it is a
formal source audit based on the committed Hardy definition.
