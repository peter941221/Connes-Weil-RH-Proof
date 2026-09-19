# 1714 — Conditional translation obstruction to the survivor-core producer

Date: 2026-09-20

Status: project candidate; not a formal Lean theorem and not a map-level
no-go ruling.

## Question

After the exact annular pointwise readback, the Tonelli exchange, and the
L2-energy identity, the remaining S3 producer is a uniform bound on the
annular kernel diagonal.  A possible structural obstruction must be checked
before investing in a pointwise estimate.

## Conditional argument

Let `H` be the source Sonin carrier at a fixed scale and let `C` be the
selected root convolution restricted from `H` to the ambient L2 space.
Assume:

1. `H` contains a nonzero vector `u`;
2. `H` is invariant under all sufficiently large right logarithmic
   translations `U_b`, with `U_b f(t) = f(t-b)`;
3. `C` commutes with these translations;
4. the translates of `u` contain an infinite orthonormal sequence after
   the usual weak-separation/Gram-Schmidt argument; and
5. `C u` is nonzero.

Then `C|H` cannot be Hilbert--Schmidt.  Indeed, translation invariance keeps
the norm of every translated output equal to `||C u||`, while an
orthonormal sequence has a square-sum of column norms bounded by the
Hilbert--Schmidt norm.  Consequently the survivor-core square sum cannot be
finite for this nonzero translation-invariant leg.  The same obstruction is
visible in expanding annuli: translated copies place a fixed amount of
output energy arbitrarily far to the right.

## Repository evidence

The radial support is the upper logarithmic half-line condition
`t >= log lambda` (`CCM24LogRadialSupport.lean`).  The committed theorem
`cc20GlobalLogTranslation_mem_ccm24LogRadialSupport` proves preservation for
the orientation `b <= 0`; because the concrete translation is `u(t+b)`, this
is precisely translation of the function toward larger log coordinates.
The translation is an isometry and forms an additive representation
(`GlobalLogCrossing.lean`).  Root convolution is the literal global
convolution owner and hence is the natural commuting candidate.

The missing implications are material, not cosmetic:

* preservation of the actual Hardy/Fourier support under the same translations;
* construction of a separated orthonormal sequence inside the intersection;
* nonvanishing of the selected root on that sequence.

None of these is currently claimed below the conditional level.  In
particular, the open carrier-witness problem means that the antecedent may be
empty.  The record therefore does not alter `docs/map/042` or declare S3
dead.

## Direction audit

The Hardy covariance law is already present in the tree:
`H(U_b u) = U_{-b}(H u)`.  Therefore the radial support preservation for
`b <= 0` does not by itself preserve the Fourier-support half: the Hardy image
is translated in the opposite direction.  In fact, invariance under every
right translation would force the Hardy image to vanish on arbitrarily long
initial intervals and is incompatible with a nonzero carrier element.  The
conditional obstruction must therefore not be used as a blanket claim that
the actual carrier is translation invariant.  The live question is whether a
finite or one-sided translated tail supplies enough separated vectors for a
noncompactness argument without assuming the false full invariance.

Record 1715 formally settles the strongest version: a nonzero source-carrier
vector cannot have its entire right-translated orbit in the carrier.  The
finite-tail and pointwise-kernel alternatives remain open.

## Consequence for the fastest route

Before attempting a pointwise diagonal estimate, discharge or refute the
three missing implications above.  If they hold, the current survivor-core
producer is structurally impossible and the route must move to a
detector-specific semi-local positivity proof that does not require a global
Hilbert--Schmidt survivor core.  If the Fourier-support invariance fails, the
translation obstruction does not apply and the pointwise estimate remains
live.
