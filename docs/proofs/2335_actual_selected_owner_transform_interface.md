# 2335 - Actual selected-owner transform interface

Date: 2026-10-01

The actual selected-owner transform has been reduced to its two source
factors, without the auxiliary P-only multiplier of 2249. This is a transform
identity, not a Fourier inversion theorem or a producer sign certificate.

## Exact object

Let B(z) be the bilateral Laplace transform of base and C(z) that of
correction. Here z is the uncentered source coordinate; n is the stored
convolution-iterate index, which means n+1 copies of base, not n copies.

```text
H(z) = B(z)^(n+1) * C(z)

selected root at z - 1/2   = H(z)
selected square at z - 1/2 = conjugate(H(1 - conjugate(z))) * H(z)
```

These identities follow from the existing half-density shift and convolution
transform laws. The new leaf makes the factorization explicit for the exact
selected owner. No assertion is made that the captured float coefficients in
2249 already instantiate a healthy negative detector.

## Frequency convention and sign boundary

For a real angular frequency t, set z = 1/2 + i*t. The paired source point
1-conjugate(z) equals z, so the selected square at i*t is |H(z)|^2. With
the numerical convention t = -2*pi*xi, its candidate Fourier-side weight is

```text
W_actual(xi) = |B(1/2 - 2*pi*i*xi)^(n+1)
                * C(1/2 - 2*pi*i*xi)|^2
```

There is no additional P factor unless it is proved to belong to the chosen
source itself. Away from the critical line the two source points differ and
the modulus-square replacement is invalid. In particular H(rho)=1 and
H(1-conjugate(rho))=-1 give a selected-square value of -1, consistent with
2319 and incompatible with the P-only zero. Positive frequency weight does
not prove the signed Weil functional nonnegative.

## What remains open

Validation: focused Linux build succeeded (3498 jobs in the build plan). All
four audited laws depend exactly on [propext, Classical.choice, Quot.sound],
with no sorryAx. Windows and Linux sources agree byte for byte. Evidence is
stored in results/2335_selected_owner_transform_interface.json and
build-logs/2335_selected_owner_interface_build.log. This is not a root build.

1. Instantiate the actual base, correction, and iterate index with proved
   healthy-detector interpolation conditions. The float capture alone is not
   such a witness.
2. Derive a support bound for that assembled source and its convolution
   square. A support cutoff gives a covering prime book; it does not by
   itself determine the exact nonzero globalPrimeIndexSet.
3. Prove the Fourier inversion and integration/summation transfer for this
   weight before repricing the signed physical-kernel budget.

Evidence: the four transform laws and their paired axiom audit in
`ConnesWeilRH/Dev/C1RouteASelectedOwnerFourierInterface.lean` and
`ConnesWeilRH/Dev/C1RouteASelectedOwnerFourierInterfaceAudit.lean`.
