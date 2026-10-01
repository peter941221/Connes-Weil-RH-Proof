# 2336 - Captured source marked values and composed support

Date: 2026-10-01

Status: SUPPORT-COMPOSITION-PROVED / MARKED-VALUES-DIAGNOSTIC-ONLY.

This record follows the object correction in 2334 and transform identities in
2335. It does not reopen map 103's frozen gate family. The captured rho is not
proved to be a source zero; the finite zero-node list is not proved complete.
The stored binary64 coefficients are not solved anew.

## Decision and object

The captured factors retain the intended marked values under three physical
quadrature readings. Therefore the capture has not lost the negative pair in
the way the P-only multiplier did. This licenses a directed interpolation
check, not a healthy-detector witness or a sign certificate.

The transform is H(z) = B(z)^(n+1) C(z). The actual square uses
conjugate(H(1-conjugate(z))) H(z), not |H(z)|^2 off the critical line. The
physical factors use radius width^2, as established in 2276.

The support upper bound must be assembled through both convolutions. R_b and
R_c are support radii of base and correction: intervals outside which those
functions vanish. Additive convolution integrates a product over a translated
coordinate, so support intervals add. The square convolves the source with its
reflected conjugate, doubling the symmetric support bound.

```text
base: n+1 copies             correction: one copy
        |                            |
        +-------------+--------------+
                      v
source radius <= (n+1) R_b + R_c
                      |
               half-density shift
               (no support change)
                      |
                convolution square
                      v
square radius <= 2 ((n+1) R_b + R_c)
```

For equal factor radii R and n=0 this is 4R, not 2R. The pin theorem is
instantiated for the packaged corrected family with R = stripRadius2303 =
6.5536001 and arbitrary coefficient/modulation vectors. It removes the
composed-square support premise for that family, not its interpolation or
sign premises.

## Diagnostic readings

The independent physical evaluator integrates each width^2 bump on 32 panels
using GL32 and GL64, and compares with a 16384-cell trapezoid. Complex family
contributions are combined before any modulus. Both coefficient MD5 guards
pass. All 30 source nodes are read back and stored individually.

```text
+------------------------------------------+------------------------+
| Quantity                                 | Diagnostic reading     |
+------------------------------------------+------------------------+
| Maximum base target residual             | 5.6858853e-12          |
| Maximum correction target residual       | 7.1240355e-09          |
| Maximum movement between the three rules | 1.1384207e-10          |
| Marked square real part, n=0              | -0.9999999998664919    |
| Marked square imaginary part, n=0         | -7.4137137e-09         |
| Four-point square sum, n=0                | -1.9999999997329838    |
+------------------------------------------+------------------------+
```

The n=1 and n=2 rows also retain the pair diagnostically. They are exponent
and support controls, not new gate candidates. The common probe threshold
1e-5 is a decision threshold only, not an enclosure radius. Floating-rule
agreements prove neither exact node values nor quadrature error bounds.
Replaying the enriched artifact reproduces all previous diagnostic readings
exactly.

## Prime-book implication and its limit

For the largest exact stored width, R is about 6.5536. At n=0 the composed
square radius expression is about 26.2144; the proved outward pin is
26.2144004. The unpinned cutoff scale exp(26.2144) is approximately
2.4253e11, versus the 2308 convention's radius 13.1072 and cutoff 492475.
The exponential scale is a float diagnostic, not a certified integer cutoff.

The 2308 2R book is the single-factor-square support convention, not the
composed-source support-cover convention. Its use for H requires an additional
support reduction or a signed treatment of the remaining book. Records 2320
and 2321-2333 have not identified the actual full book of the assembled detector.

A larger support upper bound does NOT prove that all those indices have
nonzero terms, or that the old cutoff misses a particular nonzero term.
It proves neither a lower support bound nor a gate no-go. The exact nonzero
globalPrimeIndexSet remains uninstantiated. No enormous prime list is enumerated.

## Validation and remaining obligations

Final focused build: exit 0, 3683 jobs in the build plan. All four audited
leaves use exactly [propext, Classical.choice, Quot.sound], no sorryAx. The
two Lean and two Python sources are byte-identical in Windows and Linux.
Eight selftests pass; this is not a root build. The numerical artifact source
hash matches the final probe source.

The focused support build audits four leaves: general source composition,
general square composition, captured-factor open-pin support, and packaged
selected-square pin support. Build evidence is recorded separately from the
numerical probe. Eight selftests include negative companion/sign controls and
n+1/support-count controls.

1. Certify or repair the same source's interpolation, charging every coefficient
   adjustment. Matching a numerical solve is not exact realization.
2. Establish the actual prime-book scope or a justified reduction before reusing
   the 41136-term margin. Support bounds do not determine the nonzero index set.
3. Prove Fourier inversion/readback for this source and price its signed kernel.
   Positive critical-line weight is not the desired Weil sign. No producer GO,
   gate sign, or RH claim is made here.

Evidence:

- ConnesWeilRH/Dev/C1RouteASelectedOwnerSupport.lean and paired Audit.
- scripts/routea_actual_owner_marked_support_probe_2336.py and paired selftest.
- results/2336_actual_owner_marked_support_probe.json.
- results/2336_selected_owner_support_audit.json.
- build-logs/2336_selected_owner_support_build.log.
- Prior conventions: records 1959, 2275, 2276, 2315, and 2335.
