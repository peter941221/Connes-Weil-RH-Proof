# 1535 — Source-radial specialization reaches the complete forward transport

The bridge now proves a reusable specialization of the Hardy defect consumer:
if an ambient factor satisfies the source-composed radial support identity
`E M J = M J`, then the radial defect `(I-E) M J` vanishes identically.  Only
the Fourier-gap column `E (I-Q) E M J` remains as a square-summability premise.

The existing theorem
`finiteEulerTransport_sourceRadialSupport` supplies this identity for the
complete forward finite Euler transport.  Its new consumer therefore reduces
the corresponding source commutator column to the single Fourier-gap estimate,
while the all-scale prolate commutator leg is already supplied by record 1532.

Evidence: `C1G8R3BoundaryOutputFactorizationBridge.lean` and
`C1G8R3CompositeBoundaryEnergy.lean`, built with paired Audit modules in log
`/home/peter/rh/build-logs/1738_transport_radial_consumer.log`; the build
completed with zero `error:` and zero `sorryAx` lines.  This is a formal
consumer reduction only.  No Fourier-gap estimate, B4 closure, C3 positivity,
or RH conclusion is claimed.
