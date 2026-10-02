# 2434 — Route A directed finite-sum interface

Date: 2026-10-02.

`DirectedComplexValue2433.sumFamily` transports per-term rectangle
containment through the finite complex sum used by the kernel accumulator.
Its only input is the explicit per-term containment predicate; no machine
arithmetic or stored numerical conclusion is hidden in the constructor.

The remaining certificate task is to instantiate the per-term predicate for
the actual MPFR endpoint chain and then connect the resulting rectangle to the
mathematical `correctedPhysical` summand.
