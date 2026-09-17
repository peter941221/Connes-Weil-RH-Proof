# 1599 — B4 tail is an unbounded reflected half-line problem

## Verdict

Analytic boundary clarification. The exact B4 tail
`H (I - E_w) H A` is not a finite-window remainder. By the committed
definition of the radial support, `E_w` keeps the half-line
`t >= log (wideRadialScale lambda s)`, so its complement reaches to negative
infinity. A compact-interval continuous-kernel argument cannot estimate this
tail without an additional Hardy decay or cancellation theorem.

The existing Hardy--prolate Gram module independently confirms the same
constraint: the Hardy/Fourier leakage and prolate term form one completed Gram
before the root acts; neither term may be assigned a standalone HS estimate
from the Gram identity.

## Evidence

- `Source/CC20Concrete/CCM24LogRadialSupport.lean`,
  `mem_ccm24LogRadialSupportClosedSubspace_iff`
- `Dev/C1G8R3CompositeBoundaryEnergy.lean`, `wideRadialScale`
- `Source/CCM25Concrete/CCM24FiniteSGatePhysicalHardyProlateGram.lean`
- `Dev/C1G8R3ApproximateHardySupportConsumer.lean`

## Consequence

B4 now needs a genuine reflected half-line decay/cancellation estimate for
the actual Schur columns. S3 likewise needs a source-compressed cancellation
estimate; boundedness, pointwise translated decay, and the ambient HS shortcut
are insufficient.
