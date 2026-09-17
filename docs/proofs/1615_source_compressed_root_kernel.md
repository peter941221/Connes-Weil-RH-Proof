# 1615 — Source-compressed root kernel interface

Date: 2026-09-18

## Result

Added `sourceCompressedRoot`, the actual operator
`J† ∘ C ∘ J` on the source Sonin carrier. Its matrix coefficient satisfies

`<sourceCompressedRoot u, v> = <C (J u), J v>`.

The proof is a direct adjoint identity and introduces no ambient
Hilbert--Schmidt premise. A diagonal norm identity is also recorded in the
source carrier, providing the coefficient entry point for the direct kernel
estimate.

## Acceptance

Build log: `/home/peter/rh/build-logs/1615_source_compressed_kernel_retry3.log`.

The paired implementation and audit built successfully in 3957 jobs, with
zero `error:` lines and zero `sorryAx` occurrences. The audit printed two
standard axiom sets; no new axiom is used.

Status: formal interface brick. The source-kernel energy estimate required by
S3 is still open.
