# 1616 — Four-term source-compressed root-kernel split

Date: 2026-09-18

## Result

The actual S3 operator `J† ∘ C ∘ J` is formally expanded using
`P = E Q E - R`, where `P` is the source Sonin projection and `R` is the
prolate remainder. The resulting identity is

`J† A C A J - J† A C R J - J† R C A J + J† R C R J`,

with `A = E Q E`. The two mixed terms and the remainder-square term are now
isolated as the already-prolate-controlled part; the remaining producer
target is the central Hardy-corner energy `J† A C A J`.

This is a formal algebraic reduction only. It does not assert the missing
square-summability estimate and does not change the RH claim status.

## Acceptance

Build log: `/home/peter/rh/build-logs/1616_source_compressed_kernel_split_retry13.log`.

The paired implementation and audit built successfully in 3957 jobs, with
zero `error:` lines, zero `sorryAx` occurrences, and three standard
`Quot.sound` audit markers.

Status: formal S3 narrowing brick. The central Hardy-corner estimate and B4
producer remain open.
