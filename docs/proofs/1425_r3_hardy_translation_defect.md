# Record 1425 — R3 Hardy-translation defect normal form

Date: 2026-09-14

## Verdict

R3-F4 is **FORMAL GREEN**: the arbitrary-scale Fourier-support projection has
an exact unit-scale conjugation defect decomposition. The result does not
prove that the defect vanishes, does not prove the prolate remainder is
scale-covariant, and does not prove the G8 readback. It is therefore a real
reduction of R3, not an R3 completion and not an RH claim.

## The new object

Write `T_b` for the committed global logarithmic translation and `H` for the
committed Hardy--Titchmarsh isometry. Define

```text
D^R_b = T_b H - H T_(-b)
D^L_b = H* T_(-b) - T_b H*
```

where `H*` is the Hilbert-space adjoint. The zero-defect equations are exactly
the expected anti-translation law `H T_(-b) = T_b H` and its adjoint.

For `b = log(lambda)`, the formal source projection is

```text
Q_lambda = H* T_(-b) P_+ T_b H,
```

while the unit-scale model transported to the same boundary is

```text
T_b Q_1 T_(-b) = T_b H* P_+ H T_(-b).
```

The new Lean identity proves exactly

```text
Q_lambda - T_b Q_1 T_(-b)
  = D^L_b P_+ T_b H + T_b H* P_+ D^R_b.
```

This is an operator identity, so no sign, detector health, `SourceRH`, trace
limit, or universal Weil positivity is used.

## What it buys R3

The scale-reduction dream is now a two-control theorem rather than an
unstated symmetry:

```text
zero left defect + zero right defect
  => Q_lambda = T_b Q_1 T_(-b).
```

If this can be extended through the Sonin intersection projection, then the
source prolate remainder at every scale is a unitary translate of the already
formal unit-scale owner. The existing unit-scale trace-class theorem would
then supply the legality part of R3 at arbitrary scale.

The exact remaining mathematical target is therefore one of:

1. prove the concrete L2 Fourier translation identity and deduce
   `D^R_b = D^L_b = 0`; or
2. prove a summable trace-ideal estimate for the two defect terms and carry it
   through the Sonin projection.

The pinned library exposes the L1 Fourier-integral translation identity, but
the committed Hardy operator acts on the global L2 carrier. Extending the
identity to this carrier is not silently available from the current source
API. That extension is the next genuine new-mathematics obligation.

## Lean evidence

The formal leaf is
[`C1G8R3SoninScaleDefect.lean`](../../ConnesWeilRH/Dev/C1G8R3SoninScaleDefect.lean).
It contains the generic noncommutative projection identity, its concrete
source-projection specialization, and the conditional zero-defect corollary.
The paired audit is
[`C1G8R3SoninScaleDefectAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3SoninScaleDefectAudit.lean).

Acceptance log: `1425_scale_defect_try4.log`; build completed successfully
with 3172 jobs, zero `error:` lines, zero `sorryAx`, and three audited
declarations using only `[propext, Classical.choice, Quot.sound]`.

## Route status

```text
R3-F2  radial boundary / prolate split       FORMAL GREEN
R3-F3  trace-legality iff                    FORMAL GREEN
R3-F4  scale-defect normal form              FORMAL GREEN
L2 Fourier translation => defect zero         OPEN
Sonin intersection scale transport           OPEN
G8 cutoff -> source ledger/readback           OPEN
G8SameOwnerReadbackData                      OPEN
RH                                          NOT CLAIMED
```

The result sharpens, rather than weakens, the reachability test in map 012:
the unit-scale route is viable only after the L2 zero-defect theorem (or a
quantitative defect substitute) is actually proved.
