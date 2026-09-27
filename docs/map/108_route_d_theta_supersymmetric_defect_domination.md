# 108 — Route D: theta-shadow supersymmetric defect domination

Date: 2026-09-27.

Status: FROZEN CURRENT SKETCH. No producer is licensed and RH is not claimed.

## Entry contract

Route D must feed the existing healthy `CompactLog` consumer without changing
the detector, support, or visible-prime owner:

```text
selected healthy CompactLog detector g
    -> prove qw(g) >= 0 for the same owner
    -> SourceRH
```

The exact premise to remove is

```text
ICgate(g.convolutionSquare) <= 0,
equivalently qw(g) >= 0 under the existing same-owner P2 readback.
```

ROOT-only positivity, a fixed-prime surrogate, or a nearby theta test is not
an admissible replacement.

## Core observation

The project records a corrected same-owner trace identity under analytic
trace-class, cyclicity, and readback hypotheses that are not yet discharged.
After the route's pole-vanishing conditions it has the conditional form

```text
PositiveTrace_S,Lambda(g) = QW(g,g) + D_S,Lambda(F_g).
```

The positive term is the actual square

```text
A_g = P_hat_S,Lambda P_S,Lambda theta_S(g),
PositiveTrace_S,Lambda(g) = Tr(A_g^* A_g).
```

Even if those interface hypotheses are discharged, the missing inequality
becomes the defect domination statement

```text
D_S,Lambda(F_g) <= Tr(A_g^* A_g).
```

If the defect admits the factorization

```text
D_S,Lambda(F_g) = Tr(A_g^* C_S,Lambda A_g) + boundary_S(g)
```

with

```text
0 <= C_S,Lambda <= I,
boundary_S(g) = 0,
```

then

```text
QW(g,g)
  = Tr(A_g^* (I - C_S,Lambda) A_g)
  >= 0.
```

This is the proposed route. The “supersymmetric” part is the graded
commutator structure behind the phase involution and the `A^* A` square. The
“theta-shadow” part is the use of the theta/Poisson transform to identify the
finite-prime defect without changing the actual owner.

## Why this is different from Routes A and B

```text
Route A: estimate a signed physical residual after coefficient selection
Route B: find a negative determinant and close a same-index tail
Route D: dominate the corrected trace defect by its own positive square
```

The route attacks the representation bottleneck exposed by the corrected
trace identity. The first-brick audit now shows that the bare target
`D <= PositiveTrace` is algebraically equivalent to `QW >= 0`; it is not a
smaller proved obligation. See proof record 113.

This sign convention matters: for a hypothetical off-line zero the formal
healthy detector has `qw(g) < 0`, and the P2 readback forces
`ICgate(g.convolutionSquare) > 0`. A proof of `QW >= 0` (or `ICgate <= 0`)
would be the contradiction itself, not a routine intermediate lemma.

## First decisive brick

The first brick is an owner-specific contraction factorization:

```text
D_S,Lambda(F_g)
  = Tr(A_g^* C_S,Lambda A_g) + boundary_S(g),
```

with an explicit operator `C_S,Lambda` satisfying `0 <= C <= I`, and with
the boundary term discharged from already-registered support, endpoint, and
triple-vanishing facts.

Acceptance conditions:

```text
1. C is built from finite-S phase/projection and explicit arithmetic data,
   not from QW(g,g);
2. the equality is exact for every hypothetical off-line zero's actual
   selected detector, not one fixed sampled owner;
3. the contraction bound is proved before using the desired sign;
4. all commutator and theta tails have explicit trace-class bounds;
5. no infinite Euler-product, RH, or universal Weil positivity premise enters.
```

Kill condition:

```text
the proposed C is defined using the unknown sign, or the boundary/commutator
remainder is exactly the old QW >= 0 premise under another name.
```

If the first brick fails, Route D is a scoped no-go for this defect-domination
shape and no Lean consumer is written.

The first cheap screen has already rejected the universal projection-algebra
shortcut: record 112 gives an exact 2-by-2 counterexample with positive
defect on the nullspace of the positive square. The only untested version is
an owner-specific factorization for the actual selected detector, using
arithmetic/theta data beyond the bare projection identities.

## Evidence and provenance

The corrected trace identity and the square `Tr(A_g^* A_g)` are project
artifacts recorded in `docs/proofs/016_corrected_trace_identity.md` and the
Route C manuscript. Those artifacts do not contain the contraction `C`; that
is the new mathematical obligation.

The theta/Poisson and de Branges language is inspiration, not imported
positivity. Suzuki's de Branges/Hilbert-space construction is stated under RH
and does not provide this off-RH same-owner factorization:

```text
https://arxiv.org/pdf/2301.00421
```

Provenance split:

```text
existing project fact: corrected trace identity and positive square
new project derivation: defect-contraction factorization target
formal proof: none yet
```

## Decision

```text
Route D: CURRENT SKETCH FROZEN; NEW OWNER-SPECIFIC IDENTITY REQUIRED.
```

No new producer campaign is authorized by this sketch. Reopen only with a
new owner-specific arithmetic identity that strictly reduces the named
analytic premise rather than defining `C` from the desired sign.

## Closure addendum (2026-09-27, record 2039)

Route D is now CLOSED, not merely frozen. The reopen condition above is
unreachable: at the M0 interface, "there exist C with 0 <= C <= I and
boundary b <= 0 with D = Tr(A* C A) + b" is EXACTLY EQUIVALENT to
`QW(g,g) >= 0` (the C = I, b = -QW direction is the trivial factorization),
and every decomposition's remainder is forced `>= -QW` — the boundary
always carries at least the full gap (law F82, sign conservation under
splitting). The kill condition of this map is met by force of the
committed formal facts, for every owner. See
`docs/proofs/2039_route_d_closure_sign_conservation.md`. What survives
outside this closure: direct defect negativity `D <= 0` (a non-split,
Route-A-shaped signed estimate), governed by the Route-A records.
