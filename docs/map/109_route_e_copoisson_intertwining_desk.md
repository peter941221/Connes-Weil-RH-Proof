# 109 — Route E: co-Poisson intertwining desk

Date: 2026-09-27. Updated same day (first brick outcome).

Status: **CLOSED AT THIS OWNER** (record 2044: k1 PASS, B1 DONE, B2
r-GENERIC — residual 0.7215 of ||M||, commutator 0.398 on the complete
integer lattice).  The E2 exact-exchange shape is dead at this
owner/span/resolution; E1 stays unselected with no desk action
registered.  Reopen requires a changed transcription algebra, a changed
owner, or an independent E1 preregistration.  Full desk record:
`docs/proofs/2040_route_e_copoisson_intertwining_desk.md`; outcome
record: `docs/proofs/2044_route_e_copoisson_first_brick_outcome.md`.
Registered subject to law F82 (sign-conservation-under-splitting, record
2039 — Route D's closure).

## Entry contract

Route E must eventually feed the existing healthy `CompactLog` consumer
without changing the detector, support, or visible-prime owner:

```text
selected healthy CompactLog detector g
    -> prove qw(g) >= 0 for the same owner
    -> SourceRH
```

## Core observation

Burnol's co-Poisson intertwining (arXiv:math/0112254; Ann. Inst. Fourier
57 (2007)) is an EXACT full-line exchange identity, equivalent to the
functional equation of zeta, between the sum-over-integers channel and the
integral channel:

```text
F( sum_{n != 0} g(t/n)/|n|  -  (int g(1/x)/|x| dx) * 1 )
    =  sum_{m != 0} g(m/u)/|u|  -  (int g) * 1
```

The repository's entire open obligation is the reconciliation of exactly
these two channels (discrete prime-side vs signed archimedean) — every
dead route (A estimate, B determinant, D factorization) tried to ESTIMATE
this reconciliation. The intertwining states it as an identity, and the
repository already owns the transcription bridge: record 109 verified the
selected owner's weilValue is exactly Burnol's explicit-formula pairing,
and the CompactLog owner's support [e^(-L), e^L] is precisely the class
where the identity holds.

## Why this is not Route D again

```text
Route D died by law F82: splitting the M0 identity and dominating part of
the defect conserves the sign gap (boundary forced >= -QW).

Route E is admissible only in non-split shapes:
  E1  weilValue becomes a norm/inner product in a co-Poisson-equivariant
      space (Burnol's HP_lambda) — qw >= 0 becomes a placement statement
      decidable by the repo's exact support algebra;
  E2  the archimedean signed term is the exact intertwining image of a
      positive prime-side term, remainder ZERO by support algebra.

A "control the remainder" shape is dead on arrival and must not be
registered.
```

## First decisive brick (cheap, exact, no scan)

```text
k1  record-111 scope check: compress the co-Poisson operator S to the
    owner's committed 17-dim span (record 2037 basis) and verify no
    uncontrollable boundary flux appears (111's death was a cut-induced
    boundary on a half-line read-off).
B1  re-derive the intertwining from Euler-Maclaurin on the owner's g
    class and transcribe weilValue(g_actual) exactly as a matrix
    coefficient of S on that span.
B2  compute the exact remainder r (algebra):
      r == 0 by support algebra             -> E2 live;
      r S-equivariant                       -> E1 live;
      r generic signed residual             -> Route E dead (F82).
```

Kill conditions (in order): k1 boundary flux; k2 any F67-shaped hypothesis
(Weil-positivity-equivalent import); k3 F82 shape test at B2.

## Decision

```text
Route E: REGISTERED AS DESK. No numeric scan, no Lean, no producer status
until B1/B2 land. A wave closes Route E only through the B2 structure test
or the k1/k2 kills.
```

Provenance split:

```text
literature:         Burnol co-Poisson papers (as cited in record 2040)
existing repo fact: record 109 alignment on the selected owner
new derivation:     none yet (B1/B2 registered)
formal proof:       none
```
