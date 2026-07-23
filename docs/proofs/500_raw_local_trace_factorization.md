# Proof 500: raw local trace factorization

Date: 2026-07-22

## Result

The result is good: Proof 500 closes Proof 499's concrete local
ordinary-trace legality gap for every literal suffix list.  It does not close
Gate 3U, the finite-S sign, Burnol's identity, or RH.

For

```text
Raw(S) = suffixActualBandRawQuadraticCycledResponse(owner, lambda, S),
rho_p  = primeSchurMarkovScalar p,
```

Lean now constructs a genuine complete four-branch Hilbert--Schmidt
(`S2`) pair for every `Raw(S)`, and a second pair for every local defect

```text
LocalRawDefect(p,S)
  = rho_p * Raw(p::S) - G_(p,S) * Raw(S) * R_(p,S).
```

The ordinary diagonal trace (`ordinaryTraceAlong`) is therefore legal on each
term, and the local cycle is proved by two rectangular Hilbert--Schmidt
cycles:

```text
Tr_source(G Raw(S) R)
  = Tr_boundary(B R G A†)
  = rho_p Tr_boundary(B A†)
  = rho_p Tr_source(A† B).
```

No unrestricted statement `Tr(xy)=Tr(yx)` for arbitrary bounded operators is
introduced.

```text
+---------------------------------------------------+----------------------+
| layer                                             | status               |
+---------------------------------------------------+----------------------+
| arbitrary-suffix physical four-branch pair        | closed               |
| arbitrary-suffix Raw(S) trace-class owner         | closed               |
| local RawDefect pair and trace-class owner         | closed               |
| legal two-cycle scalar sandwich                    | closed               |
| ordinary-trace local recurrence                    | closed               |
| ordinary-trace relative collapsed readout          | closed               |
| physical/Julia synthesis estimate                  | open                 |
| uniform relative Gate 3U bound                    | open                 |
| finite-S sign / Burnol identity / RH              | open                 |
+---------------------------------------------------+----------------------+
```

## 1. Complete suffix owner

`suffixActualBandForwardEndpointPairData` reuses the existing
`sourceThreeBranchPairData`.  Its common left leg is the source inclusion;
its right leg is the sum of the forward normalized Euler coframe and the
metric coframe.  The complete outer, reflected-outer, second-support, and
prolate branches remain inside that one physical pair.

The second coordinate is the opposite first-jet orientation:

```text
forward/endpoint right leg     = B A_S J + T_S† T_S J G_S^-1,
reverse right leg              = - B A_S J.
```

`BasisHilbertSchmidtPairData.l2Sum` combines these coordinates without
discarding their signed operator identity.  The resulting theorem is

```lean
suffixActualBandRawCommonPairData_traceProduct_eq_raw
```

and proves that the pair product is exactly `Raw(S)`, not a norm upper bound
or a surrogate diagonal ledger.  Its `traceProduct_isTraceClassAlong` field
gives the named-basis diagonal summability needed by the ordinary trace.

## 2. Local defect owner

The local pair is the L2 direct sum of two owned products:

```text
rho_p * Raw(p::S),
G_(p,S) * Raw(S) * R_(p,S).
```

The second product is built with
`BasisHilbertSchmidtPairData.boundedSandwich`; the minus sign is retained in
its right leg by `smulRight (-1)`.  Thus

```lean
suffixActualBandLocalRawDefectPairData_traceProduct_eq
```

identifies the pair product with the exact local defect before any absolute
value.  The companion theorem

```lean
suffixActualBandLocalRawDefect_isTraceClassAlong
```

supplies the ordinary-trace legality for the local term.

## 3. Two legal cycles

The generic helper

```lean
ordinaryTraceAlong_boundedSandwich_eq_scalar
```

accepts an owned rectangular product `A†B`, bounded `forward` and `reverse`
maps, and an explicit relation

```text
reverse ∘ forward = scalar • I.
```

It first invokes
`BasisHilbertSchmidtPairData.ordinaryTraceAlong_traceProduct_eq_cyclic` on
the sandwiched pair.  It then uses the same theorem on the original pair,
with an explicitly constructed adjoint pair on the boundary basis.  The
middle operator relation is proved pointwise from

```lean
suffixEulerFrameReverse_comp_transition
```

so the scalar appears only after the boundary product is legal.

The suffix specialization is

```lean
ordinaryTraceAlong_suffixActualBandTransitionSandwich_eq
```

and states

```text
Tr_source(G_(p,S) Raw(S) R_(p,S))
  = rho_p Tr_source(Raw(S)).
```

## 4. Relative readout

Using explicit `ordinaryTraceAlong_sub` and `ordinaryTraceAlong_smul`
premises, Lean proves

```lean
ordinaryTraceAlong_suffixActualBandLocalRawDefect_eq
```

which is exactly

```text
Tr(LocalRawDefect(p,S))
  = rho_p [Tr(Raw(p::S)) - Tr(Raw(S))].
```

Since `primeSchurMarkovScalar p > 0`, the one-step rearrangement is legal:

```lean
ordinaryTraceAlong_suffixActualBandRaw_cons_eq
```

inducts over the literal suffix list and gives

```lean
ordinaryTraceAlong_suffixActualBandRawResponse_eq_relativeCollapsed
```

with the exact Proof 499 recurrence

```text
Tr(Raw(S))
  = sum over ordered suffixes of
      rho_p^-1 Tr(LocalRawDefect(p,suffix)).
```

The arithmetic-family bridge is

```lean
ordinaryTraceAlong_sourceActualBandFiniteEulerRemainderResponse_eq
```

after rewriting `Raw(family.visiblePrimes)` to the existing finite-family
remainder.

## 5. What remains open

This proof establishes local trace-class legality and the relative algebraic
readout.  It does not identify the resulting ordered local sum with an
orthogonal completed Julia synthesis, and it gives no family-uniform estimate
for that sum.  In particular, do not use it to divide Proof 498's absolute
bound by `rho_S`, and do not feed `canonicalSynchronizedEulerModeEnergy`
into a Cauchy--Schwarz estimate without a separately constructed synthesis
map.

Gate 3U, the finite-S sign, negative-owner integration, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.

## 6. Lean ownership and verification

The source, audit, and aggregate import are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRawLocalTraceFactorization.lean

ConnesWeilRH/Dev/
  CCM24FiniteSRawLocalTraceFactorizationAudit.lean

ConnesWeilRH/Source/CCM25Concrete.lean
```

The focused audit and aggregate passed in Ubuntu 24.04 WSL2:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 500 focused axiom audit            |  3289 | PASS   |
| CCM25Concrete aggregate                  |  3777 | PASS   |
| full repository                           |  3858 | PASS   |
+------------------------------------------+-------+--------+
```

All eighteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or user axiom declaration.  The WSL localhost-proxy notice
is external to the repository.
