# 111 — Route D theta-shadow supersymmetric defect domination

Date: 2026-09-27.

Status: speculative candidate only, outside the live producer registry. This
is a mechanism proposal and kill test, not a proof and not an RH claim.

Current branch status:

```text
Route B: DEAD_ON_CURRENT_FAMILY
Route A: A-DEAD-CURRENT-CERTIFICATE
Route D: new candidate; no producer status
```

The route would keep the same healthy `CompactLog` detector and the same
support-derived finite visible-prime set. Its starting point is the corrected
same-owner trace interface, conditional on the analytic hypotheses described
in `docs/proofs/016_corrected_trace_identity.md`:

```text
PositiveTrace_S,Lambda(g) = QW(g,g) + D_S,Lambda(F_g),
PositiveTrace_S,Lambda(g) = Tr(A_g^* A_g),
A_g = P_hat_S,Lambda P_S,Lambda theta_S(g).
```

If that interface is discharged, its remaining target is the equivalent
defect inequality, not yet a strictly smaller proved obligation:

```text
D_S,Lambda(F_g) <= Tr(A_g^* A_g).
```

The proposed mechanism is to construct an owner-specific contraction:

```text
D_S,Lambda(F_g)
  = Tr(A_g^* C_S,Lambda A_g) + boundary_S(g),

0 <= C_S,Lambda <= I,
boundary_S(g) = 0.
```

It would then follow by an exact trace calculation that

```text
QW(g,g) = Tr(A_g^* (I - C_S,Lambda) A_g) >= 0.
```

This is the concrete form of the proposed theta/Poisson plus
supersymmetric/Darboux idea. It is not a claim that such `C` has already been
constructed. The first kill test is whether `C` can be built from finite-S
phase and projection data without using the unknown `QW` sign. Any boundary or
commutator remainder must be independently bounded and must preserve the
actual finite owner.

The existing positive square and corrected trace identity are documented in
`docs/proofs/016_corrected_trace_identity.md`. The de Branges connection is
only motivation; Suzuki's source is explicitly under RH and is not a proof of
this missing factorization:

```text
https://arxiv.org/pdf/2301.00421
```

Decision:

```text
SPECULATIVE ONLY; first provide an owner-specific reduction; no scan and no Lean.
```

The first cheap screen is complete. Record 112 rejects the universal
projection-algebra contraction by an exact 2-by-2 counterexample: the defect
is positive where the square vanishes. The only untested idea is an
actual-owner, actual-detector factorization. That is not current RH progress.
