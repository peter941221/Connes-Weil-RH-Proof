# Proof 315: Invertible Transport and the Sonin Split

## Result

The useful result is a separation of two constructions which must not be
identified:

```text
source Sonin intersection --theta_S--> semilocal Sonin intersection

target support producer + target Fourier unitary
                    -> target orthogonal projections
                    -> positive P Q P - (P intersect Q)
```

`theta_S` is not a unitary conjugation of a support projection. The
unconditional RH theorem remains unproved.

## External Evidence

CCM24, arXiv:2310.18423v2, Section 4.7 and Theorem 4.6, states that
`theta_S` is bounded with bounded inverse and maps the complete Sonin space:

```text
theta_S : S_lambda(R, e_infinity) -> S_lambda(X_S, alpha)
```

The same source gives the Mellin formula:

```text
F_mu w_S(theta_S(f))(s)
  = (product_p L_p(1/2 + i s))^(-1)
      (F_mu w_infinity(f))(s).                         (58)
```

Source: https://arxiv.org/html/2310.18423v2

Mathlib provides the correct closed-subspace operation:

```text
ClosedSubmodule.mapEquiv
ClosedSubmodule.mapEquiv_inf_eq
ClosedSubmodule.mem_mapEquiv_iff
```

These transport closed submodules and preserve intersections for a
`ContinuousLinearEquiv`; they do not turn `T^-1 P T` into an orthogonal
projection when `T` is not unitary.

Source:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/ClosedSubmodule.html

## Lean Owner

`ConnesWeilRH/Source/CC20Concrete/InvertibleTransportSonin.lean` contains the
generic carrier-level contract:

```text
transportedClosedSubmodule T P := ClosedSubmodule.mapEquiv T P
transportedClosedSubmodule T (P inf Q)
  = transportedClosedSubmodule T P inf transportedClosedSubmodule T Q
```

On the actual target carrier it proves all four projection absorptions and the
unconditional positive-factor identity:

```text
P R = R,  R P = R
Q R = R,  R Q = R

P Q P - R = (P - R) Q (P - R)
IsPositive (P Q P - R)
```

This algebra uses the actual orthogonal projections of `P`, `Q`, and
`P intersect Q`. It does not import projection structure from the non-unitary
transport.

`ConnesWeilRH/Dev/InvertibleTransportSoninAudit.lean` is the focused theorem
and axiom-audit entrypoint. It compiles independently and confirms that the
contract has no project-specific or sorry-generated axioms.

## Verification

Verified on 2026-07-16 in a WSL2 Linux-side ext4 verification copy.

The focused command checks the public theorem signatures and their axiom
ownership directly:

```text
lake env lean ConnesWeilRH/Dev/InvertibleTransportSoninAudit.lean
```

It exits successfully. Each audited theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The aggregate command checks that the new source is reachable from the
project's `CC20Concrete` import surface:

```text
lake build ConnesWeilRH.Source.CC20Concrete
```

It completes successfully with `3608` jobs and explicitly builds
`InvertibleTransportSonin`. A source and audit scan finds no `sorry` or
`admit`. The aggregate output contains older warnings from unrelated modules;
the new source and audit introduce no linter warning.
SHA-256 hashes for the source, audit, and aggregate import file match the
current Windows worktree byte-for-byte.

## Producer Contract

To instantiate the construction for the semilocal route, the next producer
must provide all of the following on one carrier:

```text
P_S       : actual semilocal support/vanishing subspace
F_S       : actual semilocal Fourier unitary
Q_S       = F_S^dagger P_S F_S
R_S       : orthogonal projection onto Ran(P_S) intersect Ran(Q_S)
theta_S   : bounded invertible map identifying the Sonin intersections
```

The theorem `theta_S` maps the Sonin intersection. It does not establish
`theta_S(P_infinity) = P_S`; that stronger statement must not be silently
assumed.

## Rejected Shortcut

Do not define the target orthogonal projection by

```text
Q := theta_S^(-1) P theta_S
```

For a bounded invertible but non-unitary `theta_S`, this is generally an
idempotent oblique projection, not the orthogonal projection required by the
positive-factor argument. The route would then lose self-adjointness and the
`-2 * inner(eta, xi)` residue bookkeeping.

## Remaining Gate

The missing mathematical producer is the actual semilocal/global-log support
carrier and its Fourier unitary. Once that producer is available, Proof 314's
positive intersection correction and Proof 313's three-branch commutator
ledger can be instantiated without changing the residue term.

```text
RH = UNPROVED
```
