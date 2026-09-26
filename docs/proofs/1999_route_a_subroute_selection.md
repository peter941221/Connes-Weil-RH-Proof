# Record 1999 - Route A subroute selection: owner-preserving variational selector

Date: 2026-09-26.

Status: strategy record and pre-registration specification. No theorem,
no Lean brick, no numerical verdict, and no RH claim.

## 1. Entry contract

Consumer:

```text
actual healthy selected CompactLog owner g
  -> same-owner qw(g) >= 0
  -> SourceRH
  -> Mathlib RiemannHypothesis
```

Owner:

```text
(selectedOwner base correction n).sourceTest
```

The support, finite visible-prime-power set, Mellin nodes, physical profile,
and grouped visible-prime aggregate must remain those of this owner.

Premise to remove:

```text
archimedeanTerm(selectedOwner.square)
  + integral(actual grouped aggregate)
  <= -epsilon
```

Failure criterion:

```text
NO-GO-A-VARIATIONAL-BUDGET
```

is recorded if the minimum-cost feasible selector fails the required signed
margin or if its required cost-to-margin ratio diverges on the committed
owner class. This is scoped to the proposed variational mechanism.

## 2. Decision

The recommended Route-A subroute is:

```text
A-V  owner-preserving constrained variational selector
```

The selector should minimize a proved physical derivative energy in the
finite feasible fibre, subject to the existing finite Mellin interpolation
constraints and a separately stated admissible sign/phase cone. The cone may
use only owner data and independently proved kernel inequalities; it may not
contain the missing residual budget as an assumption.

The intended proof shape is:

```text
finite Mellin constraints + owner geometry
                 |
                 v
      minimum-energy physical correction
                 |
       dual certificate / representer
                 |
                 v
      explicit derivative-cost bound
                 |
                 v
       grouped signed residual margin
```

This changes the mechanism that was killed in record 1926. It does not merely
add another residual certificate field.

## 3. Why A-V is the best probe

The current classical interpolation selector is blocked because finite node
values do not control the physical profile or its derivative cost. Record 1929
adds a minimum Euclidean coefficient selector, but it still has no uniform
physical-cost bound and no sign information. A-V attacks both missing links
at once while preserving the real owner.

The alternatives are lower priority:

```text
A-C  keep repairing the current selector
     rejected: record 1926 already gives a scoped final-sign no-go.

A-W  window-track theorem alone
     useful for COVER, but it does not prove the signed margin.

A-P  phase/variation-only selector
     possible fallback, but it lacks a priced physical norm and dual object.
```

A-W remains a supporting experiment, not the producer subroute.

## 4. First decisive probe

Before Lean, instantiate the finite owner data from the committed Route-A rig
and solve the finite constrained quadratic problem using exact owner labels.
The probe must report:

```text
feasible or infeasible;
minimum physical derivative cost;
grouped residual value;
margin ratio = available signed margin / derivative cost;
conditioning and active constraints.
```

The probe is not allowed to replace the continuum proof. It has one purpose:
kill A-V cheaply if the finite owner already violates the cost budget, or
identify an explicit constant and active-set pattern for the smallest theorem.

Pre-registered interpretation:

```text
A-V-GO        feasible with a positive margin on every registered owner,
              stable under the prescribed interval/precision checks;
A-V-NO-GO     infeasible, nonpositive margin, or budget ratio diverges;
A-V-UNRESOLVED numerical conditioning or owner mismatch prevents a verdict.
```

## 5. Proof decomposition if the probe survives

1. Prove existence and uniqueness of the owner-preserving minimizer in the
   finite-dimensional source space.
2. Prove a representer/duality identity for the physical derivative energy.
3. Bound the dual coefficients from the actual owner geometry, not from a
   fixed-prime or ROOT surrogate.
4. Prove the grouped signed residual inequality with an explicit epsilon.
5. Only then address the all-rho window-track/COVER theorem.

The order matters: a window theorem without a producer inequality does not
remove the binding premise, and a numerical minimizer without a dual bound is
not proof progress.

## 6. Scope and honesty

A-V is the most promising Route-A subroute for the next bounded experiment,
not a demonstrated RH path. COVER remains open. Route B remains a structural
backup, and Route C remains audit-only. No RH claim is made.

References:

- `route/000_rh_mainline/002_b5_compactlog/001_route_a_signed_kernel/README.md`
- `docs/proofs/1926_route_a_final_sign_current_selector_no_go.md`
- `docs/proofs/1929_route_a_finite_basis_minimum_selector.md`
- `docs/proofs/1998_cover_strategy_desk.md`