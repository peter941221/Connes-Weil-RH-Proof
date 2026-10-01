2347 - One-sided chord-panel integral bound

Date: 2026-10-01.

Purpose

The 2342 external certificate adds a panel charge to sampled complex magnitudes.
This record formalizes the mathematical implication behind that charge, without
differentiating a complex modulus or assuming the source has no zeros.

Definitions

A norm is the length of a value; for a complex value it is its distance from
zero in the plane. A chord is the straight line connecting two endpoint values.
The curvature budget M bounds the norm of the second derivative, rather than
the second derivative of the norm. These are different objects: F(x)=x+i*eps
has F second derivative zero but the norm has positive second derivative.

Let a<b be the cell ends, h=b-a, and let F be twice continuously differentiable.
If norm(F second derivative) <= M on the cell, the theorems derive

```text
norm(F(x)) <= (b-x)/h * norm(F(a)) + (x-a)/h * norm(F(b))
              + (M/2) * (x-a) * (b-x)

int_a^b norm(F) <= h/2 * (norm(F(a)) + norm(F(b))) + M*h^3/12

int_a^(a+n*h) norm(F) <= compositeTrap + h^2 * (n*h) * M/12
```

Mechanism and prior method

For each point, the existing Mathlib Hahn-Banach lemma exists_dual_vector
(with its double-prime variant) supplies a real continuous linear projection
whose norm is at most one and whose value on F(x) equals norm(F(x)). A projection
measures a component along a chosen direction; it never increases length.
For complex values, this is the supporting direction used by the 2341 paper
argument. The general normed-space proof also handles the zero value.

The projected second derivative is at least -M. Adding (M/2)*x^2 makes its
second derivative nonnegative, so the projected function becomes convex, meaning
it stays below its endpoint chord. Subtracting the quadratic gives the pointwise
bound. An explicit polynomial primitive proves the cell integral and its exact
1/12 constant. Adjacent interval integrals then assemble the uniform-grid bound.

The projection and convexity steps use existing Mathlib theorems; they are not
claimed as an original RH mechanism. The new work is their checked assembly
into the precise one-sided bound required by this evaluator.

Validation

Focused Linux Lake build completes 3711 build-plan jobs. Six audited theorem
leaves have exactly [propext, Classical.choice, Quot.sound], and the new source
has no warnings. Both Lean files match the Linux mirror by SHA-256. The unchanged
2341 panel selftests pass 11/11; they test the numerical instrument, not the
Lean proof or certificate import. The finite-node interface also proves that
individual node upper bounds can replace exact node magnitudes in the sum.

Evidence: results/2347_chord_panel_validation.json,
build-logs/2347_chord_panel_build_final.log, and
build-logs/2347_panel_regression.log.

The early grid-assembly timeout was a coercion mismatch, not a costly proof:
the integral theorem needed the real cast of the natural successor, whereas
the supplied endpoint was the real successor of a cast natural. Explicit
successor casting resolves it at the default heartbeat budget. No increased
heartbeat option remains.

Proof boundary

This is only an upper integral bound, not a two-sided quadrature error bound.
Smoothness and the actual derivative bound remain explicit analytic premises.
The norm theorem is general and hence applies to complex-valued sources. The
2346 whole-line second-derivative identity is available separately, but the
2342 derivative ladder bound, exact repaired coefficient realization, executed
Arb nodal semantics and numeric endpoint facts are not imported by this theorem.
There is no detector instantiation, signed-kernel completion, producer GO or RH.

Next steps

1. Apply the theorem to the actual weighted base and correction source, including
   the second-derivative norm channel. Derive its curvature budget from the same
   source derivative ladder. Completion is a theorem with no owner substitution.

2. Certify each finite node upper bound and the exact coefficient realization,
   then assemble the two endpoint integral facts. The grid must be the exact
   rational grid, not an uncharged binary64 linspace. Completion is a checked
   bridge from the finite certificate to those actual integrals.

3. Use those facts in the existing same-owner norm consumer, then resume the
   selected detector signed physical-kernel budget. The unsigned norm lane does
   not establish the selected Weil sign and cannot alone prove RH.
