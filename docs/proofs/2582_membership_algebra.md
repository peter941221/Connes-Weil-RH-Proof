# Record 2582: bounded-inverse membership algebra

Date: 2026-10-05

Status: FORMAL-MEMBERSHIP-ALGEBRA-PASS.

This record adds the reusable algebraic bridge needed by the 2338 owner
transfer. If A is a bounded linear operator, X is a bounded left inverse,
A coefficient equals the target, and the center residual is bounded, then the
coefficient distance is bounded by the operator norm of X times the residual.

The theorem is:

    X A = id
    A coefficient = target
    norm(target - A center) <= residual
    ------------------------------------------------
    norm(coefficient - center) <= norm(X) * residual

The proof uses only linearity, the left-inverse identity, and the operator norm
bound. It imports no numerical data and does not assume the 2338 matrix
certificate.

## Verification

The source and audit compile in a clean Linux-side HEAD verification copy.
The audit reports exactly:

    [propext, Classical.choice, Quot.sound]

Source SHA256:

    7c84b69bf72162c4dd55b26956c03a33d39967cf4e74f50954fbc631f38880c7

Audit SHA256:

    1da687b954be795b36a16045445a3056afc31bf166e1506cde765555f22e42ff

## Scope boundary

This closes the algebraic implication only. It does not yet provide the Lean
definition of the 30 by 30 analytic matrix A, the exact analytic owner, the
left inverse X, or the certified residual bound. Therefore Lean membership,
owner transfer, producer GO, and RH remain open.

## Evidence

- ConnesWeilRH/Dev/C1RouteACorrectionMembershipAlgebra2581.lean
- ConnesWeilRH/Dev/C1RouteACorrectionMembershipAlgebra2581Audit.lean
- results/2582_membership_algebra_validation.json
