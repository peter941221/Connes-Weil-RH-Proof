# Record 1704 — finite source-Schur leg is invertible

## Result

The finite visible-prime source-side Schur leg in the G8 survivor coframe is
an algebraic unit:

`g8SurvivorSourceLeg_isUnit`

in `C1G8R3SurvivorCoframeBridge.lean`.

## Evidence

The forward source transition product and the reverse transition product are
proved to multiply in both orders to the same positive Schur–Markov scalar.
The scalar is nonzero by `suffixEulerSchurMarkovScalar_pos`.  The two Gram
inverse-square-root factors are units by the existing fixed-source polar
theory, and the adjoint of a unit is a unit.  Thus the complete coframe
source leg is invertible for every finite visible-prime family.

The paired Dev/Audit build completed successfully with zero `error:` lines and
no `sorryAx`; the Audit declarations use only the standard three axioms.

## Route effect

This closes the algebraic transport question in WO-S: the Schur coframe does
not hide a kernel or lose a source direction.  It does not prove the S3
square-summability estimate.  The remaining analytic obligation is the
in-Sonin square-sum for the transported root operator, now with an explicit
bounded inverse available for bidirectional comparison.

Classification: formal, machine-checked algebraic reduction; no RH claim.
