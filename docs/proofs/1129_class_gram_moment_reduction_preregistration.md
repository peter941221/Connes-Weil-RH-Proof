# Record 1129: class-Gram moment reduction preregistration

Date: 2026-09-04.

Consumer: the healthy-`CompactLog`, B5-shaped detector-specific semi-local
chain, through the class-window `Hbox-G` input consumed by
`C1T2Assembly`.  This record addresses only the true-data Gram side of that
input.

## 1. Motivation

Records 1127 and 1128 leave 20 independent same-parity upper-triangle Gram
integral bounds.  The class-window core is a polynomial times the even bump

```text
b(x) = expNegInvGlue (1 - x^2),
w(x) = b(x)^2.
```

For the unit scale, every same-parity product of the first eight Legendre
polynomials is an even polynomial.  The next certificate should therefore
not treat the 20 entries as unrelated numerical constants.

## 2. Registered targets

1. Define the unit bump weight and its real moments
   `I_n = ∫ x, x^n * w(x)`.
2. Prove the odd-moment vanishing by exact reflection of the integral.
3. Prove, for every natural `k > 0`, the exact recurrence

   `k I_(k-1) - (2 k + 8) I_(k+1) + (k + 4) I_(k+3) = 0`.

   The proof uses the derivative of
   `x^k (1 - x^2)^2 w(x)`.  The factor `(1-x^2)^2` cancels the inverse-square
   derivative of the flat exponential branch, while compact support removes
   the boundary term.
4. Expose a consumer-facing reduction statement saying that future true
   same-parity Gram bounds may be supplied through the two base even moments
   `I_0` and `I_2`, with the polynomial coefficient calculation kept in Lean.

## 3. Integrity and scope

The recurrence is an exact analytic identity, not a fitted relation.  No
quadrature, floating-point interval, stored Gram value, endpoint widening,
`Hbox`, M-side bound, `(iv)` defect estimate, detector-specific positivity,
`SourceRH`, or RH theorem is claimed here.  The two base-moment interval
certificates remain a subsequent true-data task.

## 4. Acceptance gates

G1. The owner and paired audit build through the resource runner with the
success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every audited declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The derivative identity is proved from the actual `classBump` object and
the Mathlib flat-exponential derivative API; no derivative is postulated.

G4. Staged-diff hygiene finds no private paths, generated build artifacts,
or hidden proof terms.

RH NOT claimed.

## 5. Post-run addendum (2026-09-04, after build 16)

VERDICT: LANDED.

The preregistration commit `43bc633` preceded the implementation.  The
moment-reduction module and paired audit landed through the implementation
commit `e838008` and subsequent root-cause/style fixes through `e20e60c`.
The final focused build log is `build-logs-1129_build16.log`:

- `Build completed successfully (3657 jobs)`;
- 0 lines matching `^error:` and 0 `sorryAx` occurrences;
- 0 warnings attributable to either 1129 module;
- all 9 audited declarations have the unique axiom set
  `[propext, Classical.choice, Quot.sound]`.

The landed content proves odd-moment cancellation, the exact four-term
integration-by-parts recurrence, and the even-step form reducing all future
even moments to `I_0` and `I_2`.  It does not certify either base moment or
close `Hbox-G`; the next true-data brick is the rigorous interval certificate
for those two base moments.  RH remains unclaimed.
