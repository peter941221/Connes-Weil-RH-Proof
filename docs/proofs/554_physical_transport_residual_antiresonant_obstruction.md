# Proof 554: physical transport residual antiresonant obstruction

## Result

The residual-only producer is impossible at the ambient Euler level.  The
physical inverse and the normalized Schur transport have a nonzero symbol at
the antiresonant point, while the ambient loss factor vanishes there.  Thus
the Schur telescope cannot be turned into a Gate 3U estimate by estimating the
physical coframe residual separately.

This is not a no-go theorem for the complete signed raw row.  The four raw
terms may still cancel after the residual is recombined with the Schur row.

## Exact residual ledger

Let `J` be `sourceInclusion`, let `K` be the physical three-branch
commutator, and let `T_(p,S)` be `suffixEulerFrameTransition`.  If the actual
forward coframes differ from the proposed Schur coframes by

```text
Delta_S   = actualForward_S   - schurForward_S,
Delta_pS  = actualForward_pS  - schurForward_pS,
```

the endpoint coframes carry the same deltas.  Expanding the four-term ledger
from Proof 553 gives the exact residual row

```text
R_(p,S)
  = -Delta_S^dagger K J T_(p,S)^dagger
    + J^dagger K Delta_S T_(p,S)^dagger
    + T_(p,S)^dagger Delta_pS^dagger K J
    - T_(p,S)^dagger J^dagger K Delta_pS.
```

Define

```text
Phi(Delta) = J^dagger K Delta - Delta^dagger K J.
```

Then the same row is

```text
R_(p,S) = Phi(Delta_S) T_(p,S)^dagger
          - T_(p,S)^dagger Phi(Delta_pS).
```

This is the cancellation-preserving normal form.  It rules out estimating
`Delta_S` and `Delta_pS` as independent positive errors.

The source definitions establishing the inputs to this calculation are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger.lean
  CCM24FiniteSActualSchurForwardPhysicalDifference.lean
```

The first file defines the four-term row and its signed actual-minus-Schur
residual.  The second file gives the exact recurrence

```text
Delta_(p::S)
  = Delta_S * P_p + A_S * (P_p - SchurTransport_(p,S)),
```

where `P_p` is the normalized physical Euler inverse.

## One-prime obstruction

Put

```text
a = p^(-1/2),
U = translation by -log(p),
E = I - a U.
```

The repository definitions give

```text
P_p = (1-a) E^(-1),
T_p = (1+a)^(-1) E,
```

from `CCM24FiniteSCausalMarkov.lean` and
`CCM24FiniteSActualSchurCascade.lean`.

On the Fourier side, write `z` for the unit-circle multiplier of `U`.  The
two symbols are

```text
p(z) = (1-a)/(1-a z),
t(z) = (1-a z)/(1+a).
```

Therefore

```text
d(z) = p(z) - t(z)
     = [2 a z - a^2 (1 + z^2)] / [(1+a)(1-a z)].
```

At the antiresonant point `z = -1`,

```text
d(-1) = -2a/(1+a) != 0.
```

Proof 506's genuine ambient-loss square root is

```text
Q_p = s (I + U),
s = sqrt(a)/(1+a),
```

so its Fourier symbol is `q(z) = s(1+z)`, and `q(-1) = 0`.

The ratio `d(z)/q(z)` is unbounded as `z -> -1` along the unit circle.  In
particular, choose Fourier wave packets supported in an arc of radius
`epsilon` around `-1`.  On that arc, `|d|` stays bounded below by a positive
constant while `|q| <= s epsilon`.  Hence

```text
sup_f ||(P_p - T_p) f|| / ||Q_p f|| = infinity.
```

Consequently there is no bounded operator `B` satisfying

```text
P_p - T_p = B Q_p
```

on the ambient translation-invariant carrier.  This is the Douglas
obstruction (`Douglas factorization`) for the residual-only shortcut.

## Boundary of the obstruction

The actual source row contains frame restrictions, projections, the moving
boundary channel, and the commutator `K`.  Those operations can remove this
ambient channel, so the calculation does not prove that the complete raw row
has no factor through the actual two-channel co-defect.

It proves exactly what the route must preserve:

```text
Schur telescope alone                 insufficient;
physical residual alone               not Q-dominated;
complete signed raw row               still the only live target.
```

The next valid source theorem must estimate the combined row

```text
SchurFourTermRow + R_(p,S)
```

through the summed ambient-loss and moving-boundary analysis column, before
any absolute-value or primewise split.  No Gate 3U, finite-S sign, Burnol
identity, or RH conclusion follows from Proof 554.
