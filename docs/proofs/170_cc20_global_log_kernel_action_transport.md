# Proof 170: global logarithmic regular-kernel action transport

## Result

Good route-level infrastructure, but not an RH proof.

The ordinary CC20 regular kernel on a finite multiplicative window is now
identified with one global continuous log-kernel restricted to the matching
logarithmic interval.  For continuous inputs, the source Haar action and the
Lebesgue log-coordinate action are equal on the same test and evaluation
point.

## What is proved

`GlobalLogKernel.lean` defines:

```text
cc20GlobalLogComplexRegularKernel : C(R x R, C)
cc20GlobalLogComplexRegularProfile : C(R, C)
cc20GlobalLogComplexRegularProfile_eq_abs_exp
cc20GlobalLogComplexRegularKernel_eq_profile
cc20GlobalLogComplexRegularKernel_translation_invariant
cc20GlobalLogComplexRegularKernel_swap
cc20GlobalLogComplexRegularProfile_neg
cc20WindowComplexRegularKernel_eq_logKernel
cc20WindowLogRestriction
cc20GlobalLogWindowRegularAction
cc20GlobalLogWindowRegularAction_eq_profile
cc20WindowSourceHaarAction_eq_globalLogWindowRegularAction
```

The global kernel is obtained by evaluating the genuine positive-coordinate
`cc20RegularKernel` at `(exp t, exp s)`.  The finite-window kernel is shown to
be the same value at `(log rho, log eta)` using `exp(log rho)=rho` on the
positive subtype; no fixed `[1/2,2]` wrapper or alternate kernel is used.

Lean also proves the convolution-coordinate identity and simultaneous
translation invariance:

```text
K(t,s) = k(t-s)
K(t+a,s+a) = K(t,s).
k(-r) = k(r).
k(r) = QDeltaRegularExtension(exp(|r|)).
```

Thus the whole-line object must be treated as a convolution operator and the
finite-window objects as compressions `P_lambda K P_lambda`.  The theorem does
not falsely promote the whole-line kernel to a Hilbert--Schmidt kernel.
The explicit `exp(|r|)` formula reduces the next boundedness question to a
one-variable large-`rho` decay estimate for the genuine Q-delta profile.

For a continuous `u : C(R,C)` and a log-window point `t`, Lean proves:

```text
cc20WindowSourceHaarAction lambda hlambda
  (cc20WindowLogRestriction lambda hlambda u)
  (cc20LogWindowExpPoint lambda hlambda t)
  = cc20GlobalLogWindowRegularAction lambda t u
```

The proof proceeds in three explicit steps:

```text
finite-window kernel action
  = Haar integral of the global log integrand
  = interval integral after rho = exp(s)
  = global log-window action
  = integral_[-log lambda,log lambda] k(t-s)u(s) ds.
```

## Verification

The Windows source snapshot was synchronized to the retained WSL2 ext4
mirror without copying `.lake`.  The import-facing audit passed:

```text
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

The audit checks the new declarations and reports only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, RH premise, Weil-positivity premise, or stored action
conclusion.

## Remaining bottom

This is still only a continuous-input action identity.  It does not yet define
the global bounded/compact operator on `Lp C 2 volume`, prove compatibility of
the finite-window operators with the log projections, or establish a common
domain exhaustion.  The active mathematical obligations remain uniform control
of the three-point bad space, the diagonal `-2 Dirac_0 -> -2 Id` form identity,
and the same-test CC20 trace read-off.  RH remains unproved.
