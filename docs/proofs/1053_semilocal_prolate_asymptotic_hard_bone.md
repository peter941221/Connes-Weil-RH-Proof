# 1053 - Semilocal prolate asymptotic hard-bone verdict

Date: 2026-08-29.  Follows 1050--1052.

Status:

```text
NO-GO: fixed-cutoff exact positive readback from the current C1
       metric-projection / canonical-window owner.

ALIVE: a non-translation-invariant semilocal prolate family whose positive
       cross-spectral energy is read only after an asymptotic limit.

UNPROVED: the required first phase-correction and common-domain convergence.
RH is not claimed.
```

## 1. The Decision Boundary

The detector-selected finite-S problem is the real RH-level obstruction.  It
cannot be repaired by another estimate on the active projection response.

```text
fixed-S Euler factor + positive metric projection
                  |
                  +-- p^2 principal coefficient is a^2, not a^2 / 2
                  |   (proofs 042 and 1051)
                  |
                  +-- canonical window-to-response defect has unbounded
                  |   real trace for every nonzero test (proof 1052)
                  |
                  `-- NO-GO

positive translation multiplier / Poisson mixture
                  |
                  +-- exact a^m / m coefficients force identity bulk
                  +-- a square-factor trace loses linear prime readback
                  `-- NO-GO (proofs 111, 116, 131, 207)

semilocal prolate cross-spectral family, lambda -> infinity
                  |
                  +-- no fixed-cutoff Dirac readback is requested
                  +-- no existing counterexample covers its two-cutoff,
                  |   non-multiplier geometry
                  `-- only remaining go-shaped construction
```

The last line is not a proof that the construction works.  It is the exact
uneliminated class after the fixed-S candidates have been screened.

## 2. Why The Asymptotic Family Has The Right Arithmetic Slot

For a finite place set S containing infinity, CCM24 uses the spectral measure

```text
dm_S(s) = dm_infinity(s) * product_(p in S_f)
  |1 - p^(-1/2) exp(i s log p)|^(-2).
```

For one prime, write a = p^(-1/2) and L = log p.  Its logarithmic weight is

```text
log(dm_{infinity,p} / dm_infinity)
  = -log |1 - a exp(i L s)|^2
  = sum_(m >= 1) a^m/m *
      (exp(i m L s) + exp(-i m L s)).                 (2.1)
```

Thus the Euler denominator `1/m` occurs before any boundary crossing has been
read.  Differentiating the phase in a trace formula supplies the corresponding
`log p`; this is the only known way here to avoid the metric projection's
second-prime-power coefficient error.

CCM24's candidate is the prolate operator of the semilocal cyclic pair
`(Scaling, xi_S)`.  In the paper's notation its formal expression is

```text
W_(lambda,S) = -Scaling^2 + 2*pi*lambda^2*(4*N_S + 1) - 1/4.            (2.2)
```

Here `N_S` is the orthogonal-polynomial grading for `dm_S`.  This changes the
owner before scalar Euler scattering is extracted; it is not the rejected
Gram-corrected projection `T R (R T* T R)^(-1) R T*`.

For a proved self-adjoint realization and its spectral projections
`Pi_-(lambda,S)` and `Pi_+(lambda,S)`, the candidate positive quantity is

```text
Pos_(lambda,S)(g)
  = || Pi_-(lambda,S) * C_S(g) * Pi_+(lambda,S) ||_HS^2 >= 0.          (2.3)
```

It has no diagonal rank bulk.  At every finite lambda its translation kernel
is continuous, so it cannot exactly equal the discrete prime-power
distribution.  The readback must therefore be asymptotic, not a fixed-cutoff
identity.

## 3. The One Theorem That Decides This Route

The route needs a theorem with all four parts below on one fixed compact test
g and one fixed finite visible place set S.

```text
P0. A self-adjoint realization of W_(lambda,S), with usable positive and
    negative spectral projections.

P1. Pi_- C_S(g) Pi_+ is Hilbert--Schmidt, and its trace calculation is legal
    on the same source test used by the explicit formula.

P2. The first non-bulk asymptotic correction of (2.3) is linear in (2.1).
    Term m must therefore produce exactly a^m/m before the crossing geometry
    contributes m log p.

P3. On the common Weil-form domain,

      Pos_(lambda,S)(g)
        = QW_smooth,(lambda,S)(g,g) + R_(lambda,S)(g),

    QW_smooth,(lambda,S)(g,g) -> QW_S(g,g),
    R_(lambda,S)(g) -> 0.
```

P2 and P3 are the hard mathematics.  Their conclusion would turn the positive
quantity (2.3) into detector-selected semilocal Weil positivity, which the
route already knows how to consume into SourceRH.

The first falsifiable subproblem is deliberately narrower than P2:

```text
P2a. For S = {infinity, p}, differentiate the cross-spectral trace at the
     base log-weight in the direction 2 cos(L s).  Prove or disprove that its
     lambda -> infinity limit is the one-crossing functional at displacement L.
```

If P2a has the wrong coefficient, a surviving route is killed without building
a new Lean owner. If it has the right coefficient, it only passes the first
necessary test. The quadratic response of the first harmonic can still alter
the `p^2` one-crossing coefficient. Proof 1054 names the mandatory P2b
cancellation test before any summation over `m` or finite product over visible
primes is attempted.

## 4. Required Kill Tests

Any proposed proof of P2--P3 must pass these exact checks before formalization.

```text
1. Prime-square coefficient:
   m = 2 gives a^2/2 before the length 2 log p is read.

2. Support-gap test:
   if the convolution square vanishes at +/- m log p, no positive leftover
   may remain merely because a factorization crosses a half-line.

3. Bulk test:
   no canonical-window defect is asserted to converge to zero against a fixed
   response; proof 1052 rules that out.

4. Same-owner test:
   the positive operator, the Euler phase, the Gamma/pole terms, and the
   limiting Weil form all use the same g and the same finite S.
```

## 5. What The Sources Do And Do Not Supply

The primary papers support the setting, not P2 or P3.

```text
Connes--Consani (2020/2021):
  proves the archimedean comparison on the short support window only.
  https://arxiv.org/html/2006.13771

Connes--Consani (2019/2021):
  formulates the semilocal positivity problem as Conjecture 4.1 and explains
  why the simple positive-projection attempt fails.
  https://arxiv.org/html/1910.14368

Connes--Consani--Moscovici (2023/2024):
  proves Sonin-space stability and constructs the semilocal cyclic pair, but
  calls the prolate construction a candidate and leaves its domain delicate.
  It proves neither the fixed-test positive trace inequality nor the
  finite-S remainder sign.
  https://arxiv.org/html/2310.18423
```

Known general asymptotic tools do not close the gap.  The papers on periodic
unbounded Jacobi matrices provide leading generalized-eigenvector/density
asymptotics, and bulk Christoffel--Darboux universality gives leading local
kernel behavior.  P2 needs the first global phase correction for the specific
Gamma weight multiplied by the Euler factors, inserted into a cross-spectral
Hilbert--Schmidt trace.  That statement is stronger than the available input.

```text
Swiderski--Trojan, periodic unbounded Jacobi asymptotics:
  https://arxiv.org/abs/1602.06273

Swiderski, density formulas for periodic unbounded Jacobi matrices:
  https://arxiv.org/abs/1602.06728

Eichinger--Lukic--Simanek, bulk CD universality:
  https://arxiv.org/abs/2108.01629

Yafaev, trace-class Jacobi scattering:
  https://arxiv.org/abs/1711.05029
```

The 2026 finite Guinand--Weil work gives a useful finite certification
framework, but explicitly makes no RH claim and does not prove P2/P3 for all
compact tests:

```text
https://arxiv.org/abs/2607.02828
```

## 6. Verdict

```text
The current C1 projection-square semilocal owner is mathematically dead.

The semilocal prolate asymptotic family is not dead, but it is not yet a
feasible theorem: P2a is a necessary first-order experiment and P2b is the
first coefficient-complete mathematical gate. P2--P3 remain a new RH-level
analysis problem.

Do not add a conditional Lean producer for this family before P0, P1, and P2b
are proved.
```
