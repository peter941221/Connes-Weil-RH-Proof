# Proof 404: relative-trace cocycle Lean owner

Date: 2026-07-18

Status: Lean ownership of the noncommutative algebra introduced in Proofs
400--403.  The module proves that a cyclic trace-like functional removes a
completed forward/reverse prefix from the two-step relative numerator.  It
also proves the exact outer-minus-inner boundary expansion of the formal
nested-band first variation.

The module deliberately stores no analytic trace, trace-class, Schatten,
positivity, uniform-bound, Gate 3U, finite-`S` sign, Burnol, or RH premise.

## 1. Trace-cocycle theorem

Let `tau` be any function on a noncommutative ring satisfying

```text
tau(x+y)=tau(x)+tau(y),
tau(xy)=tau(yx).                                   (LO2.1)
```

For two paired Schur steps, Proof 399 gives

```text
N_12=G_1N_2R_1+N_1rho_2.                         (LO2.2)
```

If

```text
R_1G_1=rho_1,                                    (LO2.3)
```

Lean proves

```text
tau(N_12)=tau(N_2rho_1)+tau(N_1rho_2).           (LO2.4)
```

Equation `(LO2.4)` is the two-step formal owner of Proof 400 `(TC.6)--(TC.8)`.
Iteration gives the full finite cocycle collapse.  Analytic use of `(LO2.1)`
still requires Proof 398's local trace-class factorization.

## 2. Nested boundary theorem

The module defines

```text
projectionVariation(P,U,V)
 =(I-P)UP+PV(I-P).                                (LO2.5)
```

For arbitrary ring elements `E,R,U,V`, Lean proves

```text
projectionVariation(E,U,V)-projectionVariation(R,U,V)

 =(I-E)U(E-R)+(E-R)V(I-E)
  -(E-R)UR-RV(E-R).                               (LO2.6)
```

Taking `V=U*`, `R<=E`, `B=E-R`, and `C=I-E` gives Proof 403 `(NV.4)`.  The
ring theorem is stronger than the projection specialization: no hidden
idempotence, nesting, or adjoint assumption is used in the expansion.

## 3. Owner boundary

```text
+-----------------------------------------------+---------------------------+
| theorem                                       | ownership                 |
+-----------------------------------------------+---------------------------+
| two-step trace-cocycle collapse               | Lean ring theorem        |
| nested two-boundary variation                 | Lean ring theorem        |
| local `S_1` legality                           | Proof 398 mathematics    |
| complete CC20 first-variation estimate         | absent / open            |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```

The implementation lives in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRelativeTraceCocycle.lean
```

The focused audit prints the axioms of both public theorems.  It is run once
with the four numerical probes and the `CCM25Concrete` aggregate after the
five-proof batch is complete.

## 4. Route consequence

The active near theorem is no longer an operator-valued `rho_n` estimate.
Proof 403's ring identity concerns simultaneous ambient transport and is not
the fixed-quotient route owner.  Proof 405 supplies the corrected quotient
first jet and reduces its legal scalar to the reflected second-support and
prolate-root branches.  Their signed uniform estimate, followed by the
quadratic/higher-channel estimate, remains open.  No branch may be placed
under an absolute value before that recombination.
