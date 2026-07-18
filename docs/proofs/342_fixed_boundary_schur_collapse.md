# Proof 342: fixed-boundary Schur collapse

Date: 2026-07-18

Status: exact reduction of Proof 341's two-copy Burnol boundary Gram to one
causal quotient-crossing Gram.  One transported Burnol boundary column has
exactly the same range as its source column; eliminating that column before
taking a trace leaves a single Gram-corrected projection on the orthogonal
quotient.

This removes one inverse-after-average channel.  It does not bound the
remaining quotient Gram uniformly in the finite Euler set.  Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+--------------------------------------------------+-------------------------+
| layer                                            | judgment                |
+--------------------------------------------------+-------------------------+
| transported Burnol complement                   | Proof 341 exact owner   |
| reflected boundary column                       | fixed range             |
| fixed-column Schur elimination                  | exact                   |
| remaining frame                                 | one quotient crossing   |
| complete endpoint response                      | one relative Gram trace |
| uniform compact-root estimate                   | open                    |
| Gate 3U / RH                                     | open / unproved         |
+--------------------------------------------------+-------------------------+
```

The reduction is

```text
two transported Burnol columns
  -> reparameterize the reflected column without changing its range
  -> split off its fixed orthogonal projection
  -> one quotient-causal crossing frame
  -> one inverse Gram, still after the complete Euler product.       (FC.1)
```

No path sector, canonical term, or trace anomaly is discarded in `(FC.1)`.

## 2. Source boundary and causal transport

Let `J:H_0 -> H` be the isometric Burnol-window inclusion and put

```text
P=J J*,
mathcalF*=mathcalF,
mathcalF^2=I,
Q=mathcalF P mathcalF.                                (FC.2)
```

Here `P` is the Burnol source-window half-line.  It is Proof 256's invariant
one-sided half-line (called `C` there), not the route band projection called
`E` in Proofs 256 and 262.  The different letter prevents those two roles
from being silently identified.

Burnol's complement synthesis map is

```text
mathcalA=[J,mathcalF J]:H_0 direct-sum H_0 -> H.       (FC.3)
```

Let

```text
V=T_S^(-1).                                           (FC.4)
```

The one-sided CCM24 orientation gives both

```text
V Ran(P)=Ran(P),
mathcalF V mathcalF=V*.                               (FC.5)
```

The first equality includes invertibility of the restriction

```text
v_E=J* V J:H_0 -> H_0.                                (FC.6)
```

The second equality is the Mellin reflection of the causal Euler product.
It is stronger than commutation of the symmetric metric `V V*` with
`mathcalF` and keeps the one-sided orientation which Proof 263 requires.

## 3. One transported column is only reparameterized

Proof 341 uses the transported complement frame

```text
V* mathcalA=[V*J,V*mathcalF J].                       (FC.7)
```

By `(FC.5)--(FC.6)`,

```text
V*mathcalF J
 =mathcalF V J
 =mathcalF J v_E.                                     (FC.8)
```

Since `v_E` is invertible,

```text
Ran(V*mathcalF J)=Ran(mathcalF J)=Ran(Q).              (FC.9)
```

Right multiplication of `(FC.7)` by
`diag(I,v_E^(-1))` changes only frame coordinates.  Hence the transported
complement has the same range as

```text
mathcalK_S=[V*J,mathcalF J].                          (FC.10)
```

This is the missing simplification in the raw two-copy moment formula of
Proof 341: the second averaged Gram block is not a second moving geometric
degree of freedom.

## 4. Orthogonal Schur elimination

Define the quotient-crossing frame

```text
L_S=(I-Q)V*J,
Sigma_S=L_S*L_S
       =J*V(I-Q)V*J.                                  (FC.11)
```

The range of `L_S` is orthogonal to `Ran(Q)`.  The strict Burnol angle and
invertibility of `V` imply that `L_S` is injective with closed range, so
`Sigma_S` is positive and invertible on `H_0`.  Equations `(FC.9)--(FC.11)`
give the orthogonal direct sum

```text
Ran(V*mathcalA)
 =Ran(Q) orthogonal-direct-sum Ran(L_S).               (FC.12)
```

Therefore Proof 341's transported complement projection is exactly

```text
C_S
 =Q+L_S Sigma_S^(-1)L_S*.                             (FC.13)
```

At the source endpoint put

```text
L_0=(I-Q)J,
Sigma_0=L_0*L_0=I-F_0^2,
F_0=J*mathcalF J.                                     (FC.14)
```

Burnol's `norm(F_0)<1` proves the inverse in `(FC.14)` is legal, and

```text
C_0=I-R
   =Q+L_0 Sigma_0^(-1)L_0*.                           (FC.15)
```

Subtract `(FC.15)` from `(FC.13)` before inserting a detector:

```text
C_S-C_0
 =L_S Sigma_S^(-1)L_S*
  -L_0 Sigma_0^(-1)L_0*.                              (FC.16)
```

The infinite fixed projection `Q` cancels as an operator.  No separate
quantity `Tr(WQ)` is defined or used.

## 5. Complete Gate response on one boundary copy

Let `W=C_xi* C_eta` be Proof 263's compact-root detector.  Under Proof 261's
fixed-S root-sandwiched trace legality, rectangular cycling in the completed
difference `(FC.16)` gives

```text
Q_S(eta,xi)
 =Tr_(H_0)[
    Sigma_S^(-1)L_S* W L_S
   -Sigma_0^(-1)L_0* W L_0].                          (FC.17)
```

Equation `(FC.17)` equals Proof 341 `(BY.10)`.  It is not a new surrogate:
both are the trace of `W(C_S-C_0)` for the same transported Sonin
projection.

The full inverse remains after the complete Euler product inside
`Sigma_S`.  What has changed is its carrier:

```text
two-copy Burnol boundary Gram
  -> one-copy physical quotient crossing Gram.        (FC.18)
```

## 6. Explicit causal quotient form

Use `I-Q=mathcalF(I-P)mathcalF` and `(FC.5)` in `(FC.11)`:

```text
L_S
 =mathcalF(I-P)V mathcalF J
 =mathcalF[(I-P)V(I-P)](I-P)mathcalF J.               (FC.19)
```

The second equality uses causality, `(I-P)VP=0`.  Thus, with

```text
V_C=(I-P)V(I-P)|_(Ran(I-P)),
H_0=(I-P)mathcalF J,                                  (FC.20)
```

one has

```text
L_S=mathcalF V_C H_0.                                 (FC.21)
```

So the remaining inverse is not an arbitrary inverse of an averaged
two-state model.  It is the Gram inverse of the actual one-sided Euler
quotient acting on the fixed Burnol crossing `H_0`.  Proof 254's direct-sum
guard does not have this quotient-half-line factorization.

## 7. Literature boundary

After Mellin diagonalization, `(FC.17)` resembles a relative
Wiener--Hopf-plus-Hankel determinant.  Existing smooth-symbol determinant
theorems do not directly close it:

```text
Ehrhardt--Virtanen, A survey of asymptotics of determinants for
structured matrices, arXiv:2407.21222
https://arxiv.org/abs/2407.21222

Basor--Ehrhardt, On the asymptotics of certain
Wiener--Hopf-plus-Hankel determinants, NYJM 11 (2005), 171--203
https://nyjm.albany.edu/j/2005/11-10.pdf
```

Those formulas require a Wiener--Hopf factorization with trace-class Hankel
products for a specified smooth or Fisher--Hartwig symbol.  The Euler symbol
here is a finite almost-periodic product with atomic prime-log frequencies,
and the legal object is the root-sandwiched relative derivative `(FC.17)`.
No cited theorem supplies an `S`-uniform trace-class relative kernel or the
polynomial compact-support ledger.

The source evidence is useful only after `(FC.17)` is identified with the
theorem's actual operator.  Importing a strong Szego constant without that
identification would repeat Proof 340's owner mismatch.

## 8. Exact remaining theorem

For roots supported in `[-B_root,B_root]`, it now suffices to prove

```text
sup_(finite S)
 abs Tr_(H_0)[
   Sigma_S^(-1)L_S* C_xi* C_eta L_S
  -Sigma_0^(-1)L_0* C_xi* C_eta L_0]

 <=C(1+B_root)^d
   norm(eta)_(H^r) norm(xi)_(H^r).                   (FC.22)
```

The proof must use `(FC.19)--(FC.21)` before an absolute value.  Bounding
`Sigma_S^(-1)`, the two terms in `(FC.17)`, or the Euler factors separately
recreates the rejected condition number or total-variation estimate.

Proof 336 may be inserted only after `(FC.22)` is split into compact
displacements and the fixed-source far tail.  It does not control the near
quotient inverse by itself.

## 9. Finite algebra certificate

The companion probe uses a finite causal shift, a reflection involution, and
an invariant source half-space.  It verifies `(FC.8)--(FC.17)` by comparing
the direct transported-frame projection with the fixed-column Schur formula.
This checks the algebraic ordering only; it is not evidence for `(FC.22)`.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/342_fixed_boundary_schur_collapse_probe.py
```

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 341 full endpoint owner                  | retained                  |
| reflected boundary range                       | exactly fixed             |
| fixed-column cancellation                      | exact before trace        |
| one quotient-causal Gram owner                 | exact                     |
| generic BOGC / strong Szego import             | no matching contract      |
| uniform signed quotient estimate `(FC.22)`     | open, Gate 3U             |
| finite-S sign / Burnol identity / RH           | open / open / unproved    |
+------------------------------------------------+---------------------------+
```
