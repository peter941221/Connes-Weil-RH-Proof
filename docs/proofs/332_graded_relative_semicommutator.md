# Proof 332: graded relative semicommutator owner

Date: 2026-07-17

Status: exact symmetry correction and algebraic owner after Proof 331. This
proof replaces the rejected Helton--Howe principal-function route by a
`Z2`-graded semicommutator (graded semicommutator) which has the correct
symmetric sign. It also audits the Tang--Wang--Zheng trace formula against the
actual CCM24 compressed-metric kernel.

This does not prove the uniform analytic estimate, Gate 3U, the finite-`S`
sign, Burnol's identity, or RH. No Lean premise, route rewire, or finite-section
surrogate is introduced.

## 1. Result

```text
+--------------------------------------------------+---------------------------+
| layer                                            | judgment                  |
+--------------------------------------------------+---------------------------+
| Proof 331 distributional Q transfer             | valid                     |
| Helton--Howe principal function                  | wrong symmetry            |
| scalar Toeplitz semicommutator                   | correct symmetric owner   |
| Clifford doubled supertrace                      | exact                     |
| relative E/R grading                            | exact                     |
| support-first two-point kernel                   | exact, already Proof 301  |
| Tang--Wang--Zheng Bergman formula                | source-backed             |
| transfer to CCM24 compressed metric              | not available             |
| uniform localized relative-kernel norm           | open, Gate 3U             |
+--------------------------------------------------+---------------------------+
```

The corrected chain is

```text
actual moving E/R/K_prol response
  -> one relative graded semicommutator
  -> one relative two-point kernel distribution
  -> compact root support
  -> source-specific localized kernel estimate
  -> uniform-in-S signed bound.                         (BP.1)
```

The first three arrows are exact. The fourth arrow is the remaining analytic
theorem.

## 2. Why a principal function has the wrong sign

Let `P` be an orthogonal projection and let `W,H` be commuting self-adjoint
multipliers. Put

```text
C_P=P W(I-P)H P.                                      (BP.2)
```

The compressed Toeplitz commutator is

```text
[T_W^P,T_H^P]=C_P^dagger-C_P.                         (BP.3)
```

The completed orthogonal-flow response is instead

```text
D_P(W,H)=C_P+C_P^dagger=2 Re(C_P).                    (BP.4)
```

Helton--Howe/Carey--Pincus principal functions represent `(BP.3)`. Gate 3U
uses `(BP.4)`. Thus the principal-function arrow proposed in the first version
of Proof 331 is invalid.

## 3. Exact Clifford doubling

Write `T_P(f)=P M_f P` on `Ran(P)`. On the doubled carrier define

```text
A_W=[[0,T_P(W)], [T_P(W),0]],
B_H=[[0,T_P(H)], [-T_P(H),0]],

A_W B_H|_(symbol product)
  :=[[-T_P(W H),0], [0,T_P(W H)]].                    (BP.5)
```

Direct block multiplication gives

```text
A_W B_H-A_W B_H|_(symbol product)
  =[[C_P,0], [0,-C_P]].                               (BP.6)
```

For the grading `Gamma=diag(I,-I)`, the supertrace is therefore

```text
Str_Gamma(A_W B_H-A_W B_H|_(symbol product))
  =2 Tr(C_P).                                         (BP.7)
```

For the Hermitian diagonal detector used by Gate 3U, the legal scalar is real,
so `(BP.7)` is exactly the trace of `(BP.4)`. This is a semicommutator
supertrace, not a commutator principal function.

## 4. Relative E/R grading

For the nested pair `R<=E`, place the two compressions on a second doubled
carrier and use the relative grading

```text
Gamma_rel=diag(I_E,-I_R).                              (BP.8)
```

Applying `(BP.6)` in each block gives one relative supertrace:

```text
Str_(Gamma tensor Gamma_rel)(relative semicommutator)
  =2[Tr(C_E)-Tr(C_R)]
  =D_E(W,H)-D_R(W,H).                                 (BP.9)
```

Proofs 253, 281, 282, 301, and 323 identify `(BP.9)` with all of the following
representations of the same scalar:

```text
moving band derivative;
relative E/R Toeplitz covariance;
support-first signed two-point kernel;
recombined outer/second-support/K_prol crossing;
actual Gram-corrected finite-S moving response.        (BP.10)
```

The grading packages the signs before trace or absolute value. It does not
authorize separate trace norms of its blocks.

## 5. General reproducing-kernel trace identity

For any orthogonal projection with a legal reproducing kernel `K_P`, the
semicommutator trace is

```text
Tr(T_P(W H)-T_P(W)T_P(H))
 =1/2 doubleIntegral
    (w(x)-w(y))(h(x)-h(y))|K_P(x,y)|^2 dx dy.         (BP.11)
```

Applying the relative grading gives

```text
Tr(C_E)-Tr(C_R)
 =1/2 doubleIntegral
    (w(x)-w(y))(h(x)-h(y))
    (|K_E(x,y)|^2-|K_R(x,y)|^2) dx dy.               (BP.12)
```

Equation `(BP.12)` is Proof 301's support-first owner in graded form. The root
cross-correlation is inserted before any Euler mode split, and its support
remains inside `[-2 B_root,2 B_root]`.

## 6. Tang--Wang--Zheng audit

Tang, Wang, and Zheng prove on weighted Bergman spaces that

```text
Tr(T_f T_g-T_(f g))
 =a local first-derivative integral
  +a positive double integral of Delta f and Delta g. (BP.13)
```

Their disk formula is Theorem 1.1, equation (1.3), in:

```text
X. Tang, Y. Wang, D. Zheng,
Trace Formula of Semicommutators,
arXiv:2210.04148.
https://arxiv.org/abs/2210.04148
```

This confirms that semicommutators, rather than principal functions, have the
correct symmetry. The proof of `(BP.13)`, however, uses the explicit weighted
Bergman kernel, disk automorphisms, and integration by parts. The CCM24 kernel
is instead

```text
K_(J,S,t)(s,u)
 =tau(s)conj(tau(u))
   <(J M_|tau|^2 J)^(-1)k_(J,0,u),k_(J,0,s)>.         (BP.14)
```

The nonconstant compressed-metric inverse in `(BP.14)` has no Bergman
Möbius-invariance identity. Therefore `(BP.13)` cannot be imported as the
Gate 3U estimate. Only the universal kernel identity `(BP.11)` transfers.

## 7. Exact remaining theorem

Define the graded relative kernel distribution by testing only against compact
root correlations:

```text
<F,nu_(S,t)>
 :=doubleIntegral F(x-y)(h_(S,t)(x)-h_(S,t)(y))
    (|K_(E,S,t)(x,y)|^2-|K_(R,S,t)(x,y)|^2) dx dy.   (BP.15)
```

The required producer is

```text
abs integral_0^1 <F_(eta,xi),nu_(S,t)> dt
 <=C(1+B_root)^d
    norm(eta)_(H^r) norm(xi)_(H^r),                  (BP.16)
```

with `C,d,r` independent of finite `S`. The substitution

```text
R=E Q E-K_prol                                      (BP.17)
```

must occur inside `(BP.15)`, so the outer boundary, reflected second boundary,
two prolate interference terms, and prolate square remain one graded density.

The promising source mechanism is a graded coboundary formula: show that the
common outer/second-support histories in `(BP.15)` cancel and that the residual
is a compact-window transgression of the genuine prolate complex. Such a
formula would permit the normalized product probability law to be stopped at
the first physical boundary before one absolute value. It is not proved here.

## 8. Finite algebra check

A random complex projection with commuting real diagonal `W,H` gives

```text
graded semicommutator operator error  4.99e-16,
supertrace versus 2 Tr(C_P) error     7.22e-16,
symmetric trace readback error        0.00e+00.       (BP.18)
```

The check verifies `(BP.6)--(BP.7)` only. It is not evidence for `(BP.16)`.

## 9. Route judgment

Proof 332 closes the symmetry and ownership audit:

```text
principal function / ordinary commutator: rejected;
graded relative semicommutator:            exact owner;
Tang--Wang--Zheng Bergman formula:         correct object, wrong geometry;
relative CCM24 localized kernel bound:     open Gate 3U theorem.       (BP.19)
```

The next analytic attack should seek the graded coboundary in `(BP.17)`, not a
new endpoint determinant, a phase-only semilocal kernel, or a branchwise
Schatten estimate.
