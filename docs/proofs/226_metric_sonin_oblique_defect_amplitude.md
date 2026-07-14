# Proof 226: metric-Sonin oblique-defect amplitude

Date: 2026-07-14

Status: the nonconstant amplitude left open by Proof 225 now has an exact
same-object operator owner and a fixed sign.  Orthogonalizing the transported
Sonin range subtracts one positive defect square from a canonical oblique
phase owner.  A Schur-complement formula proves that this defect contains two
Sonin-boundary crossings, and the internal Euler-word expansion is uniformly
geometric for `0<=alpha<=p^(-1/2)`.  CC20's smoothed-commutator theorem then
makes this negative square trace legal for every genuine compact smooth
`Q`-root.  This does not yet prove compactness of the complete nested metric
residual or its three-row sign.  No Lean owner is authorized, and RH remains
unproved.

## 1. Source metric and the exact unknown

For `S={infinity,p}`, CCM24 gives at the source endpoint on the Mellin line

```text
theta_a: f(s) |-> tau_a(s) f(s),
tau_a(s)=1-a exp(-i L s),
a=p^(-1/2), L=log(p).
```

This is the source formula at
<https://arxiv.org/abs/2310.18423v2>, original TeX lines `946--981`.
Lines `986--1019` give the dual pairing, and lines `1031--1073` say that the
entire-function vector space is unchanged while the norm changes with `S`.
For the metric flow, interpolate the same formula by

```text
tau_alpha(s)=1-alpha exp(-i L s),
0<=alpha<=a.                                           (O.1)
```

Let `P` be the orthogonal projection onto the archimedean Sonin model space on
the fixed Mellin `L2` carrier.  Write

```text
T_alpha=M_(tau_alpha),
H_alpha=T_alpha* T_alpha,
A_alpha=P H_alpha P | Ran(P).                         (O.2)
```

Since `U=M_(exp(-iLs))` is unitary,

```text
(1-alpha)^2 I <= H_alpha <= (1+alpha)^2 I.            (O.3)
```

Therefore `A_alpha` is invertible and the orthogonal projection onto the
transported Sonin range is exactly

```text
P_alpha=T_alpha P A_alpha^(-1) P T_alpha*.            (O.4)
```

This is Proof 224's metric projection.  The issue in Proof 225 was the
compressed inverse `A_alpha^(-1)`.

## 2. Oblique owner and positive amplitude defect

Define the canonical oblique projection

```text
Q_alpha=T_alpha P T_alpha^(-1).                       (O.5)
```

It is idempotent and has the same range as `P_alpha`.  Hence

```text
P_alpha Q_alpha=Q_alpha,
Q_alpha P_alpha=P_alpha.                              (O.6)
```

Put

```text
Delta_alpha=Q_alpha-P_alpha.                          (O.7)
```

Equations `(O.6)` imply

```text
P_alpha Delta_alpha=Delta_alpha,
Delta_alpha P_alpha=0,
Delta_alpha^2=0.                                      (O.8)
```

Expanding `Q_alpha=P_alpha+Delta_alpha` and its adjoint now gives the exact
orthogonalization identity

```text
Q_alpha Q_alpha*
  =P_alpha+Delta_alpha Delta_alpha*,

P_alpha
  =Q_alpha Q_alpha*-Delta_alpha Delta_alpha*.         (O.9)
```

Thus the nonconstant amplitude is not a free Hermite--Biehler factor.  It is
the negative of one named positive square.  The oblique kernel in `(O.5)` is
the source phase kernel multiplied by the explicit ratio
`tau_alpha(s)/tau_alpha(t)`; it contains no compressed inverse.

Whenever a smoothing operator `C_g` makes the displayed traces legal,
cyclicity in the Hilbert--Schmidt square gives

```text
Tr(C_g* C_g P_alpha)
 =Tr(C_g* C_g Q_alpha Q_alpha*)
   -norm(C_g Delta_alpha)_HS^2.                       (O.10)
```

The amplitude contribution therefore has a fixed nonpositive sign for every
root `g`.  This statement concerns one projection `P`; it does not order the
two amplitudes obtained from the nested Sonin and half-line projections.

## 3. Exact two-crossing Schur formula

Let `P_perp=I-P` and write the blocks of `H_alpha` as

```text
A=P H_alpha P,
C=P H_alpha P_perp,
D=P_perp H_alpha P_perp,
Sigma=D-C* A^(-1) C.                                  (O.11)
```

All diagonal blocks and `Sigma` are positive and invertible by `(O.3)`.  The
`P` block of `H_alpha^(-1)` and the block inverse formula give

```text
P H_alpha^(-1) P
 =A^(-1)+A^(-1) C Sigma^(-1) C* A^(-1).              (O.12)
```

On the other hand,

```text
Q_alpha Q_alpha*
 =T_alpha P H_alpha^(-1) P T_alpha*.                  (O.13)
```

Subtracting `(O.4)` from `(O.13)` identifies the same amplitude square as

```text
Delta_alpha Delta_alpha*
 =T_alpha P A^(-1) C Sigma^(-1) C* A^(-1) P T_alpha*.
                                                               (O.14)
```

The off-diagonal metric block is

```text
C=-alpha P(U+U*)P_perp.                               (O.15)
```

Therefore every amplitude term contains one `P -> P_perp` crossing and its
adjoint.  In particular it begins at order `alpha^2`; no single-crossing Weil
atom is hidden inside the amplitude.  This is the exact operator reason that
the dangerous one-crossing channel belongs to the oblique principal owner.

## 4. Uniform Euler-word summability

On `Ran(P)`, put

```text
V=P(U+U*)P,
norm(V)<=2.
```

Then

```text
A_alpha=(1+alpha^2)I-alpha V,

A_alpha^(-1)
 =(1/(1+alpha^2))
   sum_(n>=0) (alpha/(1+alpha^2))^n V^n.              (O.16)
```

The norm ratio is bounded by

```text
eta(alpha)=2alpha/(1+alpha^2).
```

For every prime and every interpolation parameter in `(O.1)`,

```text
eta(alpha)<=eta(1/sqrt(2))=2sqrt(2)/3<1.              (O.17)
```

Consequently the internal word count is uniformly summable, and for every
fixed nonnegative integer `r`,

```text
sum_(n>=0) n^r eta(alpha)^n < infinity                (O.18)
```

uniformly over the full interpolation interval.  Thus any polynomial growth
in the Euler word length introduced by differentiating translations is not a
new combinatorial summability obstruction.  Bounded-operator convergence in
`(O.16)` still does not prove compactness of the complete post-`Q` nested
residual by itself.

## 5. Smoothed amplitude trace legality

Let `M_g` be multiplication by the Mellin transform of one compact smooth
`Q`-root.  It commutes with `T_alpha`, `H_alpha`, and `U`.  CC20 Lemma
`quantsmooth`, original TeX lines `2087--2120` in
<https://arxiv.org/abs/2006.13771>, proves that the commutator of a Schwartz
multiplier with the Hardy half-line projection `P_0` is trace class.

The transfer to the Sonin projection `P` uses two exact CC20 identities, not a
false equality of projections:

```text
P_hat=u_infinity* (I-P_0) u_infinity,
P_0 P_hat P_0=P+K_prol,                               (O.19)
```

where `K_prol` is positive trace class; see original TeX lines `542--548` and
`1072--1103`.  Since all Mellin multipliers commute, commutators with
`P_0 P_hat P_0` reduce to commutators with `P_0`, while commutators with
`K_prol` remain trace class.  The scattering phase has polynomially bounded
derivatives, so its product with a Schwartz Mellin root remains Schwartz;
CC20 proves exactly this at original TeX lines `448--464`.

It follows that

```text
[M_g,P] is trace class,
M_g [P,U+U*] is Hilbert--Schmidt.                      (O.20)
```

For the second statement, the half-line block has the explicit smooth kernel
and the scattering-conjugate block has the same estimate; the `K_prol` terms
are trace class.  Since `C=-alpha P(U+U*)P_perp`, `(O.20)` gives `M_g C`
Hilbert--Schmidt.

The compressed inverse causes no new ideal-class premise.  Put
`M_P=P M_g P | Ran(P)`.  On `Ran(P)`,

```text
[M_P,A]
 =P[M_g,P]H_alpha P+P H_alpha[M_g,P]P,

[M_P,A^(-1)]
 =-A^(-1)[M_P,A]A^(-1).                              (O.21)
```

Therefore

```text
P M_g P A^(-1)C
 =A^(-1)P M_g C+[M_P,A^(-1)]C,

P_perp M_g P A^(-1)C
 =[M_g,P]P A^(-1)C.                                  (O.22)
```

Both displayed terms are Hilbert--Schmidt, so
`M_g P A^(-1)C` is Hilbert--Schmidt.  Multiplying by the bounded factors in
`(O.14)` shows that
`M_g Delta_alpha Delta_alpha* M_g*` is trace class; equivalently
`M_g Delta_alpha` is Hilbert--Schmidt.  This makes `(O.10)` legal.  The bounds
are uniform on `0<=alpha<=p^(-1/2)` because `(O.3)` is uniformly bounded away
from zero there.

Thus the amplitude's post-`Q` contribution is a genuine finite nonpositive
quadratic form on every selected smooth root.  This does not construct one
compact bounded operator on the pre-root `L2` completion, and it does not order
the Sonin and half-line defect squares in the nested residual.

## 6. Relation to Proof 225

Proof 225 computes the fixed-frequency triangular response arising from the
phase kernel.  Formula `(O.9)` now fixes the missing organization:

```text
oblique phase owner Q_alpha Q_alpha*
  - positive two-crossing amplitude defect
  = exact orthogonal metric projection P_alpha.       (O.23)
```

Termwise fixed-`q` compactness must not be summed before this cancellation is
organized.  The archimedean response has rapidly growing translated
derivatives, so absolute estimates on the separated phase terms can lose the
defect-square cancellation.  The correct common-domain target is the complete
difference in `(O.23)`, or an estimate on `(O.14)` strong enough to justify
the subtraction before the Euler sum.

For the nested pair `R<=E` of Proof 224, apply `(O.23)` separately to `R` and
`E`.  The remaining residual is the difference of the two oblique phase
owners minus the difference of their two positive defect squares.  Neither
positive-square ordering follows from `R<=E`; the final nested-complement sign
remains independent.

This failure has an exact three-dimensional guard.  Let `U` be the cyclic
orthogonal map

```text
U e1=e2, U e2=e3, U e3=e1,
alpha=1/4,
R=span(e1), E=span(e1,e2).                             (O.24)
```

For a projection `J`, write

```text
Amp(J)=Q_J Q_J*-J_alpha.
```

Direct rational calculation gives

```text
Amp(E)-Amp(R)

 = [ -256/4641    704/5967    -64/2457 ]
   [  704/5967   2032/41769    -16/819  ]
   [  -64/2457    -16/819       16/2457 ].             (O.25)
```

Its quadratic values on `e1` and `e2` have opposite signs.  Thus nesting
alone cannot settle the amplitude difference.  This counterexample does not
reject a sign from the special Sonin scattering phase; it proves that such a
sign must use that geometry rather than abstract projection order.

## 7. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/226_metric_sonin_oblique_defect_amplitude.py
```

The deterministic certificate checks:

```text
the common-range and nilpotent-defect identities (O.6)-(O.8);
the positive-square identity (O.9);
the Schur formula (O.12)-(O.14);
the negative trace penalty (O.10);
the convergent Neumann expansion (O.16);
the exact nested-amplitude ordering counterexample (O.24)-(O.25).
```

The finite matrix is only an independent algebra check.  The proof is the
operator derivation above; the script does not certify a post-`Q` domain or RH.

## 8. Route judgment

```text
same-object amplitude owner:                    exact
amplitude as a positive defect square:           exact
amplitude contribution to legal positive trace:  nonpositive
two-boundary-crossing factorization:              exact
bounded Euler-word summability:                   uniform
smooth Q-root amplitude trace legality:           proved
bounded pre-root amplitude operator:               open
complete metric residual compactness:             open
nested amplitude ordering from R<=E:               rejected in general
nested-complement / three-row sign:               open
Lean owner or route rewire:                       none
RH:                                                unproved
```
