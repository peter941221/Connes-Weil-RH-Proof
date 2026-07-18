# Proof 347: atomic singular root localization

Date: 2026-07-18

Status: exact trace-domain closure for a compact convolution root on the
atomic singular-inner/Paley--Wiener block, together with a scaling rejection
of the naive use of Proof 346 in the continuous limit.

For every fixed finite Euler transport, both the source and transported root
compressions are trace class, and nested Paley--Wiener approximants converge
in the trace norm needed by the determinant jet.  Thus the continuous
singular block does not require the raw Euler background to be `I+S_1`.

This does not identify Proof 343's literal quotient carrier with that atomic
block, give a uniform estimate in `S`, prove Gate 3U, prove the finite-`S`
sign, prove Burnol's identity, or prove RH.  The fixed-`S` bound below contains
the forbidden Euler condition number and is used only for convergence.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| atomic singular model                         | Paley--Wiener interval    |
| compact-root source compression               | trace class, exact       |
| fixed-S transported compression               | trace class              |
| nested singular-block approximation           | S1 convergence           |
| raw Euler background in ambient S1             | unnecessary              |
| Proof 346 global H^(1/2) limit                 | diverges like sqrt(R)    |
| mixed localized Szego pairing                  | remains order one        |
| literal Proof 343 carrier identification       | open                     |
| uniform condition-number-free estimate         | open, Gate 3U            |
| RH                                             | unproved                  |
+------------------------------------------------+---------------------------+
```

The usable distinction is

```text
fixed S:
  compact root -> S2 crossing -> S1 determinant direction -> legal limit;

uniform S:
  never bound the transported root by the Euler condition number;
  retain the mixed background/root pairing before Cauchy--Schwarz.    (AS.1)
```

## 2. Atomic singular model

On the upper half-plane, the atomic singular inner function

```text
Theta_a(s)=exp(2 i a s),   a>0,                              (AS.2)
```

has model space

```text
K_(Theta_a)=H^2 minus-orthogonal Theta_a H^2.                 (AS.3)
```

Under the Paley--Wiener Fourier isometry, `(AS.3)` is the physical interval
carrier

```text
L2(I_a),   I_a=(0,2a),                                      (AS.4)
```

embedded in `L2(R)`.  This is the continuous-multiplicity block which a finite
Blaschke model does not see.  The same identification is standardly described
as the equivalence between an atomic singular model space and a Paley--Wiener
space.

Relevant primary/technical sources are:

```text
Lopatto--Rochberg, Schatten-class Truncated Toeplitz Operators,
atomic singular models and their continuous nests,
arXiv:1410.1906:
https://arxiv.org/abs/1410.1906

Bessonov, Schatten properties of Toeplitz operators on the
Paley--Wiener space,
arXiv:1610.02167:
https://arxiv.org/abs/1610.02167
```

The proof below uses only `(AS.4)` and elementary Hilbert--Schmidt calculus;
it does not import a determinant theorem from either source.

## 3. Exact compact-root trace ideal

Let `P_a` be multiplication by `1_(I_a)` in the physical coordinate.  For a
compact smooth root `g`, let

```text
(C_g f)(x)=integral_R g(x-y)f(y)dy.                         (AS.5)
```

The operator `C_g P_a:L2(I_a)->L2(R)` has kernel

```text
g(x-y)1_(I_a)(y).                                           (AS.6)
```

Consequently,

```text
norm(C_g P_a)_2^2
 =integral_(y in I_a) integral_R |g(x-y)|^2 dx dy
 =|I_a| norm(g)_2^2.                                       (AS.7)
```

For two roots `eta,xi`, put

```text
W_(eta,xi)=C_xi* C_eta.                                    (AS.8)
```

Then

```text
P_a W_(eta,xi) P_a
 =(C_xi P_a)* (C_eta P_a) in S_1,                          (AS.9)

norm(P_a W_(eta,xi) P_a)_1
 <=|I_a| norm(xi)_2 norm(eta)_2.                          (AS.10)
```

On the diagonal, `(AS.9)` is positive and

```text
Tr(P_a C_eta* C_eta P_a)
 =|I_a| norm(eta)_2^2.                                    (AS.11)
```

Equations `(AS.7)--(AS.11)` are the continuous analogue of the finite-model
root direction.  The raw translation background is not Hilbert--Schmidt, but
the actual compact-root determinant direction is trace class.

## 4. Fixed-S transported trace domain

Let `tau` be a bounded invertible convolution operator.  It commutes with
every `C_g`.  The orthogonal projection onto `tau Ran(P_a)` is

```text
P_(tau,a)
 =tau P_a G_tau^(-1) P_a tau*,

G_tau=P_a tau* tau P_a|_(Ran(P_a)).                        (AS.12)
```

Since

```text
G_tau>=norm(tau^(-1))^(-2) P_a,                            (AS.13)
```

the inverse in `(AS.12)` exists and

```text
norm(G_tau^(-1))<=norm(tau^(-1))^2.                        (AS.14)
```

Use commutation before taking the Hilbert--Schmidt norm:

```text
C_g P_(tau,a)
 =tau C_g P_a G_tau^(-1)P_a tau*.                          (AS.15)
```

Equations `(AS.7)` and `(AS.14)--(AS.15)` imply

```text
norm(C_g P_(tau,a))_2
 <=kappa(tau)^2 sqrt(|I_a|) norm(g)_2,

kappa(tau)=norm(tau)norm(tau^(-1)).                        (AS.16)
```

Therefore

```text
P_(tau,a) W_(eta,xi) P_(tau,a) in S_1,                    (AS.17)

norm(P_(tau,a) W_(eta,xi) P_(tau,a))_1
 <=kappa(tau)^4 |I_a| norm(xi)_2 norm(eta)_2.             (AS.18)
```

For every fixed finite `S`, `(AS.17)` makes the completed transported
projection jet

```text
Tr[C_eta(P_(tau,a)-P_a)C_xi*]                              (AS.19)
```

an ordinary trace.  Rectangular cycling inside each completed trace reads it
as the difference of the two trace-class compressions in `(AS.9)` and
`(AS.17)`.  This does not assert that either raw product
`W_(eta,xi)P_(tau,a)` or `W_(eta,xi)P_a` is trace class.  This proves legality
only.  The factor `kappa(tau)^4` in `(AS.18)` is precisely the Euler condition
number rejected by Proofs 254, 255, and 265.  It must never be used as the
Gate 3U estimate.

## 5. Trace-norm passage through the continuous block

Let `P_n` be an increasing sequence of orthogonal projections with

```text
P_n<=P_a,
P_n ->P_a strongly.                                         (AS.20)
```

Let `P_(tau,n)` project onto `tau Ran(P_n)`.  The ranges are increasing and
dense in `tau Ran(P_a)`, hence

```text
P_(tau,n)->P_(tau,a) strongly.                              (AS.21)
```

If `A P_(tau,a)` is Hilbert--Schmidt, the standard finite-rank approximation
argument in `S_2` gives

```text
norm(A(P_(tau,n)-P_(tau,a)))_2 ->0.                         (AS.22)
```

Apply `(AS.22)` with `A=C_eta,C_xi`, using `(AS.16)`.  Holder's inequality
`S_2*S_2->S_1` then yields

```text
P_(tau,n) W_(eta,xi) P_(tau,n)
 ->P_(tau,a) W_(eta,xi) P_(tau,a) in S_1.                  (AS.23)
```

The source convergence follows from `(AS.7)` in the same way.  Thus the
root-sandwiched determinant jets converge for every fixed transport.  Strong
projection convergence alone would not imply `(AS.23)`; the compact-root
Hilbert--Schmidt estimate is the indispensable input.

This closes the functional-analytic passage for an explicitly identified
atomic singular block.  It does not prove that Proof 343's `K` is that block
or that a chosen finite-Blaschke sequence realizes the same nested
approximants.

## 6. Why Proof 346 does not survive by a global norm bound

The obstruction can be quantified without any model-space guess.  Put a
physical spectral box of length `R` on a circle and approximate one continuous
translation frequency `z>0` by

```text
k_R=round(z R/(2 pi)).                                      (AS.24)
```

If the real Euler logarithm has coefficients `c` at `+/-k_R`, its discrete
half-Sobolev energy is

```text
E_background(R)=k_R |c|^2
 ~R z |c|^2/(2 pi).                                         (AS.25)
```

Let `phi` be the compact physical correlation of the root detector.  The
periodic detector coefficients with the correct Riemann-sum normalization are

```text
w_(R,k)=(2 pi/R) phi(2 pi k/R).                             (AS.26)
```

Their half-Sobolev energy has a finite limit:

```text
sum_(k>=1) k |w_(R,k)|^2
 ->integral_0^infinity u |phi(u)|^2 du.                     (AS.27)
```

Hence Proof 346 `(UG.3)` gives only

```text
4 sqrt(E_background(R) E_detector(R))=O(sqrt(R)).           (AS.28)
```

But the actual mixed quadratic Szego pairing of this mode is

```text
2 k_R c w_(R,k_R)
 ->2 z c phi(z),                                            (AS.29)
```

which is order one.  The lost factor in `(AS.28)` is created exactly when
Cauchy--Schwarz separates the continuous background from the root direction.
No choice of finite Blaschke approximants repairs that loss.

Thus the finite-model positivity theorem remains valid, but its global norm
corollary is too coarse for the singular-inner limit.  The successor must
retain a mixed or relative quadratic form analogous to `(AS.29)`.

## 7. Corrected near theorem

The analytic target after Proofs 343--346 is not a bound on the two global
`H^(1/2)` norms.  It is a relative mixed-gradient estimate:

```text
abs D Phi_(Burnol,relative)(f_S)[w_(eta,xi)]

 <=C (1+B_root)^d
   sqrt(mathcalE_S(8B_root+4))
   norm(eta)_(H^r) norm(xi)_(H^r),                         (AS.30)
```

where all of the following occur before the first Cauchy--Schwarz or absolute
value:

```text
the literal Proof 343 quotient carrier;
the outer-minus-Sonin relative determinant;
the compact-root S1 direction `(AS.9)--(AS.17)`;
the mixed continuous pairing, not the ambient background norm;
Proof 335's half-density cancellation;
Proof 336's far displacement removal.                            (AS.31)
```

Proof 344 supplies the arithmetic bound only after `(AS.30)` is proved on the
same owner.  Equation `(AS.23)` supplies a legal fixed-`S` limiting mechanism
for any atomic block identified inside that owner.

## 8. Reproducible scaling certificate

The companion script checks `(AS.25)--(AS.29)` for an explicit compact smooth
correlation.  It is a scaling audit, not a finite-section proof of Gate 3U.

The WSL2 run gives

```text
continuum detector energy =2.222222222264e-1,
continuum mixed pairing   =5.875536969872e-1.

+------+----------------+----------------+----------------+
| R    | E_background/R | UG/sqrt(R)     | mixed pairing  |
+------+----------------+----------------+----------------+
|   64 | 5.46875000e-2  | 4.40159395e-1  | 5.87964858e-1 |
|  128 | 5.46875000e-2  | 4.40759188e-1  | 5.87964858e-1 |
|  256 | 5.46875000e-2  | 4.40908737e-1  | 5.87964858e-1 |
|  512 | 5.46875000e-2  | 4.40946100e-1  | 5.87964858e-1 |
| 1024 | 5.51757813e-2  | 4.42919615e-1  | 5.87537074e-1 |
+------+----------------+----------------+----------------+
```

The displayed `UG/sqrt(R)` approaches a nonzero constant, so the unscaled
Proof 346 bound grows as `sqrt(R)`.  The mixed pairing error at `R=1024` is
`1.66e-5` despite that divergence.

Run in WSL2 without a Lean build:

```text
python3 -B docs/proofs/347_atomic_singular_root_localization_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| compact-root atomic-block trace domain         | closed                    |
| fixed-S transported trace domain               | closed                    |
| nested root-sandwiched S1 limit                | closed                    |
| use of kappa(tau) as uniform bound             | forbidden                 |
| naive global UG.3 singular limit               | rejected by AS.28        |
| mixed localized gradient AS.30                 | open, exact near bottom  |
| literal Burnol quotient identification         | open                      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
