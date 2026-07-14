# Proof 227: complete nested metric flow

Date: 2026-07-14

Status: exact same-object flow reduction.  The phase and oblique-defect pieces
from Proof 226 are not separate analytic channels.  After they are recombined
into the nested complement projection, all diagonal terms cancel and the
derivative consists of one difference of two off-diagonal boundary crossings.
The whole Euler word series is owned by one bounded resolvent, uniformly on the
one-prime interpolation interval.  This removes the separated principal-mode
and amplitude-mode summability gates.  The remaining analytic theorem is a
local Hilbert--Schmidt estimate for the complete crossing difference on the
same `Q`-root.  The flow is generically indefinite, so projection monotonicity
cannot prove the final sign.  No Lean owner is authorized, and RH remains
unproved.

## 1. Source geometry and the object that must stay whole

For one finite prime, CCM24 gives the multiplier

```text
T_alpha=I-alpha U,
U=M_(exp(-i log(p) s)),
0<=alpha<=p^(-1/2).                                  (F.1)
```

This is the source calculation at
<https://arxiv.org/abs/2310.18423v2>, original TeX lines `946--981`.
Lines `983--1029` prove that it transports the archimedean Sonin space to the
semilocal one by a bounded Hilbertian isomorphism.

Let `R<=E` be the Sonin projection and the crossed half-line projection from
Proof 224.  For `J=R,E`, let

```text
J_alpha=orthogonal projection onto T_alpha Ran(J).   (F.2)
```

Put

```text
B_alpha=E_alpha-R_alpha,
C_alpha=I-E_alpha.                                    (F.3)
```

Since `Ran(R_alpha)<=Ran(E_alpha)`, `B_alpha` is itself an orthogonal
projection.  It is the complete nested-complement remainder owner.  Proof 226
rewrites each `J_alpha` as an oblique phase square minus a positive defect
square, but estimating those four terms separately loses an exact cancellation.

The special Sonin geometry behind the cancellation is source-backed.  CC20
proves

```text
P P_hat P
 =R_Sonin+sum_n lambda_n^2 |zeta_n><zeta_n|,          (F.4)
```

at <https://arxiv.org/abs/2006.13771>, original TeX lines `1072--1076`.
The prolate singular values have rapid decay at original TeX lines
`960--984`.  The scattering conjugacy of the two half-line projections is at
lines `542--548`, and the smoothed Hardy commutator is trace class by
`quantsmooth` at lines `2087--2120`.

## 2. Projection flow before nesting

Let `T_alpha` be any norm differentiable path of bounded invertible operators
and define its right logarithmic derivative

```text
X_alpha=T_alpha' T_alpha^(-1).                        (F.5)
```

For a fixed orthogonal projection `J`, the orthogonal projection `J_alpha`
onto `T_alpha Ran(J)` satisfies

```text
J_alpha'
 =(I-J_alpha)X_alpha J_alpha
   +J_alpha X_alpha* (I-J_alpha).                     (F.6)
```

To prove `(F.6)`, differentiate `J_alpha^2=J_alpha`.  This says the diagonal
blocks of `J_alpha'` vanish.  If `v_alpha=T_alpha v` lies in the moving range,
then its normal velocity is `(I-J_alpha)X_alpha v_alpha`, which fixes the
lower-left block.  Self-adjointness fixes the upper-right block.  Equivalently,
one may differentiate the exact metric projection formula

```text
J_alpha
 =T_alpha J(J T_alpha* T_alpha J)^(-1)J T_alpha*.
```

For `(F.1)`, the logarithmic derivative is the exact resolvent

```text
X_alpha
 =-U(I-alpha U)^(-1)
 =-sum_(m>=1) alpha^(m-1) U^m.                        (F.7)
```

## 3. Complete nested cancellation

Use the orthogonal decomposition

```text
I=R_alpha+B_alpha+C_alpha.                            (F.8)
```

Applying `(F.6)` to `E_alpha=R_alpha+B_alpha` gives

```text
E_alpha'
 =C_alpha X_alpha(R_alpha+B_alpha)
  +(R_alpha+B_alpha)X_alpha* C_alpha.                 (F.9)
```

Applying it to `R_alpha`, whose orthogonal complement is
`B_alpha+C_alpha`, gives

```text
R_alpha'
 =(B_alpha+C_alpha)X_alpha R_alpha
  +R_alpha X_alpha*(B_alpha+C_alpha).                (F.10)
```

Subtract `(F.10)` from `(F.9)`.  The two `C_alpha <-> R_alpha` channels cancel
exactly.  What remains is

```text
B_alpha'
 = C_alpha X_alpha B_alpha
   +B_alpha X_alpha* C_alpha
   -B_alpha X_alpha R_alpha
   -R_alpha X_alpha* B_alpha.                        (F.11)
```

Define the single complete crossing

```text
Y_alpha
 =C_alpha X_alpha B_alpha
  -R_alpha X_alpha* B_alpha.                         (F.12)
```

Then

```text
B_alpha'=Y_alpha+Y_alpha*.                            (F.13)
```

This is the correct replacement for Proof 225's separated triangular phase
and Proof 226's separated amplitude defect.  Every term in `(F.13)` begins in
`Ran(B_alpha)` and ends in its orthogonal complement, or vice versa.  In
particular,

```text
B_alpha B_alpha' B_alpha=0,
(I-B_alpha)B_alpha'(I-B_alpha)=0.                    (F.14)
```

The nonzero diagonal pieces that appear after differentiating the oblique
phase squares cancel exactly against the diagonal pieces of the defect
squares before `(F.11)` is formed.  Thus an estimate that takes absolute
values before this subtraction is not an estimate of the metric projection.

## 4. Kato owner and uniform Euler resolvent

Put

```text
K_alpha=Y_alpha-Y_alpha*.                             (F.15)
```

It is skew-adjoint, and `(F.13)--(F.14)` give

```text
B_alpha'=[K_alpha,B_alpha].                           (F.16)
```

Let `W_alpha` solve

```text
W_alpha'=K_alpha W_alpha,
W_0=I.                                                (F.17)
```

Then `W_alpha` is unitary and uniqueness for `(F.16)` gives the exact
same-object transport

```text
B_alpha=W_alpha B_0 W_alpha*.                         (F.18)
```

For a unitary `U`, `(F.7)` has the uniform bounds

```text
norm(X_alpha)<=1/(1-alpha),
sum_(m>=1) alpha^(m-1) norm(U^m)<=1/(1-alpha).         (F.19)
```

Since `alpha<=p^(-1/2)<=1/sqrt(2)`, the right side is uniformly finite.  More
generally, every fixed polynomial word weight is summable:

```text
sum_(m>=1) m^r alpha^(m-1)<infinity                   (F.20)
```

uniformly on the interpolation interval.  Also,

```text
norm(Y_alpha)<=2 norm(X_alpha),
norm(B_alpha')<=4/(1-alpha).                          (F.21)
```

The scaling differential defining `Q` commutes with every `U^m`.  Therefore
`Q` does not create the exponential endpoint growth seen when the normalized
phase kernel is first split into separate widths `m log(p)`.  The full
resolvent `(F.7)` owns those words before any kernel asymptotic is taken.

This is a combinatorial and operator-norm result, not yet the missing ideal
estimate.  The projections in `(F.12)` still carry the Sonin boundary.

## 5. Exact remaining compactness contract

Let `I` be the compact logarithmic support interval of the selected pre-root.
For smooth `eta,xi` supported in `I`, apply the genuine `Q`-root on both sides
and define the infinitesimal residual form from `(F.13)`:

```text
q_alpha(eta,xi)
 =Tr(C_(L_+ eta) (Y_alpha+Y_alpha*) C_(L_+ xi)*),
L_+=d/dx+1/2.                                         (F.22)
```

The next sufficient theorem is now one statement about one object:

```text
there are kernels kappa_alpha in L2(I x I) such that

q_alpha(eta,xi)=<eta,Kappa_alpha xi>,
integral_0^a norm(kappa_alpha)_L2 d alpha<infinity.    (F.23)
```

If `(F.23)` holds, then

```text
Kappa_a=integral_0^a Kappa_alpha d alpha              (F.24)
```

is Hilbert--Schmidt and represents the complete post-`Q`
`B_a-B_0` correction.  CC20's `quantsmooth`, its scattering-conjugate form,
and the rapid prolate angles in `(F.4)` are the exact source inputs available
for `(F.23)`.

The point is what `(F.23)` does not ask for:

```text
no separate locally H2 estimate for every principal width m log(p);
no separate locally H2 estimate for an amplitude defect;
no summation of their absolute values before cancellation.                (F.25)
```

Those were artifacts of the separated representation.  The remaining issue
is the local ideal class of the difference in `(F.12)`, uniformly in `alpha`.

## 6. Monotonicity sign is impossible

Let

```text
Gamma_alpha=2B_alpha-I.                               (F.26)
```

By `(F.14)`,

```text
Gamma_alpha B_alpha' Gamma_alpha=-B_alpha'.           (F.27)
```

Thus the spectrum of `B_alpha'` is symmetric about zero.  More directly, if
`B_alpha'` were positive semidefinite, conjugating by the unitary
`Gamma_alpha` would make `-B_alpha'` positive semidefinite as well, forcing
`B_alpha'=0`.  The same argument applies to negative semidefiniteness.

Therefore

```text
nonzero complete nested flow => indefinite instantaneous form.            (F.28)
```

This rejects any proof of the final route sign based only on monotonicity of
the nested complement under `alpha`.  It does not reject a sign after
integration, after adding the archimedean owner, or on the three-Mellin-row
subspace.  Those are genuinely more structured questions.

## 7. Reproduction and diagnostic boundary

Run in WSL:

```text
python3 -B docs/proofs/227_complete_nested_metric_flow.py
python3 -B docs/proofs/227_complete_nested_metric_flow.py --prime 3
```

The deterministic certificate checks:

```text
the projection derivative (F.6) by an independent central difference;
the complete cancellation (F.11)-(F.14);
the Kato commutator identity (F.16);
the resolvent series (F.7);
the exact cancellation of separated phase/defect diagonal blocks;
the positive and negative spectrum forced by (F.27).
```

The enlarged Proof 224 scattering diagnostic was also rerun at `p=2` through
`28` cells per `log(p)` and modulations through `100`.  The post-`Q` samples
range from about `+1.59` to `-5.28` and do not approach a stable constant or a
fixed periodic tail on that finite section.  This rejects numerical
negligibility but proves neither compactness nor noncompactness, because the
Sonin cutoff and high-energy limits are not separated by that model.

## 8. Route judgment

```text
complete nested-complement derivative:          exact
single same-object crossing owner:               Y_alpha
Kato unitary transport:                          exact
Euler resolvent / polynomial word summability:   uniform
separate principal/amplitude summability gates:  removed
abstract monotonicity sign:                      rejected unless flow is zero
complete Q-root local Hilbert--Schmidt estimate:  open, contract (F.23)
integrated three-row sign:                       open
Lean owner or route rewire:                      none
RH:                                              unproved
```

The next proof must attack `(F.23)` using the CC20 scattering conjugacy and
rapid prolate angle on the complete difference `(F.12)`.  Proving the two
summands separately is not a valid substitute.
