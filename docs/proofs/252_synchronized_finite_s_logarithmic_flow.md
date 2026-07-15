# Proof 252: Synchronized finite-S logarithmic flow

Date: 2026-07-15

Status: exact finite-S operator algebra and a reproducible finite-section
survivor diagnostic.  The complete transported nested complement can be
integrated along one synchronized path whose right logarithmic derivative is
an additive prime-power sum.  This is a different object from the absolute
sum of the mixed Hessians isolated in Proof 251.  In the tested sections the
quadratic mixed approximation grows and changes sign, while the complete
endpoint stays bounded and is negative on one fixed four-mode witness through
all primes up to `997`.  Higher connected terms are therefore material.

This is not a continuous bound or sign theorem.  The values are sensitive to
the finite box and are not converged under refinement.  The complete
constrained operator remains indefinite.  No Lean owner or route rewire is
authorized, and RH remains unproved.

## 1. Result first

Proof 251 derives a nonzero mixed Hessian with dressed scale
`1/sqrt(p*q)`.  That result is decisive against an estimate which first takes
the norm of every pair channel.  It is not a uniform approximation to the
complete finite-`S` projection when

```text
sum_(p in S) p^(-1/2)
```

is large.  At the largest tested cutoff this sum is about `12.65`.

The correct complete finite-`S` comparison is obtained by turning on every
local factor before taking a norm.  Put

```text
a_p=p^(-1/2),
U_p=translation by log(p),

T_S(t)=product_(p in S) (I-t a_p U_p),
0<=t<=1.                                                (G.1)
```

For the transported half-line and Sonin projections `E_S(t)` and `R_S(t)`, put

```text
B_S(t)=E_S(t)-R_S(t).                                  (G.2)
```

The exact endpoint correction is

```text
Delta B_S=B_S(1)-B_S(0).                               (G.3)
```

On the default section, the fixed witness gives

```text
+--------+-------------+---------------+---------------+-------------+
| p <=   | complete    | one-prime sum | connected     | pair Hessian|
+--------+-------------+---------------+---------------+-------------+
|      2 | -1.509483   | -1.509483     |  0.000000     |  0.000000   |
|      3 | -1.683783   | -1.327543     | -0.356239     | -0.345072   |
|      5 | -1.196791   | -1.375604     |  0.178813     |  0.602046   |
|      7 | -1.180877   | -1.378926     |  0.198049     |  0.893276   |
|     11 | -1.205540   | -1.379610     |  0.174070     |  0.772305   |
|     17 | -1.196731   | -1.380284     |  0.183553     |  1.144615   |
|     29 | -1.158720   | -1.380087     |  0.221367     |  1.212646   |
|     97 | -1.124698   | -1.380267     |  0.255569     |  1.306314   |
+--------+-------------+---------------+---------------+-------------+
```

Here

```text
connected=complete-one-prime sum.                       (G.4)
```

The pair Hessian is not the connected endpoint.  Starting at `p=5`, it has
the wrong magnitude, and its growth is cancelled by higher connected orders.
This does not prove that the continuous complete endpoint is bounded.  It
does prove that the pair truncation is not a faithful finite-section proxy for
the complete owner.

## 2. Exact right logarithmic derivative

Every factor in `(G.1)` is invertible because `a_p<1`, and all translations
commute.  The product rule therefore gives

```text
X_S(t):=T_S'(t) T_S(t)^(-1)

 =-sum_(p in S) a_p U_p (I-t a_p U_p)^(-1)

 =-sum_(p in S) sum_(m>=1)
      t^(m-1) p^(-m/2) U_p^m.                          (G.5)
```

The series converges in operator norm uniformly on `0<=t<=1`, since
`a_p<=1/sqrt(2)` for every finite prime.  Integrating the scalar coefficient
in `(G.5)` gives the factorwise logarithmic generator

```text
Z_S
 =sum_(p in S) log(I-a_p U_p)
 =-sum_(p in S) sum_(m>=1) p^(-m/2) U_p^m/m,

exp(Z_S)=T_S(1).                                       (G.6)
```

Formula `(G.6)` uses the norm-convergent logarithm of each local factor.  It
does not assert that the principal logarithm of the complete product has one
global branch.  No trace of `Z_S`, Fredholm determinant, or Fock trace is used.

The finite-section script verifies `(G.5)` independently in the common
Fourier diagonalization: it differentiates the full product multiplier and
compares after division by the product.  The largest default error is below
`3e-15`.

## 3. Complete nested projection flow

Proof 227 proves for an arbitrary differentiable invertible path `T(t)` that
the projection `J(t)` onto `T(t) Ran(J)` satisfies

```text
J'(t)
 =(I-J(t))X(t)J(t)+J(t)X(t)*(I-J(t)),
X(t)=T'(t)T(t)^(-1).                                  (G.7)
```

Apply `(G.7)` to `E_S(t)` and `R_S(t)`.  With

```text
C_S(t)=I-E_S(t),

Y_S(t)
 =C_S(t) X_S(t) B_S(t)
  -R_S(t) X_S(t)* B_S(t),                             (G.8)
```

the `C_S <-> R_S` channels cancel before any norm is taken, and

```text
B_S'(t)=Y_S(t)+Y_S(t)*.                                (G.9)
```

Consequently

```text
Delta B_S
 =integral_0^1 (Y_S(t)+Y_S(t)*) dt.                   (G.10)
```

The script evaluates both sides after the exact trace-diagonal and pre-root
differential.  For `S={p:p<=29}`, 12-point Gauss--Legendre integration gives

```text
relative endpoint error       6.17e-10
nested/direct derivative error 2.29e-15
```

Thus the synchronized flow is not a new stored value.  It is an exact path to
the same endpoint projection difference.

## 4. Why Proof 251 is a truncation

For a fixed projection `P`, Proof 251's mixed Hessian `H_P(U,V)` is symmetric
and bilinear in commuting `U,V`.  Put

```text
W_S=sum_(p in S) a_p U_p.                              (G.11)
```

Polarization gives the exact quadratic identity

```text
sum_(p<q) a_p a_q H_P(U_p,U_q)

 =1/2 [H_P(W_S,W_S)
       -sum_p a_p^2 H_P(U_p,U_p)].                     (G.12)
```

The script compares `(G.12)` with the direct pair sum for the first three
primes, separately for the half-line and Sonin projections.  The maximum
relative error is below `3e-15` in every reported run.

However, `(G.12)` is only the degree-two part of `(G.3)`.  Define

```text
C_S
 =Delta B_S-sum_(p in S) Delta B_{p}.                 (G.13)
```

Then `C_S` contains the pair Hessian plus every higher mixed cluster.  There is
no small total expansion parameter as `S` grows.  Taking the norm of `(G.12)`
before constructing `(G.13)` is therefore not an estimate of `(G.3)`.

## 5. Numerical stability checks

The probe uses actual translation lengths `log(p)`, not grid-rounded prime
locations.  On a periodic Fourier section, each `U_p` is an exactly unitary
Fourier multiplier.  The following independent checks are mandatory:

```text
full-product derivative = additive resolvent sum;
translations commute;
forward and reverse prime order give the same range projection;
sequential local QR and the directly multiplied Fourier symbol agree;
polarized and explicit pair sums agree;
integrated projection flow recovers the endpoint.
```

For all primes through `997` at `size=256`, `step=0.08`, the diagnostics are

```text
+--------------------------------------+---------------+
| check                                | relative error|
+--------------------------------------+---------------+
| maximum translation commutator       | 2.13e-14      |
| right logarithmic derivative         | 1.25e-14      |
| forward/reverse factor order         | 4.78e-14      |
| sequential/direct product projection | 6.19e-14      |
+--------------------------------------+---------------+
```

The complete multiplier has logarithmic condition number about `20.39`, or an
ordinary condition number of order `7e8`.  The direct-product check therefore
matters: sequential reorthogonalization is not being accepted by itself as
evidence.

## 6. Large-S diagnostic

At fixed half-box width `10.24`, `size=256`, and `step=0.08`, the complete
witness remains negative through 168 prime factors:

```text
+--------+-------+----------+-----------+-----------+-----------+
| p <=   | count | sum p^-1/2| complete | singles   | connected |
+--------+-------+----------+-----------+-----------+-----------+
|     97 |    25 |   5.5365 | -1.158429 | -1.380514 |  0.222085 |
|    199 |    46 |   7.2778 | -0.981371 | -1.380385 |  0.399015 |
|    499 |    95 |   9.9462 | -1.100462 | -1.380430 |  0.279968 |
|    997 |   168 |  12.6536 | -0.858116 | -1.380412 |  0.522296 |
+--------+-------+----------+-----------+-----------+-----------+
```

This is a survivor diagnostic, not a convergence theorem.  A difference of
finite-dimensional projections is automatically bounded, and the fixed root
read-off is finite dimensional.  The useful information is narrower: the
complete endpoint does not track the growing pair Hessian, and the connected
correction is numerically material.

The cutoff-`997` refinement is not converged:

```text
+------+----------+----------+-----------+-----------+-----------+
| size | step     | half-box | complete  | singles   | connected |
+------+----------+----------+-----------+-----------+-----------+
|  256 | 0.080000 | 10.240   | -0.858116 | -1.380412 |  0.522296 |
|  320 | 0.064000 | 10.240   | -0.745773 | -1.269101 |  0.523328 |
|  384 | 0.053333 | 10.240   | -0.647484 | -1.114958 |  0.467473 |
|  384 | 0.048000 |  9.216   | -0.869621 | -1.042460 |  0.172839 |
+------+----------+----------+-----------+-----------+-----------+
```

The last row exposes substantial box sensitivity.  No limiting value, fixed
sign theorem, or operator-norm bound is inferred from these data.  In every
run the constrained spectrum also crosses zero, so the experiment does not
restore a uniform three-row sign.

## 7. Relation to earlier rejections

This construction does not reopen a rejected object under a new name.

Proof 026 rejects the direct scattering-cocycle remainder because its pure
finite-place term leaves a post-`Q` Dirac-comb principal part.  Its reopening
condition is an exact same-object cancellation before the positive trace
read-off.  Proofs 224--234 supply precisely a different, later object: the
complete metric projection is recombined before `Q`, and the resulting
finite-window correction is compact.  Equations `(G.8)--(G.10)` keep that
recombined object whole.

Proof 118 rejects adding a compact Wiener--Hopf repair to an unchanged
essential prime symbol.  The synchronized `T_S(t)` is a noncompact
pre-read-off transport of both nested ranges; it is within Proof 118's stated
exception for an identity which changes the principal symbol before assigning
the Weil main channel.

Proof 119 rejects a Fredholm determinant of the unitary translations.  No
determinant or trace logarithm occurs in `(G.5)--(G.10)`.

Proof 027 studies a growing prolate spectral cutoff and distributional recovery
of prime atoms.  Here `S` is finite, there is no prolate-rank limit, and the
prime ledger remains the already named single-crossing owner.

## 8. Source boundary

CCM24 gives the finite-place multiplier product and the common semilocal
carrier:

```text
dm_S(s)
 =|product_(v in S) L_v(1/2-is)|^2 ds,
```

and proves that the archimedean and semilocal Sonin spaces are Hilbertian
isomorphic.  See equation (6), Theorem 2, and Sections 4.7--4.8 of

```text
https://arxiv.org/html/2310.18423v2
```

Proof 227 records the exact one-prime factor `I-alpha U`, the general
projection derivative, CC20's scattering conjugacy, and

```text
P P_hat P=R_Sonin+K_prol.
```

Neither CCM24 nor CC20 states `(G.5)--(G.13)` for the complete finite-`S`
nested complement, nor do they prove the uniform detector estimate below.
The synchronized algebra is a project derivation.  The continuous estimate is
a project obligation.

## 9. New analytic bottom

For a compact root interval `I`, let `eta,xi` be smooth pre-roots supported in
`I`, and define the same-object flow form

```text
q_(S,t)(eta,xi)
 =Tr(C_(L_+ eta)
       (Y_S(t)+Y_S(t)*)
       C_(L_+ xi)*),

L_+=d/dx+1/2.                                         (G.14)
```

The next continuous theorem must produce kernels `kappa_(S,t)` on `I x I`
such that

```text
q_(S,t)(eta,xi)=<eta,Kappa_(S,t)xi>,                  (G.15)

integral_0^1 q_(S,t)(xi_n,xi_n) dt
 =o(1)                                                (G.16)
```

for the actual resonant negative-owner sequence `xi_n` and its visible finite
place sets `S_n`.  A sufficient, stronger estimate is

```text
abs(integral_0^1 q_(S_n,t)(xi_n,xi_n) dt)

 <=C (1+B_n)^d ||L_+ xi_n||_(H^r)^2,                 (G.17)
```

where `[-B_n,B_n]` contains the source support and `C,d,r` are independent of
`S_n`.  Proof 249's resonant contraction would make the right side tend to
zero.

The proof must not bound `X_S(t)` by
`sum_p p^(-1/2)/(1-p^(-1/2))`.  That recreates the rejected absolute route.
It must instead use the complete product metric on CCM24's common de Branges
carrier, or an equivalent scattering identity, before estimating.  The
`K_prol` insertions must be retained with their trace-class tail; they do not
vanish under common translation.

If the complete continuous form retains a nonzero prime-density bulk after
this resummation, the detector-specific finite-`S` smallness route is rejected.
If `(G.16)` or `(G.17)` holds, the next gates remain the negative-owner
integration, the same-object finite-`S` trace identity, and Burnol's all-zero
identity.

## 10. Reproduction

Run sequentially in WSL:

```text
python3 -B \
  docs/proofs/252_synchronized_finite_s_logarithmic_flow_probe.py

python3 -B \
  docs/proofs/252_synchronized_finite_s_logarithmic_flow_probe.py \
  --size 256 --step 0.08 --root-width 0.96 \
  --prime-cutoffs 97,199,499,997 \
  --skip-pair-hessian --skip-flow-integral

python3 -B \
  docs/proofs/252_synchronized_finite_s_logarithmic_flow_probe.py \
  --size 384 --step 0.05333333333333334 --root-width 0.96 \
  --prime-cutoffs 997 \
  --skip-pair-hessian --skip-flow-integral
```

The first command verifies every algebraic and flow identity.  The later
commands are larger endpoint diagnostics and deliberately skip already checked
quadratic and path-integration work.

## 11. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| finite-S multiplier product                    | source-backed            |
| synchronized right logarithmic derivative      | exact                    |
| complete nested projection flow                | exact                    |
| mixed-Hessian polarization                     | exact                    |
| pairwise absolute finite-S estimate             | still rejected target    |
| pair Hessian as proxy for complete endpoint     | rejected in probe        |
| higher connected cancellation                  | survives in probe        |
| fixed four-mode complete endpoint               | negative, not converged  |
| complete constrained operator sign              | indefinite in probe      |
| continuous synchronized-flow kernel             | open, new active bottom  |
| uniform detector estimate (G.16)/(G.17)         | open                     |
| same-object finite-S trace identity             | open                     |
| Lean owner or route rewire                      | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 251 remains the correct guard against taking pair norms.  It is no
longer the decisive death theorem for the complete finite-`S` owner.  The next
proof must analyze `(G.14)` with all local factors present before any absolute
value is taken.  More finite periodic sections do not move the route.
