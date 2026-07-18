# Proof 348: prime-cluster local S2 obstruction

Date: 2026-07-18

Status: exact half-line crossing Gram formula and unconditional rejection of
a localized Hilbert--Schmidt/Koplienko estimate for the linearly expanded Euler
logarithm.  Compact root support makes distant displacement modes orthogonal,
but it makes the many prime modes in one short logarithmic interval coherent.
Their off-diagonal Gram mass is exponentially larger than Proof 344's
diagonal Szego ledger.

This is a route guard, not Gate 3U.  It does not reject a mixed estimate for
the complete Euler product after the outer-minus-Sonin and half-density
cancellations.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one completed half-line crossing Gram          | exact                     |
| compact-root displacement locality             | exact                     |
| short prime-log cluster                        | coherent, positive        |
| local S2 norm of linear Euler logarithm         | >=c exp(L)/L             |
| Proof 344 diagonal energy of same cluster       | O(1)                     |
| local Koplienko from raw log perturbation       | rejected                  |
| complete nonlinear relative determinant        | not rejected              |
| Gate 3U / RH                                   | open / unproved           |
+------------------------------------------------+---------------------------+
```

The forbidden route is

```text
expand log(T_S) into prime modes
  -> compact-root every mode
  -> take one local S2 norm
  -> invoke Koplienko / Cauchy--Schwarz
  -X-> exponential coherent prime-cluster cost.                 (PC.1)
```

The only surviving quadratic route is

```text
complete Euler product
  -> quotient Gram inverse
  -> outer-minus-Sonin recombination
  -> Proof 335 half-density cancellation
  -> compact-root mixed scalar
  -> one final quadratic estimate.                              (PC.2)
```

## 2. Exact root-smoothed crossing Gram

Work on `H=L2(R)` and let `P` be multiplication by `1_[0,infinity)`.  For
`z>0`, orient translation so that

```text
A_z=(I-P)U_zP                                             (PC.3)
```

maps the input strip `[0,z]` across the origin.  If `C_g` is convolution by a
compact `L2` root `g`, then `C_g A_z` has kernel

```text
k_z(x,y)=g(x-y+z) 1_[0,z](y).                            (PC.4)
```

It follows directly that

```text
<C_g A_z,C_g A_w>_(S2)

 =integral_(0 to min(z,w)) integral_R
    conjugate(g(x-y+z))g(x-y+w) dx dy

 =min(z,w) Gamma_g(w-z),                                 (PC.5)

Gamma_g(h)=integral_R conjugate(g(t))g(t+h)dt.            (PC.6)
```

In particular,

```text
norm(C_g A_z)_2^2=z norm(g)_2^2.                          (PC.7)
```

Equation `(PC.7)` is the completed-crossing identity behind Proof 260.  The
off-diagonal formula `(PC.5)` is the part a diagonal Szego ledger does not
record.

If `g` is real, nonnegative, and nonzero, then `Gamma_g` is continuous,

```text
Gamma_g(0)=norm(g)_2^2>0.                                (PC.8)
```

Hence there are fixed `delta,c_g>0` such that

```text
Gamma_g(h)>=c_g,   |h|<=delta.                            (PC.9)
```

Compact support also gives `Gamma_g(h)=0` for sufficiently large `|h|`.
Thus the crossing family is local in displacement, but nearby modes are
positively coherent rather than orthogonal.

## 3. A short interval of prime modes

Fix `epsilon>0` so small that

```text
log(1+epsilon)<=delta.                                    (PC.10)
```

For a large real `X`, let

```text
P_X={p prime:X<=p<=(1+epsilon)X},
z_p=log(p),
a_p=p^(-1/2).                                             (PC.11)
```

Use only the `m=1` modes of the actual Euler logarithm and form

```text
mathcalX_X=sum_(p in P_X) a_p A_(z_p).                    (PC.12)
```

All coefficients have the same sign.  Equations `(PC.5)` and `(PC.9)--(PC.11)`
give the lower bound

```text
norm(C_g mathcalX_X)_2^2

 =sum_(p,q in P_X)
    (pq)^(-1/2) min(log p,log q) Gamma_g(log(q/p))

 >=c_g log(X) |P_X|^2/((1+epsilon)X).                     (PC.13)
```

The prime number theorem on a fixed relative interval gives

```text
|P_X|~epsilon X/log(X).                                  (PC.14)
```

Substitution into `(PC.13)` yields

```text
norm(C_g mathcalX_X)_2^2
 >=c_(g,epsilon) X/log(X)                                (PC.15)
```

for all sufficiently large `X`.  With `L=log(X)`, this is

```text
norm(C_g mathcalX_X)_2^2
 >=c_(g,epsilon) exp(L)/L.                               (PC.16)
```

The prime number theorem used in this obstruction is an unconditional
theorem.  No RH input is used.  A Chebyshev-type lower bound on a suitable
fixed relative interval is also enough; the asymptotic form `(PC.14)` simply
makes the mechanism transparent.

## 4. Compare the diagonal Szego ledger

For exactly the same `m=1` prime cluster, Proof 344's diagonal quadratic
energy is

```text
mathcalE_X
 =sum_(p in P_X) log(p)/p.                               (PC.17)
```

The prime number theorem, or partial summation from `(PC.14)`, gives

```text
mathcalE_X ->log(1+epsilon),                             (PC.18)
```

so it is bounded independently of `X`.  Equations `(PC.16)` and `(PC.18)`
show

```text
local root-smoothed S2 energy       >=c exp(L)/L;
diagonal atomic Szego energy         =O(1).              (PC.19)
```

The discrepancy is not a missing constant.  It is the square of the coherent
sum of roughly `epsilon X/log(X)` modes whose log displacements lie within the
same root-correlation window.

## 5. Consequence for Koplienko localization

The ordinary Koplienko trace formula requires one Hilbert--Schmidt
perturbation before taking the second-order trace remainder.  If that
perturbation is chosen to be the compact-root-smoothed linear Euler logarithm,
`(PC.16)` supplies an exponential lower bound.  It cannot produce Proof 344's
polynomial support ledger.

The precise ideal contract is stated in the abstract of:

```text
Gesztesy--Pushnitski--Simon,
On the Koplienko spectral shift function, I. Basics,
arXiv:0705.3629:
https://arxiv.org/abs/0705.3629

KoSSF is defined for A-B in I_2; the test function is applied only after
that perturbation hypothesis.
```

Root sandwiching after the trace remainder does not repair the hypothesis:
double-operator-integral/Koplienko calculus acts on the perturbation ideal
before the test functional is evaluated.  A new relative theorem would have
to perform the cancellations in `(PC.2)` first; calling the raw sum in
`(PC.12)` a localized `S_2` perturbation is false.

This also sharpens Proof 347's scaling guard.  One continuous mode loses a
factor `sqrt(R)` under separated global norms.  A dense prime cluster is
worse: even the one-root local `S_2` norm itself is exponentially larger than
the diagonal prime-square ledger.

## 6. What remains viable

Proof 348 does not contradict the finite Blaschke theorem.  On the disk, its
integer Fourier modes are globally orthogonal before the model compression.
The real-line compact root localizes the physical boundary and replaces that
global orthogonality by the Gram kernel `(PC.5)`.

Nor does Proof 348 reject the complete endpoint owner.  The following pieces
are absent from `(PC.12)`:

```text
the normalized complete Euler product;
the quotient Gram inverse of Proof 343;
the Sonin branch with its identical prime history;
the prolate correction;
the exact half-density residue cancellation of Proof 335.          (PC.20)
```

Those pieces must convert the coherent prime cluster before any `S_2` norm.
The corrected mixed near target is therefore stronger than Proof 347
`(AS.30)`: its proof may use Proof 344 only after establishing an exact
same-object nonlinear orthogonalization.  It may not obtain that
orthogonalization by norming the linear logarithmic crossings.

## 7. Reproducible arithmetic/Gram certificate

The companion script uses the normalized indicator root

```text
g=1_[-B,B]/sqrt(2B),
Gamma_g(h)=max(0,1-|h|/(2B)),                        (PC.21)
```

enumerates primes in `[X,(1+epsilon)X]`, and evaluates both sides of
`(PC.13)` together with `(PC.17)`.  The discontinuous root is used only because
its autocorrelation is exact; smooth nonnegative approximations preserve the
lower bound `(PC.9)`.

Run in WSL2 without a Lean build:

```text
python3 -B docs/proofs/348_prime_cluster_local_s2_obstruction_probe.py
```

The script is an arithmetic certificate for the exact Gram formula.  The
continuous proof is `(PC.4)--(PC.19)`.

The default WSL2 run reports

```text
+---------+--------+------------+------------+------------+-----------+
| X       | primes | diagonal E | Gram S2^2  | lower bound| Gram / E  |
+---------+--------+------------+------------+------------+-----------+
|     100 |      4 | 0.1774028  |   0.683453 |   0.606000 |      3.85 |
|    1000 |     16 | 0.1059267  |   1.637818 |   1.454400 |     15.46 |
|   10000 |    106 | 0.0935936  |   9.587239 |   8.511271 |    102.43 |
|  100000 |    861 | 0.0948560  |  78.948670 |  70.193842 |    832.30 |
| 1000000 |   7216 | 0.0953627  | 665.296321 | 591.652912 |   6976.49 |
+---------+--------+------------+------------+------------+-----------+
```

At the largest scale, `Gram*log(X)/X=0.00919`, already stable across the
last three rows, while the diagonal energy tends to
`log(1.1)=0.09531...`.  This is the predicted `X/log(X)` versus constant
separation.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| compact-root crossing Gram                     | closed                    |
| coherent short prime cluster                   | proved                    |
| raw-log localized S2/Koplienko route           | rejected                  |
| Proof 344 inside complete nonlinear owner      | still viable             |
| mixed nonlinear orthogonalization theorem      | open, Gate 3U near bottom|
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
