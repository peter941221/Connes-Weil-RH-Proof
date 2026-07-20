# Proof 420: relative log-partition cocycle

Date: 2026-07-19

Status: exact finite-dimensional determinant-line theorem.  The corrected
four-term weighted determinant from Proof 407 is frame invariant, obeys an
exact multiplicative cocycle on the moving carrier, and differentiates to the
ordered projection-response cocycle of Proofs 400--401.  A scalar Hardy guard
shows that its Gram/Jacobian counterterm is quadratic in one Euler amplitude,
while the completed detector response remains linear.

Thus the determinant cocycle supplies the correct bookkeeping but no automatic
half-power gain.  A Gate 3U proof must estimate the complete signed Burnol
cocycle before the first absolute value.  This proof does not construct the
infinite root-relative determinant, prove that estimate, prove the finite-`S`
sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+---------------------------+
| layer                                                | judgment                  |
+------------------------------------------------------+---------------------------+
| normalized four-term determinant                    | frame invariant           |
| product transport                                    | exact moving-space cocycle|
| detector derivative                                 | projection response       |
| derivative cocycle                                  | Proof 400/401 telescope   |
| one-factor Gram/Jacobian counterterm                 | `a^2+O(a^4)`             |
| one-factor completed detector response               | `2ca+O(a^2)`             |
| local energy-to-response estimate                    | rejected                  |
| global signed square/energy estimate                 | open, source-specific     |
| Gate 3U / finite-S sign / Burnol / RH                 | open / open / open / open |
+------------------------------------------------------+---------------------------+
```

The distinction proved below is

```text
correct determinant line
  -> exact multiplicative telescope
  -> exact signed local projection increments;

correct determinant line
  -/-> each local increment is quadratic in `p^(-1/2)`.
                                                               (LP.1)
```

## 2. Frame-invariant relative partition

Let `M` be an `r`-dimensional subspace of a finite-dimensional Hilbert space
`H`, and let

```text
J : C^r -> H                                             (LP.2)
```

be any injective frame with range `M`.  It need not be isometric.  Let `m` be
invertible on `H`, let `W=W*`, and let `s` be real.  Define

```text
L_J(m;s)
 :=log det(J* m* exp(sW) m J)
   -log det(J* m* m J),                                (LP.3)

Psi_M(m;s)
 :=L_J(m;s)-L_J(I;s).                                  (LP.4)
```

Every matrix inside a logarithm is positive definite, so `(LP.3)` uses the
ordinary real logarithm.  Equation `(LP.4)` is exactly the finite version of
Proof 407's four-term relative determinant.  The fixed Burnol weight is part
of `J`; if `M=g_0 K_Theta`, then `J=g_0 J_Theta` and no weight is discarded.

Replace the frame by `J C`, where `C` is invertible on `C^r`.  For every
positive Gram matrix `A`,

```text
det(C* A C)=abs(det C)^2 det A.                       (LP.5)
```

The factor `abs(det C)^2` cancels once in each difference in `(LP.3)`.
Therefore `L_J`, and hence `Psi_M`, depends only on the subspace `M` and not on
the chosen coordinates.

This cancellation is why all four terms are required.  A numerator-only
determinant is a frame-dependent quantity.

## 3. Exact product chain rule

Let `m_1,m_2` be invertible, and use the natural frame

```text
J_1=m_1 J                                               (LP.6)
```

for the moving space `m_1 M`.  Directly from `(LP.3)`,

```text
L_(J_1)(m_2;s)=L_J(m_2 m_1;s),
L_(J_1)(I;s)  =L_J(m_1;s).                            (LP.7)
```

Subtracting the two identities and then inserting `L_J(I;s)` gives

```text
Psi_M(m_2 m_1;s)
 =Psi_(m_1 M)(m_2;s)+Psi_M(m_1;s).                    (LP.8)
```

There is no commutativity assumption on `m_1,m_2,W`.  Iterating, with

```text
M_j=m_j ... m_1 M_0,                                  (LP.9)
```

gives the exact ordered telescope

```text
Psi_(M_0)(m_n ... m_1;s)
 =sum_(j=1)^n Psi_(M_(j-1))(m_j;s).                  (LP.10)
```

Equation `(LP.10)` is the finite determinant-line version of Proof 400's
signed local cocycle.  It does not replace the moving carrier `M_(j-1)` by the
fixed initial carrier.

## 4. Detector derivative and Proof 400

The orthogonal projection onto the transported range is

```text
P_(mM)
 =m J (J* m* m J)^(-1) J* m*.                        (LP.11)
```

Jacobi's log-determinant identity gives

```text
partial_s L_J(m;s)|_(s=0)=Tr(W P_(mM)).               (LP.12)
```

Consequently

```text
partial_s Psi_M(m;s)|_(s=0)
 =Tr(W(P_(mM)-P_M)).                                  (LP.13)
```

Differentiating `(LP.8)` gives

```text
Tr(W(P_(m_2m_1M)-P_M))

 =Tr(W(P_(m_2m_1M)-P_(m_1M)))
  +Tr(W(P_(m_1M)-P_M)).                               (LP.14)
```

After Proof 401 identifies

```text
rho_j^(-1) Tr(f_j)=Tr(W(P_j-P_(j-1))),                (LP.15)
```

equations `(LP.10)--(LP.14)` are exactly Proof 400's normalized trace
telescope.  The four-term determinant therefore preserves, rather than
replaces, the signed local owner.

## 5. The Gram counterterm does not square the response

The simplest Hardy model decides the local scale exactly.  Work on the disk
Hardy space, take

```text
M=K_z=span{1},
m_a(z)=1/(1-a z),
W(e^(i theta))=2c cos(theta),
0<a<1.                                                (LP.16)
```

The normalized transported density is the Poisson kernel

```text
P_a(theta)
 =(1-a^2)/abs(1-a e^(i theta))^2
 =1+2 sum_(n>=1) a^n cos(n theta).                    (LP.17)
```

With normalized circle integration, `(LP.4)` becomes

```text
Psi_a(s)
 =log [ integral P_a(theta) exp(2cs cos(theta)) dtheta
        / integral exp(2cs cos(theta)) dtheta ].      (LP.18)
```

Differentiation at the detector origin uses the reproducing property of the
Poisson kernel:

```text
Psi_a'(0)=2ca.                                        (LP.19)
```

Now split the four terms into the tilted determinant ratio and its Gram
normalization:

```text
T_a(s)
 :=log integral abs(m_a)^2 exp(2cs cos(theta)) dtheta
   -log integral exp(2cs cos(theta)) dtheta,

G_a
 :=log integral abs(m_a)^2 dtheta
   =-log(1-a^2),

Psi_a(s)=T_a(s)-G_a.                                  (LP.20)
```

The normalization has the exact expansion

```text
G_a=a^2+O(a^4).                                       (LP.21)
```

For fixed nonzero `s`, put

```text
mu_s
 := integral cos(theta) exp(2cs cos(theta)) dtheta
    / integral exp(2cs cos(theta)) dtheta.            (LP.22)
```

Equation `(LP.17)` gives

```text
Psi_a(s)=2a mu_s+O(a^2),
T_a(s)  =2a mu_s+O(a^2).                              (LP.23)
```

Thus the Gram/Jacobian counterterm is genuinely quadratic, but the tilted
detector determinant and their completed difference both retain the odd
half-power.  This is the determinant-level form of Proofs 402 and 418.

The conclusion is not that the full Euler product is unbounded.  It is the
more precise guard

```text
abs(local response) <= C local quadratic energy       (LP.24)
```

is false.  Any quadratic gain must occur after the complete signed telescope,
for example through a source-specific square estimate, not by estimating the
terms of `(LP.10)` separately.

## 6. Literature boundary

Migler proves the relevant abstract determinant contracts:

```text
Joseph Migler,
Functional Calculus and Joint Torsion of Pairs of Almost Commuting Operators,
https://arxiv.org/abs/1409.6289

Lemma 2.6:
  [A,B] in S_1
  -> tau(exp A,exp B)=exp(Tr[A,B]);

Lemma 2.8(1):
  joint torsion is multiplicative in a product variable;

Theorem 5.2:
  f,g in L_infinity intersection W^(1/2,2)
  -> [T_f,T_g] in S_1;

Theorem 5.15:
  smooth nonvanishing circle symbols
  -> the Helton--Howe/Carey--Pincus integral formula. (LP.25)
```

These theorems support the determinant-line analogy but do not construct the
route object.  A continuous atomic prime-log translation has a non-Hilbert--
Schmidt sharp-half-line crossing.  Proof 261 obtains `S_1` only after the
compact-root-completed detector difference is assembled.  Therefore the raw
Euler Toeplitz pair has not been shown to satisfy the hypotheses needed to form
Migler's joint torsion and then differentiate it.  The standard circle-symbol
theorem does not supply those hypotheses for this real-line atomic owner.

The project chain rule `(LP.8)` is elementary finite Gram algebra.  Its
infinite Burnol successor still needs one completed root-relative determinant,
or an equivalent form-level construction of Proof 415's `Lambda_(S_F)(F)`.

## 7. Exact remaining theorem

Let the support-coupled canonical Euler family from Proof 416 be ordered as
`m_1,...,m_n`, and let `M_j` be `(LP.9)`.  The determinant organization says
that the desired near response is one completed scalar

```text
Lambda_(S_F)(F)
 =partial_s Psi_(M_0)(m_n ... m_1;s)|_(s=0)
 =sum_j partial_s Psi_(M_(j-1))(m_j;s)|_(s=0),        (LP.26)
```

provided the first equality is constructed on the actual weighted Burnol
carrier.  The second line is signed and may not be replaced by a sum of
absolute values.

The viable successor is a root-localized global estimate such as

```text
(abs Lambda_(S_F)(F))^2
 <=C_lambda (1+B_F)^d E(S_F)
      norm(F)_(R_(B_F)^r)^2,                          (LP.27)
```

or Proof 416 `(EN.7)` with another fixed polynomial of the same canonical
energy.  Proof 416 gives `E(S_F)=O((1+B_F)^2)`.  Equation `(LP.19)` is
compatible with `(LP.27)` because one local response is `O(a)` while its
energy is `O(a^2)`; it rejects only the stronger linear-in-energy local bound.

To prove `(LP.27)`, the outer, reflected second-support, and prolate terms must
remain recombined inside `Lambda` before compact support and before the final
absolute value.  The cocycle algebra alone supplies no such estimate.

## 8. Reproducible certificate

The companion script checks, in a noncommuting finite matrix model,

```text
frame invariance `(LP.5)`;
the product chain rule `(LP.8)`;
the detector derivative `(LP.13)`;
the derivative telescope `(LP.14)`.
```

It separately checks the Hardy identities `(LP.18)--(LP.23)` by circle
quadrature.  Run from the WSL2 ext4 verification mirror:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/420_relative_log_partition_cocycle_probe.py
```

The analytic proofs are the determinant cancellation and Poisson expansion
above.  Floating-point output is only an implementation certificate.

## 9. Decision

```text
four-term weighted determinant owner:            exact finite model;
frame independence:                              exact `(LP.5)`;
moving-space product cocycle:                    exact `(LP.8)`;
Proof 400 derivative readback:                   exact `(LP.13)--(LP.15)`;
Gram counterterm scale:                          quadratic `(LP.21)`;
completed local response scale:                  linear `(LP.19),(LP.23)`;
termwise energy estimate:                        rejected;
global Burnol square/energy estimate `(LP.27)`: open;
Gate 3U / finite-S sign / Burnol / RH:            open / open / open / unproved.
```
