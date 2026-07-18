# Proof 388: Gram/Julia prefix alignment audit

Date: 2026-07-18

Status: exact comparison of the moving Gram-normalized prefix with Proof
351's Julia defect prefix.  The moving frame and the sequential canonical
graph frame differ by a unitary cocycle.  The Julia prefix is instead a
genuine contraction product.  They are not coordinate versions of one
another.

An explicit two-dimensional one-parameter unitary group, using the route
coefficients for `p=2,3`, makes the first Julia transfer zero while the next
physical graph sine is nonzero.  Thus the abstract prefix geometry does not
imply Proof 382 `(JR.19)` or even its kernel condition.  A source-specific
causal boundary theorem is still possible, but it must insert the Julia
transfer product as a real operator factor.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| direct Gram-normalized prefix                 | isometric frame          |
| sequential canonical graph frame             | isometric frame          |
| relation between the two                      | unitary cocycle          |
| Julia prefix `Psi`                            | contraction product      |
| `unitary cocycle = Psi`                       | false in general        |
| abstract Julia kernel alignment               | false, exact guard      |
| source-specific causal insertion              | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Two legitimate source coordinates

Let the inverse Euler factors before step `j` be `T_1,...,T_(j-1)` and put

```text
T_<j=T_(j-1)...T_1.                               (GA.1)
```

The direct Gram-normalized frame used in Proofs 343 and 368 is

```text
N_<j
 =T_<j U_0(U_0* T_<j* T_<j U_0)^(-1/2).          (GA.2)
```

It is an isometry from `K_0` onto the current range `K_(j-1)`.

Proofs 350--351 construct a different canonical isometry.  If `V_k` is the
positive-cosine graph isometry for the `k`-th step, then

```text
J_0=U_0,
J_k=V_k J_(k-1).                                  (GA.3)
```

This is also an isometry from `K_0` onto `K_k`.

## 3. Exact unitary cocycle

Since `N_<j` and `J_(j-1)` have the same initial space and the same closed
range, define

```text
Omega_(j-1)=J_(j-1)* N_<j.                        (GA.4)
```

Then

```text
Omega_(j-1)*Omega_(j-1)=I,
Omega_(j-1)Omega_(j-1)*=I,                        (GA.5)

N_<j=J_(j-1)Omega_(j-1).                         (GA.6)
```

Thus the direct polar coordinate differs from the sequential graph coordinate
only by a unitary cocycle.  It does not differ by a strict contraction.

For a physical right leg pulled back through `(GA.2)`, the range sine is

```text
S_j N_<j A_root
 =S_j J_(j-1)Omega_(j-1)A_root.                  (GA.7)
```

## 4. The Julia prefix is not that cocycle

Proof 351 instead defines

```text
F_k=J_(k-1)*Phi_kJ_(k-1),
Psi_0=I,
Psi_k=F_kPsi_(k-1),                               (GA.8)
```

where `Phi_k` is the Julia transfer contraction.  Its defect is

```text
D_k^2=I-F_k*F_k.                                  (GA.9)
```

Whenever the current range is not invariant under the translation, `D_k`
can be nonzero.  Then `F_k`, and hence generally `Psi_k`, is not unitary.
Equations `(GA.5)` and `(GA.9)` show that

```text
Omega_k=Psi_k                                     (GA.10)
```

cannot be a coordinate identity.

The actual Julia range row is

```text
S_jJ_(j-1)Psi_(j-1)A_root.                        (GA.11)
```

Comparing `(GA.7)` and `(GA.11)`, equality on the chosen source requires the
additional annihilation theorem

```text
S_jJ_(j-1)(Omega_(j-1)-Psi_(j-1))A_root=0.        (GA.12)
```

No Gram normalization, unitary pullback, or window containment proves
`(GA.12)`.

## 5. Exact two-dimensional guard

Take

```text
H=C^2,
K_0=span(e_1),
a=1/sqrt(2),
b=sqrt(1-a^2),                                    (GA.13)

U_1=[[-a,b],
     [ b,a]].                                     (GA.14)
```

The matrix `U_1` is self-adjoint unitary.  Relative to `K_0`, its Julia
transfer at the route coefficient `a` is

```text
Phi_1
 =-a+a b^2/(1-a^2)
 =0.                                              (GA.15)
```

Choose a self-adjoint generator `X` with

```text
exp(i log(2) X)=U_1,                              (GA.16)
```

and define the commuting translation group `U(t)=exp(i t X)`.  At the next
prime use

```text
U_2=U(log(3)),
a_2=1/sqrt(3).                                    (GA.17)
```

The two spectral values of `U_2` are distinct, while the transported line
`K_1=(I-aU_1)^(-1)K_0` contains both spectral components.  Therefore `K_1`
is not invariant under `U_2`, and its second graph sine satisfies

```text
S_2!=0.                                           (GA.18)
```

But `(GA.15)` gives

```text
Psi_1=0,
S_2J_1Psi_1=0,                                   (GA.19)
```

whereas the direct moving frame gives

```text
S_2J_1Omega_1!=0.                                 (GA.20)
```

Hence

```text
ker(S_2J_1Psi_1) not-subset ker(S_2J_1Omega_1).   (GA.21)
```

This is exactly the Douglas-kernel failure from Proof 382 `(JR.14)`.  The
guard uses commuting members of one unitary group and the genuine
`p^(-1/2)` coefficients; it is not an artifact of noncommuting synthetic
prefixes.

## 6. Consequence for Proof 387

Proof 387's right insertion column is

```text
Ahat_j=mathcalA_jU_0H_j^(-1/2).                   (GA.22)
```

After the ambient/source coordinate is pulled back, its frame part carries
`Omega_(j-1)`, not `Psi_(j-1)`.  The quotient-correction slots also contain
right-dressed factors `A_rV_jE`.  Therefore the following inference is
invalid:

```text
fixed near window
  + same transported range
  + unitary source pullback
  => Ahat_j factors through the Julia row.         (GA.23)
```

The source-specific theorem still needed is one of the following equivalent
kinds:

```text
1. derive an exact causal identity which inserts every F_k into `(GA.22)`;

2. prove directly that the complete corrected physical column vanishes on
   the Julia kernel and satisfies Proof 382 `(JR.19)`;

3. replace the Julia row by a different Bessel owner whose prefixes are the
   actual unitary cocycles and prove its square estimate.         (GA.24)
```

Option 3 is not supplied by the present geometry: a row of unitary prefixes
has no defect telescope analogous to Proof 351 `(JB.9)`.

## 7. Reproducible certificate

The companion probe has two cohorts.  A multi-step commuting translation
model checks

```text
the graph defect identity and sequential graph frames;
the direct/sequential range equality;
the unitary cocycle `(GA.4)--(GA.6)`;
the Julia defect telescope;
the nonzero physical/Julia right-leg mismatch.     (GA.25)
```

The exact two-dimensional cohort checks `(GA.13)--(GA.21)` and reports the
physical leakage left after the Julia column has vanished.

Run only after Proofs 385--389 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/388_gram_julia_prefix_alignment_audit_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| direct/sequential frame relation              | closed `(GA.6)`          |
| automatic `Omega=Psi` alignment               | rejected `(GA.15)`      |
| abstract Douglas kernel condition             | rejected `(GA.21)`      |
| Proof 387 fixed-prefix insertion              | retained                 |
| Proof 382 `(JR.9)/(JR.19)`                    | still open               |
| next analytic producer                        | causal Julia insertion   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
