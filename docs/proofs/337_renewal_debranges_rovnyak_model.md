# Proof 337: Renewal de Branges--Rovnyak model

Date: 2026-07-17

Status: exact replacement of Proofs 290--296's finite renewal grid by the
canonical observability model of one pure contraction.  The right-path range
converges to a de Branges--Rovnyak model space whose reproducing kernel is
contractively dominated by the Hardy kernel, uniformly in the finite prime
set.  Proof 298's reciprocal-gap obstruction is therefore avoided rather than
estimated sector by sector.

This does not yet prove that the complete root/Sonin boundary functional is a
uniform Hardy-bounded Hankel functional.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+---------------------------------------------------+--------------------------+
| layer                                             | judgment                 |
+---------------------------------------------------+--------------------------+
| renewal state contraction                        | Delta                     |
| canonical defect output                          | exact                     |
| finite observability path                        | exact isometry            |
| infinite observability range                     | de Branges--Rovnyak model |
| renewal path projection limit                    | exact for fixed S         |
| model reproducing kernel                         | Hardy dominated           |
| constants                                        | independent of S          |
| finite-horizon reflected zero counting           | no longer used            |
| source root/Sonin Hardy functional               | open                      |
| Gate 3U and RH                                    | open / unproved          |
+---------------------------------------------------+--------------------------+
```

The new coordinate is

```text
Proof 290 renewal path
  -> pure contraction Delta
  -> isometric observability map O_Delta
  -> model projection P_Delta
  -> universal Hardy-kernel domination
  -> prove one source Hankel/Carleson bound
  -> Gate 3U.                                           (BU.1)
```

This supersedes the proposed attempt to add another fixed-mode zero to Proof
296. Proof 298 proves that such a local zero ledger is nonuniform at the
reciprocal survival-gap scale.

There are two related contraction models and they must not be conflated:

```text
Delta model:
  owns Proof 290's finite right-path range projection;

D=sqrt(Delta) model:
  owns Proof 270's renewal scalar Tr(C_L* C_K).       (BU.1a)
```

Sections 2--7 use the first model.  Section 7a records the second model,
which is the direct scalar owner.

## 2. The exact defect pair

Retain Proof 290's state objects on the source band:

```text
K* K=Gamma,
Delta=I-Gamma,
0<=Delta<I                                           (BU.2)
```

for each fixed finite `S`. Define

```text
C=K(I+Delta)^(1/2).                                  (BU.3)
```

All functions of `Delta` commute with `Gamma=I-Delta`, hence

```text
C* C
 =(I+Delta)^(1/2)(I-Delta)(I+Delta)^(1/2)
 =I-Delta^2.                                        (BU.4)
```

Thus the block column

```text
[Delta; C]                                           (BU.5)
```

is an isometry. No lower spectral bound for `Gamma` occurs in `(BU.4)`.

## 3. Finite observability isometry

For a horizon `n`, define

```text
O_n x
 =(Cx,C Delta x,...,C Delta^n x,Delta^(n+1)x).       (BU.6)
```

Using `(BU.4)`,

```text
O_n*O_n
 =sum_(k=0)^n Delta^k(I-Delta^2)Delta^k
   +Delta^(2n+2)
 =I.                                                 (BU.7)
```

Therefore every `O_n` is an exact isometry, uniformly in `S` and `n`. Its
range projection is

```text
Pi_n=O_n O_n*.                                       (BU.8)
```

Proof 290's right path is

```text
R_n x
 =(Kx,K Delta x,...,K Delta^n x,Delta^(n+1)x).       (BU.9)
```

On the emission slots,

```text
K Delta^k
 =C Delta^k(I+Delta)^(-1/2).                        (BU.10)
```

The only finite-horizon mismatch between `(BU.6)` and `(BU.9)` is the
survivor-tail preconditioning. Since `norm(Delta)<1` for fixed finite `S`,
that tail tends to zero. Consequently the orthogonal right-path projection

```text
P_n=R_n(R_n*R_n)^(-1)R_n*                            (BU.11)
```

converges in norm, for fixed `S`, to the same infinite observability range
projection as `Pi_n`.

This convergence is not uniform in `S`; it is used only to identify the exact
infinite model. The model's kernel bound below is uniform.

## 4. Infinite model and reproducing kernel

Since `norm(Delta)<1`, the infinite observability operator

```text
O x=(Cx,C Delta x,C Delta^2 x,... )                  (BU.12)
```

is an isometry from the band space into vector-valued Hardy space
`H2(H_E)`. In analytic notation,

```text
(O x)(z)=C(I-z Delta)^(-1)x.                         (BU.13)
```

Its closed range is a reproducing-kernel Hilbert space with kernel

```text
K_Delta(z,w)
 =C(I-z Delta)^(-1)
   (I-conj(w)Delta)^(-1)C*.                         (BU.14)
```

The isometric colligation theorem supplies an operator-valued Schur function
`S_Delta` such that

```text
K_Delta(z,w)
 =[I-S_Delta(z)S_Delta(w)*]/[1-z conj(w)].           (BU.15)
```

Primary source:

```text
Joseph A. Ball and Vladimir Bolotnikov,
de Branges--Rovnyak spaces: basics and theory,
Theorem 1 and the observability construction around equations (4.8)--(4.12),
arXiv:1405.2980.
https://arxiv.org/abs/1405.2980
```

Equation `(BU.15)` is a structural theorem, not the Gate estimate.

## 5. Uniform Hardy domination

Because `S_Delta` is Schur, the difference between the Hardy kernel and
`K_Delta` is positive. Hence

```text
0<=K_Delta<=K_Hardy,
K_Hardy(z,w)=I/[1-z conj(w)].                        (BU.16)
```

In particular, for `0<=r<1`,

```text
(1-r^2)
 C(I-r Delta)^(-1)(I-r Delta)^(-1)C*
 <=I.                                                (BU.17)
```

The constant in `(BU.17)` is exactly one and is independent of:

```text
the visible finite prime set S;
the smallest eigenvalue of Gamma;
the path horizon;
the Euler condition number.                         (BU.18)
```

This is the uniform resource that the reflected path blocks did not expose.

## 6. Exact location of the remaining near theorem

Let `mathcalW` be the constant coefficient-wise output detector on
`H2(H_E)`, and retain the band detector `W_B`. The observability
intertwinement defect is

```text
mathfrakD_W(z)
 =mathcalW C(I-z Delta)^(-1)
  -C(I-z Delta)^(-1)W_B.                            (BU.19)
```

Its Taylor coefficients are the normalized version of Proof 291's single
path generator and its descendants. The off-model component is

```text
(I-P_Delta)mathfrakD_W.                              (BU.20)
```

Proof 293's physical readback remains

```text
g_W
 =-E W C_outer A iota_B
  -E A R[W,R]iota_B,                                (BU.21)
```

with the outer and Sonin terms kept signed. Substituting
`R=E E_hat E-K_prol` must still occur inside `(BU.21)`.

The near Gate 3U theorem is now the following Hardy-model statement:

```text
the Q-root-completed boundary functional of
  (I-P_Delta)mathfrakD_W

extends continuously to H2(H_E), with norm

 <=C(1+B_root)^d norm(eta)_(H^r)norm(xi)_(H^r),     (BU.22)
```

uniformly in finite `S`.

Once `(BU.22)` is proved, `(BU.16)` makes its restriction to every
`H(S_Delta)` no larger. The horizon limit and reciprocal-gap boundary layer
then require no separate estimate.

The missing step is source-specific: it must identify the boundary functional
in `(BU.22)` with the actual compact-root outer-minus-Sonin Hankel functional.
The generic de Branges--Rovnyak theorem does not do that.

## 7. Why this is stronger than another path estimate

Proof 298 found nonzero hyperbolic limits for all four Proof 296 parity
sectors when

```text
n(1-Delta) approximately constant.                  (BU.23)
```

Equations `(BU.7)--(BU.17)` already include that boundary layer. The
contraction may approach one arbitrarily closely; the observability map is
still isometric and its kernel is still Hardy dominated.

Therefore the allowed near proof order is

```text
complete physical generator
  -> infinite observability defect
  -> Q-root boundary functional
  -> Hardy/Hankel norm
  -> de Branges--Rovnyak restriction
  -> one absolute value.                              (BU.24)
```

Do not return to:

```text
fixed-horizon zero counting;
positive sums over path blocks;
norm(L_n) or norm(Z_n);
finite-sector trace cycles;
primewise expansion of Delta.                        (BU.25)
```

## 7a. Direct survivor model for the scalar response

Proof 270 uses

```text
D=Delta^(1/2),
K*K=I-D^2.                                           (BU.25a)
```

Thus the direct survivor observability map

```text
O_D x=(Kx,KDx,KD^2x,...),
(O_D x)(z)=K(I-zD)^(-1)x                             (BU.25b)
```

is an isometry.  Its kernel

```text
K_D(z,w)
 =K(I-zD)^(-1)(I-conj(w)D)^(-1)K*                  (BU.25c)
```

is again a de Branges--Rovnyak kernel and is contractively dominated by the
full Hardy kernel.  This is the exact model behind Proof 270's right survivor
column, not merely a finite-horizon limit.

For the complete physical reward `L_W`, put

```text
F_L(z)=L_W(I-zD)^(-1),
F_K(z)=K(I-zD)^(-1).                                 (BU.25d)
```

For `0<r<1`, coefficient orthogonality gives the exact Abel pairing

```text
integral_T Tr(F_L(r zeta)* F_K(r zeta)) d zeta
 =sum_(k>=0) r^(2k)
    Tr((L_W D^k)*(K D^k)).                           (BU.25e)
```

The fixed-`S` limit `r->1` is Proof 270's extended trace
`Tr(C_L* C_K)`.  Equation `(BU.25e)` removes the renewal horizon and lower
spectral gap without cycling an infinite-dimensional trace.

This direct model does not by itself preserve Proof 289's separate
`I-G_S` and outer-escape channels.  Recombining those channels into `Delta`
before compact support is exactly the circular return in
`(AZ.26a)--(AZ.26c)`.  Therefore Hardy domination may be applied only after a
source functional has retained that complete signed physical information.

There is also no automatic quadratic prime ledger.  Proof 289 proves

```text
I-G_p
 =p^(-1/2) R_p(I-U_p)(I-U_p*)R_p*.                  (BU.25f)
```

The leading coefficient is still `p^(-1/2)`, not `p^(-1)`.  Any additional
half-power must come from the completed source pairing or from a complete
product cancellation; it cannot be asserted from `I-G_p` alone.

## 8. Finite certificate

The companion probe constructs `(BU.3)--(BU.11)` from Proof 290's existing
source-shaped finite model.  It also constructs `(BU.25a)--(BU.25c)` for the
direct survivor model. It reports

```text
defect identity error             8.34e-16,
direct survivor isometry error    8.94e-16,
Hardy kernel violation            0,
maximum exact error               1.06e-15.
```

The renewal/model projection gap decreases as

```text
+---------+------------------------+
| horizon | projection gap         |
+---------+------------------------+
|       1 | 3.910e-2               |
|       2 | 1.586e-2               |
|       4 | 2.582e-3               |
|       8 | 7.171e-5               |
|      16 | 6.260e-8               |
|      32 | 5.748e-14              |
+---------+------------------------+
```

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/337_debranges_rovnyak_observability_probe.py
```

The convergence is a finite certificate of the coordinate, not evidence for
the continuous source functional `(BU.22)`.

## 9. Route judgment

```text
far source Schur lane:                    closed mathematically by 333--336;
finite renewal horizon:                   eliminated as estimator;
near complete-product contraction model:  closed algebraically here;
uniform near Hardy/Hankel functional:      open;
Gate 3U:                                  open;
finite-S sign / Burnol identity / RH:      open.       (BU.26)
```

The next proof must construct the explicit Hardy Hankel kernel of
`(BU.21)` after `Q` and prove its trace/Sobolev norm on the full Hardy space.
Only then may `(BU.16)` transfer the estimate uniformly to all finite `S`.
