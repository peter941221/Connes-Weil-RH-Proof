# Proof 355: half-angle detector split

Date: 2026-07-18

Status: exact half-angle realization of Proof 354's canonical midpoint and a
condition-number-free split of its detector corner.  The part coming from the
detector diagonal contains an additional half-sine factor; only the genuine
old-projection detector crossing survives at zeroth angular order.

This reduces the analytic near row but does not bound that surviving crossing
uniformly in the finite Euler set.  Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| canonical midpoint as a half-angle graph      | exact                     |
| old graph sine -> midpoint range corner        | same singular values      |
| midpoint detector corner split                | exact                     |
| diagonal detector contribution                | one extra half-sine       |
| old detector crossing contribution             | no Euler condition number|
| finite certificate                            | passes                    |
| uniform old-crossing row                       | open, next bottom         |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The reduction is

```text
Proof 354 midpoint corner D_W
  -> rotate by the canonical half angle
  -> split W into old diagonal/off-diagonal blocks
  -> diagonal part earns a half-sine
  -> only old physical crossing remains at order zero.          (HA.1)
```

## 2. Graph cosine and sine

Let `P` be the old orthogonal projection.  Relative to

```text
H=Ran(P) orthogonal-direct-sum Ran(I-P),             (HA.2)
```

write the normalized isometry of the new graph as

```text
V=[C;S],
C=C*>0,
C^2+S*S=I.                                          (HA.3)
```

Let

```text
D=(I-SS*)^(1/2).                                    (HA.4)
```

The canonical direct rotation from `P` to the graph projection is

```text
mathcalU=[[C,-S*],[S,D]].                            (HA.5)
```

The defect intertwining relation

```text
DS=SC                                                   (HA.6)
```

makes `(HA.5)` unitary.  This is the operator-valued cosine--sine
decomposition; no scalar principal-angle basis is selected.

## 3. Canonical half rotation

Define

```text
C_h=((I+C)/2)^(1/2),
S_h=S[2(I+C)]^(-1/2),
D_h=((I+D)/2)^(1/2).                                (HA.7)
```

Functional calculus and `(HA.6)` give

```text
C_h^2+S_h*S_h=I,
D_h^2+S_h S_h*=I,
D_h S_h=S_h C_h.                                    (HA.8)
```

Hence

```text
mathcalU_h=[[C_h,-S_h*],[S_h,D_h]]                  (HA.9)
```

is unitary and `mathcalU_h^2=mathcalU`.  The canonical midpoint projection is

```text
Q=mathcalU_h P mathcalU_h*
  =[C_h;S_h][C_h;S_h]*.                             (HA.10)
```

The complementary midpoint isometry is

```text
V_h_perp=[-S_h*;D_h].                               (HA.11)
```

In these coordinates, Proof 354's range corner is unitarily equivalent to the
full-angle graph sine `S`; in particular the two have the same nonzero
singular values.

## 4. Exact detector split

Write a bounded self-adjoint detector in the old coordinates as

```text
W=[[W_00,W_01],[W_10,W_11]],
W_01=W_10*.                                         (HA.12)
```

Proof 354's midpoint detector corner is

```text
D_W=V_h_perp* W [C_h;S_h].                          (HA.13)
```

Split `W=W_diag+W_off` relative to `P`.  Direct block multiplication gives

```text
D_diag
 =-S_h W_00 C_h+D_h W_11 S_h,                       (HA.14)

D_off
 =-S_h W_01 S_h+D_h W_10 C_h,                       (HA.15)

D_W=D_diag+D_off.                                   (HA.16)
```

Equation `(HA.14)` contains at least one half-sine in every term.  Equation
`(HA.15)` contains the genuine old detector crossing

```text
K_W=(I-P)WP=W_10                                    (HA.17)
```

through contractions only.  No inverse Euler factor, graph tangent, or Gram
condition number appears outside `K_W`.

## 5. Hilbert--Schmidt consequence

Whenever `K_W` and `S_h` are Hilbert--Schmidt, ideal contraction gives

```text
norm(D_off)_2<=sqrt(2) norm(K_W)_2,
norm(D_diag)_2<=2 norm(W) norm(S_h)_2.               (HA.18)
```

The first inequality follows more invariantly because the full off-diagonal
operator `W_off` has

```text
norm(W_off)_2^2=2 norm(K_W)_2^2,                    (HA.19)
```

and `D_off` is one compression of `W_off` by two isometries.  Also

```text
norm(S_h)_2^2
 =Tr[(I-C)/2]
 <=(1/2)Tr[I-C^2]
 =(1/2)norm(S)_2^2.                                 (HA.20)
```

Therefore

```text
norm(D_W)_2^2
 <=4 norm(K_W)_2^2+4 norm(W)^2 norm(S)_2^2.          (HA.21)
```

The constants are independent of the Euler coefficient and of every earlier
prime.  Equation `(HA.21)` is deliberately loose but condition-number free.

## 6. Sequential consequence

For the `j`-th Julia step, the second term in `(HA.21)` carries an additional
graph sine.  After the common source/root pullback used in Proof 351, its
weighted contribution is controlled by the existing range Bessel row.

The only new source estimate still required by the midpoint method is thus the
old-crossing row

```text
sum_(log(p_j)<=L)
  norm((I-P_(j-1)) W P_(j-1) A_root)_2^2/(p_j-1)

 <=C_root L(1+L).                                   (HA.22)
```

Here `P_(j-1)` is the literal Gram-corrected Proof 343 quotient projection,
not a raw half-line support projection.  The factor `A_root` denotes the
single source-owned Hilbert--Schmidt input required by Proof 351; it may not
be chosen separately for every prime.

Equation `(HA.22)` is strictly narrower than Proof 354 `(MI.20)`: all
diagonal-intertwining terms have been paid for by the Julia angle row.  It is
not yet proved.

## 7. Guard against a false shortcut

It is invalid to replace `(HA.22)` by

```text
sup_j norm((I-P_j)WP_j)_2<infinity                 (HA.23)
```

unless that supremum is proved from the complete real-line
outer-minus-Sonin-plus-prolate geometry.  Proof 261 gives fixed-`S` ideal
legality with constants depending on `S`; Proof 348 shows that raw translated
half-line crossings can add coherently before Gram orthogonalization.

The half-angle split says where the remaining zeroth-order detector crossing
lives.  It does not bound it by declaration.

## 8. Reproducible certificate

The companion probe constructs commuting Euler translations, a random source
subspace, and a self-adjoint detector.  At every sequential prime step it
checks

```text
the direct half-angle frame and midpoint projection;
mathcalU_h^2=mathcalU;
the exact detector split `(HA.14)--(HA.16)`;
equality of midpoint and graph-sine singular values;
the Hilbert--Schmidt inequalities `(HA.18)--(HA.21)`. (HA.24)
```

Run after the five-batch research phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/355_half_angle_detector_split_probe.py
```

The unified WSL2 run reports maximum exact error
`7.339378462921e-15`; every Hilbert--Schmidt bound violation is zero.

The probe certifies finite operator algebra only.  It does not prove
`(HA.22)`.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| midpoint half-angle frame                     | exact                     |
| old-coordinate quadratic detector term         | retained and angle-paid  |
| surviving zeroth-order crossing                | literal `(I-P)WP`        |
| condition-number dependence                    | absent                   |
| uniform old-crossing row `(HA.22)`             | open, active near bottom |
| Proof 336 far lane                             | already closed            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
