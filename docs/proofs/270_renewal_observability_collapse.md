# Proof 270: Renewal inverse as a signed observability column

Date: 2026-07-15

Status: exact fixed-`S` algebraic reduction of the Gate 3U renewal.  The common
inverse `Gamma^(-1)` disappears from the scalar trace.  The three physical
branches form one left reward map `L_W`, while the surviving Sonin-band map
`K=EAB` forms a right column over the renewal powers.  The right column is an
isometry.  Proof 273 shows that Gate 3U cannot estimate the complete left row
by a positive `H1` norm.  Compact support acts after the left/right scalar
pairing.

An ordinary operator-norm observability bound cannot finish the trace estimate.
An exact direct-sum guard keeps that norm fixed while the response and the
observability trace grow with the number of blocks.  The source proof must use
the compact root, the signed extended trace, and Proof 269's
coefficient-weighted chirp inside the left column.  That local square has scale
`p^(-m)` and is not summable over the first prime modes.  A compact-support
concentration factor makes that positive square-energy ledger summable, but
Proof 274 shows that the signed scalar still owns only one
`p^(-m/2)` coefficient before the complete physical cancellation.

No uniform source estimate, finite-S sign, arithmetic trace identity, or RH
proof follows from this reduction.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| complete numerator N_W=L_W* K                 | exact                        |
| renewal square root D=Delta^(1/2)              | exact                        |
| right survivor column                          | isometry                     |
| Gamma^(-1) in the scalar trace                 | eliminated                   |
| left observability Stein equation              | exact                        |
| ordinary observability operator norm           | insufficient by direct sum  |
| positive compact-root H1 column estimate       | rejected by Proof 273      |
| signed scalar local coefficient                | p^(-m/2), exact              |
| complete signed extra half-power               | open, Proof 274 (AK.12)      |
| finite-S sign and RH                           | unproved                     |
+------------------------------------------------+------------------------------+
```

The new control flow is

```text
three-branch reward L_W
  -> renewal observability column (L_W D^k)_k
  -> prime innovation refinement
  -> pairing with the survivor column
  -> real-line scalar trace
  -> stopped chirp and concentration estimate.           (AG.1)
```

## 2. One complete left reward

Use the source projections

```text
R<=E,
R<=Q,
B=E-R,
C=I-E.                                                  (AG.2)
```

Let `A=T^(-1)` be the normalized causal inverse and set

```text
K=E A B,
Gamma=K* K,
Delta=B-Gamma.                                         (AG.3)
```

Proof 266 decomposes the centered numerator into

```text
N_W=O_W+S_W+P_W,                                       (AG.4)

O_W=-B A* C[W,E]E A B,

S_W=B(I-Q)[W,Q]R A*E A B,

P_W=B Q W R A*E A B.                                  (AG.5)
```

Assume `W=W*`.  Define three maps from `Ran(B)` to the source Hilbert space:

```text
L_O=-[W,E]* C A B,

L_S=A R[W,Q]*(I-Q)B,

L_P=A R W Q B,

L_W=L_O+L_S+L_P.                                      (AG.6)
```

Taking adjoints in `(AG.6)` gives

```text
L_O* K=O_W,
L_S* K=S_W,
L_P* K=P_W.                                           (AG.7)
```

Therefore

```text
N_W=L_W* K.                                            (AG.8)
```

Equation `(AG.8)` keeps the Proof 258 cancellation inside `L_W`.  Estimating
the three summands in `(AG.6)` before their sum remains forbidden.

## 3. Replace the inverse by two columns

For fixed finite `S`, Proof 266 proves

```text
0<Gamma<=B,
0<=Delta<B,
Gamma=B-Delta.                                         (AG.9)
```

Put

```text
D=Delta^(1/2).                                         (AG.10)
```

Define the right survivor column and left reward column by

```text
C_K x=(K D^k x)_(k>=0),

C_L x=(L_W D^k x)_(k>=0).                             (AG.11)
```

Since `Gamma=B-D^2` commutes with `D`, the right Gram telescopes:

```text
C_K* C_K
 =sum_(k>=0)D^k K*K D^k

 =sum_(k>=0)D^k(B-D^2)D^k

 =B.                                                    (AG.12)
```

Thus `C_K` is an isometry on `Ran(B)`.  Its norm does not contain the Euler
condition number.

Proof 261 makes each fixed-`S` renewal term trace class after the prescribed
root smoothing.  Cyclicity on that completed term gives

```text
Tr_B(N_W Delta^k)
 =Tr_B(L_W* K D^(2k))

 =Tr_B((L_W D^k)*(K D^k)).                             (AG.13)
```

Summing `(AG.13)` yields

```text
Tr_B(N_W Gamma^(-1))
 =Tr_B(C_L* C_K),                                      (AG.14)
```

where the right side uses the same extended trace limit as the left side.
Equation `(AG.14)` removes `Gamma^(-1)` before estimation.

## 4. The left observability Gramian

The formal left column Gram is

```text
X_W:=C_L* C_L
 =sum_(k>=0)D^k L_W*L_W D^k.                          (AG.15)
```

It solves the discrete Stein equation

```text
X_W=L_W*L_W+D X_W D.                                  (AG.16)
```

This is the observability Gramian of the renewal contraction `D` with output
map `L_W`.  It contains the complete physical reward in every term.

A source theorem of the form

```text
L_W*L_W<=C Gamma                                      (AG.17)
```

would imply `X_W<=C B` by `(AG.12)`.  This operator-order estimate still does
not control the ordinary trace on an infinite-dimensional band.  The detector
root must enter the column norm before a trace estimate.

## 5. Direct-sum guard

Take one finite block satisfying `(AG.2)--(AG.10)` and form `N` orthogonal
copies.  The column identities become

```text
C_(K,N)*C_(K,N)=I_N tensor B,

norm(X_(W,N))=norm(X_W),                               (AG.18)
```

while

```text
Tr(N_(W,N) Gamma_N^(-1))
 =N Tr(N_W Gamma^(-1)),

Tr(X_(W,N))=N Tr(X_W).                                 (AG.19)
```

The companion certificate gives:

```text
+--------+---------------+---------------+---------------+---------------+
| copies | response      | obs op norm   | obs trace     | right HS norm |
+--------+---------------+---------------+---------------+---------------+
|      1 | 1.30749e-3    | 1.97130e-2    | 4.23590e-2    | 2.00000       |
|      2 | 2.61497e-3    | 1.97130e-2    | 8.47181e-2    | 2.82843       |
|      4 | 5.22994e-3    | 1.97130e-2    | 1.69436e-1    | 4.00000       |
|      8 | 1.04599e-2    | 1.97130e-2    | 3.38872e-1    | 5.65685       |
|     16 | 2.09198e-2    | 1.97130e-2    | 6.77745e-1    | 8.00000       |
+--------+---------------+---------------+---------------+---------------+
```

The guard rejects these estimators:

```text
norm(X_W),
norm(C_K)=1,
an unweighted Hilbert-Schmidt norm of C_K.              (AG.20)
```

The response needs a compact-root signed column norm.  Proof 260's nuclear-norm
guard also remains active: a direct sum of separate branch factorizations
measures total variation and loses the zero-trace chirp cancellation.

## 6. Conditioning stress

The finite source-shaped model varies the diagonal of the causal Jordan factor
from `0.10` to `0.97`.  The minimum eigenvalue of `Gamma` changes from about
`5.3e-3` to `9.4e-1`.  The left observability operator norm stays between
`1.56e-2` and `4.53e-2`.

This finite result supports the algebraic organization in `(AG.14)`.  It does
not prove a uniform source estimate.  The model has finite multiplicity and no
real-line prime density.

## 7. Prime-channel refinement

Proof 266 gives

```text
Delta=I_rand*I_rand+I_C*I_C,                           (AG.21)

I_rand=(I-P_0)V_S B,
I_C=C A_S B.                                           (AG.22)
```

Proof 269 decomposes `I_rand` into orthogonal prime innovations.  Proof 228's
coefficient-weighted chirp has the local square scale

```text
sum_p sum_(m>=1)
 (1+m log(p))^(2d)p^(-m).                              (AG.23)
```

The `m=1` part contains `sum_p 1/p` and diverges.  The former
`p^(-3m/2)` majorant multiplied Proof 228's already weighted endpoint by the
same geometric coefficient a second time.  Proof 269 keeps that cubic series
only as a rejected regression guard.

The positive square-energy stopping ledger is

```text
sum_p sum_(m>=1)
 (1+m log(p))^(2d)p^(-m) Q_(S,p,k)(4B_root),           (AG.24)
```

where `Q_(S,p,k)(4B_root)` bounds the concentration of the residual relative
displacement after the renewal and predictable factors have been kept.  Proof
272 proves the corresponding positive sum for the ordered future cloud.

Proof 273 rejects placing this factor in a positive norm of
`L_W D^k I_(rand,p)*`.  A compact-root crossing can have zero scalar trace and
strictly positive trace norm.  The next source construction must first pair
the left and right rows.  It must satisfy all of these requirements:

```text
the right survivor column stays paired with the left row;

the complete product takes its scalar trace before compact support is used;

each prime innovation reaches Proof 228's restricted-Fourier chirp;

the three physical branches remain inside the same scalar product;

the renewal index is resummed before a positive column norm.              (AG.25)
```

Proof 273 equation `(AJ.11)` is the exact signed first-missing pairing.  Its
active successor is the scalar disintegration `(AJ.14)--(AJ.15)`, not an
operator-column estimate.

Proof 274 then fixes the scalar ownership: the local signed coefficient in
that disintegration is `p^(-m/2)`.  Reaching the `p^(-m)` envelope in
`(AJ.15)` requires a new extra half-power from the complete paired renewal;
it does not follow from `(AG.23)--(AG.24)`.

## 8. Martingale literature boundary

Pisier and Xu established noncommutative Burkholder-Gundy inequalities and the
duality

```text
(H^1(mathcalM))*=BMO(mathcalM)
```

for martingales in a tracial von Neumann algebra.  Hong and Mei give column and
row John-Nirenberg estimates and atomic `H^1` decompositions in the same
setting:

```text
Hong and Mei,
John-Nirenberg inequality and atomic decomposition for noncommutative
martingales,
arXiv:1112.3187v2.
https://arxiv.org/abs/1112.3187

Pisier and Xu,
Non-commutative martingale inequalities,
Communications in Mathematical Physics 189 (1997), 667-698.
```

Those results start with a von Neumann algebra, a faithful tracial state, a
filtration, and martingale differences whose column or row square functions
belong to `L1`.  Equation `(AG.14)` provides a renewal column and an extended
`S1`-times-bounded trace pairing.  It does not supply the required tracial
martingale embedding or prove that the compact-rooted `L_WD^k` column lies in
`H^1` with a bound independent of `S`.

Use `H^1`--`BMO` duality only after constructing that embedding from the
Proof 266 prime filtration.  Invoking the abstract duality before the
real-line three-branch chirp estimate would rename the Gate 3U premise.

## 9. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/270_renewal_observability_collapse_probe.py

python3 -B docs/proofs/270_renewal_observability_collapse_probe.py \
  --multiplicity 10 --seed 271
```

The default certificate reports:

```text
three-branch left factor error     6.82e-16
defect square error                6.95e-16
right column isometry error        5.45e-16
column pairing trace error         8.53e-16
Stein equation error               2.93e-18
```

It also runs the conditioning stress and the direct-sum trace guard.

## 10. Route judgment

Proof 270 removes the conditioned inverse from the Gate 3U estimator at the
renewal level.  The active object is the signed pairing of the complete left
observability row with the survivor row, not `Gamma^(-1)`, a raw endpoint
coordinate difference, or a sum of branch norms.

The remaining analytic theorem is Proof 274 `(AK.12)`: combine `(AG.14)` with
the real-line crossing kernel and obtain an additional `p^(-m/2)` inside
Proof 273's complete signed scalar disintegration.  Proof 272 remains a
positive square-energy probability lemma.  Gate 3U, the arithmetic
same-object finite-S identity,
negative-owner integration, Burnol's identity, and RH remain open.  No Lean
owner or route rewire is authorized.
