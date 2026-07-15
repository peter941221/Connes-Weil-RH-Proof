# Proof 290: Biorthogonal finite-horizon renewal colligation

Date: 2026-07-16

Status: exact fixed-`S` removal of the renewal inverse at every finite horizon.
The ordered causal Gram numerator is the observable defect of a biorthogonal
survival/emission colligation.  Its right path map is uniformly conditioned,
independently of the horizon and of the lower spectral bound of `Gamma`.

The exact path response splits into a uniformly bounded canonical-dual
intertwinement defect and one path-projection commutator.  The latter must be
controlled by the real-line compact-support geometry before its null coframe
is estimated.  This proof does not establish that source estimate, Gate 3U,
the finite-`S` sign, the arithmetic same-object identity, Burnol's identity,
or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| ordered numerator N_W                         | exact                        |
| finite renewal partial sum                     | exact path pairing           |
| left/right path pairing                        | biorthogonal                 |
| right path Gram                                | explicit function of Delta  |
| right path condition number                    | at most sqrt(2)              |
| canonical dual norm                            | at most sqrt(2)              |
| detector bulk                                  | cancels exactly              |
| remaining detector dependence                 | two completed commutators   |
| raw left/null coframe norm                     | horizon-growing / forbidden |
| source compact-support commutator estimate     | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The ownership change is

```text
N_W Gamma^(-1)
  -X-> do not bound the inverse;

finite renewal horizon
  -> one biorthogonal path pairing
  -> uniformly conditioned right survivor path
  -> canonical dual plus path-range commutator
  -> compact support before the horizon limit.          (BA.1)
```

## 2. Source input

Retain Proofs 264--265:

```text
K=E A iota_B,
Gamma=K* K,
Delta=I_(H_B)-Gamma,
0<Gamma<=I_(H_B),
0<=Delta<I_(H_B).                                    (BA.2)
```

For a compact cross-root detector

```text
W=C_xi* C_eta,
W_B=iota_B* W iota_B,                                (BA.3)
```

the ordered centered numerator is

```text
N_W=K* W K-W_B Gamma.                                (BA.4)
```

The factor order in `(BA.4)` is mandatory.  Proof 264's trace-anomaly guard
forbids replacing `W_B Gamma` by `Gamma W_B` or cycling the final
`Gamma^(-1)` to a polar expression.

For fixed finite `S`, Proof 261 makes every completed scalar

```text
Tr_B(N_W Delta^k)                                    (BA.5)
```

ordinary and trace legal.

## 3. The two path maps

Fix a finite horizon `n>=0` and use the path output space

```text
Y_n=H_E^(direct-sum (n+1)) direct-sum H_B.            (BA.6)
```

Define the right survival/emission path

```text
R_n x
 =(Kx,K Delta x,...,K Delta^n x,Delta^(n+1)x),        (BA.7)
```

and the left renewal coframe

```text
L_n x
 =(Kx,Kx,...,Kx,x).                                   (BA.8)
```

They are not adjoints of one another.  Their asymmetry is precisely the
ordered renewal convention in `(BA.4)`.

Since `K*K=Gamma=I-Delta`,

```text
L_n* R_n
 =sum_(k=0)^n Gamma Delta^k+Delta^(n+1)
 =I_(H_B).                                            (BA.9)
```

Thus `L_n` and `R_n` are biorthogonal path frames.  No inverse of `Gamma`
occurs.

## 4. Exact finite-horizon response

Put the same whole-line detector on every emission slot and the compressed
detector on the surviving band slot:

```text
O_n=diag(W,...,W,W_B) on Y_n.                         (BA.10)
```

Direct multiplication gives

```text
L_n* O_n R_n-W_B

 =sum_(k=0)^n K* W K Delta^k
   +W_B Delta^(n+1)-W_B

 =sum_(k=0)^n
   (K* W K-W_B Gamma)Delta^k

 =sum_(k=0)^n N_W Delta^k.                            (BA.11)
```

Equation `(BA.11)` is an operator identity on `H_B`; it precedes the
root-completed trace.  It preserves the ordered anomaly, the base level, and
every renewal level.

For fixed `S`, `norm(Delta)<1`, so

```text
lim_(n->infinity) right side of (BA.11)
 =N_W Gamma^(-1).                                    (BA.12)
```

The point of `(BA.11)` is not to rederive `(BA.12)`.  It provides a finite
path owner on which compact support can act before the horizon limit.

## 5. The right path is uniformly conditioned

The right Gram is

```text
S_n:=R_n*R_n
 =sum_(k=0)^n Delta^k Gamma Delta^k+Delta^(2n+2).
                                                               (BA.13)
```

Because `Gamma=I-Delta` commutes with `Delta`, scalar functional calculus
gives

```text
S_n
 =(I+Delta^(2n+3))(I+Delta)^(-1).                    (BA.14)
```

For `0<=lambda<=1`,

```text
1/2 <=(1+lambda^(2n+3))/(1+lambda)<=1.                (BA.15)
```

Therefore

```text
1/2 I<=S_n<=I,
norm(R_n)<=1,
norm(S_n^(-1))<=2.                                   (BA.16)
```

These constants are independent of `n`, `S`, and `lambda_min(Gamma)`.  The
Euler condition number has disappeared from the right path.

## 6. Canonical dual and the only path commutator

Define the canonical dual and the orthogonal right-path projection:

```text
F_n=R_n S_n^(-1),
P_n=R_n S_n^(-1)R_n*.                                (BA.17)
```

Then

```text
F_n*R_n=I,
norm(F_n)<=sqrt(2),
P_n*=P_n=P_n^2.                                      (BA.18)
```

Let the null coframe be

```text
Z_n=L_n-F_n.                                         (BA.19)
```

Equations `(BA.9)` and `(BA.18)` imply

```text
Z_n*R_n=0,
Z_n*P_n=0.                                           (BA.20)
```

Use `F_n*R_n=I` to remove the detector bulk:

```text
F_n*O_nR_n-W_B
 =F_n*(O_nR_n-R_nW_B).                               (BA.21)
```

Use `(BA.20)` and `P_nR_n=R_n` on the remaining term:

```text
Z_n*O_nR_n
 =Z_n*[O_n,P_n]R_n.                                  (BA.22)
```

Combining `(BA.11)` and `(BA.19)--(BA.22)` proves the canonical split

```text
sum_(k=0)^n N_W Delta^k

 =F_n*(O_nR_n-R_nW_B)
  +Z_n*[O_n,P_n]R_n.                                 (BA.23)
```

Every occurrence of the detector in `(BA.23)` is now in a difference:

```text
O_nR_n-R_nW_B:
  detector intertwinement defect along the physical path;

[O_n,P_n]:
  detector crossing of the complete right-path range.               (BA.24)
```

If `W` is the scalar fixed mode, both terms vanish exactly.  This is the
complete scalar-gauge cancellation before an estimate.

There is an equivalent first-missing coordinate.  Since

```text
R_n*L_n=I,
P_nL_n=R_nS_n^(-1)=F_n,
Z_n=(I-P_n)L_n,                                      (BA.24a)
```

put

```text
E_n=O_nR_n-R_nW_B.                                   (BA.24b)
```

Then `(BA.23)` becomes

```text
sum_(k=0)^n N_W Delta^k
 =F_n*E_n+L_n*(I-P_n)E_n.                            (BA.24c)
```

The two terms have sharply different roles:

```text
F_n*E_n:
  uniformly bounded canonical-dual response;

L_n*(I-P_n)E_n:
  the part of the detector defect which genuinely leaves the complete
  right survival-path space.                          (BA.24d)
```

Compact support must be applied to `(I-P_n)E_n` while it is still paired with
`L_n`.  Replacing that residual by `norm(L_n)norm((I-P_n)E_n)` is forbidden.

## 7. Why the null coframe must not be normed

The exact left Gram is

```text
L_n*L_n=I+(n+1)Gamma.                                (BA.25)
```

Thus `norm(L_n)` and generally `norm(Z_n)` grow like `sqrt(n)` on any spectral
region where `Gamma` stays positive.  This is not a condition-number problem;
it is repeated left occupancy.

Taking

```text
norm(Z_n) norm([O_n,P_n])                            (BA.26)
```

before compact support would recreate the positive path-counting route
rejected by Proofs 260, 273, and 288.  Equation `(BA.22)` is a scalar/support
factorization, not a product-norm estimate.

The right side is fundamentally different:

```text
R_n and F_n:
  uniformly bounded;

Z_n:
  allowed only while paired with the completed path commutator.       (BA.27)
```

## 8. Source readback

The first block of the intertwinement defect is

```text
W K-K W_B.                                            (BA.28)
```

Using `K=E A iota_B` and commutation of `W` with the whole-line convolution
`A`, `(BA.28)` expands only through detector crossings of `E`, `R`, and their
complements.  The later blocks retain the same defect after the complete
`Delta` survival history; they must not be expanded into prime paths.

Proofs 278--281 give the fixed-boundary channel contract which a source
readback of the second term must satisfy: `[O_n,P_n]` must retain both the
even/two-boundary channel and the odd/prolate channel.  Those proofs do not
already identify the path projection `P_n` with a Burnol boundary projection.
A prolate-only estimate is forbidden by Proof 278's zero-prolate survivor.

The active continuous theorem is

```text
sup_(finite S,n)
 |Tr_root(
    F_n*(O_nR_n-R_nW_B)
    +Z_n*[O_n,P_n]R_n)|

 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r).                    (BA.29)
```

Compact cross-correlation support must act on the complete scalar in
`(BA.29)` before `n->infinity`.  If `(BA.29)` holds, fixed-`S` convergence in
`(BA.12)` gives Proof 289 `(AZ.26)` without a primewise estimate or a
`Gamma^(-1)` norm.

## 9. Finite certificate

The companion certificate uses Proof 266's source-shaped finite model and
Proof 285's non-Hermitian compact cross detector.  It verifies independently:

```text
biorthogonality (BA.9);
finite-horizon response (BA.11);
right Gram formula and bounds (BA.14)--(BA.16);
canonical dual and projection (BA.17)--(BA.20);
two-defect split (BA.23);
first-missing/off-range split (BA.24c);
fixed-mode deletion;
exact horizon tail to N_W Gamma^(-1).                 (BA.30)
```

The default cohort reports

```text
maximum exact error                    1.02e-15,
right path minimum singular value      0.8348,
canonical dual norm                    1.1979,
left path growth guard                 3.6831x.        (BA.31)
```

The alternate cohort reports

```text
maximum exact error                    1.70e-15,
right path minimum singular value      0.8359,
canonical dual norm                    1.1963,
left path growth guard                 3.6991x.        (BA.31a)
```

The exact values are emitted by the certificate and are finite algebra
guards, not continuous bounds.

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/290_biorthogonal_finite_horizon_renewal_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/290_biorthogonal_finite_horizon_renewal_probe.py \
  --multiplicity 12 --root-radius 2 --seed 2290 --horizon 10
```

Both runs report

```text
finite_horizon_renewal=EXACT_PATH_PAIRING,
right_path_conditioning=UNIFORM_SQRT2,
canonical_dual=UNIFORM_SQRT2,
detector_bulk=ELIMINATED,
null_coframe_norm_used=FALSE,
source_path_commutator_bound=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 10. Evidence and route judgment

Project evidence:

```text
Proof 264, ordered causal Gram owner and trace-anomaly guard:
docs/proofs/264_causal_gram_response.md

Proof 265, N_W and physical boundary factorization:
docs/proofs/265_causal_boundary_renewal.md

Proof 270, observability-column isometry and positive-norm guard:
docs/proofs/270_renewal_observability_collapse.md

Proof 289, complete-prime telescope and renewal circularity guard:
docs/proofs/289_complete_prime_markov_telescope.md
```

Operator-model background:

```text
Ball--Bolotnikov, de Branges-Rovnyak spaces and norm-constraint
interpolation, arXiv:1405.2985.
https://arxiv.org/abs/1405.2985
```

The external source motivates contraction-defect and colligation coordinates;
equations `(BA.7)--(BA.23)` are direct project derivations and do not import a
uniform estimate from that paper.

Proof 290 replaces the vague right-multiplication coboundary from Proof 289 by
an exact ordered finite-horizon path theorem.  The next attack is

```text
two-defect owner (BA.23)
  -> real-line kernel of O_nR_n-R_nW_B
  -> Burnol coordinate for [O_n,P_n]
  -> cancel paths missing both physical boundaries
  -> apply compact support before norm(Z_n) or n->infinity
  -> prove (BA.29)
  -> Gate 3U.                                             (BA.32)
```

The source path-commutator bound, Gate 3U, finite-`S` sign, arithmetic
same-object trace identity, negative-owner integration, Burnol's all-zero
identity, and RH remain open.  No Lean owner or route consumer is changed.

Successor refinement: Proof 291 shows that the full defect
`E_n=O_nR_n-R_nW_B` is generated by the single base intertwinement

```text
d_W=WK-KW_B
```

and its left companion.  In particular,

```text
[W_B,Delta]=d_W^left K-K*d_W,
```

so no new detector owner appears with the horizon.  For diagonal roots,
`d_W^left=d_W*`.  Use Proof 291 `(BB.16)--(BB.20)` as the active source
contract.
