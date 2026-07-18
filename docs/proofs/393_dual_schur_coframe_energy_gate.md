# Proof 393: dual Schur-coframe energy Gate

Date: 2026-07-18

Status: exact inverse-energy identity for the dual row forced by Proof 391's
ordered similarity.  The row that remains after the contractive co-defect
history is paired with `Gamma_n^(-1)` has square exactly equal to the growth
of the inverse Schur Gram.  Hence no abstract contraction argument can bound
it uniformly.

This isolates the source-specific stable-coframe theorem required of Proof
387's complete corrected root column.  It does not prove that theorem, Gate
3U, the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| forward Schur co-defect row                   | contraction, Proof 392   |
| inverse-prefix dual row                       | exact energy identity    |
| generic uniform dual bound                    | false                    |
| raw common root bundle under inverse cascade  | insufficient            |
| corrected root stable-coframe estimate         | exact remaining theorem |
| cumulative condition number estimate           | forbidden               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Invertible contraction cascade

Let `G_1,...,G_n` be Proof 391's normalized Schur factors.  Each is an
invertible contraction.  Put

```text
Gamma_j=G_1...G_j,
Gamma_0=I,                                        (DC.1)

D_j=(I-G_j*G_j)^(1/2).                            (DC.2)
```

Proof 391's input-defect row uses suffix contractions and is bounded by one.
The ordered similarity in `(SC.21)` instead introduces inverse prefixes.

## 3. Exact dual row

Define the dual-coframe block

```text
H_j
 =D_jG_j^(-1)Gamma_(j-1)^(-1).                   (DC.3)
```

The local square is

```text
H_j*H_j

 =Gamma_(j-1)^(-*)
   G_j^(-*)D_j^2G_j^(-1)
   Gamma_(j-1)^(-1).                              (DC.4)
```

Since `D_j^2=I-G_j*G_j`,

```text
G_j^(-*)D_j^2G_j^(-1)
 =G_j^(-*)G_j^(-1)-I.                             (DC.5)
```

Substitute `(DC.5)` into `(DC.4)`.  With

```text
Delta_j=Gamma_j^(-*)Gamma_j^(-1),                 (DC.6)
```

one obtains

```text
H_j*H_j=Delta_j-Delta_(j-1).                      (DC.7)
```

Summing before taking a norm gives the exact identity

```text
sum_(j=1)^n H_j*H_j
 =Gamma_n^(-*)Gamma_n^(-1)-I.                     (DC.8)
```

Thus, for every Hilbert--Schmidt source input `A_root`,

```text
sum_j norm(H_jA_root)_2^2

 =norm(Gamma_n^(-1)A_root)_2^2
  -norm(A_root)_2^2.                              (DC.9)
```

Equation `(DC.9)` is an equality.  A triangle inequality did not create the
inverse growth.

## 4. Why the forward Bessel row is not enough

Proof 392 factors the complete intertwinement as

```text
mathcalE_n=C K O,
norm(C)<=1.                                       (DC.10)
```

Here `C` is the co-defect history row and `O` contains the physical boundary
root column with suffix contractions.  The ordered response is

```text
mathcalE_nGamma_n^(-1).                           (DC.11)
```

The `j`-th right block in `(DC.11)` reduces algebraically to a block of the
form `(DC.3)`, after the local right defect is inserted.  Therefore a second
ordinary Bessel estimate is unavailable: its exact square is `(DC.8)`, not an
operator bounded by `I`.

## 5. Uniform one-step inverse is not enough

Proof 390 gives

```text
Z_j=(I-a_jPhi_j)C_j,
G_j=Z_j/(1+a_j).                                  (DC.12)
```

From Proof 350 `(JG.11)`,

```text
C_j>=sqrt(1-a_j^2)I.                              (DC.13)
```

Also `norm(Phi_j)<=1`, so

```text
norm((I-a_jPhi_j)^(-1))<=1/(1-a_j).               (DC.14)
```

Consequently,

```text
norm(G_j^(-1))
 <=(1+a_j)/[(1-a_j)sqrt(1-a_j^2)]
 <=C_2,                                           (DC.15)
```

where `C_2` is the fixed value at `p=2`.  This proves every local inverse is
uniformly bounded.  Multiplying `(DC.15)` over primes is nevertheless the
forbidden cumulative condition number and does not bound `(DC.9)`.

## 6. Exact generic guard

Take scalar contractions

```text
G_j=g_jI,
0<g_j<1.                                          (DC.16)
```

Then

```text
Gamma_n^(-1)
 =product_j g_j^(-1) I,                           (DC.17)
```

and `(DC.9)` becomes

```text
sum_j norm(H_jA_root)_2^2
 =[product_j g_j^(-2)-1]norm(A_root)_2^2.         (DC.18)
```

Every forward factor is contractive and every one-step inverse may be bounded
by the same constant, while the dual energy still grows exponentially.  This
guard concerns an arbitrary source input.  In the physical invariant scalar
channel the completed detector crossing is zero, so a correct boundary root
column must vanish there rather than pay `(DC.18)`.

## 7. The stable-coframe theorem

Let `A_corr` denote the literal complete corrected root insertion from Proof
387 after the Schur co-defect factorization of Proof 392.  The remaining
source theorem is

```text
norm(Gamma_n^(-1)A_corr)_2^2
 -norm(A_corr)_2^2

 <=C(1+L+B_root)^d norm(g)_(H^r)^2,               (DC.19)
```

or its two-sided polarized form.  Equivalently, the corrected root column
must lie in a polynomially stable subspace of the inverse Schur cascade.

The quantifiers in `(DC.19)` are important:

```text
one fixed compact-root source;
all complete outer/second/prolate signs retained;
all quotient-compression corrections retained;
constant independent of the finite prime set.     (DC.20)
```

Proof 383's raw seven-leg norm bound does not imply `(DC.19)`.  The
cancellation that removes the unstable scalar channels must occur inside the
complete corrected column before the inverse cascade is applied.

## 8. Trace-anomaly dichotomy

Proof 392 `(CD.25)` offers two formal manipulations:

```text
keep the prefix similarities:
  retain the forward Bessel row but expose `(DC.8)` on the right;

cycle each prefix similarity:
  remove the inverse prefix only if every local root-completed term is
  individually trace class, but lose the cross-prime defect telescope.     (DC.21)
```

Neither branch alone proves Gate 3U.  The required source argument must show
that the same completed boundary cancellation supplies both local trace
legality and the stable-coframe estimate `(DC.19)`.

## 9. Reproducible certificate

The companion probe checks `(DC.7)--(DC.9)` for Schur factors produced by a
commuting translation cascade.  It also evaluates the scalar guard
`(DC.16)--(DC.18)` and compares the contractive forward row with the growing
dual energy.

Run only after Proofs 390--394 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/393_dual_schur_coframe_energy_gate_probe.py
```

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| inverse Schur energy                          | exact `(DC.8)--(DC.9)`   |
| generic dual Bessel claim                     | rejected `(DC.18)`      |
| local inverse bound                           | closed `(DC.15)`         |
| corrected stable coframe `(DC.19)`             | open, active Gate bottom|
| old Julia alignment bottom                    | superseded               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
