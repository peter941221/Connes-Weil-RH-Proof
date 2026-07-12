# Parity Schur Inverse Rejection

Date: 2026-07-12

Status: reflection symmetry gives an exact scalar Schur recursion for the
nested cutoff-free Weil matrices, but its positive pivots are produced by
near-total cancellation against the inverse of the previous band. The standard
Loewner displacement identity does not remove that inverse or determine its
sign. Fixed-fraction, diagonal-dominance, and RKHS-distance arguments are
rejected; no inverse-free arithmetic recurrence or Lean owner survives.

## 1. Exact Nested Recursion

At fixed prime cutoff `c`, the full matrix on frequencies `-N,...,N` commutes
with reflection. In normalized parity coordinates it splits as

```text
Q_N = E_N direct_sum O_N,

E_N on 0,1,...,N,
O_N on 1,...,N.
```

Both blocks are nested principal extensions. Writing the new block as

```text
[ A_(N-1)  b_N ]
[ b_N^T     a_N ],
```

the exact last LDL pivot is

```text
s_N = a_N - b_N^T A_(N-1)^(-1) b_N
    = det(A_N)/det(A_(N-1)).
```

Positive `s_N` extends positive definiteness by one coordinate. This is an
equivalent recursion, not yet a lower proof.

## 2. Two Parity Loewner Kernels

Let `psi` be the odd divided-difference source of the full matrix. For positive
frequencies `j,k`, direct contraction of the `+/-` pairs gives

```text
E_(j,k)
 = (psi(j)-psi(k))/(j-k)
   + (psi(j)+psi(k))/(j+k)
 = 2 (Phi(j^2)-Phi(k^2))/(j^2-k^2),

Phi(x)=sqrt(x) psi(sqrt(x)),
```

and

```text
O_(j,k)
 = (psi(j)-psi(k))/(j-k)
   - (psi(j)+psi(k))/(j+k)
 = 2jk (Chi(j^2)-Chi(k^2))/(j^2-k^2),

Chi(x)=psi(sqrt(x))/sqrt(x).
```

Thus each parity recursion is a multipoint Loewner/Pick recursion. The
displacement identity

```text
D L - L D = phi 1^T - 1 phi^T
```

has rank at most two for every source function `phi`, including sources whose
Loewner matrices are indefinite. Low displacement rank therefore supplies
fast algebra but no sign.

The Schur pivot is the squared residual norm of a new evaluation kernel only
after the old Loewner kernel is known positive. Using that RKHS interpretation
to prove positivity assumes the exact property being sought.

## 3. Arb-Certified Cancellation

The probe constructs the exact parity embeddings and performs natural-order
Arb LDL. Representative rows are:

```text
+-----+----+--------+----------------+----------------+----------------+
| c   | N  | parity | new diagonal   | Schur pivot    | pivot/diagonal |
+-----+----+--------+----------------+----------------+----------------+
| 13  | 1  | even   | 9.2232e-2      | 9.9206e-6      | 1.0756e-4      |
| 13  | 4  | even   | 1.4222e-1      | 4.1262e-10     | 2.9012e-9      |
| 13  | 8  | even   | 9.0183e-1      | 9.3393e-11     | 1.0356e-10     |
| 13  | 16 | even   | 1.0137         | 9.7649e-10     | 9.6333e-10     |
| 13  | 4  | odd    | 3.2278e-2      | 8.5342e-9      | 2.6439e-7      |
| 13  | 8  | odd    | 7.3363e-1      | 7.5357e-10     | 1.0272e-9      |
| 13  | 16 | odd    | 9.8811e-1      | 3.8076e-9      | 3.8535e-9      |
| 29  | 4  | even   | 9.9461e-2      | 1.5817e-12     | 1.5903e-11     |
| 29  | 8  | even   | 1.7770         | 1.9626e-15     | 1.1045e-15     |
| 29  | 4  | odd    | 1.4492e-2      | 5.0063e-11     | 3.4545e-9      |
| 29  | 8  | odd    | 1.9073         | 3.4641e-14     | 1.8162e-14     |
+-----+----+--------+----------------+----------------+----------------+
```

Every displayed pivot is a strictly positive Arb interval. The issue is not
floating-point sign uncertainty. The inverse correction

```text
b_N^T A_(N-1)^(-1)b_N = a_N-s_N
```

matches the new diagonal to as many as 15 decimal orders in the tested rows.
Pivots also oscillate with `N`; for example, the `c=13` even pivot rises from
`4.09e-10` at `N=5` to `1.43e-9` at `N=6`, then falls to `4.11e-11` at `N=7`.
There is no observed monotone or fixed geometric recurrence to certify.

## 4. Rejected Proof Shapes

```text
s_N >= delta(c) a_N with a macroscopic fixed delta(c): false
diagonal dominance after parity splitting: false
discard or coarsely bound the inverse correction: false
RKHS residual norm without prior kernel positivity: circular
determinant-ratio positivity without a new identity: equivalent to PSD
rank-two Loewner displacement alone: sign-free
```

An inverse-free proof would need an additional arithmetic identity expressing
`det(A_N)/det(A_(N-1))` as a manifestly positive prime/Gamma quantity before
using any earlier matrix sign. The operator-monotone, continuous Bernstein,
and discrete Stieltjes structures that normally provide such identities were
already rejected in `056` and `058`.

## 5. Reproduction

With the official arXiv:2607.02828 source package and `python-flint`:

```text
python3 -B docs/proofs/059_parity_schur_band_probe.py \
  --upstream anc/arb_ldlt_certify.py \
  --c 13 --max-N 16 --prec 4096

python3 -B docs/proofs/059_parity_schur_band_probe.py \
  --upstream anc/arb_ldlt_certify.py \
  --c 29 --max-N 8 --prec 2048
```

## 6. Verdict

```text
exact parity decomposition: passed
scalar nested Schur recursion: passed
tested Schur signs: Arb-positive
fixed or monotone margin: rejected
inverse-free positive recurrence: not found
using old inverse positivity: circular / RH-level
new Lean owner: none
unconditional RH: unproved
```

Sources:

```text
https://arxiv.org/abs/2607.02828
docs/proofs/055_loewner_bernstein_probe.py
docs/proofs/059_parity_schur_band_probe.py
```
