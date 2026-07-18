# Proof 351: Julia prime-defect Bessel row

Date: 2026-07-18

Status: exact assembly of Proof 350's one-prime graph angles into one
orthogonal defect row.  After pulling every current transported subspace back
to the fixed source coordinate, the Julia transfer defects and one final
survivor form an isometry.  Each Gram-normalized range sine is
`1/sqrt(p-1)` times a contraction of the corresponding defect slot.  Hence the
whole family satisfies a weighted Bessel inequality, including its
Hilbert--Schmidt amplification.

This closes the range side of the proposed prime square function.  It does not
identify the complete Proof 343 compact-root outer-minus-Sonin-prolate scalar
with the dual pairing against this row.  That detector row, its source Bessel
bound, Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| current-space Julia transfers                 | contractions              |
| fixed-source pullback                         | exact                     |
| defect outputs plus survivor                  | one isometry              |
| normalized range sine at p                    | 1/sqrt(p-1) * contraction|
| weighted prime range row                      | Bessel constant one       |
| Hilbert--Schmidt amplification                 | Bessel constant one       |
| complete source detector as dual row           | open, next producer      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The new owner is

```text
sequential Gram-corrected prime ranges
  -> pull every step back to H_0
  -> multiply the Julia transfer contractions
  -> keep every defect output in its own direct-sum slot
  -> use one Pythagorean identity
  -> pair the complete physical detector only afterward.          (JB.1)
```

No prime branch is placed under an absolute value in `(JB.1)`.

## 2. Fixed-source coordinates

Use Proof 350's sequential subspaces

```text
K_j=(I-a_j U_j)^(-1)K_(j-1),
a_j=p_j^(-1/2),                                      (JB.2)
```

and let

```text
V_j:K_(j-1)->K_j                                     (JB.3)
```

be the canonical Gram-normalized graph isometry from Proof 350 `(JG.12)`.  Put

```text
J_0=I_(K_0),
J_j=V_j J_(j-1):K_0->K_j.                            (JB.4)
```

Every `J_j` is unitary onto `K_j`.  Let `Phi_j` be the Julia transfer
contraction `(JG.6)` formed relative to `K_(j-1)`, and pull it back to the fixed
source carrier:

```text
F_j=J_(j-1)* Phi_j J_(j-1):K_0->K_0.                (JB.5)
```

Then

```text
F_j*F_j<=I.                                          (JB.6)
```

Define

```text
D_j=(I-F_j*F_j)^(1/2),
Psi_0=I,
Psi_j=F_j Psi_(j-1).                                 (JB.7)
```

The order in `Psi_j` is the chronological prime order.  The endpoint Euler
range is order independent because the physical factors commute, but the
defect-coordinate factorization uses one fixed order.

## 3. Exact defect-row isometry

For every `x in K_0`, one step gives

```text
norm(Psi_(j-1)x)^2-norm(Psi_j x)^2

 =<Psi_(j-1)x,(I-F_j*F_j)Psi_(j-1)x>
 =norm(D_j Psi_(j-1)x)^2.                            (JB.8)
```

Sum `(JB.8)` before taking any norm estimate:

```text
sum_(j=1)^n norm(D_j Psi_(j-1)x)^2
  +norm(Psi_n x)^2

 =norm(x)^2.                                         (JB.9)
```

Thus the row

```text
mathcalO_n x
 =(D_1x,D_2Psi_1x,...,D_nPsi_(n-1)x,Psi_nx)          (JB.10)
```

is an isometry from `K_0` into the direct sum of the `n` defect copies and one
survivor copy.  The defect slots are orthogonal because they are different
coordinates of this direct sum; no separation of the numbers `log(p_j)` is
used.

## 4. Factor the normalized range sine through the defect

Let `X_j` and `S_j` be Proof 350's graph and Gram-normalized sine for step `j`.
Pull the input coordinate back by `J_(j-1)`.  Equation `(JG.11)` gives

```text
(X_j J_(j-1))* (X_j J_(j-1))
 =c_j^2 D_j^2,

c_j=a_j/sqrt(1-a_j^2)=1/sqrt(p_j-1).                 (JB.11)
```

By polar decomposition there is a partial isometry `Omega_j` such that

```text
X_j J_(j-1)=c_j Omega_j D_j.                         (JB.12)
```

Since

```text
S_j=X_j(I+X_j*X_j)^(-1/2),                           (JB.13)
```

functional calculus and `(JB.11)--(JB.12)` give

```text
S_j J_(j-1)
 =c_j Omega_j D_j(I+c_j^2D_j^2)^(-1/2).              (JB.14)
```

The last three factors after `c_j` form a contraction on each defect output.
Consequently,

```text
norm(S_j J_(j-1)Psi_(j-1)x)
 <=c_j norm(D_jPsi_(j-1)x).                          (JB.15)
```

## 5. Weighted prime Bessel inequality

Insert `(JB.15)` into the exact row identity `(JB.9)`.  Since
`c_j^(-2)=p_j-1`,

```text
sum_(j=1)^n (p_j-1)
  norm(S_j J_(j-1)Psi_(j-1)x)^2

 <=sum_(j=1)^n norm(D_jPsi_(j-1)x)^2
 <=norm(x)^2.                                        (JB.16)
```

This is the complete prime range Bessel bound.  It is stronger than summing
the operator inequalities `S_j*S_j<=1/(p_j-1)` separately: `(JB.16)` retains
the transfer prefixes and places all outputs in one orthogonal row.

Proof 348's coherent local Gram is therefore not the correct range-side square
function after sequential Gram orthogonalization.

## 6. Hilbert--Schmidt amplification

Let `A:H_aux->K_0` be Hilbert--Schmidt.  Apply `(JB.16)` to an orthonormal basis
of `H_aux` and sum nonnegative terms.  Tonelli gives

```text
sum_(j=1)^n (p_j-1)
 norm(S_j J_(j-1)Psi_(j-1)A)_2^2

 <=norm(A)_2^2.                                      (JB.17)
```

Equivalently, define the weighted range row

```text
mathcalS_n A
 =(
    sqrt(p_j-1)
    S_jJ_(j-1)Psi_(j-1)A
   )_(j=1)^n.                                        (JB.18)
```

Then

```text
norm(mathcalS_n A)_(direct-sum S2)<=norm(A)_2.        (JB.19)
```

The constant is exactly one, independent of the number, order, size, and
spacing of the visible primes.

## 7. The only legal final Cauchy--Schwarz

Suppose the complete route response is proved to have a same-object identity

```text
Q_S(eta,xi)
 =sum_(j=1)^n Tr(H_j* R_j),                           (JB.20)

R_j=S_jJ_(j-1)Psi_(j-1)A_(eta,xi),                  (JB.21)
```

where each `H_j` is a completed detector innovation and the common
Hilbert--Schmidt input `A_(eta,xi)` is source-owned.  Then one, and only one,
Cauchy--Schwarz inequality gives

```text
abs Q_S(eta,xi)

 <=[
    sum_j norm(H_j)_2^2/(p_j-1)
   ]^(1/2)
   [
    sum_j (p_j-1)norm(R_j)_2^2
   ]^(1/2)

 <=[
    sum_j norm(H_j)_2^2/(p_j-1)
   ]^(1/2)
   norm(A_(eta,xi))_2.                               (JB.22)
```

The missing source theorem is therefore concrete:

```text
sum_j norm(H_j)_2^2/(p_j-1)

 <=C(1+B_root)^d
   norm(eta)_(H^r)^2 norm(xi)_(H^r)^2,               (JB.23)
```

with `(JB.20)` equal to the literal Proof 343 endpoint.

The proposed `H_j` must be formed only after

```text
outer crossing
  -Sonin crossing
  +K_prol
  +half-density residue cancellation
  +canonical/boundary-anomaly terms                 (JB.24)
```

have been recombined.  Proofs 260, 268, and 340 forbid replacing `(JB.23)` by
a direct sum of branch trace norms.

## 8. Relation to earlier defect rows

Proof 271 and Proof 337 construct Markov/renewal defect rows.  Their local
prime covariance begins at `p^(-1/2)`, as Proof 268 correctly records.  The row
here has a different origin:

```text
Markov row:
  probability covariance before orthogonal range correction;

Julia row:
  transfer defect of the complete inverse factor, followed by
  the canonical graph Gram correction.                              (JB.25)
```

The explicit coefficient `c_j=1/sqrt(p_j-1)` in `(JB.14)` is what carries the
prime square gain.  The unit-norm defect row `(JB.10)` supplies the orthogonal
multiplicity owner.

## 9. Reproducible certificate

The companion script constructs independent unitary colligations for several
Euler coefficients and verifies:

```text
the transfer defect identities from Proof 350;
the exact Pythagorean telescope `(JB.9)`;
the sine/defect factor `(JB.14)` at the square level;
the vector Bessel inequality `(JB.16)`;
the Hilbert--Schmidt inequality `(JB.17)`;
the direct-sum Cauchy--Schwarz inequality `(JB.22)`.   (JB.26)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/351_julia_prime_defect_bessel_row_probe.py
```

This is an exact finite linear-algebra certificate for identities valid on
arbitrary Hilbert spaces.  It does not construct `(JB.20)` or `(JB.23)`.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed-source Julia defect row                 | isometry                  |
| prime range sine factor                       | exact coefficient         |
| weighted vector Bessel bound                  | constant one              |
| weighted S2 Bessel bound                      | constant one              |
| complete detector dual-row identity            | open `(JB.20)`            |
| source detector Bessel estimate                | open `(JB.23)`            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
