# Proof 386: reflected/prolate two-sided root bundle

Date: 2026-07-18

Status: exact two-Hilbert--Schmidt insertion for both orientations of the
genuine reflected second-support crossing and for the signed prolate
commutator.  The reflected branch uses the repository identity
`H W_g H=W_gref`; the prolate branch uses the positive square root of the
trace-class remainder on both sides.

This closes the remaining fixed physical atoms needed beside Proof 385.  It
does not identify their moving Gram-normalized right legs with Proof 351's
Julia defect column.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH
remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reflected positive detector                   | explicit compact root    |
| second-support crossing, both orientations    | two `S_2` legs          |
| prolate commutator, both orientations         | two `S_2` legs          |
| rectangular trace insertion                   | legal                    |
| signs before direct-sum readout                | retained                 |
| moving prefix/Gram and Julia alignment         | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Reflected second support

Let `H` be the self-adjoint Hardy--Titchmarsh involution and put

```text
Q_f=H E_+ H,
H*=H,
H^2=I.                                            (RP.1)
```

For the positive compact-root detector

```text
W_g=C_g* C_g,                                     (RP.2)
```

the repository proves the exact readback

```text
H W_g H=W_gref=C_gref* C_gref.                    (RP.3)
```

No commutation of `H` with `C_g` or `W_g` is asserted.  The forward
second-support crossing is instead conjugated as a whole:

```text
D_ref
 =(I-Q_f)W_g Q_f
 =H E_- W_gref E_+ H.                             (RP.4)
```

If `supp(g_ref) subset [-B,B]`, Proof 385 applies inside `(RP.4)`.  With
`E_B=1_[-B,B]`, define

```text
L_ref=H E_- C_gref* E_B,
A_ref=E_B C_gref E_+ H.                           (RP.5)
```

Then

```text
D_ref=L_ref A_ref,                                (RP.6)

norm(L_ref)_2^2<=2B norm(g)_2^2,
norm(A_ref)_2^2<=2B norm(g)_2^2.                  (RP.7)
```

The reverse orientation is

```text
D_ref_rev=Q_f W_g(I-Q_f)
         =L_ref_rev A_ref_rev,                    (RP.8)

L_ref_rev=H E_+ C_gref* E_B,
A_ref_rev=E_B C_gref E_- H.                       (RP.9)
```

It satisfies the same bounds.  The unitary factors `H` do not change either
Hilbert--Schmidt norm.

## 3. Reflected rectangular insertion

Let `R_ref:Ran(Q_f)->Ran(I-Q_f)` be bounded.  Both factors displayed below
are Hilbert--Schmidt, so the rectangular cycle is legal:

```text
Tr_(Ran(Q_f))(D_ref* R_ref)

 =Tr_(L2([-B,B]))(L_ref* R_ref A_ref*)
 =<L_ref,R_ref A_ref*>_(S_2).                     (RP.10)
```

The reverse orientation has the identical formula with the two `rev` legs.
Thus the compact root is inserted on both sides before any finite-prime sum.

## 4. Prolate two-sided root

Let

```text
K=K_prol>=0,
K trace class,
S=K^(1/2).                                        (RP.11)
```

Then `S` is Hilbert--Schmidt and `norm(S)_2^2=Tr(K)`.  For any bounded
detector `W`, define the row and column

```text
L_K=(W S,-S):H direct-sum H->H,
A_K=(S,S W)^T:H->H direct-sum H.                  (RP.12)
```

Direct multiplication gives the exact signed factorization

```text
[W,K]
 =W S^2-S^2 W
 =L_K A_K.                                        (RP.13)
```

Both sides of `(RP.13)` are Hilbert--Schmidt legs:

```text
norm(L_K)_2^2
 =norm(W S)_2^2+norm(S)_2^2
 <=[1+norm(W)^2]Tr(K),

norm(A_K)_2^2
 =norm(S)_2^2+norm(S W)_2^2
 <=[1+norm(W)^2]Tr(K).                            (RP.14)
```

Consequently `[W,K]` is trace class.  For any bounded `R_K`,

```text
Tr([W,K]* R_K)=<L_K,R_K A_K*>_(S_2).              (RP.15)
```

The opposite convention `[K,W]` is obtained by replacing `L_K` by `-L_K`.
The sign remains in the left readout; the right owner is unchanged.

## 5. Relation to Proof 383's seven legs

Proof 383 uses the finer positive-detector root bundle

```text
(S,S C_g,S C_g*).                                 (RP.16)
```

It factors `[C_g,K]` and `[C_g*,K]` separately.  Equation `(RP.13)` is the
completed positive-detector commutator and naturally uses `(S,S W_g)`.
These statements are compatible but not interchangeable:

```text
root-level midpoint split     -> use `(RP.16)`;
completed `[W_g,K]` ledger    -> use `(RP.12)`.    (RP.17)
```

In particular, one may not claim that the seven-leg bundle factors
`[W_g,K]` without first applying the Leibniz/root split that produces the
two root commutators.

## 6. Fixed signed direct sum

Bundle the two reflected right legs and the prolate column:

```text
A_ref,prol x
 =(A_ref x,A_ref_rev x,A_K x).                    (RP.18)
```

There are four scalar copies after expanding `A_K`.  Its square budget is

```text
norm(A_ref,prol)_2^2
 <=4B norm(g)_2^2+[1+norm(W_g)^2]Tr(K_prol).       (RP.19)
```

Every fixed signed combination of the reflected and prolate atoms is one
bounded left readout of `(RP.18)`.  Equation `(RP.19)` is independent of the
number and spacing of visible primes.

## 7. Reproducible certificate

The companion finite probe checks

```text
the reflected conjugation and both factorizations `(RP.4)--(RP.9)`;
the two reflected trace insertions `(RP.10)`;
the prolate factorization `(RP.13)` and bounds `(RP.14)`;
the prolate trace insertion `(RP.15)`;
the fixed direct-sum square `(RP.19)`.             (RP.20)
```

Run only after Proofs 385--389 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/386_reflected_prolate_two_sided_root_bundle_probe.py
```

The continuous proof uses the existing reflected-root theorem, Proof 385's
support argument, the ideal property, and `S=K^(1/2)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reflected two-sided root insertion            | closed `(RP.10)`         |
| completed prolate two-sided insertion          | closed `(RP.15)`         |
| fixed physical atom bundle                     | closed `(RP.18)`         |
| complete corrected quotient recombination     | next proof               |
| moving Julia coordinate alignment              | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
