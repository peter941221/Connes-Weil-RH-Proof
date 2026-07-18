# Proof 383: two-orientation boundary-root bundle

Date: 2026-07-18

Status: explicit source-owned Hilbert--Schmidt bundle containing every compact
root orientation and prolate square-root leg that can occur in the corrected
near physical bracket.  The number of summands is fixed, and its square cost
is polynomial in the root support and independent of the visible prime set.

This supplies a concrete candidate for Proof 382's `A_root`.  It does not
prove that Proof 380's actual range-root column factors through the actual
Julia column built from this candidate.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| outer root and adjoint                        | one common near window   |
| reflected root and adjoint                    | second common copy      |
| prolate square-root words                     | three fixed copies      |
| total number of owner copies                  | seven                   |
| Hilbert--Schmidt square                       | polynomial              |
| dependence on prime count/spacing             | none                    |
| Julia insertion/alignment                     | open `(JR.9)/(JR.19)`  |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Four compact boundary roots

Let `g in L1(R) intersection L2(R)` satisfy

```text
supp(g) subset [-B_root,B_root].                   (BR.1)
```

Use the four route orientations

```text
g,
g_dagger(x)=conjugate(g(-x)),
g_ref,
g_ref_dagger.                                      (BR.2)
```

Reflection and involution preserve support and the `L2` norm.  Let

```text
J=J_(L,B_root)                                    (BR.3)
```

be Proof 357's common near output interval, with

```text
abs(J)<=L+2B_root.                                 (BR.4)
```

For every root `h` in `(BR.2)`, define

```text
A_h=R_J C_h.                                       (BR.5)
```

The exact finite-output convolution calculation gives

```text
norm(A_h)_2^2=abs(J) norm(h)_2^2.                  (BR.6)
```

Every oriented root crossing whose translated output interval lies in `J`
is a contraction of the corresponding `A_h`, by Proof 357 `(NW.6)--(NW.7)`.
The same `J` is used for every near prime and prime power.

For the genuine second support, the route does not assert that the raw
Hardy--Titchmarsh conjugate of `C_g` is a compact convolution.  Instead, the
existing exact positive-detector identity reads the completed second-support
branch with the explicit reflected compact root.  The two reflected copies in
`(BR.2)` are used only inside that exact readback.

## 3. Three prolate root legs

Let

```text
K=K_prol>=0,
K trace class,
S=K^(1/2).                                         (BR.7)
```

For the original compact convolution root `C=C_g`, define

```text
A_prol x=(Sx,S Cx,S C*x).                          (BR.8)
```

This is Hilbert--Schmidt and

```text
norm(A_prol)_2^2
 <=Tr(K)[1+2 norm(C)^2].                           (BR.9)
```

The three legs contain both root commutator orientations.  For example,

```text
[C,K]x
 =(C S)(Sx)-S(S Cx),                              (BR.10)

[C*,K]x
 =(C* S)(Sx)-S(S C*x).                            (BR.11)
```

Thus every fixed signed prolate word needed after the positive detector is
root-split factors through `(BR.8)` with a bounded left operator.  No prolate
eigenbasis or finite-rank truncation is chosen.

## 4. The complete candidate

On the fixed direct-sum output carrier define

```text
A_root x=
 (A_g x,
  A_g_dagger x,
  A_g_ref x,
  A_g_ref_dagger x,
  A_prol x).                                       (BR.12)
```

The last entry in `(BR.12)` itself has three components.  Equations
`(BR.4)--(BR.9)` give

```text
norm(A_root)_2^2

 <=4(L+2B_root) norm(g)_2^2
   +Tr(K_prol)[1+2 norm(C_g)^2].                   (BR.13)
```

The right side is independent of the number, order, and spacing of all
visible primes.

After applying the fixed quotient isometry `U_0`, use the adjoint orientation
of `(BR.12)` to obtain the source map required by Proof 351:

```text
A_root_source:H_aux->K_0.                          (BR.14)
```

Adjointing and fixed unitary coordinate changes preserve `(BR.13)`.

## 5. What the bundle owns

The bundle contains fixed right factors for

```text
both outer-boundary root orientations;
both reflected second-support root orientations;
the prolate commutators with `C_g` and `C_g*`;
the two Proof 365 quotient-boundary corrections;
every translation whose displacement is at most `L`.            (BR.15)
```

The last claim uses the translated nested-window factorization before any
prime sum.  It does not expand the Euler product into a coherent sum of raw
translated crossings.

All physical signs remain in one bounded left readout from the direct sum.
The direct sum only records a fixed number of analytic species; it does not
create one slot per prime.

## 6. Remaining alignment theorem

Proof 383 removes the possibility that Proof 382 is missing a source-owned
Hilbert--Schmidt object with the correct support budget.  The remaining issue
is coordinate alignment:

```text
Proof 380 actual range-root column
        |
        |  retain corrected quotient bracket
        v
Proof 351 actual Julia defect column applied to `(BR.14)`.
                                                               (BR.16)
```

Precisely, one must prove Proof 382 `(JR.9)` and `(JR.19)` with the common
source formed from `A_root_source`.  The following weaker facts do not prove
them:

```text
each physical branch factors through one component of `(BR.12)`;
the total bundle has the polynomial norm `(BR.13)`;
the endpoint root commutators satisfy `(MR.6)`.      (BR.17)
```

The missing statement must keep the two compression-boundary corrections and
both mixed covariance terms from Proofs 365--369 inside the same readout.

## 7. Reproducible certificate

The companion probe uses cyclic discrete convolution so every finite output
row has the exact same root norm.  It checks

```text
the four finite-window Hilbert--Schmidt identities `(BR.6)`;
the seven-copy bundle square and bound `(BR.13)`;
the prolate commutator factorizations `(BR.10)--(BR.11)`;
nested output restrictions as contractions of one common window. (BR.18)
```

Run only after Proofs 380--384 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/383_two_orientation_boundary_root_bundle_probe.py
```

The finite certificate verifies the fixed bundle, not the alignment theorem
`(BR.16)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| explicit source `A_root` candidate            | closed `(BR.12)`         |
| polynomial Hilbert--Schmidt budget            | closed `(BR.13)`         |
| actual Julia/root alignment                   | open `(BR.16)`           |
| active positive inequality                    | Proof 382 `(JR.19)`     |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
