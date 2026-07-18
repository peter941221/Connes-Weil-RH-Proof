# Proof 336: Angle-resolvent far Schur tail

Date: 2026-07-17

Status: fixed-source analytic completion of the far-displacement Schur lane
after Proof 335.  Burnol's boundary inverse splits into two unconditioned
half-line channels plus a fixed trace-class angle resolvent.  Compact root
support deletes the unconditioned half-line trace beyond the support window.
After the rank-one half-density residue from Proof 335 is subtracted, CC20's
prolate derivative bounds and rapid eigenvalue decay sum the angle-resolvent
remainder at the next boundary order.

This closes the fixed-source far tail at the mathematical route-evidence
level.  It has no Lean owner and does not prove the near complete-product
stopped-path estimate, Gate 3U, the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

Use Proof 334's complete covariance

```text
S_R(Q phi,z)
 =integral (Q phi)(u) Tr G^(-1)[
    M(z+u)-M(z)G^(-1)M(u)
  ]du.                                               (BT.1)
```

For a compact smooth even root correlation supported in `[-B,B]`, there are
fixed-source constants `C,r` such that, for `z>=B+1`,

```text
|S_R(Q phi,z)|
 <=C exp(-3z/2)
   integral_(-B)^B exp(3|u|/2)
     sum_(k<=r)|partial^k phi(u)|du.                 (BT.2)
```

The reflected estimate holds for `z<=-B-1`.  In the Gate 3U far region
`|z|>=4B+4`, the exponential support weight in `(BT.2)` is absorbed by the
displacement decay:

```text
exp(-3|z|/2)exp(3B/2)
 <=exp(-9|z|/8).                                     (BT.3)
```

Thus the far Euler modes are absolutely summable without a primewise
condition number and without spending an exponential factor in the final
support-width bound.  The near region `|z|<4B+4` remains inside Proof 289's
complete-prime telescope.

## 2. Trace-class angle split

On `H_0 direct-sum H_0`, put

```text
mathcalF=[[0,F_0],[F_0,0]],
G=I+mathcalF.                                        (BT.4)
```

The even finite-window Fourier operator has prolate eigenvalues `lambda_n`.
CC20's explicit bound is

```text
|lambda_n|
 <=2^(2n) pi^(2n+1/2) ((2n)!)^2
   /((4n)! Gamma(2n+3/2)),                           (BT.5)
```

which is super-exponentially small.  Therefore `F_0`, `mathcalF`, and

```text
J:=G^(-1)-I=-G^(-1)mathcalF                          (BT.6)
```

are trace class.  In the Hadamard plus/minus channels, the eigenvalues of `J`
are

```text
j_(n,+)=-lambda_n/(1+lambda_n),
j_(n,-)= lambda_n/(1-lambda_n).                      (BT.7)
```

Every denominator is nonzero because Burnol proves `norm(F_0)<1`.  The first
negative-channel coefficient is large because
`lambda_0=0.999971376...`, but it is one fixed archimedean constant.  For
large `n`, `(BT.5)` makes both sequences in `(BT.7)` absolutely summable
against every polynomial in `n`.

Primary evidence:

```text
Burnol projection and strict angle:
https://arxiv.org/abs/math/0208121

CC20 prolate spectrum and rapid-decay, source labels
prolateeq, rapid-decay, Rokh, boundWang:
https://arxiv.org/abs/2006.13771
```

## 3. Unconditioned channel is the completed half-line trace

Substitute `G^(-1)=I+J` into `(BT.1)`, but do not take an absolute value.  The
terms with no `J` are the two unconditioned boundary copies.  In physical
coordinates they are the two orientations of the completed half-line
crossing

```text
C_g(I-E)U_zE C_g^dagger.                            (BT.8)
```

Proofs 260, 275, 324, and 330 identify its ordinary trace with the compact
cross-correlation at displacement `z`.  Hence

```text
trace of the J-free channel=0,   |z|>B.              (BT.9)
```

Here `B` denotes the support radius of the correlation itself; for roots
supported in `[-B_root,B_root]`, use `B=2B_root`.

Equation `(BT.9)` is a completed scalar cancellation.  It does not say that
the J-free operator or either half-line factor has zero trace norm.

The remaining terms contain at least one `J`.  They are ordinary trace-class
boundary expressions before the prolate sum is expanded.

## 4. Rank-one subtraction before the prolate sum

Proof 335 gives, as boundary bilinear forms,

```text
M(z)=exp(-z/2)M_+ +R_z,
M_+=|a><b|,                                         (BT.10)

G^(-1)a=(epsilon,0),
G^(-1)b=(0,epsilon/2).                               (BT.11)
```

It also proves that both appearances of `M_+` in `(BT.1)` vanish after the
`Q phi` pairing.  Thus every angle-resolvent term may be rewritten with at
least one remainder `R_z`; the large fixed coefficient in `(BT.7)` never
multiplies an uncancelled `exp(-z/2)` mode.

This order is mandatory:

```text
assemble the Schur difference
  -> subtract M_+
  -> use Q annihilation
  -> expand J in prolate modes
  -> estimate the remainder.                         (BT.12)
```

Expanding `J` before `(BT.11)` recreates the misleading factor
`1/(1-lambda_0)` on two separately large terms.

## 5. Next-order boundary estimate

Let `f,g` be smooth even window vectors.  Directly from the four blocks of
Proof 335 `(BS.7)`, after subtracting `(BS.8)`, one obtains

```text
|<f,R_z g>|
 <=C exp(-3z/2)
   norm(f)_(H^r([0,1])) norm(g)_(H^r([0,1])).        (BT.13)
```

A convenient fixed `r>=3` suffices.  The four estimates are:

```text
P U_z P:
  y=rho x and even Taylor expansion at x=0;

P U_(-z)P:
  the same expansion in the opposite argument;

P Fourier U_z P:
  cos(2 pi x y/rho)=1+O(rho^-2);

P U_z Fourier P:
  X=rho x, Fourier inversion at 0, then one
  integration by parts for the tail X>rho.           (BT.14)
```

The last block is the limiting one: the compact-window endpoint produces an
`O(rho^-1)` oscillatory tail after the leading boundary evaluation, hence
`rho^-1/2 O(rho^-1)=O(rho^-3/2)`.  The other three blocks are no worse.

For the `n`-th prolate vector, CC20's `Rokh` and `boundWang` estimates bound
the Sobolev factors in `(BT.13)` by a polynomial in `n`.  Therefore

```text
sum_n (|j_(n,+)|+|j_(n,-)|)
  |<prolate_n,R_z prolate_n>|

 <=C exp(-3z/2).                                     (BT.15)
```

Terms containing two copies of `J` are controlled by the product of two
absolutely summable sequences and satisfy the same displacement bound.

The finitely many low modes, including `n=0`, contribute only to `C` after
their leading residue has been removed by Proof 335.

## 6. Compact-correlation translation

In `(BT.1)` the remainder is evaluated at `z+u`.  If
`supp(phi) subset [-B,B]` and `z>=B+1`, `(BT.13)--(BT.15)` give

```text
exp(-3(z+u)/2)
 <=exp(-3z/2)exp(3|u|/2).                            (BT.16)
```

Differentiating the compact correlation only changes the fixed Sobolev order
in `(BT.2)` and does not enlarge support.  This proves `(BT.2)`.

The exponential weight in `(BT.2)` is not a valid global Gate 3U support
bound.  It becomes harmless only after the explicit far split `(BT.3)`.  Do
not use `(BT.2)` for the near region.

## 7. What is and is not closed

```text
fixed-source static half-density residue:       closed by Proof 333;
compressed Schur half-density residue:          closed by Proof 335;
fixed-source next-order far Schur tail:          closed here mathematically;
far Euler-mode absolute summation:               available after |z|>=4B+4;
near complete-product stopped path:              open;
uniform Gate 3U scalar:                          open;
finite-S sign / Burnol identity / RH:            open.             (BT.17)
```

The next proof must insert the far cutoff into Proof 289 `(AZ.20)` without
reopening primewise absolute values in the near set.  All near prime channels
must first telescope to `I-G_S`, and the renewal levels must remain in Proof
290's finite-horizon ordered path.  Proof 336 supplies no permission to count
near primes or norm the all-even/path-boundary sectors separately.
