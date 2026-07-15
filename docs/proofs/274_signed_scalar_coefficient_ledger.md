# Proof 274: Signed-scalar coefficient ledger after the H1 withdrawal

Date: 2026-07-15

Status: coefficient-ownership correction after Proof 273.  Proof 272 proves a
uniform concentration sum for the positive square energy `p^(-m)`.  Proof 273
rejects the positive `H1` square-function route.  The surviving signed scalar
pairing carries one local Euler coefficient `p^(-m/2)`, not its square.

The Levy concentration bound from Proof 272 does not make this scalar ledger
summable.  The complete outer/Sonin/prolate renewal must earn an additional
half-power through a same-object signed cancellation, or the source must prove
a sharper location-aware stopping estimate.  Gate 3U and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| weighted chirp operator norm                   | p^(-m/2), exact              |
| positive square-function energy                | p^(-m), exact                |
| signed scalar local coefficient                | p^(-m/2), exact              |
| reuse p^(-m) after H1 withdrawal               | rejected                     |
| Proof 272 Levy concentration bound             | valid probability lemma     |
| scalar ledger plus Levy bound                  | non-summable majorant        |
| complete signed extra half-power               | open, active Gate 3U        |
| finite-S sign and RH                           | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected coefficient flow is

```text
Euler coefficient a_p^m
        |
        +-- weighted operator norm:  a_p^m
        |
        +-- positive norm squared:   a_p^(2m)
        |
        +-- signed scalar channel:   a_p^m
                                           (AK.1)
```

The square in the middle line belongs only to a positive square-function
estimate.  Proof 273 removes that estimator from the route.

## 2. The source scalar contains one coefficient

For one prime put

```text
a=p^(-1/2),
L=log(p).
```

Proof 222 computes the exact outer finite-prime channel:

```text
-L sum_(m>=1)a^m [F(mL)+F(-mL)].                      (AK.2)
```

Equivalently,

```text
-sum_(m>=1)p^(-m/2)log(p)
  [F(m log(p))+F(-m log(p))].                         (AK.3)
```

Proof 264 equation `(AA.27a)` recovers the same series from the ordered causal
Gram response.  The scalar owner therefore contains one `a^m` coefficient.

Proof 228 proves that the coefficient-weighted chirp operator has

```text
norm(K_(p,m))<=C a^m=Cp^(-m/2).                       (AK.4)
```

Squaring `(AK.4)` gives the positive energy `p^(-m)` used in Proof 272.  It
does not change the coefficient in the scalar trace `(AK.2)`.

## 3. The Stinespring legs do not add a second coefficient

Proof 271 writes a prime innovation through a probability-space Stinespring
map.  A local geometric event has probability

```text
nu_p(m)=(1-a_p)a_p^m.                                 (AK.5)
```

Each of the two paired Stinespring legs carries `sqrt(nu_p(m))`; their product
recovers `nu_p(m)` once.  It does not produce `nu_p(m)^2`.

Proof 269's original cubic error multiplied `(AK.5)` by an operator that had
already received `a_p^m`.  After Proof 273, using the square energy
`a_p^(2m)` as the scalar coefficient would make the same ownership mistake in
a different form.

## 4. Correct stopped scalar ledger

For the ordered future relative law `mu_(S,<p)`, define the location-aware
stopping probability

```text
q_(S,p,m)(B_root)
 =mu_(S,<p)(
    [-m log(p)-2B_root,
     -m log(p)+2B_root]).                              (AK.6)
```

It satisfies

```text
q_(S,p,m)(B_root)
 <=Q_(4B_root)(mu_(S,<p)),                             (AK.7)
```

where `Q_h` is Proof 272's Levy concentration function.  The scalar
prime/mode majorant has the coefficient ledger

```text
sum_(p in S)sum_(m>=1)
 (1+m log(p))^(2d)p^(-m/2)q_(S,p,m)(B_root).           (AK.8)
```

This differs from Proof 272's square-energy sum by one factor `p^(m/2)`.

## 5. The available concentration bound is insufficient

List the active large primes as `r_1<...<r_n`.  Proof 272 gives

```text
Q_h(mu_(S,<r_j))
 <=C [(j-1)r_j^(-1/2)]^(-1/2)
 =C r_j^(1/4)/sqrt(j-1).                              (AK.9)
```

For the first mode, `(AK.7)--(AK.9)` yield only

```text
r_j^(-1/2)Q_h(mu_(S,<r_j))
 <=C r_j^(-1/4)/sqrt(j-1).                            (AK.10)
```

Since `r_j>=j+1`, the decreasing envelope in `(AK.10)` is

```text
C j^(-3/4),                                            (AK.11)
```

up to fixed logarithmic word weights.  The series in `(AK.11)` diverges.
Therefore the Kolmogorov--Rogozin estimate does not prove summability of
`(AK.8)`.

This is a failure of the available upper bound, not a proof that the signed
source response diverges.  The location-aware probability in `(AK.6)` can be
smaller than the Levy supremum, and the complete physical branches can cancel
after the renewal has been resummed.

## 6. Reclassification of Proof 273's source contract

Proof 273 proposed the sufficient scalar envelope

```text
|Phi_(S,p,m)(z;g)|
 <=C(1+m log(p))^(2d)p^(-m)norm(g)_(H^r)^2.            (AK.12)
```

Equation `(AK.12)` remains a valid target, but Proofs 228 and 272 do not prove
it.  Relative to the exact scalar coefficient `(AK.3)`, `(AK.12)` contains the
missing extra half-power.

The source must produce that gain through one of these same-object mechanisms:

```text
complete outer-minus-Sonin-prolate cancellation;

signed cancellation across the k-renewal before an absolute value;

a location-aware bound for (AK.6) stronger than Levy concentration.       (AK.13)
```

Estimating branches, renewal powers, or Stinespring legs separately cannot
establish `(AK.12)`.

## 7. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/274_signed_scalar_coefficient_ledger_probe.py

python3 -B docs/proofs/274_signed_scalar_coefficient_ledger_probe.py \
  --maximum-prime 1000000 --maximum-rank 1000000
```

The certificate compares the single-coefficient scalar ledger with Proof
272's square-energy ledger under the same ordered-future concentration proxy.
The default cutoff `p<=100000` gives

```text
stopped signed-scalar proxy:  1.23764e3,
stopped square-energy proxy:  4.29376e1.
```

These values are diagnostics.  The analytic exponent `(AK.11)` certifies that
the available scalar majorant is not summable; the probe does not establish a
lower bound for the source response.

## 8. Route judgment

Proof 274 keeps Proof 272 as a square-energy probability lemma and rejects its
use as a completed scalar estimate after Proof 273's `H1` withdrawal.

The active Gate 3U bottom is the extra-half-power clause `(AK.12)`: derive it
from the complete signed scalar disintegration in Proof 273, or replace it
with a source-specific location-aware estimate that sums `(AK.8)`.  Proof 275
reduces the one-prime linear part exactly: after compact support deletes the
outer half-line scalar, `(AK.12)` requires the complete Sonin/prolate tangent
to decay as `exp(-z/2)` at displacement `z=m log(p)`.  That continuous source
estimate and its determinant-resummed mixed-prime extension remain open.  The
finite-S sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's identity, and RH remain open.  No Lean owner or route
rewire is authorized.

Successor correction: Proof 289 shows that `(AK.12)` is sufficient but not
necessary for the signed route.  The same completed reward occurs in every
Doob prime channel, and the mandatory future Markov factors telescope:

```text
sum_p G_fut(p)(I-G_p)=I-product_p G_p.
```

Thus no primewise absolute sum, and hence no primewise extra-half-power
estimate, is required after all prime channels remain signed.  The active
bottom is Proof 289 `(AZ.26)`, the complete global renewal-boundary estimate.
