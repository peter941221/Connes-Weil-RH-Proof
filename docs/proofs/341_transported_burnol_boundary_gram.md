# Proof 341: transported Burnol boundary Gram

Date: 2026-07-18

Status: exact same-object boundary formula for the complete endpoint Gate 3U
response.  The Gram-corrected projection onto the transported Sonin space is
replaced by the canonical projection onto a transported Burnol complement.
The resulting scalar is the first derivative of one relative Gram determinant
on the fixed two-copy source window.

This formula retains the canonical response, all path sectors, and the trace
anomaly rejected in Proof 340.  The uniform Markov-boundary estimate, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| Burnol source complement frame                | exact                    |
| complement of transported Sonin space         | exact frame             |
| transported complement projection             | exact Gram correction   |
| endpoint band difference                      | same projection difference|
| compact detector boundary trace               | exact                    |
| relative boundary Gram determinant first jet  | exact                    |
| Markov moment readback                         | exact                    |
| uniform inverse-average estimate               | open                     |
| Gate 3U / RH                                   | open / unproved          |
+------------------------------------------------+--------------------------+
```

The ownership change is

```text
moving/renewal path
  -> complete endpoint projection difference
  -> transported Burnol complement
  -> one fixed-boundary relative Gram determinant
  -> one Markov average of the actual boundary moment.       (BY.1)
```

Unlike Proof 339, every arrow in `(BY.1)` is an operator or completed-trace
identity for the full Gate response.

## 2. Abstract complement transport

Let `H` be the source Hilbert space, let `R` be the source Sonin projection,
and write

```text
C_R=I-R.                                             (BY.2)
```

Burnol's boundary synthesis map is

```text
mathcalA:Y=H_0 direct-sum H_0 -> H,
G=mathcalA*mathcalA,
C_R=mathcalA G^(-1)mathcalA*.                       (BY.3)
```

Here `mathcalA(f,g)=Jf+Fourier(Jg)` and `G` is the fixed Burnol Gram
`[[I,F_0],[F_0,I]]`.

Let `T` be a bounded invertible Euler transport and let `R_T` be the
orthogonal projection onto `T Ran(R)`.  A vector `y` is orthogonal to
`T Ran(R)` exactly when

```text
T* y in Ran(C_R).
```

Therefore

```text
Ran(I-R_T)=Ran(T^(-*)mathcalA).                     (BY.4)
```

Put

```text
M_T=T^(-1)T^(-*),
G_T=mathcalA* M_T mathcalA.                         (BY.5)
```

The canonical frame projection gives

```text
I-R_T
 =T^(-*)mathcalA G_T^(-1)mathcalA*T^(-1).           (BY.6)
```

This is an orthogonal projection.  It is not the oblique similarity
`T C_R T^(-1)`.

## 3. Endpoint band difference

For the one-sided CCM24 orientation, the outer support projection `E` is
preserved by the causal Euler transport.  Put

```text
B=E-R,
B_T=E-R_T.                                          (BY.7)
```

Then the outer complement cancels algebraically:

```text
B_T-B
 =(E-R_T)-(E-R)
 =(I-R_T)-(I-R).                                    (BY.8)
```

Thus `(BY.6)` is a same-object formula for the complete band response, not a
surrogate boundary projection.

## 4. Boundary trace readback

Let `W` be the compact-root convolution detector.  The route has

```text
[W,T]=[W,T*]=0.                                     (BY.9)
```

Under Proof 261's fixed-`S` completed trace legality, rectangular cycling in
the two already trace-class products gives

```text
Tr_H(W(B_T-B))

 =Tr_Y(
    G_T^(-1) mathcalA* W M_T mathcalA
   -G^(-1)   mathcalA* W mathcalA).                 (BY.10)
```

The order in `(BY.10)` is mandatory.  In particular, `G_T^(-1)` remains the
inverse of the averaged boundary Gram; it is not replaced by an average of
pointwise inverses.

Equation `(BY.10)` contains the complete projection difference before a norm.
The finite path's canonical, all-even, and boundary-anomaly pieces are already
resummed inside `G_T^(-1)`.

## 5. Relative Gram determinant

For a diagonal Hermitian detector define

```text
G_T(s)=mathcalA* exp(sW) M_T mathcalA,
G_0(s)=mathcalA* exp(sW) mathcalA.                   (BY.11)
```

At `s=0`, these are `G_T` and `G`.  Whenever the completed relative quotient
is defined in the determinant line, its normalized scalar is

```text
tau_(T,W)(s)
 =det_Y(G_T(s)G_T^(-1))
  /det_Y(G_0(s)G^(-1)).                             (BY.12)
```

Individual infinite determinants in `(BY.12)` need not exist.  The legal
definition is the relative Fredholm determinant supplied by Proofs 267--281;
`(BY.12)` is its Burnol boundary coordinate.  Differentiating at zero gives

```text
partial_s log tau_(T,W)(s)|_(s=0)
 =Tr_H(W(B_T-B)).                                    (BY.13)
```

This is the correct boundary determinant successor to Proof 340.  It owns the
endpoint scalar itself rather than an unweighted path corner.

## 6. Markov boundary moment

Proof 253 identifies the normalized inverse metric as a probability average
of logarithmic translations.  Write

```text
M_T=integral_R U_z dnu_T(z),
nu_T(R)=1.                                           (BY.14)
```

Use Burnol's actual operator-valued boundary moment

```text
mathfrakM(z)=mathcalA*U_z mathcalA.                  (BY.15)
```

Then

```text
G_T=integral mathfrakM(z)dnu_T(z).                  (BY.16)
```

For a compact correlation detector

```text
W_F=integral F(u)U_u du,                            (BY.17)
```

commutation and Fubini on the completed root pairing give

```text
mathcalA*W_F M_T mathcalA
 =integral_z integral_u
    F(u)mathfrakM(z+u)du dnu_T(z).                  (BY.18)
```

Substituting `(BY.16)--(BY.18)` into `(BY.10)` produces the exact scalar

```text
Tr[
 (integral mathfrakM(z)dnu_T(z))^(-1)
 (integral_z integral_u F(u)mathfrakM(z+u)
    du dnu_T(z))

 -G^(-1) integral_u F(u)mathfrakM(u)du
].                                                  (BY.19)
```

Equation `(BY.19)` is the first formula in the route which simultaneously
has:

```text
the complete finite-S endpoint;
the fixed Burnol boundary carrier;
the actual compact correlation;
the complete Euler history as one probability law;
the inverse taken only after the whole history is averaged.       (BY.20)
```

## 7. Relation to Proofs 334--336

Proof 334 uses the same moment `mathfrakM(z)`.  Proof 335 identifies and
annihilates its rank-one half-density residue after the `Q` root completion.
Proof 336 controls the next boundary order for large `|z|`.

Those theorems can now be inserted into the same-object formula `(BY.19)`.
They may not be applied before the inverse average in `(BY.19)` is controlled.
In particular, the invalid step is

```text
(integral mathfrakM(z)dnu(z))^(-1)
  -X-> integral mathfrakM(z)^(-1)dnu(z).            (BY.21)
```

The remaining near theorem is therefore an inverse-average Schur estimate,
not the path-symbol `B^1_1` estimate proposed in Proof 339.

## 8. Exact remaining theorem

Let `F=Q phi` be the route's compact completed correlation.  The Gate 3U
boundary theorem is

```text
sup_(finite S)
 abs Tr[
   G_(nu_S)^(-1) N_(nu_S,Qphi)
  -G^(-1)N_(delta_0,Qphi)]

 <=C(1+B_root)^d norm(g)_(H^r)^2,                  (BY.22)
```

where

```text
G_nu=integral mathfrakM(z)dnu(z),
N_(nu,F)=integral_z integral_u
  F(u)mathfrakM(z+u)du dnu(z).                      (BY.23)
```

The constants must be independent of the visible finite set.  The proof must
use the actual one-sided Euler laws `nu_S`; a generic probability measure is
not enough because Proof 254's two-state direct-sum guard still applies.

If `(BY.22)` is proved, Proof 263 polarization supplies cross roots and the
same scalar is the endpoint Gate 3U owner.  Proof 336 supplies the far moment
tail within this formula.

## 9. Finite certificate

The companion probe verifies `(BY.4)--(BY.13)` for random commuting normal
transport and detector data.  The default cohort reports

```text
transport/detector commutator error    8.44e-16,
transported complement formula error  8.12e-16,
boundary response error               7.22e-16,
determinant derivative error           1.35e-10,
response magnitude                     2.85e-1.       (BY.24)
```

The alternate cohort has complement error `1.12e-15`, boundary error
`6.61e-16`, derivative error `1.56e-10`, and nonzero response `9.12e-2`.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/341_transported_burnol_boundary_gram_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/341_transported_burnol_boundary_gram_probe.py \
  --size 26 --complement-dimension 12 --seed 2341
```

The certificate is finite algebra only.  It does not prove the probability-law
estimate `(BY.22)`.

## 10. Evidence and route judgment

Primary source for `(BY.3)` and the boundary moment:

```text
Jean-Francois Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation
de Fourier, Theorem 4,
https://arxiv.org/abs/math/0208121
```

Project owners:

```text
Proof 253: normalized inverse metric is a translation probability average;
Proof 263: legal compact-root Hermitian response and polarization;
Proof 316/317: Gram-corrected transported Sonin projection;
Proofs 334--336: the same Burnol moment residue and far tail.
```

Final status:

```text
full endpoint -> fixed boundary Gram:       closed mathematically;
relative boundary determinant first jet:    closed mathematically;
complete Euler law -> moment average:        closed mathematically;
uniform inverse-average Schur estimate:      open;
Gate 3U:                                     open;
finite-S sign / Burnol identity / RH:         open.       (BY.25)
```
