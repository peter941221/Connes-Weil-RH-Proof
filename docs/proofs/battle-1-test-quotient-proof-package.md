# Battle 1 Test And Quotient Proof Package

Status: mathematical proof package for Battle 1.

This file advances the proof of:

```text
TestAndQuotientCompatibility(S,I,lambda).
```

It does not certify Battle 1 as complete. It proves the half-density and Tate
quotient-to-pole parts at the level of the current source interfaces, then
reduces the remaining work to one named project lemma:

```text
RankRepairFiniteNormalForm(S,I).
```

## Source Anchors

| item | source anchor |
|---|---|
| `QW(f,g)=Psi(f^* * g)` | manuscript source map `docs/manuscripts/connes-weil-rh-proof-draft.md:37`, formula dependency `:66` |
| `W_(0,2)(F)=hat F(i/2)+hat F(-i/2)` | manuscript source map `docs/manuscripts/connes-weil-rh-proof-draft.md:38`, formula dependency `:67` |
| restricted `QW_lambda` formula | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001` |
| CCM25 source lines for `QW`, `Psi`, and `W_(0,2)` | source reread audit `docs/audits/source-reread-v0.2.md:47` |
| CCM25 source lines for restricted `QW_lambda` | source reread audit `docs/audits/source-reread-v0.2.md:48` |
| CC20 half-density convention | source reread audit `docs/audits/source-reread-v0.2.md:51` |
| route-side source trace audit | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:797-890` |
| imported exploration target | `docs/ConnesWeilPositivity.md:143121-143132` |

External source identifiers:

```text
CCM25: arXiv:2511.22755, https://arxiv.org/abs/2511.22755
CC20:  arXiv:2006.13771, https://arxiv.org/abs/2006.13771
```

## Theorem Target

For an admissible tuple `(S,I,lambda,g)`, define:

```text
F_g = g^* * g.
```

Let `h(F_g)` be the Connes source group test obtained from `F_g` in the CCM
half-density convention. Then:

```text
Trace(R_Lambda U(h(F_g)))
```

has main term:

```text
QW_lambda(g,g),
```

and its no-strip finite-dimensional quotient channels are exactly:

```text
Tate pole channels:  hat g(+i/2), hat g(-i/2)
rank channel:        hat g(0).
```

No finite-prime term may enter through the quotient channels.

## Decomposition

```text
TestAndQuotientCompatibility(S,I,lambda)
        |
        +-- TestHalfDensityCompatibility(lambda)
        |
        +-- TateDirectionsToPoleLedger(lambda)
        |
        +-- RankRepairToZeroModeLedger(S,I)
```

The first two legs close from the current source anchors. The last leg is a
project lemma about the fixed-S positive-compression repair.

## Lemma 1. Test Half-Density Compatibility

Statement:

```text
TestHalfDensityCompatibility(lambda):
  the source test used in Trace(R_Lambda U(h)) is h(F_g)=F_g,
  where F_g=g^* * g is formed in the CCM half-density convention.
```

Proof.

CCM25 reads the Weil quadratic form through:

```text
QW(f,g)=Psi(f^* * g).
```

The manuscript records this formula at
`docs/manuscripts/connes-weil-rh-proof-draft.md:66`, with source target
`CCM25 equation bombtest`. The restricted formula used by Theorem 1 is the
displayed `QW_lambda(g,g)` formula at
`docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001`.

The source reread audit records the half-density convention as a CC20 source
interface at `docs/audits/source-reread-v0.2.md:51`. The exploration note spells
out the corresponding map:

```text
F = Delta^(1/2) f,
F(x)=x^(1/2) f(x).
```

See `docs/ConnesWeilPositivity.md:143159-143170`.

Therefore the source object that enters `Psi` for the route vector `g` is the
convolution square:

```text
F_g = g^* * g.
```

The route-side source trace audit states the same object at
`docs/manuscripts/connes-weil-rh-proof-draft.md:822-830`. Hence the test
conversion closes provided the route's `theta_S(g)` is already expressed in
the same half-density convention.

Output:

```text
h(F_g)=F_g
```

inside the source trace read-off.

## Lemma 2. Tate Directions To Pole Ledger

Statement:

```text
TateDirectionsToPoleLedger(lambda):
  the two Tate quotient directions removed in the Connes source trace produce
  exactly W_(0,2)(F_g), with no finite-prime or Cdef contribution.
```

Proof.

The two Tate directions in the source trace are represented before
half-density normalization by:

```text
f(0),
int f dx.
```

The exploration note records this at
`docs/ConnesWeilPositivity.md:143225-143231` and again at
`docs/ConnesWeilPositivity.md:143381-143392`.

Under the CCM half-density convention, the old Mellin variable `s` and the
Guinand-Weil Fourier variable `t` satisfy:

```text
s = 1/2 + i t.
```

Thus:

```text
s=0  <->  t=+i/2
s=1  <->  t=-i/2
```

with the sign fixed by the convention `u^(-it)`. This is the variable-change
calculation recorded at `docs/ConnesWeilPositivity.md:143403-143426`.

CCM25 writes the corresponding pole functional as:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2).
```

The manuscript source map records this at
`docs/manuscripts/connes-weil-rh-proof-draft.md:67`, and the source reread
audit points to `mc2arXiv.tex:445-470` at
`docs/audits/source-reread-v0.2.md:47`.

For the route's quadratic test:

```text
F_g = g^* * g,
```

the restricted CCM formula displays the same pole contribution as:

```text
2 Re(hat g(i/2) overline{hat g(-i/2)}).
```

See `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001` and
`docs/ConnesWeilPositivity.md:143446-143460`.

Finite-prime terms cannot enter this quotient calculation. CCM25 places finite
primes in the separate summand:

```text
-sum_p W_p(F),
```

as recorded in `docs/manuscripts/connes-weil-rh-proof-draft.md:68-70` and
`docs/ConnesWeilPositivity.md:143462-143469`.

Output:

```text
Tate quotient channels = W_(0,2)(F_g)
```

and these channels are supported only at:

```text
hat g(+i/2), hat g(-i/2).
```

## Lemma 3. Rank Repair Reduction

Current status: closed at route-evidence level, source- and Cdef-conditional.

The remaining project lemma is:

```text
RankRepairFiniteNormalForm(S,I):
  every no-strip fixed-S rank repair is a scalar multiple of hat g(0),
  and every non-pure fixed-S repair term contains a projection defect.
```

Focused proof packages:

```text
docs/proofs/rank-repair-finite-normal-form.md
docs/proofs/semilocal-q-compact-form.md
docs/proofs/fixed-s-no-defect-compact-form-read-off.md
```

It must imply:

```text
Rank_(S,I)(g)=C_(S,I)|hat g(0)|^2
```

modulo endpoint-strip `Cdef` terms.

The exploration note gives the intended mechanism:

```text
pure Euler metric term
      |
      v
scalar action on hat h(0)

non-pure fixed-S term
      |
      v
contains [P_I,M_S], [P_hat_I,M_S], [P_I,M_S^*], or [P_hat_I,M_S^*]
      |
      v
endpoint-strip Cdef
```

See `docs/ConnesWeilPositivity.md:143491-143553`.

This is not yet a proof. A proof must supply the finer lemma chain recorded in
`docs/proofs/rank-repair-finite-normal-form.md`. In particular, it must prove
the semilocal Q compact form identity and the boundary-jet rank/Cdef dichotomy.

At the level of this Battle 1 package, the missing outputs are:

| obligation | required output |
|---|---|
| pure rank classification | a finite list of no-strip rank repair terms |
| scalar zero-mode action | proof that each pure term acts by `A_S(0) hat h(0)` |
| non-pure defect classification | proof that each remaining term has an `M_S` or `M_S^*` projection commutator |
| Cdef routing | proof that each such commutator enters the endpoint-strip Cdef package |

## Conditional Battle 1 Result

Assume:

```text
RankRepairFiniteNormalForm(S,I).
```

Then:

```text
TestAndQuotientCompatibility(S,I,lambda)
```

holds for the route's admissible tests.

Proof.

Lemma 1 identifies the source test as:

```text
h(F_g)=F_g=g^* * g.
```

Lemma 2 identifies the two Tate quotient directions with:

```text
W_(0,2)(F_g),
```

supported only at `hat g(+i/2)` and `hat g(-i/2)`.

The assumed rank normal form identifies the separate positive-compression rank
repair with:

```text
C_(S,I)|hat g(0)|^2,
```

with all non-pure repair terms charged to endpoint-strip `Cdef`.

Therefore the no-strip quotient ledger has exactly the three channels:

```text
hat g(0),
hat g(+i/2),
hat g(-i/2).
```

No finite-prime term enters through these channels. The finite-prime terms
remain inside the CCM25 `-sum_p W_p(F)` part of the Weil form and are handled
through the admissible finite-prime visibility condition.

## Triple-Vanishing Consequence

On the triple-killed domain:

```text
hat g(0)=hat g(+i/2)=hat g(-i/2)=0,
```

the Battle 1 quotient ledger vanishes:

```text
W_(0,2)(F_g)=0,
Rank_(S,I)(g)=0.
```

This supports Theorem 2 only after Battle 2 has already transported the
positive support-square trace and Battle 3 has defined the endpoint-strip
`Cdef` remainder.

## Completion Gate

Battle 1 required a proof of:

```text
RankRepairFiniteNormalForm(S,I).
```

Current reduction:

```text
RankRepairFiniteNormalForm(S,I)
  follows from
FixedSNoDefectCompactFormReadOff(S,I)
```

The intermediate reduction through `SemilocalQCompactFormIdentity(S,I)` and
`BoundaryJetRankCdefDichotomy(S,I)` is recorded in
`docs/proofs/rank-repair-finite-normal-form.md`. The projection-defect part of
that reduction is handled in `docs/proofs/semilocal-q-compact-form.md`; the
no-defect fixed-S compact-form read-off is handled in
`docs/proofs/fixed-s-no-defect-compact-form-read-off.md`.

The current mathematical status is:

```text
half-density leg: closed from source anchors
Tate pole leg:    closed from source anchors
rank repair leg:  closed at route-evidence level
Battle 1:         source- and Cdef-conditional
```
