# CCM25 Finite-Prime Support Pairing Discharge

Status: proof package for the finite-prime part of the CCM25 source-interface
discharge.

This package attacks the two finite-prime gates isolated by
`CCM25RestrictedReadOffDischarge(lambda,g)`:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

It does not prove the CCM25 source paper inside Lean. It fixes the exact
prime-power support, coefficient, and pairing obligations that must replace the
current symbolic fields in `ConnesWeilRH.WeilFormSymbols`.

## Evidence Boundary

| claim | evidence |
|---|---|
| finite-prime Weil term | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:36`, `53`, `69` |
| prime-power pairing | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:40`, `71`, `999-1001` |
| restricted finite-prime sign | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1017-1019`, `1349-1357` |
| fixed-S visible-prime condition | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:312-328`, `1043-1057`, `1368-1374` |
| source ranges | `docs/audits/source-reread-v0.2.md:47-48` |
| Lean symbols to replace | `ConnesWeilRH/Basic.lean:46-54`, `77-101` |
| route bridge using the symbols | `ConnesWeilRH/Route/AdmissibleWindow.lean:43-68` |

## Target Statement

For the source-backed fixed-`S` test `g`, let:

```text
F_g = g^* * g.
```

The finite-prime discharge target is:

```text
CCM25FinitePrimeSupportPairingDischarge(lambda,g):
  every prime-power atom visible to F_g is represented in the restricted
  finite-prime index set for lambda, and its finite-prime term equals the CCM25
  von Mangoldt weight times the CCM25 prime-power pairing.
```

In Lean-facing form, this means:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

plus the global coverage statement used before restriction:

```text
GlobalPrimeIndexCoverageStatement W F_g.
```

## Lemma 1. Prime-Power Atom Shape

Statement:

```text
CCM25PrimePowerAtomShape:
  finite-prime atoms are prime-power evaluations of F_g at p^m and p^(-m).
```

Proof.

The manuscript records the source finite-prime formula as:

```text
W_p(F)=(log p) sum_(m>=1) p^(-m/2)(F(p^m)+F(p^(-m))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:53
docs/manuscripts/connes-weil-rh-proof-draft.md:69
docs/audits/source-reread-v0.2.md:47
```

Thus a visible finite-prime atom for `F_g` must be represented by a
prime-power support point, not by a free scalar term. This rules out the
failure mode where the fixed-S trace contains a finite-prime summand but the
restricted index set cannot point to a concrete prime-power atom.

Lean replacement target:

```text
finitePrimeAtomVisible : Nat -> TestFunction -> Prop
```

must be replaced by a concrete predicate saying that the corresponding
prime-power evaluation of `F_g` is visible in the source support.

## Lemma 2. Restricted Index Coverage

Statement:

```text
CCM25RestrictedPrimeIndexCoverage(lambda,F_g):
  if a prime-power atom is visible to F_g in the restricted window, then its
  index belongs to the restricted finite-prime index set for lambda.
```

Proof.

The restricted formula uses:

```text
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:997
docs/manuscripts/connes-weil-rh-proof-draft.md:1019
```

The fixed-S side condition says the route may read the fixed-S source trace as
the full restricted form only after all finite primes visible to `F_g` are
covered:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
```

Therefore the restricted index set cannot be empty or merely formal. It must
match the source prime-power support inside the `lambda` window.

Lean replacement target:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
```

defined in `ConnesWeilRH/Basic.lean:81-84` and currently derived in
`ConnesWeilRH/Route/AdmissibleWindow.lean:56-62`.

Remaining discharge burden:

```text
Define restrictedPrimeIndexSet lambda as the source prime-power support set
selected by the CCM25 restricted formula, then prove visible atoms of F_g land
in that set.
```

## Lemma 3. Von Mangoldt Weight Normalization

Statement:

```text
CCM25VonMangoldtNormalization:
  the finite-prime coefficient is the CCM25 Lambda(n) weight, not a route-local
  coefficient.
```

Proof.

The restricted formula records:

```text
-sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

The source-sign audit records that finite primes enter with the negative sign
from the CCM Weil form, not through a shortcut trace identity.

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1017-1019
docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1366
```

The negative sign belongs to the surrounding `QW_lambda` formula. The local
finite-prime term normalization should therefore identify the atom with:

```text
Lambda(n) * <g|T(n)g>
```

and leave the subtraction to the restricted Weil-form sum.

Lean replacement target:

```text
vonMangoldtWeight : Nat -> Real
```

must become the CCM25 von Mangoldt weight on prime-power indices.

## Lemma 4. Prime-Power Pairing Normalization

Statement:

```text
CCM25PrimePowerPairingNormalization:
  the route pairing is the CCM25 pairing

    <g|T(n)g>
      =
    n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

Proof.

The manuscript records the pairing formula at:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:70-71
docs/manuscripts/connes-weil-rh-proof-draft.md:999-1001
```

The source reread audit points the pairing to the CCM25 restricted quadratic
form source range:

```text
docs/audits/source-reread-v0.2.md:48
```

Thus the route pairing is not an arbitrary bilinear form. It is the explicit
prime-power operator pairing in the restricted formula.

Lean replacement target:

```text
primePowerPairing : Nat -> TestFunction -> TestFunction -> Real
```

must be replaced by the source pairing, and the selected diagonal use must be
`primePowerPairing n g g`.

## Lemma 5. Term Normalization

Statement:

```text
CCM25FinitePrimeTermNormalization(g):
  for every prime-power index n,

  finitePrimeTerm n (g^* * g)
    =
  vonMangoldtWeight n * primePowerPairing n g g.
```

Proof.

Combine Lemma 3 and Lemma 4. The finite-prime term is the CCM25 coefficient
times the CCM25 pairing. The support test is `F_g=g^* * g`, already fixed by
the restricted read-off package.

Lean replacement target:

```text
FinitePrimeTermNormalizationStatement W g g
```

defined in `ConnesWeilRH/Basic.lean:86-90` and currently derived in
`ConnesWeilRH/Route/AdmissibleWindow.lean:64-68`.

Remaining discharge burden:

```text
Replace finitePrimeTerm, vonMangoldtWeight, and primePowerPairing by concrete
CCM25 definitions, then prove the displayed equality for every prime-power
index in the source support.
```

## Lemma 6. Fixed-S Visibility Before Lambda Exhaustion

Statement:

```text
FixedSVisiblePrimeSetBeforeLimit(g):
  the finite set S_A is chosen from the support of F_g before lambda tends to
  infinity.
```

Proof.

The manuscript states:

```text
If supp(F_g) subset exp([-A,A]), take
S_A={infinity} union {p : log p <= A}
before lambda -> infinity.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
```

This prevents the route from growing `S` with `lambda`. It also prevents the
fixed-S trace from missing a finite-prime atom that still appears in the
restricted CCM25 sum.

This is a route-side admissibility condition, not a CCM25 source theorem. It
must stay in the project bridge layer.

## Combined Result

The six lemmas give the finite-prime discharge package:

```text
CCM25FinitePrimeSupportPairingDischarge(lambda,g)
```

with outputs:

```text
GlobalPrimeIndexCoverageStatement W F_g
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

These are exactly the finite-prime components of:

```text
FinitePrimeVisibilityStatement W g g.
```

## Current Status

```text
prime-power atom shape:              source-identified
restricted index coverage:           Lean target exposed, source-backed
von Mangoldt normalization:          source-identified
prime-power pairing normalization:   source-identified
finite-prime term normalization:     Lean target exposed, source-backed
fixed-S visibility before limit:     route-side admissibility condition

CCM25FinitePrimeSupportPairingDischarge: source-interface proof package written
Formal/accepted source discharge:        still open
```

This package narrows the finite-prime work to concrete replacements for the
symbolic `WeilFormSymbols` fields:

```text
globalPrimeIndexSet
restrictedPrimeIndexSet
finitePrimeAtomVisible
finitePrimeTerm
primePowerPairing
vonMangoldtWeight
```

Until those fields are replaced by source definitions or formal imports, the
finite-prime part remains source-conditional.
