# CCM25 Finite-Prime Normalization Spine Discharge

Status: proof package for the finite-prime normalization spine.

This package attacks the third remaining formal gate from:

```text
docs/audits/source-interface-discharge-completion-audit.md
```

The gate is:

```text
finite-prime normalization
```

The package does not formalize CCM25 arithmetic in Lean. It records the order
and strength of the finite-prime theorem that a later source-import or Lean
pass must expose before the route can use the finite-prime part of `QW` or
`QW_lambda`.

## Evidence Boundary

| object | evidence |
|---|---|
| finite-prime support-pairing package | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| finite-prime index normalization package | `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` |
| restricted `QW_lambda` package | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` |
| global CCM25 `QW/Psi` package | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` |
| source definition spine | `docs/proofs/source-object-definition-spine-discharge.md` |
| source reread audit | `docs/audits/source-reread-v0.2.md:47-48` |
| source-object definition ledger | `docs/audits/source-object-definition-ledger.md:84-89` |

## Target Statement

The finite-prime normalization target is:

```text
CCM25FinitePrimeNormalizationSpine(lambda,g):
  every finite-prime term in the global and restricted CCM25 formulas is
  indexed by a source prime-power atom n;
  the restricted index set is the source support cut by 1 < n <= lambda^2;
  the coefficient is the source von Mangoldt weight Lambda(n);
  the pairing is the source <g|T(n)g> pairing on F_g=g^* * g;
  the equality finitePrimeTerm n F_g = Lambda(n)<g|T(n)g> holds pointwise
  before any finite-prime sum is formed.
```

The dependency order is:

```text
source test g and F_g=g^* * g
      |
      v
source prime-power atom n
      |
      v
global W_p support membership
      |
      v
restricted lambda cut 1 < n <= lambda^2
      |
      v
source coefficient Lambda(n)
      |
      v
source pairing <g|T(n)g>
      |
      v
pointwise term equality
      |
      v
global and restricted finite-prime sums
```

The key rule is:

```text
finite-prime sums are downstream of pointwise normalization.
```

## Lemma 1. Nat Indices Must Factor Through Source Prime Powers

Statement:

```text
FinitePrimeNatIndexFactorsThroughSource(n,F_g):
  if a route finite-prime predicate mentions n, then n first factors through
  the source prime-power support of F_g.
```

Proof.

The source finite-prime term uses evaluations at prime powers:

```text
F(p^m) and F(p^(-m)).
```

The route currently uses `Nat` indices in the compact symbolic record. That
choice is useful for a scaffold, but it does not encode prime-power status.

A later source-object package must therefore expose either a source index type
or a predicate:

```text
SourcePrimePowerIndex n.
```

Every route-visible finite-prime atom must factor through that predicate before
it can enter `globalPrimeIndexSet`, `restrictedPrimeIndexSet lambda`, or
`finitePrimeTerm`.

Failure blocked:

```text
a non-prime-power natural number enters the finite-prime sum.
```

## Lemma 2. Global Support And Restricted Support Are Linked

Statement:

```text
FinitePrimeGlobalRestrictedSupport(lambda,n,F_g):
  restricted support is the lambda cut of the same source support used by the
  global finite-prime leg of Psi.
```

Proof.

The global source spine uses the finite-prime part of:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

The restricted formula uses:

```text
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

These are not two independent finite-prime objects. The restricted support is
the lambda-windowed part of the global prime-power support for the same:

```text
F_g=g^* * g.
```

The formal theorem should expose:

```text
n in restrictedPrimeIndexSet lambda
  iff
n in globalPrimeIndexSet
  and
SourcePrimePowerIndex n
  and
VisiblePrimePowerAtom n F_g
  and
1 < n
  and
n <= lambda^2.
```

or an equivalent pair of source-backed inclusions that preserves the same
information.

Failure blocked:

```text
the restricted formula covers the visible atoms but uses a finite set not tied
to the global CCM25 finite-prime support.
```

## Lemma 3. The Lambda Cut Cannot Absorb Visibility

Statement:

```text
FinitePrimeVisibilityBeforeLambdaCut(lambda,n,F_g):
  source visibility of n in F_g is proved before the lambda cut is applied.
```

Proof.

The fixed-S route side chooses the finite set of visible primes from the support
of:

```text
F_g=g^* * g.
```

before the lambda limit. The lambda condition:

```text
1 < n <= lambda^2
```

then selects the restricted source summands for `QW_lambda`.

If a proof folds visibility into the lambda cut, it can hide two errors:

```text
1. a prime-power atom visible to F_g is omitted;
2. a non-visible atom is added because it satisfies the numeric cut.
```

So the later theorem must keep these predicates distinct:

```text
VisiblePrimePowerAtom n F_g
SourcePrimePowerIndex n
1 < n
n <= lambda^2.
```

Failure blocked:

```text
the restricted index set is numerically plausible but not the source support
of F_g.
```

## Lemma 4. The Weight And Pairing Are Separate Theorems

Statement:

```text
FinitePrimeWeightPairingSplit(n,g):
  source weight normalization and source pairing normalization are separate
  theorem outputs before they are multiplied.
```

Proof.

The restricted source term is:

```text
Lambda(n)<g|T(n)g>.
```

The weight theorem identifies:

```text
vonMangoldtWeight n = Lambda(n).
```

The pairing theorem identifies:

```text
primePowerPairing n g g = <g|T(n)g>.
```

Those two normalizations have different failure modes. The weight can carry a
hidden sign or scale factor. The pairing can use the wrong test or a route-local
bilinear form. Multiplying the two too early hides which leg failed.

Failure blocked:

```text
the finite-prime term is correct as a product while the weight or pairing is
not source-normalized on its own.
```

## Lemma 5. Pointwise Equality Precedes Sum Equality

Statement:

```text
FinitePrimePointwiseBeforeSum(lambda,g):
  finitePrimeTerm n F_g = Lambda(n)<g|T(n)g> is proved for each source
  prime-power index n before the global or restricted finite-prime sum is used.
```

Proof.

The current symbolic route already names:

```text
FinitePrimeTermNormalizationStatement W g g.
```

The source-object replacement packages sharpen this to the pointwise target:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>.
```

This package adds the certification rule: a theorem about the whole sum does
not replace the pointwise theorem. A sum-level equality can hide a wrong atom
through cancellation.

The finite-prime sum may enter only after:

```text
for each n:
  SourcePrimePowerIndex n
  SourceVonMangoldtWeight n
  SourcePrimePowerPairing n g
  SourceFinitePrimeTermNormalization n g.
```

Failure blocked:

```text
the restricted finite-prime sum matches after cancellation while individual
source terms use wrong weights or pairings.
```

## Lemma 6. The Finite-Prime Sign Belongs To QW/Psi, Not The Atom

Statement:

```text
FinitePrimeSignOwnedByFormula(n,g):
  the local finite-prime term is Lambda(n)<g|T(n)g>; the negative sign belongs
  to the surrounding CCM25 `Psi` or `QW_lambda` formula.
```

Proof.

The global CCM25 spine uses:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

The restricted formula uses:

```text
... - sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

The atom theorem must not absorb the negative sign into `Lambda(n)`, the
pairing, or `finitePrimeTerm`. The sign bridge to CC20 depends on knowing which
part of the formula owns the sign.

Failure blocked:

```text
the final sign bridge passes only because a local finite-prime atom has been
defined with the wrong sign.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
CCM25FinitePrimeNormalizationSpine(lambda,g)
```

with these Lean-facing theorem targets:

```text
SourcePrimePowerIndexFactorization
SourceGlobalRestrictedPrimeSupportCompatibility
SourceVisiblePrimePowerBeforeLambdaCut
SourceVonMangoldtWeightNormalization
SourcePrimePowerPairingNormalization
SourceFinitePrimeTermPointwiseNormalization
SourceFinitePrimeFormulaOwnsSign
```

This strengthens the older finite-prime packages:

```text
CCM25FinitePrimeSupportPairingDischarge(lambda,g)
CCM25FinitePrimeIndexNormalization(lambda,g)
```

The older packages name the finite-prime objects. This package fixes the order
and proof strength needed for certification.

## Formalization Consequence

A later Lean interface should not expose only:

```text
globalPrimeIndexSet : Finset Nat
restrictedPrimeIndexSet : Real -> Finset Nat
finitePrimeTerm : Nat -> TestFunction -> Real
vonMangoldtWeight : Nat -> Real
primePowerPairing : Nat -> TestFunction -> TestFunction -> Real
```

as unrelated fields.

It should expose a package shaped like:

```text
FinitePrimeNormalizationSpine
  +-- SourcePrimePowerIndex n
  +-- VisiblePrimePowerAtom n F_g
  +-- restricted support equals global support cut by 1<n<=lambda^2
  +-- vonMangoldtWeight_eq_Lambda
  +-- primePowerPairing_eq_Tn_pairing
  +-- finitePrimeTerm_eq_Lambda_mul_Tn_pairing
  +-- finite-prime sign is owned by QW/Psi formula
```

Then the current compact finite-prime statements can project from that package.

## Remaining Boundary

| task | reason |
|---|---|
| define or import source prime-power indices | `Nat` is still only a carrier |
| prove restricted support is the source lambda cut | coverage alone is weaker than equality or two-sided characterization |
| define or import `Lambda(n)` | current weight field remains symbolic |
| define or import `<g|T(n)g>` | current pairing field remains symbolic |
| prove pointwise finite-prime term equality | this is the theorem that blocks cancellation errors |
| keep the finite-prime sign outside the local atom | final CC20 sign bridge depends on the sign owner |

This package does not prove RH. It removes a finite-prime loophole: the route
must prove source-normalized atoms before it is allowed to use the global or
restricted finite-prime sums.
