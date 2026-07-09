# CCM25 Concrete Normalization Spine

Status: first Lean-facing spine for the CCM25 normalization milestone.

This file records the first implementation step for the plan to replace broad
source-interface assumptions by exact theorem rows.

## Result

Good result:

```text
ConnesWeilRH/Source/CCM25Concrete/ now names the CCM25 theorem rows in small
modules instead of consuming the broad CCM25Interface only as one bundle.
```

Certification result:

```text
This is not yet a proof of CCM25 from source formulas. It exposes current
assumptions row by row and names the stronger finite-prime exact-support
target that remains open.
```

## Theorem Rows Exposed

| row | Lean theorem or target | evidence source |
|---|---|---|
| QW definition | `CCM25Concrete.Global.qw_definition_statement` | `ConnesWeilRH/Source/CCM25.lean` interface row |
| Psi sign expansion | `CCM25Concrete.Global.psi_sign_expansion_statement` | `ConnesWeilRH/Source/CCM25.lean` interface row |
| QW_lambda formula | `CCM25Concrete.Restricted.qw_lambda_formula_statement` | `ConnesWeilRH/Source/CCM25.lean` interface row |
| pole normalization | `CCM25Concrete.Restricted.pole_normalization_statement` | pole normalization interface |
| global prime coverage | `CCM25Concrete.FinitePrime.global_prime_index_coverage_statement` | finite-prime normalization interface |
| restricted prime coverage | `CCM25Concrete.FinitePrime.restricted_prime_index_coverage_statement` | finite-prime normalization interface |
| pointwise finite-prime term | `CCM25Concrete.FinitePrime.finite_prime_term_normalization_statement` | finite-prime normalization interface |

## Module Split

| module | scope | first build target |
|---|---|---|
| `ConnesWeilRH.Source.CCM25Concrete.Global` | only `QW` and `Psi` global rows | yes |
| `ConnesWeilRH.Source.CCM25Concrete.Restricted` | only `QW_lambda` and pole normalization | no |
| `ConnesWeilRH.Source.CCM25Concrete.FinitePrime` | finite-prime coverage and exact-support targets | no |
| `ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact` | fixed-`lambda` exact-support certificate implies fixed-window coverage | no |
| `ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport` | source prime-power support record with the concrete lambda cut `1 < n` and `(n : Real) <= lambda^2` | no |
| `ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm` | pointwise local atom normalization before any finite-prime sum | no |
| `ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate` | combines fixed-`lambda` support skeleton with pointwise term normalization | no |

## Logic Gap Made Visible

The current Lean interface proves one-way coverage:

```text
finitePrimeAtomVisible n F -> n in globalPrimeIndexSet
finitePrimeAtomVisible n F -> n in restrictedPrimeIndexSet lambda
```

That is not the same as exact support:

```text
n in indexSet <-> n is exactly a source-visible finite-prime atom
```

The new module therefore defines these stronger targets:

```text
GlobalPrimeSupportExactStatement
RestrictedPrimeSupportExactStatement
FinitePrimeExactSupportStatement
```

They are not derived from `CCM25Interface` yet. That is intentional: deriving
them from the current interface would hide the support-exactness gap.

## Why This Matters

The restricted-to-full bridge and the final sign bridge both rely on the
finite-prime part not changing its support, coefficient, pairing, or sign.

If coverage is mistaken for exact support, the proof can still omit or add
source prime-power atoms while all visible route atoms appear covered. That
would invalidate the later equality:

```text
QW_lambda(g,g) = QW(g,g)
```

for the same fixed test.

## Next Target

The next Lean-facing target is to replace symbolic support coverage with a
concrete finite-prime support record, including:

```text
sourcePrimePowerIndex n
sourcePrimePowerAtomVisible n F_g
restricted lambda cut 1 < n and n <= lambda^2
pointwise Lambda(n)<g|T(n)g> normalization
```

Only after that can the CCM25 finite-prime row claim more than one-way
coverage.

## Fixed-Lambda Guard

`ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact` starts the exact-support
replacement at one fixed `lambda`. This is intentional. The source restricted
formula is a lambda-window cut, so the next proof should first show:

```text
exact support at this lambda
  -> global coverage
  -> restricted coverage at this lambda
  -> pointwise term normalization
```

It should not immediately claim the broader current interface:

```text
forall lambda, restricted coverage at lambda
```

until the lambda quantifier and support containment are proved separately.

## Prime-Power Support Record

`ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport` makes the next target
more concrete by naming:

```text
sourcePrimePowerIndex n
sourceAtomVisible n F_g
SourceLambdaCut(lambda,n) := 1 < n and (n : Real) <= lambda^2
```

and proving:

```text
SourcePrimePowerSupportAtLambda(W,f,g,lambda)
  -> ExactSupportAtLambda(W,f,g,lambda)
  -> fixed-lambda finite-prime visibility
```

This still does not prove the source support theorem from CCM25. It prevents
the next pass from using arbitrary predicates in place of the source
prime-power support and numeric lambda cut.

The module now separates the non-term support data as:

```text
SourcePrimePowerSupportSkeletonAtLambda(W,f,g,lambda)
```

This skeleton deliberately has no pointwise coefficient theorem. It prevents a
future proof from treating correct support as if it also proved the local
finite-prime atom normalization.

## Pointwise Term Guard

`ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm` isolates the local finite
prime atom at one index:

```text
finitePrimeTerm n F_g = Lambda(n) * primePowerPairing n g g
```

The module deliberately keeps the negative sign out of the local atom. The sign
belongs to the surrounding `Psi` or `QW_lambda` formula. This blocks a common
failure mode where the sign is absorbed locally and then subtracted again in
the finite-prime sum.

## Combined Fixed-Lambda Certificate

`ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate` combines the two
obligations in the safe order:

```text
SourcePrimePowerSupportSkeletonAtLambda(W,f,g,lambda)
SourcePrimePowerTermNormalization(W,f,g)
  -> SourcePrimePowerSupportAtLambda(W,f,g,lambda)
  -> ExactSupportAtLambda(W,f,g,lambda)
  -> FinitePrimeVisibilityAtLambdaStatement(W,f,g,lambda)
```

This is still only a fixed-`lambda` certificate. It does not prove the broad
current source interface:

```text
forall lambda, restricted finite-prime visibility at lambda
```

That broader quantifier still requires a separate support-containment and
fixed-test lambda-choice argument.
