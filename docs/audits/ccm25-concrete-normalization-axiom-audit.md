# CCM25 Concrete Normalization Axiom Audit

Date: 2026-06-28

Status:

```text
first CCM25 concrete-normalization split: built
accepted-source certification: open
exact finite-prime support: open
```

## Result

Good result:

```text
The CCM25 concrete-normalization spine is split into small Lean modules and
builds in a WSL ext4 verification copy.
```

Boundary:

```text
This audit does not prove CCM25 from source formulas. It verifies only that the
new Lean spine exposes the current CCM25Interface rows without adding project
axioms, and that it names the finite-prime exact-support gap instead of
silently closing it.
```

## Modules Checked

| module | scope | build result |
|---|---|---|
| `ConnesWeilRH.Source.CCM25Concrete.Global` | `QW(f,g)=Psi(f^* * g)` and `Psi` sign expansion | pass |
| `ConnesWeilRH.Source.CCM25Concrete.Restricted` | `QW_lambda` formula and pole normalization | pass |
| `ConnesWeilRH.Source.CCM25Concrete.FinitePrime` | one-way finite-prime coverage, pointwise term normalization, exact-support targets | pass |
| `ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact` | fixed-`lambda` exact-support certificate implies fixed-window coverage | pass |
| `ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport` | source prime-power record with concrete lambda cut implies fixed-window exact support | pass |
| `ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm` | pointwise local atom normalization implies finite-prime term normalization | pass |
| `ConnesWeilRH.Source.CCM25Concrete` | aggregate module | pass |
| `ConnesWeilRH` | project target with the new aggregate import | pass |

## Verification Commands

Run in a temporary WSL ext4 verification copy after copying the current Windows
source files into that copy:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.Global
lake build ConnesWeilRH.Source.CCM25Concrete.Restricted
lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrime
lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact
lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm
lake build ConnesWeilRH.Source.CCM25Concrete
lake build ConnesWeilRH
```

Axiom audit commands:

```text
#print axioms ConnesWeilRH.Source.CCM25Concrete.Global.qw_definition_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.Global.psi_sign_expansion_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.Restricted.qw_lambda_formula_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.Restricted.pole_normalization_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrime.global_prime_index_coverage_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrime.restricted_prime_index_coverage_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrime.finite_prime_term_normalization_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrime.finite_prime_visibility_statement
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact.global_coverage_of_exact_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact.restricted_coverage_of_exact_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact.term_normalization_of_exact_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact.visibility_at_lambda_of_exact_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport.exact_support_of_source_prime_power_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport.visibility_at_lambda_of_source_prime_power_support
#print axioms ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm.finite_prime_term_normalization_of_source_terms
```

All printed theorem rows depend only on:

```text
propext
Classical.choice
Quot.sound
```

No new project axiom, `sorry`, `admit`, `opaque`, or `unsafe` was introduced.

## Logic Gap Preserved

The new finite-prime module intentionally separates:

```text
coverage:
  finitePrimeAtomVisible n F -> n in indexSet
```

from:

```text
exact support:
  n in indexSet <-> n is exactly a source-visible finite-prime atom
```

The current `CCM25Interface` provides the former, not the latter. Therefore the
next proof task is not another route wrapper. It is a concrete finite-prime
support record proving exact source prime-power support, lambda cut, weight,
pairing, and pointwise atom normalization before any finite-prime sum is used.

The first replacement step is fixed-`lambda`, not `forall lambda`: an exact
support certificate for one cutoff should imply coverage for that cutoff. The
broader lambda quantifier must be discharged separately through support
containment and the fixed-test choice of lambda.

## Fixed-Lambda Step

The fixed-window exact-support module proves:

```text
ExactSupportAtLambda(W,f,g,lambda)
  -> GlobalPrimeIndexCoverageStatement(W,F_g)
  -> RestrictedPrimeIndexCoverageStatement(W,lambda,F_g)
  -> FinitePrimeTermNormalizationStatement(W,f,g)
```

It does not prove `ExactSupportAtLambda` from CCM25 source formulas. It makes
that object the next source-facing theorem target.

## Prime-Power Record Step

The source prime-power support module makes the next target more concrete:

```text
SourcePrimePowerSupportAtLambda(W,f,g,lambda)
  -> ExactSupportAtLambda(W,f,g,lambda)
```

It introduces the fixed-cutoff predicate:

```text
SourceLambdaCut(lambda,n) := 1 < n and (n : Real) <= lambda^2
```

This prevents a later proof from using an arbitrary cutoff predicate while
claiming to model the CCM25 restricted finite-prime support.

## Pointwise Term Step

The pointwise term module introduces:

```text
SourcePrimePowerTermAtIndex(W,f,g,n)
```

and proves:

```text
SourcePrimePowerTermNormalization(W,f,g)
  -> FinitePrimeTermNormalizationStatement(W,f,g)
```

This keeps the finite-prime sign discipline visible: the local atom is
`Lambda(n) * <g|T(n)g>`, and the negative sign is supplied by the surrounding
`Psi` or `QW_lambda` formula.

The module was checked in a WSL ext4 verification copy with:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm
lake build ConnesWeilRH.Source.CCM25Concrete
lake build ConnesWeilRH
```

The theorem:

```text
finite_prime_term_normalization_of_source_terms
```

also printed only:

```text
propext
Classical.choice
Quot.sound
```

The module was checked in a WSL ext4 verification copy with:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
lake build ConnesWeilRH.Source.CCM25Concrete
lake build ConnesWeilRH
```

The two prime-power support rows:

```text
exact_support_of_source_prime_power_support
visibility_at_lambda_of_source_prime_power_support
```

also printed only:

```text
propext
Classical.choice
Quot.sound
```
