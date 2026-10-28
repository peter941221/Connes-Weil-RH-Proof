# 3150: Indexed CCM25 constructor boundary

Date: 2026-10-28

Added `IndexedCCM25SourceArithmeticConstructorInput` and
`IndexedCCM25SourceArithmeticConstructorInput.toIndexedConcreteArithmeticRows`
in `ConnesWeilRH/Source/CCM25TheoremBase.lean`.

The constructor boundary accepts the indexed finite-prime source-test
certificate family and packages it with the existing global, restricted, and
pole rows. The conversion is a structure-preserving reassembly; it does not
construct the certificate obligations, prove the normalized root, establish
`SourceRH`, or prove RH.

The legacy `CCM25SourceArithmeticConstructorInput` remains unchanged. This is
intentional: existing consumers still require legacy fields, and replacing
them globally would create an invalid half-migration. The next migration step
is an indexed CCM25 source-model/package consumer, followed by indexed fields
in `ObjectTheoremBasePackage` and only then a root migration.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

