# 3153: Indexed object-package provenance

Date: 2026-10-28

Added `IndexedSourceObjectTheoremBasePackage` in
`ConnesWeilRH/Source/ObjectTheoremBasePackage.lean`.

The wrapper retains the established `SourceObjectTheoremBasePackage` as its
consumer-facing `base`, while recording the indexed CCM25 constructor input
and an explicit `ccm25Model_readback` equality. The indexed constructor input
now produces this wrapper through `toIndexedPackage`.

This makes source provenance checkable at the package boundary without
changing the many existing route consumers that still accept the legacy
package type. It does not migrate the normalized root, remove legacy source
data, establish `SourceRH`, or prove RH.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

