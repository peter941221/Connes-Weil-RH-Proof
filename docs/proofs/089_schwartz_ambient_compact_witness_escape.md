# 089 Schwartz Ambient Carrier, Compact Witness Escape

Date: 2026-07-12

## API escape

Use the ambient Schwartz space itself:

```text
Test            = SchwartzMap ℝ ℂ
legacy.encode   = id
legacy.decode   = id
convolutionStar = SchwartzMap.convolution (mul : ℂ ->L[ℝ] ℂ ->L[ℝ] ℂ)
involution      = reflection/conjugation on SchwartzMap
```

`TestFunction` is already `SchwartzMap ℝ ℂ`, so the legacy equivalence is
definitional. Finite complex linear combinations are legal. Compact support is
supplied by a witness predicate; the existing `CompactLogTest` provides such
witnesses.

## Why this avoids proof 086

The earlier mismatch came from making the carrier itself the compact-support
subtype. That subtype cannot be equivalent to all Schwartz functions. The
ambient carrier has no such problem:

```text
ambient linear carrier: all Schwartz functions
compact witness: a Schwartz function + HasCompactSupport proof
```

Mathlib already provides `SchwartzMap.convolution` and its Fourier product
theorem. The project separately proves compact-log integral convolution and
Laplace product in proofs 087-088. A compact witness can be encoded into the
ambient carrier while retaining its support proof outside the carrier.

## Remaining same-object gate

The route must prove that the CC20 and CCM25 operations on the ambient Schwartz
carrier are the same operations as the `CompactLogTest` witness after the
positive-variable/log pullback:

1. ambient convolution square equals the encoded compact-log convolution square;
2. centered Mellin read-off uses that same square;
3. M4 bad-space inner products are defined on the encoded Schwartz object;
4. finite linear combinations preserve the compact-support witness chosen for
   the fixed interval.

These must be explicit transport theorems; no conclusion is stored in the
carrier.

## Verdict

```text
full legacy equivalence: rescued by ambient Schwartz carrier
finite linear combinations: available
genuine convolution: available
compact witnesses: available
CC20/CCM25 same-square transport: open
```

This is a smaller API change than replacing `SourceTestAlgebra`; Plan 026
should pursue it first.

