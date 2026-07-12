# 026 Schwartz Multiplicative Source Owner

Date: 2026-07-12

Status: rejected as a direct source owner (2026-07-12). The ambient Schwartz
carrier passes convolution/type probes, but the existing finite-prime package
has a universal finite-support quantifier incompatible with genuine Schwartz
tests. See proof 094.

## Route obligation

Provide a genuine same-object source carrier on which the Xi quotient,
finite-dimensional M4 orthogonalization, CCM25 Weil read-off, and CC20 trace
all refer to one test.

## Proposed owner

Use `Test = TestFunction = SchwartzMap ℝ ℂ` as the ambient carrier with
identity legacy equivalence and Mathlib's genuine Schwartz convolution. Use the
repository's `CompactLogTest` as a compact witness mapped into that carrier.

```text
Test              = SchwartzMap ℝ ℂ
legacy.encode     = id
legacy.decode     = id
convolutionStar   = additive-group convolution
involution f (x)  = conj (f (-x))
```

The additive convolution of Schwartz functions is again Schwartz, and the
existing compact owner proves the same closure for compact witnesses. Fourier/
Mellin transform multiplicativity has the correct product shape, unlike the
current additive toy model.

## Required gates

1. **Ambient carrier escape.** Keep the existing full legacy equivalence by
   taking `Test = TestFunction = SchwartzMap ℝ ℂ`; compact support is a witness
   predicate, not a subtype. See proof 089.

The minimal Lean type probe for the ambient convolution, involution, complex
linear carrier, and Fourier product theorem passes. See proof 090.

The same probe also proves pointwise transport of the ambient convolution to
the `CompactLogTest` convolution. `WeilFormSymbols` already has this ambient
carrier, so no route type rewrite is needed. See proofs 091-092.

The probe now also compiles a complete existing `SourceTestAlgebra` instance
with this ambient carrier. See proof 093. The only active gate is rebuilding
the source arithmetic and CC20 trace package on the genuine square.
2. **Schwartz convolution closure.** Reuse Mathlib's `SchwartzMap.convolution`
   and the project's `CompactLogTest.convolution` instead of redefining either.
3. **Mellin half-density bridge.** The raw log-to-Mellin identity already
   survives in `CC20YoshidaConvolution.lean` via
   `laplaceAt_compactLogTestOfWindow_eq_mellin`; finish only the centered
   parameter shift `u=s-1/2` and its orbit involution. See proof 087.

The convolution and Laplace multiplication subgate is accepted by the
existing `laplaceAt_convolution` theorem. See proof 088.

The direct owner is now dead: `SourceFinitePrimeExactSupportData` requires one
finite prime carrier exact for every ambient Schwartz test. Reopen only with a
cutoff-indexed finite package plus a separately proved prime tail.
4. **Support owner.** Compact support is an extra predicate on Schwartz tests;
   prove compact smooth witnesses and convolution support addition without
   claiming every Schwartz function is compactly supported.
5. **Prime/pole read-off.** Rebuild the CCM25 finite-prime and pole functionals
   on the same convolution square, not on the old additive model.
6. **CC20 trace owner.** Transport the fixed-interval `K_I` and positive trace
   to this carrier. No stored conclusion or arbitrary source data field is
   permitted.

## Immediate death gates

```text
Mathlib has no usable Schwartz convolution theorem with the needed normalization
the centered Mellin map is not multiplicative on this carrier
compact-support cutoffs leave the source class or break the trace owner
the prime translations cannot be defined on the same square
```

Any one of these rejects 026 before Lean route integration.

## Why this is the right lower owner

It repairs exactly the defect in proof 085: finite complex linear combinations
are now actual tests, while the operation is no longer the invalid `f + g` toy
operation. The Xi quotient plus fixed-interval bad-space orthogonalization can
therefore be tested on a mathematically honest carrier before any final RH
claim is wired.
