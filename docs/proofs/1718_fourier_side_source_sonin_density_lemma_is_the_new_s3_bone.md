# 1718 — The new S3 bone is a Fourier-side source-Sonin density lemma

Date: 2026-09-20

## Audit result

The selected root convolution is already defined through the Plancherel
multiplier construction.  The source Sonin object, however, currently has
only the following formal interface:

```text
sourceSoninProjection = orthogonal projection onto
  log-radial-support ∩ archimedean-Fourier-support.
```

The tree has no theorem identifying the diagonal of

```text
C ∘ sourceSoninProjection ∘ C†
```

with a Fourier integral, nor a density estimate for that diagonal.  The
existing Hardy transport and prolate-factor theorems therefore cannot close
S3 by operator rewriting alone.

## Exact new lemma required

For the selected compact root multiplier `m_g`, one needs a source-Sonin
density statement of the following form, with all representatives and
normalizations made explicit:

```text
diagonal(C ∘ sourceSoninProjection ∘ C†)(t)
  =/≤ ∫ |m_g(ξ)|² D_lambda(t, ξ) dξ,
```

where the right side has an integrable annular majorant uniform in the outer
cutoff.  A sufficient consequence is the uniform bound on the annular Gram
trace consumed by
`sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound`.

This is a genuine new analytic lemma, not a missing Lean composition.  It
must use the radial/Fourier coupling of the same healthy `CompactLog` carrier;
replacing the source projection by an ambient Fourier or radial projection
would change the owner and is not admissible under the B5 route.

## Status

The route remains active.  The detector-specific negative side and the RH
exit are formal; S3's source-Sonin density lemma is open.  No numerical
claim and no RH conclusion is made here.
