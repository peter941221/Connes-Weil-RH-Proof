# Record 1703: compressed annular trace dominated by ambient trace

Status: formal, 2026-09-19.

The source-compressed annular window is the ambient annular output followed by
the adjoint of the source inclusion.  Since that adjoint is contractive, the
existing column-energy identities and summability certificates give the formal
comparison

`Re trace(sourceCompressedRootAnnularGram) <= Re trace(sourceRootAnnularGram)`.

The theorem is
`sourceCompressedRootAnnularGram_trace_re_le_sourceRootAnnularGram_trace_re`
in `C1G8R3SourceRootFiniteWindowCriterion.lean`; the paired Audit leaf prints
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

This removes the compressed annular trace as an independent analytic target:
any uniform ambient annular Gram upper bound immediately supplies the
compressed bound and hence the S3 survivor-core consumer.  It does not prove
that ambient bound, the source-projection square-sum, the carrier witness, or
RH.

Evidence: `build-logs/1703_annular_trace_dominance_v3.log`, 3962 jobs,
successful footer, zero error lines and zero `sorryAx` lines.
