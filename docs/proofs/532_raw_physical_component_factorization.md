# Proofs 532--535: raw physical component factorization

## Result

The raw four-term adjoint normal form is now named as one operator target,
suffixActualBandRawPhysicalFourTermRow, and is connected to the actual
two-channel physical analysis column.

For component rows:

    ambientRow  : finiteSCarrier -> sourceSoninCarrier
    boundaryRow : finiteSCarrier -> sourceSoninCarrier

the packed readout is:

    readout(x_ambient, x_boundary)
      = ambientRow(x_ambient) + boundaryRow(x_boundary).

Its composition with the physical analysis column is exactly:

    ambientRow * ambientLossColumn
      + boundaryRow * boundary_dagger.

Therefore a source-specific equality of this sum with the named raw
four-term row gives the Proof 531 raw-readout contract. The operator-norm
bound is at most the sum of the two component bounds, and the uniform family
version preserves the same quantifiers over every visible prime and suffix.

## What this changes

The remaining producer obligation is no longer an unnamed four-term
expression. It must supply two actual rows on the two physical coordinates,
with their signed sum retained before any estimate:

    raw four-term row
      = ambientRow * primeEulerAmbientLossFactor_dagger * oldFrame
        + boundaryRow * boundary_dagger.

The physical analysis Gram identity remains available:

    analysis_dagger * analysis = leftCoDefect_dagger * leftCoDefect.

## Proof 533 strengthening

Proof 533 proves the converse interface direction. Any packed raw readout can
be recovered as the packed readout of its two coordinate restrictions:

    ambientRow  = readout * leftEmbedding
    boundaryRow = readout * rightEmbedding

    packed(ambientRow, boundaryRow) = readout.

Consequently the component-row interface and the packed raw-readout interface
are equivalent at the level of exact factorization data. The component bounds
in the recovered direction are the actual operator norms of those coordinate
restrictions, so this adds no new analytic estimate.

## Proof 534 strengthening

Proof 534 proves that both coordinate embeddings are contractive:

    norm(leftEmbedding) <= 1
    norm(rightEmbedding) <= 1

Therefore a packed raw readout with uniform bound C gives component rows with
uniform bounds (C, C). Together with Proof 532's component-to-raw conversion,
Lean now proves the exact existence equivalence:

    exists uniform component readout
      <-> exists uniform packed raw readout.

The direction from component rows to packed raw readout uses the sum of the
two component constants. The reverse direction reuses the raw constant for
each coordinate. This is still bookkeeping for the same analytic obligation,
not a construction of the source-specific rows or a proof of the uniform
bound.

## Proof 535 strengthening

Proof 535 composes Proof 534 with Proof 531's raw/physical equivalence.
Lean now proves:

    exists uniform component readout
      <-> exists uniform physical Douglas domination.

This removes the last formal distinction among the three current interfaces:

    component rows
      <-> packed raw readout
      <-> physical Douglas domination.

The theorem is an exact interface equivalence. It does not produce the
uniform bound required by Gate 3U.

No component rows are constructed by this proof. No family-uniform bound,
Gate 3U, finite-S sign, Burnol identity, or _root_.RiemannHypothesis is
proved.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 532--535 owning module  3327 jobs, PASS
    Proof 532--535 focused audit  PASS
    CCM25Concrete aggregate       3805 jobs, PASS

The audited principal declarations use exactly:

    [propext, Classical.choice, Quot.sound]

The new source and audit contain no sorry, admit, or user axiom
declaration. Existing repository linter warnings are unchanged. No commit,
push, PR, issue comment, or other public outbound action was performed.

## Boundary

The finite-S sign, Gate 3U, negative-owner integration, Burnol identity, and
_root_.RiemannHypothesis remain open.
