# Proof 719: Composed Completed-History Energy

## Result

Proof 712 supplies the uncomposed equality

```text
rightLeg o endpoint = readout o completedColumn.
```

The valid consequence is obtained by composing both sides with the same
source input:

```text
rightLeg o endpoint o sourceInput
  = readout o completedColumn o sourceInput.
```

The new source module records the corresponding energy as
`sourceActualBandCombinedPhysicalRightEnergy_comp`.  A contractive readout
bounds it by the Hilbert--Schmidt energy of `sourceInput`; the fixed physical
source input supplies the existing `2 * fixedPhysicalEnergyMajorant` bound.

## Boundary

This is an exact interface correction, not the missing Gate 3U producer.  The
original Gate energy is evaluated on the unmodified source basis:

```text
sum_i ||rightLeg (endpoint (sourceBasis i))||^2.
```

The new composed energy is instead

```text
sum_i ||rightLeg (endpoint (sourceInput (sourceBasis i)))||^2.
```

The former cannot be replaced by the latter without an additional source
factorization or a uniform endpoint estimate.  The finite-S sign, the signed
Gate 3U producer, Burnol's identity, and RH remain open.

## Verification

The focused source and import-facing audit pass in the Ubuntu-24.04 WSL2 ext4
mirror with `3303/3303` jobs.  The `CCM25Concrete` aggregate and full
repository build also pass with `3314/3314` and `4071/4071` jobs.  All three
new declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The remaining producer obligation is therefore precise: either prove a
factorization of the original endpoint through the fixed physical input, or
prove a family-uniform raw endpoint bound strong enough to control the source
basis energy.  The current uncomposed readout and dense-range cancellation do
neither.
