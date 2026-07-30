# Proof 577: old-carrier spectral-gap producer

## Result

This batch closes the functional-analytic implication needed by bone 1, but
it does not prove the source-specific hypotheses.  For

```text
W  = suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
R0 = suffixActualBandRawPhysicalReducedRow
```

the exact sufficient inputs are:

```text
gap * ||y||^2 <= ||W y||^2       (uniform spectral gap)
||R0|| <= rawBound               (uniform reduced-row norm)
```

with `gap > 0` and `rawBound >= 0`.  Lean derives the explicit bound

```text
C = rawBound / sqrt(gap)
```

and proves

```text
||R0 y||^2 <= C^2 ||W y||^2
```

for every visible prime, suffix, and old-carrier vector.

## Dependency diagram

```text
 +------------------------------+       +------------------------------+
 | Uniform spectral gap         |       | Uniform raw-row norm         |
 | gap * ||y||^2 <= ||W y||^2  |       | ||R0|| <= rawBound            |
 +---------------+--------------+       +---------------+--------------+
                 |                                        |
                 +------------------+---------------------+
                                    v
                     +-------------------------------+
                     | C = rawBound / sqrt(gap)      |
                     +---------------+---------------+
                                     |
                                     v
                     +-------------------------------+
                     | ||R0 y||^2 <= C^2 ||W y||^2   |
                     +---------------+---------------+
                                     |
                                     v
                     +-------------------------------+
                     | bounded readout F              |
                     | F * W = R0, ||F|| <= C         |
                     +-------------------------------+
                                     |
                                     v
                     +-------------------------------+
                     | packed physical raw domination |
                     +-------------------------------+
```

The readout is obtained through the existing closed-range Douglas constructor;
the proof does not assume that `range W` is closed in advance.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapAudit.lean
```

The main declarations are:

```text
normSq_le_of_spectralGap_of_norm_le
exists_factor_of_spectralGap_of_norm_le
suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm
suffixRawOldCarrierUniformDominationDataOfSpectralGap
suffixRawAmbientBoundaryUniformDominationDataOfSpectralGap
suffixRawAmbientBoundaryUniformReadoutDataOfSpectralGap
exists_uniform_suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm
```

The old-carrier and packed-physical uniform contracts are separate structures.
The conversion uses the already proved old-frame factorization; no carrier
similarity or oblique projection is introduced.

## Obstruction

`noExistsUniformOldCarrierDomination_of_approximateKernel` proves the necessary
converse guard.  If a family of old-carrier vectors satisfies

```text
||W_n y_n|| -> 0
epsilon <= ||R0_n y_n|| eventually
```

then no finite uniform old-carrier domination package exists.  The theorem does
not construct such a sequence on the actual finite-S carrier.

## Remaining source bottom

The new source module does not prove either of the two uniform inputs:

```text
exists gap > 0, forall p S y,
  gap * ||y||^2 <= ||W(p,S)y||^2

exists rawBound >= 0, forall p S,
  ||R0(p,S)|| <= rawBound
```

In particular, Proofs 575--576 still provide only injectivity, positivity, and
the exact Gram identity.  Those facts do not imply a uniform lower bound on the
infinite-dimensional global-log `L2` carrier.  Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

## Verification

Verification ran in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing from
the Windows source of truth:

```text
focused source build: 3332 jobs, PASS
focused audit + CCM25Concrete aggregate: 3845 jobs, PASS
full repository build: 3925 jobs, PASS
```

Every audited declaration depends only on
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain
no `sorry`, `admit`, or user axiom declaration.  `git diff --check` passes after
the documentation and memory updates.
