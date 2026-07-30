# Proof 580: raw physical quotient guard

## Result

Bone 1 remains a genuine source theorem.  This batch proves the precise
logical boundary around it: positivity, injectivity, and bounded raw norm do
not produce one uniform Douglas readout.

The scalar countermodel is

```text
A_epsilon = epsilon * I
R         = I
```

For every `epsilon > 0`, `A_epsilon` is injective and
`A_epsilon^dagger A_epsilon` is positive.  Both the analysis and raw maps are
uniformly bounded on the unit interval.  Nevertheless, for every finite `C`,
choosing `epsilon = 1 / (|C| + 1)` gives

```text
||R 1||^2 = 1
    > C^2 * epsilon^2
     = C^2 * ||A_epsilon 1||^2.
```

Therefore the following inference is invalid:

```text
positive Gram + injective analysis + bounded raw row
        -/-> uniform Douglas domination
```

## Relevance to the actual carrier

Proofs 575--579 prove the actual old-carrier Gram identity, injectivity, the
old-carrier/source-carrier reduction, and the conditional local Douglas
bridge.  Proof 580 does not instantiate the scalar family on the CCM24
global-log carrier.  It closes only the generic shortcut and leaves the real
fork explicit:

```text
                 +------------------------------+
                 | actual signed raw row R0      |
                 +---------------+--------------+
                                 |
                                 v
                 +------------------------------+
                 | actual analysis W             |
                 | W^dagger W = I - T P T^dagger|
                 +---------------+--------------+
                                 |
             +-----------------+-----------------+
             |                                   |
             v                                   v
  source-specific bounded quotient       source-specific approximate kernel
  R0 = F W, uniformly in p,S              W y_n -> 0, R0 y_n !=> 0
             |                                   |
             v                                   v
       Gate 3U handoff                  no uniform Douglas producer
```

The next productive source step must supply one of these two actual
statements.  No finite-S sign, Burnol identity, or RH conclusion is claimed.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierQuotientGuard.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierQuotientGuardAudit.lean
```

The declarations use only the standard axiom set
`[propext, Classical.choice, Quot.sound]`.

## Verification

The Windows source was synchronized to an Ubuntu-24.04 WSL2 ext4 mirror
before running Lake:

```text
focused source build: 3333 jobs, PASS
focused audit: 3334 jobs, PASS
CCM25Concrete aggregate: 3847 jobs, PASS
full repository build: 3928 jobs, PASS
git diff --check: PASS
```

The focused audit prints exactly `[propext, Classical.choice, Quot.sound]`
for all seven audited declarations.  No `sorry`, `admit`, or user axiom was
added.
