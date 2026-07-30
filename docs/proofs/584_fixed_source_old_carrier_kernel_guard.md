# Proof 584: fixed-source old-carrier approximate kernel

## Result

The new source module

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard.lean
```

proves the following pointwise estimate for the genuine two-channel
old-carrier analysis `W_p`:

```text
q_p = ccm24PrimeEulerCoefficient p = p^(-1/2)
y_p = newSuffixFrame lambda [] x

||W_p y_p||
  <= (2 * sqrt(q_p) + 2 * q_p) * ||x||.
```

The two terms have distinct sources:

```text
 +--------------------------+       +------------------------------+
 | ambient loss             |       | moving-boundary channel      |
 | ||loss_p^dagger||        |       | ||(I - N N^dagger) T_p^dagger
 | <= 2 sqrt(q_p)           |       |       (N x)|| <= 2 q_p ||x|| |
 +-------------+------------+       +---------------+--------------+
               |                                      |
               +------------------+-------------------+
                                  v
                 ||W_p (newSuffixFrame x)||
                   <= (2 sqrt(q_p) + 2 q_p) ||x||
```

The sequence theorem
`tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient`
then shows that any visible-prime sequence whose coefficients tend to zero
gives a fixed-source approximate kernel.  The canonical carrier-only sequence

```text
canonicalVisiblePrimeSequence n = (n + 2)^2
```

has coefficient `1 / (n + 2)`, so the corresponding analysis norm tends to
zero.  `CCM24VisiblePrime` records only `p > 1`; this canonical sequence is a
decay sanity check and is not being presented as an arithmetic prime sequence.

## Why this matters for bone 1

```text
fixed source column
        |
        v
W_p (newFrame[] x) -> 0
        |
        +--> possible Douglas obstruction only if the same column also has
             ||M_p oldFrame_p^dagger (newFrame[] x)|| >= epsilon.
```

The second line is not proved here. Therefore this batch does not yet rule out
the uniform old-carrier Douglas quotient. It isolates the remaining moment
question on an explicit, genuinely small old-carrier column. In particular,
the estimate must not be advertised as a completed Proof 583 obstruction.

## Lean evidence

The focused source build passes in the Ubuntu-24.04 WSL2 ext4 mirror:

```text
lake env lean \
  ConnesWeilRH/Source/CCM25Concrete/\
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard.lean
```

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuardAudit.lean
```

The audit target is the repository's standard axiom-clean set:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, Gate 3U estimate, finite-S sign, Burnol
identity, or RH proof is supplied by this document.
