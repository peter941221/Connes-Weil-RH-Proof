# 1023 - Lane R Gamma_R shifted-tail majorant

Date: 2026-08-18.

## Verdict

The summed Gamma_R owner now has an explicit magnitude estimate for every
shifted tail.  This closes the analytic size interface needed by the coupled
finite-prefix argument.  It does not prove that the tail has either sign.

## Lean Owner

`ConnesWeilRH/Dev/C1XiCenterTwoGammaTailEstimate.lean` exposes the one-profile
estimate
`exists_gammaRArchProfileIntegral_norm_bound`:

```text
||I_n(F)|| <= L / (2n)^2
  + 2 ||F.test(0)|| exp(-(2n+1)(supportRadius(F)+1))
```

The real-valued definitions
`gammaRArchProfileIntegralMajorant` and
`gammaRArchProfileTailMajorant` retain both terms in one owner.  The public
theorem
`gammaRArchProfileTailNorm_le_explicit_majorant` proves, for `N > 0`,

```text
sum' n, ||I_(n+N)(F)||
  <= sum' n, gammaRArchProfileIntegralMajorant(F,L,n+N).
```

The majorant is summable because its first component is a scalar multiple of
the real p-series with exponent two and its second component is a scalar
multiple of a geometric series with ratio
`exp(-2(supportRadius(F)+1))`, which is strictly below one.

## Scope Boundary

The result is a norm bound, not a sign theorem.  In particular, it does not
justify either of these stronger claims:

```text
forall N, tail(N) <= 0
tail(N) <= C / N with a closed explicit C
```

The finite-prefix sign and the tail magnitude must still be combined on the
same triple-vanishing owner.  The prime-inclusive Lane R inequality and RH
remain open.

## Verification

WSL2 ext4 verification built the owner and import-facing probe at 3540 jobs.
`#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, project axiom, unconditional RH theorem, or numerical sign is
used by the new result.
