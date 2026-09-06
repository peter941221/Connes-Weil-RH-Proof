# 1191 - Exact horizontal defect of the P2 spectral prefix

Date: 2026-09-06.

Status: FORMAL identity and integral readback. P2 remains OPEN; RH is not claimed.

Consumer: the same healthy CompactLog detector's finite spectral prefix in
`BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData`, and the signed
semi-local comparison on that same detector. No new conditional exit is added.

## Derived identity

`C1P2SpectralHorizontalDefect.lean` starts from the genuine Hermitian square
law. Write `s = rho - 1/2`, `a = laplaceAt g s`, `b = laplaceAt g (-star s)`,
and `m = xiMultiplicity rho`. Define actual scalar functions, not input fields:

```text
A(g,rho) = m/2 * (normSq a + normSq b)
D(g,rho) = m/2 * normSq (a - b)
```

Both are nonnegative, and the kernel-checked identity is

```text
Re(spectralTerm(g.square,rho)) = A(g,rho) - D(g,rho).
qw(g) = sum_prefix A - sum_prefix D + Re(same-owner shell tail).
```

The second statement holds at every shell cutoff, including the canonical
Bombieri cutoff. Multiplicities and the precise shell boundary are retained.
This is a finite decomposition; it asserts no separate infinite summability
of the A and D series.

The difference also has an integrable, original-test readback:

```text
a - b = integral_x (exp(s*x) - exp((-star s)*x)) * g.test(x).
```

Integrability is supplied by the two compact exponential weights. In
particular, no use is made of a divergent integral's totalized value.
`D = 0` is equivalent to equality of these two Laplace evaluations. The
critical-line condition implies it; the converse is NOT claimed for a test.

The same leaf now proves a producer-facing lower bound. Whenever a finite
prefix has real spectral value at most `-m(rho)`, its horizontal-defect sum is
at least

```text
m(rho) + sum_prefix pairedMass.
```

This follows from the exact decomposition and nonnegativity of each paired
mass. It applies both to shell prefixes and arbitrary finite prefixes. Thus
the negative detector prefix cannot be identified with a positive Bombieri
quadratic form by omitting the horizontal defect; a valid identification must
carry that defect or prove a compensating same-owner cancellation.

The same lower bound is now instantiated for the actual `selectedOwner`
orbit construction. Its hypotheses are precisely the existing finite-height
target equations and square-zero equations from the healthy interpolation
package; no new sign premise is introduced.

The pinned zero configuration also has an exact anchor value: under the raw
target equations, the selected-owner horizontal defect at `rho` is exactly
`2 * xiMultiplicity rho`. This uses the orbit values `1` and `-1` and the
half-density shift, and is a concrete constraint on any future
finite-prefix/qIntegrand identification.

The paired-mass side is now exact as well: the same selected-owner anchor has
`pairedMass = xiMultiplicity rho`. Hence its individual spectral summand is
exactly `-xiMultiplicity rho` after subtracting the horizontal defect. The
direct Lean readback is
`selectedOwner_spectralTerm_re_anchor_eq_neg_multiplicity`.

Combining the existing orbit-controlled prefix theorem with the same-owner
mass-minus-defect identity gives a finite-set consequence: after removing the
anchor, the remaining paired-mass sum is at most the remaining horizontal
defect sum. This is formalized as
`selectedOwner_nonanchor_mass_le_defect_of_orbit_control`.

The anchor calculation is formalized as
`selectedOwner_horizontalDefect_anchor_eq_two_mul_multiplicity`: with the
existing raw target equations, the selected-owner defect at `rho` is exactly
`2 * xiMultiplicity rho`.

The canonical Bombieri `qIntegrand` prefix contract is also read back
formally: its endpoint-corrected real value equals the same shell prefix's
paired-mass sum minus horizontal-defect sum. Consequently, whenever that
finite spectral prefix is at most `-xiMultiplicity rho`, the endpoint-corrected
`qIntegrand` value is at most the same negative anchor.
Since the Wirtinger remainder is nonnegative, the same contract also forces
the shell horizontal-defect sum to be no larger than the paired-mass sum.
Equivalently, the canonical finite spectral prefix itself is nonnegative;
this direct transport is formalized as
`canonicalQIntegrandPrefix_re_nonneg`.
Therefore the contract is formally incompatible with a finite prefix bounded
by `-xiMultiplicity rho` at any nontrivial zero; this is an interface guard,
not a claim that the canonical cutoff has that negative-prefix property.
Specializing the orbit-controlled negative-prefix theorem to the selected
owner now gives the conditional guard
`no_selectedOwner_canonicalQIntegrandPrefix_of_orbit_control`: if the
canonical cutoff is exactly a shell prefix already certified by the orbit
control hypotheses, the canonical qIntegrand contract yields a contradiction.
This rules out that cutoff alignment only; it does not construct the finite
producer or prove the detector-specific P2 sign.

## Frequency and producer boundary

FORMAL: the actual frequency `gamma = -I * (rho - 1/2)` satisfies
`rho - 1/2 = I * gamma` and `Im gamma = 1/2 - Re rho`. Thus its imaginary
part vanishes exactly on the critical line. Directly casting actual zero
frequencies into the existing real-Gamma matrix loses information unless an
independent transformation accounts for it. This does not refute an indirect
real-Gamma producer or the Bombieri branch.

The identity does not identify `sum A` with Bombieri's quadratic form. For a
candidate finite form Q, the prefix identification must account for the full
quantity `sum A - sum D - Q`. Neither discarding D nor identifying the positive
pieces by their sign proves the missing equality.

Source audit: the canonical bridge still requires finite parameters, a
nonzero vector, the eigen-relation and its reciprocal relation. Those are
producer obligations even though the only remaining analytic equality field
is named `finitePrefix_eq_qIntegrand`.

Quantifier audit: record 1187 chooses a cutoff after fixing a positive finite
main term. It is not a theorem about a main term Q_N varying with the cutoff.
Tail convergence and pointwise Q_N > 0 alone do not imply tail_N < Q_N:
already T_N = 1/(N+1), Q_N = T_N/2 is an elementary counterexample to that
abstract inference. This is a mathematical audit observation, not a new Lean
counterexample or a refutation of the existing fixed-data cutoff theorem.

Next producer work must derive the finite data and the signed identification
from the pinned detector, or control the explicit horizontal integral within
the same-owner semi-local comparison. No sign estimate is proved here.

## Acceptance

The focused source plus import-facing audit build in the ext4 mirror reports
`Build completed successfully (3666 jobs).` in
`build-logs/p2-horizontal-defect-r34.log`, with no `error:` or `sorryAx` matches.
All 26 audited declarations print exactly
`[propext, Classical.choice, Quot.sound]`. Both modules have real `Built` lines.
Windows and WSL source MD5 values agree:

```text
C1P2SpectralHorizontalDefect.lean       df53bc09b2a3a3f5a72f2616b46f7035
C1P2SpectralHorizontalDefectAudit.lean  dda0804ea105d017f7570a23800cec11
```
