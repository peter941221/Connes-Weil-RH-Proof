# 1034 - Complex Lane R owner split

Date: 2026-08-19.

Owner: `Dev/C1XiCenterTwoGammaComplexSplit.lean`.

Probe: `Dev/C1XiCenterTwoGammaComplexSplitProbe.lean`.

## Verdict

The complex compact-log test owner now has an axiom-clean real/imaginary
decomposition through the Lane R interfaces already present in the repository.
For `g : CompactLogTest`, the owner constructs real-valued component tests
whose sum is exactly `g`:

```text
g.test = realPartTest(g).test + i * imagPartTest(g).test.
```

The decomposition is carried through the following layers:

- the bilateral Laplace transform at every complex parameter;
- the three real-node vanishing conditions `0`, `1/2`, and `1`;
- the real part of the Hermitian convolution square;
- the archimedean numerator, integrand, and complete term;
- each Gamma_R paired-profile term and its interval integral;
- the fixed `N = 21` Lane R finite-prefix quadratic value.

The central readback identities are:

```text
L(g,s) = L(realPartTest(g),s) + i * L(imagPartTest(g),s)

Re((g^* * g)(x))
  = Re((Re(g)^* * Re(g))(x))
  + Re((Im(g)^* * Im(g))(x))

arch(g^* * g)
  = arch(Re(g)^* * Re(g)) + arch(Im(g)^* * Im(g)).
```

This is an owner and algebra decomposition, not a sign producer.  In
particular, it does not prove the fixed-prefix sign target, global spectral
nonnegativity, or RH.

## Important boundary

The module deliberately does not prove that prime-free support of the complex
convolution square transfers to both component squares.  In general, cross
convolution terms can cancel in the complex square, so

```text
support(g^* * g) narrow
```

does not by itself imply

```text
support(Re(g)^* * Re(g)) narrow
support(Im(g)^* * Im(g)) narrow.
```

Any component-level prime-free conclusion needs an additional root-support
hypothesis or a separately proved support identity.

## Verification

The owner and import-facing probe were rebuilt in the WSL2 verification
environment.  The owner completed at job `3630`; the probe completed at job
`3631`.  The audited declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

No numerical sign claim is imported into Lean.  The formal result is limited
to exact identities and vanishing transport on the same test owner.

## Reproduction

```text
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplit
lake env lean ConnesWeilRH/Dev/C1XiCenterTwoGammaComplexSplitProbe.lean
```
