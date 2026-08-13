# 1003 - PSP / prolate attack plan for the scattering Toeplitz kernel

Status: corrected plan, 2026-08-12. This plan does not treat an inner/outer
factorization as a witness. RH is not claimed. No Lean axiom or `sorry` is
added.

## Target

For the repository scattering phase

```text
m(xi) = Gamma_R(1/2 - i * 2*pi*xi) /
        Gamma_R(1/2 + i * 2*pi*xi),
```

prove the nontriviality of the L2 Toeplitz kernel

```text
exists psi in H+, psi != 0, P+(m * psi) = 0.
```

Here `H+ = ccm24HardyPositiveSubspace`, `P+` is
`ccm24PositiveFrequencyProjection`, and the multiplier is
`ccm24ArchimedeanScatteringMultiplier`. This is the `L2` form of
`m * psi in H-`.

## Why the old plan stopped

An a.e.-unimodular factor `P` has constant modulus one on `R`, hence does not
belong to `L2(R)`. The assignment `psi = P` therefore fails before any
Fourier-to-Sonin transport. Wiener--Hopf factorization can organize a Toeplitz
problem, but it cannot replace a proof that this particular kernel is nonzero.

## Work packages

```text
T1  Define the scattering Toeplitz operator on H+.
T2  Prove ker(T_m) iff m*psi lies in H- in the repository projection model.
T3  Prove the transport from ker(T_m) to sourceSoninCarrier(lambda).
T4  Construct a nonzero kernel vector from a prolate/Sonin spectral problem.
T5  Prove its restriction to W is nonzero in L2(volume.restrict W).
T6  Feed T5 through the coframe strip identity to twoOuterNonzeroObligation.
```

`T1` has begun: `Dev/SoninWindowWitness.lean` defines
`archimedeanScatteringToeplitzKernel_nontrivial` and proves the immediate
projection-to-`H-` consequence. `T2` through `T6` remain open.

## Prolate candidate

The candidate is not a generic factorization. The source-backed prolate route
uses a negative eigenfunction of the self-adjoint prolate operator. The
Connes--Moscovici article states that such an eigenfunction belongs to the
Sonin space:

```text
https://pmc.ncbi.nlm.nih.gov/articles/PMC9295779/
```

The implementation must prove the domain, spectral sign, carrier transport,
and window restriction. Each is an independent theorem, not a stored scalar.

## Acceptance criteria

Each package closes only with a theorem that has no project axiom or `sorry`, a
focused WSL `flock lake build`, and a `#print axioms` audit. A nonzero Sonin
witness would reject the current `{2}` infinite-carrier Gate-3U route; it would
not prove RH.
