# 1002 - PSP scattering reduction: the unresolved Toeplitz-kernel condition

Status: corrected 2026-08-12. The earlier factorization argument did not prove
that `V_arch` is nontrivial. This document records the exact unresolved
Fourier-side condition. RH is not claimed. No Lean axiom or `sorry` is added.

## 1. Repository scattering phase

`CCM24HardyTitchmarsh.lean` defines, for real `xi`,

```text
A(xi) = Gamma_R(1/2 - i * 2*pi*xi)
m(xi) = A(xi) / conj(A(xi))
      = A(xi) / A(-xi)
      = Gamma_R(1/2 - i * 2*pi*xi) /
        Gamma_R(1/2 + i * 2*pi*xi).
```

The equality with `A(-xi)` is theorem
`ccm24ArchimedeanScatteringPhase_eq_factor_ratio`. The prior display with
`conj(Gamma_R(1/2 + i * 2*pi*xi))` in the denominator was wrong: for real
`xi`, that denominator equals the numerator and would make the displayed ratio
identically one.

## 2. Exact Fourier-side target

After translating the two half-line support conditions through Fourier and
reflection, the required candidate has the form

```text
find psi in H+ intersect L2(R), psi != 0, such that m * psi is in H- intersect L2(R).
```

With the repository projections, this is the Toeplitz-kernel condition

```text
psi in ccm24HardyPositiveSubspace,
psi != 0,
P+ (ccm24ArchimedeanScatteringMultiplier psi) = 0.
```

`Dev/SoninWindowWitness.lean` now exposes this exact predicate as
`archimedeanScatteringToeplitzKernel_nontrivial`. The phase is unit modulus, so
the multiplier is an L2 isometry. The remaining work is to prove that this
Fourier-side condition transports to a member of `sourceSoninCarrier` and that
the member has nonzero restriction to the log-2 window.

## 3. Retraction of the previous factorization argument

The statement

```text
m = Q / P, |P| = |Q| = 1 a.e., psi = P
```

does not produce an L2 vector on the infinite-measure line. If `|P| = 1`
almost everywhere, then `integral_R |P|^2 = infinity`, so `P` is not an
element of `L2(R)`. A Wiener--Hopf factorization also does not by itself imply
that the corresponding Toeplitz operator has nonzero kernel: its index and
Hardy-space assumptions decide the kernel.

M. C. Camara's survey gives the relevant operator identity
`f+ in ker(T_g)` iff `g*f+ in H-`, and relates the kernel to the factorization
index rather than to factorization alone:

```text
https://arxiv.org/html/1710.11572
```

Thus the prior claim "`V_arch` is nontrivial via `psi = P`" is retracted.

## 4. Viable construction route

The prolate route is a candidate source of a genuine L2 witness. Connes and
Moscovici state that a negative eigenfunction of their self-adjoint prolate
operator belongs to the Sonin space:

```text
https://pmc.ncbi.nlm.nih.gov/articles/PMC9295779/
```

The formal route requires all of the following.

```text
prolate operator and domain
  -> negative spectral eigenfunction
  -> transport into sourceSoninCarrier(lambda)
  -> nonzero L2 restriction on W = (log lambda, log lambda + log 2)
  -> exact coframe strip identity
  -> twoOuterNonzeroObligation.
```

This branch can reject the current infinite-carrier Gate-3U route for the
family `{2}`. It does not establish RH.

## 5. Next proof obligations

1. Formalize the scattering Toeplitz operator on the repository Hardy
   subspaces and prove the exact Fourier-to-Sonin equivalence.

2. Formalize the prolate operator or another concrete L2 construction and
   prove a nonzero kernel vector.

3. Prove nonzero `L2` restriction on the log-2 window, consume the coframe
   identity, and classify the infinite-carrier Gate-3U route from the result.
