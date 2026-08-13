# 1001 - V_arch = simultaneous half-line annihilation (PSP sub-target C setup)

Status: C-setup DONE (typed, axiom-clean); the existential band construction is
still the live OPEN new-analysis leaf. RH not claimed. No sorry / axiom.

## 1. Where we are

Sub-targets A (nonzero radial window element) and B (HT isometry assembly)
are closed axiom-clean. Sub-target C must build a nonzero `L2` element in
`V_arch = Radial(lambda) INTER HT^-1(Radial(lambda))`; a separate sub-target
must prove nonzero restriction to the log-2 window.

## 2. The exact condition (now a Lean theorem)

`Dev/PaleyWindowAnalysis.lean` proves, for `l = lambda` and any u, the iff

```
vArch_mem_iff_support_ae :
  u in ccm24ArchimedeanSoninClosedSubspace l
  <->  (a.e. t < log lambda => u t = 0)
       /\  (a.e. t < log lambda => (HT u) t = 0)
```

with `HT = ccm24ArchimedeanHardyTitchmarsh`. Sub-target A gives the first
branch for u = soninWindowIndicator. So C reduces to the *second* branch:
`(HT u) t = 0` a.e. for t < log-lambda.

## 3. Why the naive / eigen-route is empty

A nonzero radial ±-eigenvector of HT (`HT u = u` or `-u`) would trivially be
in V_arch; the exact level-set of the scattering multiplier m(2*pi*xi) is thin
in L2, so the Fourier-class eigen candidates vanish (docs/1000). Band-limited
/Paley-Wiener building blocks do not by themselves guarantee the HT-half.

## 4. The operator form the proof must solve

Think on the Fourier axis with `phi = F(u)`. Beta/radial (support on t >= log
lambda) equals phi analytic in the upper half-plane (Paley-Wiener/Titchmarsh).
HT reads phi(xi) = m(xi) * phi(-xi) on the real line; the second half-line
condition demands the whole `xi -> m(xi) * phi(-xi)` extend to an upper-half-plane
Hardy function as well. Writing alpha(xi) = phi(-xi) (lower-hardy when phi is
upper), the load leaf is exact simultaneous

```
  phi      upper Hardy,    and    m * alpha upper Hardy,
  m(x) = Gamma_R(1/2 - i * 2*pi*x) / Gamma_R(1/2 + i * 2*pi*x).
```

This is the scattering Toeplitz-kernel condition. It needs a concrete nonzero
`L2` pair. A Wiener--Hopf factorization alone does not supply one.

## 5. Candidate route (probe, not yet a proof)

Use a prolate/Sonin spectral construction rather than a formal factorization.
The candidate must establish the `L2` domain, the scattering Toeplitz-kernel
condition, the transport to `V_arch`, and its nonzero restricted norm.

## 6. Next steps

1. Define the Toeplitz operator and prove its equivalence with the two Hardy
   support conditions.
2. Build a genuine nonzero `L2` kernel vector and transport it to `V_arch`.
3. Prove its window restriction is nonzero and lift
   `twoOuterNonzeroObligation`.
