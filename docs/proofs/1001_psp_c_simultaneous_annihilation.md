# 1001 - V_arch = simultaneous half-line annihilation (PSP sub-target C setup)

Status: C-setup DONE (typed, axiom-clean); the existential band construction is
still the live OPEN new-analysis leaf. RH not claimed. No sorry / axiom.

## 1. Where we are

Sub-targets A (nonzero radial window element) and B (HT isometry assembly)
are closed axiom-clean. The single remaining leaf is sub-target C: build a
nonzero L2 element u in V_arch = Radial(lambda) INTER HT^-1(Radial(lambda)),
with nonzero mass on the log2 window.

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
  m(x) = Gamma_R(1/2 - i 2 pi x) / conj( Gamma_R(1/2 + i 2 pi x) ).
```

This is a joint Hardy / multiplier condition with |m|=1 and is genuinely new
mathematics (docs/999 already records this is not an assembly leaf): a constructive, concrete, nonzero
pair (a, alpha) whose scattering image is again Hardy on the matching half. It
is not a Lean-assembly leaf and is not yet proved.

## 5. Candidate route (probe, not yet a proof)

The most receptive family is a "reflection-built" analytic alpha:
alpha(x) = P(x) / Gamma_R(1/2 + i 2 pi x) with P real on the axis and P chosen
so m*alpha = reflect of alpha / ... . Concretely one tries

P(x+ix0) built from the Gamma-R transform of a Gaussian / Laguerre in a
half-density, so the HT maps it back into the radial half-line; then project
it to the window. Possibly only a *first* radial antiderivative exists; the
construction boundary condition is where the new tool (a PSP band limit)
is needed.

## 6. Next steps

1. Solve the phi/m Hardy programming problem for a concrete candidate phi.
2. Lift a constructed pair to u by the typed gate
   `vArch_mem_iff_support_ae` (both branches).
3. Prove the window has nonzero mass (sub-target D) and lift
   `twoOuterNonzeroObligation` (sub-target E), then flip AGENTS 998/999.