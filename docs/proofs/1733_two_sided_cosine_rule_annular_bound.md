# 1733 — Two-sided cosine rule: the S3 uniform annular bound reduces to one scattering-phase moment

Date: 2026-09-20. Classification: PAPER PROOF (complete derivation from committed
definitions), with exactly one named analytic remainder (the first moment of the
Hardy-transformed kernel, supplied classically by the digamma asymptotics of the
committed phase). No Lean theorem in this record. RH not claimed. The result is a
MASS-face closure only: by the record 1694/1695 corrections the gate additionally
needed sign (heq) and index, which the map-046/047 exit now carries by other
means; nothing here touches `0 <= qw`.

## 1. The target, verbatim from the committed chain

The last open producer of the S3 square-sum is the uniform annular
kernel-diagonal bound (records 1718/1722/1723/1724): the hypothesis

```text
hdiag : forall n >= N,
  lintegral t, sum' i, ENNReal.ofReal (||(annular output column i)(t)||^2)
    <= ENNReal.ofReal B
```

consumed by
`sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound`
(`ConnesWeilRH/Dev/C1G8R3AnnularKernelDiagonalMass.lean:91`), which closes the
survivor-core square-sum through the already-formal 1676 -> 1659 chain.
Record 1719 named the missing object as "the quantitative rate ... or its
continuous weighted analogue" of the qualitative Hardy tail decay. This
record supplies exactly that continuous weighted analogue, in the sanctioned
shape: 1707's no-go requires the producer to use "the interaction between
[the carrier's] radial half-line condition and its Fourier-support
condition" — which is precisely the engine below.

## 2. Committed objects (all verified in source this session)

* Ambient `H = finiteSCarrier = cc20GlobalLogCrossingL2 = L^2(R, dx)`.
* `E = radialSupportProjection lambda`: orthogonal projection onto
  `{u : u vanishes below log lambda}` (`CCM24LogRadialSupport.lean:40-52`;
  the forbidden region is `Iio (log lambda)`).
* `Ht = ccm24ArchimedeanHardyTitchmarsh` (`CCM24HardyTitchmarsh.lean:331`):
  L2 isometric involution, Fourier readback
  `F(Ht u) = m(xi) * (F u)(-xi)` with `|m| = 1` the committed scattering
  phase (`:340-344`).
* `Q = sourceFourierSupportProjection lambda` = projection onto comap Ht of
  the radial support subspace (`:361-366`); the conjugation identity
  `Q = Ht^-1 E Ht` is formal
  (`sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation`).
* `W = sourceSoninCarrier lambda = E-subspace n Q-subspace` (`:376-380`);
  `R = sourceSoninProjection`.
* `C = rootConvolution owner = cc20GlobalLogConvolution h`,
  `h = owner.sourceTest.involution.test : SchwartzMap R C`
  (`GlobalLogConvolution.lean:43`), the Plancherel convolution
  `C = F^-1 M_{Fh} F`.
* Annulus: `sourceRootAnnularOutputWindow owner lambda N n =
  (1_Icc(-n,n) - 1_Icc(-N,N)) ∘ C ∘ J` with `N <= n`
  (`C1G8R3SourceRootFiniteWindowCriterion.lean:61-66`); its Gram trace along
  a carrier ONB equals the column-energy tsum (`:95-108`).
* Translation reversal is formal:
  `Ht (T_t u) = T_{-t} (Ht u)` (`archimedeanHardyTitchmarsh_globalLogTranslation`,
  consumed by `C1G8R3HardyTranslatedTail.lean:251-278`).

## 3. The kernel family and the two-factor cosine rule

Fix the carrier ONB `{u_i}` of `W` and define the translated kernel family

```text
k_0(y) = conj(h(-y)),      k_t = T_t k_0   (mass of k_t sits near y = t).
```

Step 1 (per-t Bessel). For every u in the ambient and a.e. t,

```text
(C u)(t) = <u, k_t>          (inner = integral of u * conj(k_t))
```

as L2 functions of t: both sides equal `F^-1 ((Fh) * F u)` — the identity on
the Schwartz core is the committed convolution-Fourier readback
(`cc20GlobalLogConvolution_toLp`, up to the explicit flip), and both sides
depend on u only through `F u` with operator bound `|Fh| <= ||h||_1`, so
density extends to L2. Hence, a.e. in t,

```text
sum_i |(C J u_i)(t)|^2 = sum_i |<J u_i, k_t>|^2 = ||R k_t||^2     (Bessel).
```

Step 2 (cosine rule). For any two orthogonal projections with `W <= E` and
`W <= Q`, every u satisfies

```text
||W u|| <= min(||E u||, ||Q u||).
```

Proof: `||W u||^2 = <W u, u>` (W idempotent self-adjoint), and since
`W u = Q W u`, `<W u, u> = <W u, Q u> <= ||W u|| ||Q u||`; divide by
`||W u||` (zero case trivial). Symmetrically with E. This three-line
estimate is the whole mechanism — the meet's own kernel/density is never
needed.

Step 3 (structure). `||Q k_t|| = ||E Ht k_t||` (conjugation identity,
Ht isometric). By translation reversal `Ht k_t = Ht T_t k_0 = T_{-t} v`
with the FIXED vector `v := Ht k_0`. Therefore

```text
||Q k_t||^2 = ||E T_{-t} v||^2 = integral_{x >= a} |v(x+t)|^2 dx
            = integral_{a+t}^infty |v(s)|^2 ds,      a = log lambda,
```

the RIGHT tail of the fixed L2 function v. Symmetrically the E-side reads

```text
||E k_t||^2 = integral_{a-t}^infty |k_0(s)|^2 ds,
```

the right tail of `k_0 = conj h(-.)`, i.e. the LEFT tail of h.

## 4. Assembly (Tonelli; both annulus wings)

The annulus is `(Icc(-n,n) \ Icc(-N,N)) ⊆ Iic(-N) ∪ Ici(N)`. By Steps 1-3
and Tonelli (all integrands nonnegative):

```text
sum_i ||annular output column i||^2
  = integral_annulus ||R k_t||^2 dt
  <= integral_{-infty}^{-N} ||E k_t||^2 dt + integral_N^infty ||Q k_t||^2 dt
  = integral_{a+N}^infty (s-a-N)|k_0(s)|^2 ds
    + integral_{a+N}^infty (s-a-N)|v(s)|^2 ds
  <= integral_{a+N}^infty s (|k_0(s)|^2 + |v(s)|^2) ds
  =: B(N).
```

`B(N)` is independent of `n` (uniform annular bound, exactly the 1680/1723
interface) and `B(N) -> 0` as `N -> infty` provided the single

```text
ANALYTIC HYPOTHESIS (M):  integral_{a+1}^infty s |v(s)|^2 ds < infty,
                          v = Ht(conj h(-.)),
```

holds; the k_0 moment is free because `k_0 in Schwartz` (h is the committed
Schwartz test; every polynomial moment of |h|^2 is finite).

## 5. The one analytic remainder: (M) is a digamma one-pager

`v = F^-1 theta`, `theta(xi) = m(xi) * conj((Fh)(xi))`. Two integrations by
parts give `|v(s)| <= ||theta''||_1 / (2 pi s)^2` (theta in W^{2,1}, so the
boundary terms vanish), whence the hypothesis (M) holds with the explicit
bound `integral_X^infty s|v|^2 <= ||theta''||_1^2 / (8 pi^4 X^2)` — using
only

```text
|m'(xi)| = |gamma'(xi)| = O(log(2+|xi|)),
|m''(xi)| <= |gamma''(xi)| + gamma'(xi)^2 = O((1+|xi|)^{-1}) + O(log^2(2+|xi|)),
```

against the Schwartz decay of `Fh`. These growth bounds are classical
digamma/Stirling asymptotics of the COMMITTED phase: record 1683 already
derived the exact formula `gamma' = 4 pi log lambda - 2 pi log pi +
2 pi Re psi(1/4 + pi i xi)` (digamma; FD-verified 1e-13) and only the bounds
`Re psi(z) = O(log|z|)`, `psi'(z) = O(1/|z|)` (DLMF 5.15.1) are owed. That
one page converts Sections 3-4 from conditional to unconditional.

## 6. Calibrations (all pass)

* m = 1 model: `Ht = flip`, `W = L^2[a,-a]` (lambda < 1), `v = conj h`, and
  `B(N) = 0` exactly once `a + N > R` (support radius) — this reproduces the
  1678 calibration "B = 0 exactly for N >= a+R" verbatim, and the forced-meet
  lattice of 1675/F61 is untouched (continuous statement).
* 1694 mass rig: the same quantity was priced as `integral |kappa|^2 D` with
  the shear density `D ~= (log|xi| - 2a)_+`; the present bound never needs D
  (the cosine rule prices the meet by its FACTORS' violations), and is
  consistent with the rig's 1-3% confirmation that the moment is finite.
* 1707 no-go respected: the linear-in-window-length mechanism (norm-one
  projection estimate) is absent — the right wing is priced by the FIXED
  tail of v, not by window length.
* 1655/F59, 1715, 1717, 1722 rulings respected: no ambient full-basis HS, no
  carrier translation orbit, no shifted-Hardy transfer, no detector-response
  substitution.
* This is exactly record 1724's "form 2" (a direct integrable majorant for
  the annular kernel diagonal), the branch that record called equivalent to
  the Hardy-regularity bridge.

## 7. Boundary

* The theorem proved here is the mass face only. By 1694 the endpoint gate
  decomposes as mass + sign + index; the sign face was relocated to the
  two-premise exit (map 047). NOTHING here implies `0 <= qw` or RH.
* Remaining work: (i) the digamma page of section 5 (paper);
  (ii) the formal skeleton — LANDED this wave: `C1G8R3AnnularTailCosineRule.lean`
  proves the cosine rule `norm_starProjection_le_of_submodule_le`, the Bessel
  identity `tsum_norm_inner_sq_eq_starProjection_normSq` (Hilbert-basis form,
  real-part-normalized), and the abstract annulus-split assembly
  `annular_lintegral_le_of_pointwise` matching the 1723 consumer's
  `hdiag` shape; paired Audit leaf prints standard axioms only
  (`propext, Classical.choice, Quot.sound`); 2449-job focused build clean,
  zero `sorryAx`.  Still owed: the kernel readback (density argument) and
  the translation-tail integral identities that wire section 4 into the
  1723 consumer; (iii) map update (S3 producer re-priced from OPEN to
  conditional-on-one-classical-moment).
* No numerical claim is made; no sorry is introduced; RH not claimed.
