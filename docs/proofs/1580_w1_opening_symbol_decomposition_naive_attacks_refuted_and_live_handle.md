# 1580 — W1 opening: the symbol decomposition, two naive attacks refuted by hand, the live handle named

Date: 2026-09-17.

Status: `PAPER` - track W milestone W1 (the owner-funded face, card option (iv)
of 1576, W0 landed in 1578). Zero Lean spend, zero digits as authority (laws
F26/F27); every number below is either a hand derivation from committed
definitions or a self-check, and the two "attack" verdicts are quantitative
rebuttals, not computations. RH not claimed.

## 1. Beat-0 sweep over committed material

- The symbol layer is committed at the digamma level:
  `logDeriv_GammaR_eq_log_pi_add_digamma`
  (`C1XiCenterTwoGamma.lean:906`) gives
  `logDeriv GammaR s = -log(pi)/2 + digamma(s/2)/2` on the half-plane, and
  `:932` `logDeriv_GammaR_eq_halfAnchor` rewrites it as a half-anchor Gauss
  integral - UNDER THE HYPOTHESIS `HalfAnchorGaussContract`.
- FLAG (registered, not funded): the Gauss value
  `psi(1/4) = -gamma - pi/2 - 3 log 2`, used by 1578's hand derivation as a
  paper fact, is NOT committed as a Lean theorem - every committed consumer
  carries it as a contract hypothesis. Any future FORMAL pass on W1 inherits
  this gap.
- No Paley-Wiener Hilbert-space theory of the kind W1 needs (bandlimited
  entire functions with L2 boundary values, complex-point evaluation,
  reproducing kernels) exists in the repo or in the pinned Mathlib v4.30.
  W1 stays a paper target by availability, not by choice.
- The fourth normal form `A(g) = int |g-hat|^2 Phi` is paper-only (1417); the
  committed spatial form `archimedeanTerm` (`SelectedWeilFormula.lean:96-109`,
  `C1SameOwnerWeil.lean:61-64`) is the same functional in the other
  coordinate - both were transcribed in 1578.

## 2. The decomposition (hand-derived, self-checkable)

With `a_n := n + 1/4`, `t := pi*xi`, from the digamma partial-fraction series
`Re psi(1/4 + it) = -gamma + sum_n [1/(n+1) - a_n/(a_n^2 + t^2)]`
(the series used in 1578 s1; convergence is absolute and uniform on compacta
since the n-th summand is `t^2 / (a_n (a_n^2 + t^2)) = O(n^-3)`), subtracting
the value at `t = 0` gives, termwise and exactly,

```text
Phi(2 pi xi) = Phi(0) - sum_{n>=0} h_n(xi),
h_n(xi) := pi^2 xi^2 / ( a_n (a_n^2 + pi^2 xi^2) )   >= 0,
H(xi) := sum_n h_n(xi) = Phi(0) - Phi(2 pi xi), increasing in |xi| to +infinity.
```

Monotone convergence justifies integrating against `|g-hat|^2` on the form
domain D of 1578 s3, so

```text
(OB)  <=>  for all g in class:   int |g-hat|^2 H  >=  Phi(0) * ||g||^2 .
```

This is the escape form of the window theorem: the constrained class must
carry its spectral energy against the weight `H` up to the constant `Phi(0)`.

## 3. Two naive attacks, both refuted quantitatively by hand

**Attack 1 (multiplier-only escape-core).** Bound from below by cutting the
integral at a radius rho: `int |g-hat|^2 H >= H(rho) * leak(rho)` with
`leak(rho) := int_{|xi|>rho} |g-hat|^2`. Then (OB) follows from any leakage
floor `leak >= Phi(0)/H(rho) * ||g||^2`. But H is continuous, `H(0) = 0` and
`H -> +infinity`, so it crosses `Phi(0)` (the hand check places the crossing
near `rho approx 1.08`, between `H < Phi(0)` below and `H > Phi(0)` above);
AT the crossing the required leakage floor is exactly 100 percent of
`||g||^2`, and below it the requirement exceeds 100 percent - an
impossibility, not a difficulty. Above the crossing the requirement is
sub-total, but no uniform leakage floor exists there either: the near-
counterexamples are exactly the prolate/Slepian concentrating sequences -
the eigenfunctions of the time-frequency pair decay toward spectral
concentration on `[-rho,rho]` arbitrarily well within `PW_R` - which are the
same objects 1578 s5 already excluded from the UNCONSTRAINED problem. And no
bound of this shape can use the constraint, since it was derived pointwise in
the multiplier. Verdict: DEAD as stated; the constraint MUST enter through
the bandlimited structure, not through weights alone.

**Attack 2 (termwise positive-kernel splitting).** Each h_n has a positive
definite kernel: `h_n = (1/a_n) * (1 - a_n^2/(a_n^2 + pi^2 xi^2))`, whose
inverse transform is `(1/a_n) delta_0` minus a Poisson kernel of width
`1/(2 pi a_n)`. The delta masses `sum 1/a_n` DIVERGE against
`Phi(0) ||g||^2`, so the termwise split is `infinity - infinity`; only the
renormalized sum (the committed spatial kernel of `archimedeanIntegrand`
divided by `2 sinh`) is finite. Verdict: DEAD - third independent
manifestation (1578 s1 counter-term tail, 1578 s6 truncation error, this
record) of the same structural fact: the renormalization is NON-LOCAL and
any proof must treat the counter-term as part of the kernel, never as an
afterthought.

## 4. The first-mode orientation computation (MODEL self-check only)

The extremal of Attack 1's failure is what W1 really asks. The
"least-oscillating" members of the class are the weighted first Legendre
modes: with `v(x) = e^{x/2}` on `[-R,R]` (`R = log 2/2 = 0.346574`, and
`|v - 1| <= e^{R/2} - 1 = 0.189`, so the constraint `int g v = 0` forces
`|g-hat(0)| = |int g (v-1)| <= 0.189 sqrt(2R) ||g|| = 0.157 ||g||`), the
first mode `g_1` is `v`-orthogonal and odd, and its transform is a constant
times `(w cos w - sin w)/w^2` in the variable `w = 2 pi R xi = R r`.
Hand-solving its extremum and zero:

```text
  |g_1-hat|^2:  quadratic zero at r = 0,
                first maximum at w* = 2.079  (root of (2-w^2) tan w = 2w)
                                       i.e. r* = w*/R = 6.00,
                first zero      at w  = 4.493 (root of tan w = w)
                                       i.e. r  = 12.97.
  symbol zero:  r_0 = 6.290                    (1578 s1)
```

The verdict of the comparison is the honest one: the first mode's MAIN PEAK
(`r* = 6.00`) sits INSIDE the positive plateau, barely - a factor 0.95 of
the symbol zero - and the negative region catches the lobe's right flank and
the `1/w^2` tail against a `-log` weight. The mode-peak heuristic therefore
does NOT decide the sign; (OB) at `R = log 2/2` is a genuine knife-edge
competition that only the full variational analysis (W1c) can settle. What
the heuristic DOES prove structurally: `r* = w*/R` is strictly decreasing in
`R`, so any LARGER window pushes the first mode deeper into the positive
plateau and makes (OB) harder - **the prime-freeness ceiling `2R = log 2`
(`log p >= log 2`, the committed 1417 mechanism) is simultaneously the
hardest window on which (OB) can hold.** That is the exact sense in which
1417 chose its window critically, and W1 is an extremal-oscillation
theorem, not a multiplier estimate.

Per law F27 this paragraph is ORIENTATION, not evidence: it names which
inequalities must survive any proof and kills no gate.

## 5. The live handle, named with its first test

The classical tool shape for s4 is variation-diminishing: if the
renormalized kernel `K(x - y)` of the FORM (the committed spatial form of
`archimedeanIntegrand` / `2 sinh`, read on the window square `[-R,R]^2`)
is strictly sign-regular (all minors of the kernel matrix with ordered nodes
have the checkerboard sign), then the maximizer of a quadratic form with
OSCILLATORY kernel over a codimension-one orthogonal class is the first
orthogonal mode - a Krein-Nudelman/Bary-type comparison reduces (OB) to the
single inequality `A(g_1) <= 0`. Registered prior: map 011's 1417 preflight
refuted total positivity of the Bohr-compactification kernel (263 s8, minor
`det = -0.70708`) - a DIFFERENT object; the question for THIS kernel is open
and it is a finite determinant computation from a committed closed form.

Sub-milestones (replacing the single W1 row in map 011):

```text
  W1a  write K(x-y) on the window square from the committed spatial form,
       hand, including the counter-term (no truncation - 1578 s6 lesson).
  W1b  sign-check the 2x2 minors at ordered nodes (the variation test);
       pass => go W1c, fail => name the failure point and the comparison
       theorem dies; W1 reverts to full compressed-operator pricing.
  W1c  the comparison theorem => A(g) <= A(g_1)-type bound; conclude the
       sign of A(g_1) by the s2 escape form (one 1-D inequality).
```

## 6. Boundary

- MOVED: W1 opened with a hand-verified equivalence (s2), two dead routes
  typed with their quantitative reasons (s3), an orientation ledger of the
  three radii (s4), and a falsifiable first test W1b (s5).
- REGISTERED GAP: the Gauss value at 1/4 is a contract, not a committed
  theorem (`HalfAnchorGaussContract` hypothesis at :934); irrelevant to paper
  W1, fatal to any formal pass, and now on record.
- NOT MOVED: (OB) is neither proved nor refuted; (star), B4, rho5, R4, the
  tower and RH all untouched; nothing machine-checked.
  RH NOT claimed.
