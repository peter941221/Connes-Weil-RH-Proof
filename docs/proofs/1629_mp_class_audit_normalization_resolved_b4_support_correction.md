# 1629 — The MP criterion's class audit (F40), the carrier's Toeplitz normalization resolved, and the B4 support-lemma correction

Date: 2026-09-18.

Status: route record, **no Lean brick** (all content is analytic: N-class
membership, Herglotz growth, the Toeplitz dictionary at the committed facts,
and a support-direction correction). The carrier base stays OPEN; the 1628
redirect to `D⁺_BM(Λ(m))` is **withdrawn as a criterion** (class misapplication)
while its computed value stands as a number about a different operator. RH is
not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); the route map
redrawn this round is [043](../map/043_route_map_to_rh_after_1629.md).

## 1. Definitions retrieved, and the one gap that remains

Exact quotes (A. Hartmann, M. Mitkovski, "Kernels of Toeplitz operators",
<https://arxiv.org/abs/1511.08326>, §8), completing 1628 §1:

```text
Prop 8.6: let Lambda = {lambda_n} be discrete, Theta = e^{i theta} a
  MEROMORPHIC INNER FUNCTION WHOSE INCREASING ARGUMENT theta satisfies
  theta(lambda_n) = 2 n pi. Then
  (i)  if |theta'(x)| ~ |x|^kappa,  sup{ a >= 0 : Ker T_{conj(Theta) S^a} != {0} }
       = D^-_BM(Lambda)                      (interior density),
  (ii) for arbitrary theta,  inf{ a >= 0 : Ker T_{conj(S)^a Theta} != {0} }
       = D^+_BM(Lambda)                      (exterior density);
  equivalently: the radius of completeness of {e^{i lambda_n x}} in L^2[0,a]
  equals D^+_BM(Lambda).

failure of shortness (8.3):  SUM_n |I_n|^2 / (1 + dist(0,I_n)^2) = infinity.
Theorem 8.4 (little multiplier): gamma real-analytic, of bounded variation,
  gamma' bounded from below; not short => gamma + eps x != d + h~;
  short => gamma - eps x = d + h~  (for every eps > 0).
Smirnov-Nevanlinna form: Ker^+ T_U = {0}  <=>  gamma = d + h~.
Theorem 8.5 (big multiplier, the HARDY-space case): under rather mild
  regularity assumptions on gamma, shortness decides (up to eps) whether
  gamma = -phi - h~ with phi the argument of a meromorphic inner function,
  h in L^1(dPi), e^h in L^1(R); the companion extension allows polynomial
  growth |psi'| <= |x|^kappa of the phase.
```

**Gap (open, filed):** the definition of the set `Σ(γ)` and of the intervals
`I_n` in the shortness condition (8.2) was **not retrieved** (the arXiv text
extraction drops display equations; three targeted passes failed), and the
**full statement of Theorem 8.5** (its exact hypotheses, its exact kernel
object, the sign of the `ε`-shift) was not retrieved either. Both are named
retrieval targets; nothing below depends on the missing text except where
flagged.

## 2. Class audit: the 1628 redirect is a class misapplication (law F40)

1628 §1 concluded "the WO base is governed by the single number
`D⁺_BM(Λ(m))`". The exact Prop 8.6 quoted above shows why that conclusion
does not stand: the theorem couples the node sequence to **its own** symbol, a
meromorphic *inner* function with *increasing* argument. Node sequences do not
determine symbols: any discrete `Λ` is the node set of many symbols.

Three independent obstructions, all about `m` itself:

```text
+----------------------------+------------------------------------------------------------+
| test                       | result for m = A/B, A = Gamma_R(1/2 - 2 pi I xi)           |
+----------------------------+------------------------------------------------------------+
| bounded in C_+ (inner)?    | NO.  |m(x+iy)| ~ |x|^{2 pi y} is unbounded for every y>0    |
|                            | (1626 ledger; 1628 erratum F39) => m is NOT in H^inf(C_+)  |
| argument increasing?       | NO.  gamma'(xi) = -2 pi log|xi| + O(1/|xi|) < 0 for      |
|                            | |xi| > 1: gamma has a local max ~7.07 at xi = 1 and        |
|                            | decreases to -infinity on both outer rays (1626)           |
| in the Nevanlinna class N? | NO.  see the Herglotz-growth argument below                |
+----------------------------+------------------------------------------------------------+
```

**`m ∉ N` (new, elementary).** Suppose `f ∈ N(ℂ₊)` with `|f*| = 1` a.e. on `ℝ`
(our `m` qualifies on the boundary: `|m(x)| = 1` for real `x`, since
`|B(x)| = |A(−x)| = |A(x)|`). Write `f = g/h` with `g, h ∈ H^∞`; then
`|g*| = |h*|` a.e., and inner–outer factorization gives `g = c·Θ_g`,
`h = c'·Θ_h` (an outer function of modulus `1` a.e. is a unimodular constant),
so `f = Θ₁/Θ₂` is a ratio of inner functions and `γ = θ₁ − θ₂` is a
difference of arguments of bounded inner functions.

For a bounded inner `Θ`, `−log|Θ| ≥ 0` is a positive harmonic function on
`ℂ₊`, so by the Herglotz representation `−log|Θ(z)| = C·Im z + P[μ](z)` with
`C ≥ 0` and `μ` a finite positive measure; its harmonic conjugate is
`θ(z) = C·Re z + P̃[μ](z) + const`, and the conjugate of a Poisson integral of a
finite measure is `O(log|x|)` on `ℝ` (classical; the disk analogue: the
conjugate of a bounded harmonic function is in BMO). Hence

```text
theta(x) = C*x + O(log|x|),   C >= 0  ==>  gamma = theta_1 - theta_2
                                              = (C_1 - C_2) x + O(log|x|),
```

while our `γ = −2πξlog|ξ| + 2πξ + O(1/|ξ|)` grows super-linearly. Contradiction
=> `m ∉ N(ℂ₊)`.

Consequences:

```text
+-------------------------------------------------------------+----------------------------------+
| classical triviality theorem                                | fires for m?                     |
+-------------------------------------------------------------+----------------------------------+
| m bounded (m in H^inf)  =>  ker T_m = {0}                   | NO (m unbounded)                 |
| m in N^+ with L^2 boundary values  =>  m in H^2  =>         | NO (m not in N at all)           |
|   ker T_m = {0}                                             |                                  |
| Theta inner with increasing argument => Prop 8.6 threshold  | NO (same reason)                 |
+-------------------------------------------------------------+----------------------------------+
```

So the base sits outside **every** classical criterion in the surveyed
literature, in both directions: no theorem forces the kernel to be trivial,
and no theorem produces a witness. Law **F40** filed:

> Before computing a threshold quantity from a cited criterion, audit the
> criterion's MODEL CLASS (is the symbol an inner function? is its argument
> increasing? does it lie in `N`?), not only the stated hypotheses on the
> phase. A node sequence is not a symbol: `Λ(m)` can be the node set of an
> increasing-argument inner function while `m` itself is none of those things,
> and the threshold then decides the kernel of the OTHER symbol.

**The number, for the record.** With `Λ(m) = {ξ : γ(ξ) ∈ πℤ}` and
`γ(ξ) = −2πξlog|ξ| + 2πξ + (π/4)sgn ξ + O(1/|ξ|)`, the right-branch nodes
solve `2π|λ_n|log|λ_n| ≈ nπ`, i.e. `|λ_n| ~ n/(2 log n)`: counting function
`n(R) ~ 4R log R`, local spacing `~ 1/(2 log R)` at height `R`. Every standard
Beurling–Malliavin density of a sequence with super-linear counting function is
infinite, so `D⁻_BM(Λ(m)) = D⁺_BM(Λ(m)) = ∞`. Read through Prop 8.6 this says
the exponential system `{e^{iλ_n x}}` is complete in `L²[0,a]` for every finite
`a` — a statement about that system, **not** about `ker T_m`. With §2's class
audit this number is a symptom of the mismatch, not a verdict on the base; 1628
§1's two-branch table is withdrawn in its criterion reading (the model check
`m ≡ 1` below shows the tree's kernel does exist below a finite threshold, so
"infinite density => empty at every scale" was never a valid inference).

## 3. The carrier's Toeplitz normalization, resolved and model-checked

The 1628 caveat "`a ↔ −log λ` normalization NOT verified" is closed. Derivation
from committed facts only.

Committed input (1622, `Dev/SoninCarrierMultiplierConjugate.lean`): the carrier
is the radial `u` with `U_m u ∈ R(Radial(λ))`, `U_m = F∘L M_m∘L F⁻¹`,
`H = R∘L U_m`, `U_m u = R(H u)`. Committed dictionaries (1624/1626):

```text
supp w subset [c,inf)     <=>  e^{2 pi I c xi}(F w)(xi) in H^2(C_-)
supp w subset (-inf,c]    <=>  e^{2 pi I c xi}(F w)(xi) in H^2(C_+)
```

Write `a := log λ`, `g := F u`. Condition 1 (`u ∈ Radial(λ)`) is
`e^{2πiaξ}g ∈ H²(ℂ₋)`; condition 2 (`U_m u` supported in `(−∞,−a]`) is
`e^{−2πiaξ}(m·g) ∈ H²(ℂ₊)`. Setting `h := e^{2πiaξ}g ∈ H²(ℂ₋)` and
substituting into condition 2 gives `e^{−4πiaξ}m·h ∈ H²(ℂ₊)`, and reflecting
(`h ↦ h(−·)`, `ξ ↦ −ξ`) gives the final form

```text
(CARRIER-Toeplitz)   carrier(lambda) != {0}
   <=>  exists H in H^2(C_+), H != 0, with
        e^{4 pi I (log lambda) xi} * m(-xi) * H(xi)  in  H^2(C_-).
```

Two structural readings, both new to the ledger:

- the operator is a **Toeplitz operator with the conjugate multiplier**
  `m(−ξ) = 1/m(ξ)` (matching the committed module name
  `SoninCarrierMultiplierConjugate`), modulated by `e^{4πi(logλ)ξ}`;
- in the `S(ξ) = e^{iξ}` normalization the shift is `ã := 4π log(1/λ) ≥ 0`, and
  for `λ ≤ 1` the symbol is exactly `conj(S)^ã · m̄` — the same shape as
  Prop 8.6(ii)'s `T_{conj(S)^a Θ}`.

**Model check (`m ≡ 1`), explicit.** `(CARRIER-Toeplitz)` becomes: exists
nonzero `H ∈ H²(ℂ₊)` with `e^{4πiaξ}H ∈ H²(ℂ₋)`. Take `a < 0` and
`H = −F(1_{[2a,0]})`: the indicator sits in `(−∞,0]`, so `H ∈ H²(ℂ₊)`
(dictionary, second row of the table); and
`e^{4πiaξ}H = −F(1_{[2a,0]}(· − 2a)) = −F(1_{[0,−2a]})` with `[0,−2a] ⊆ [0,∞)`,
so `e^{4πiaξ}H ∈ H²(ℂ₋)` (first row). For `a ≥ 0` no nonzero `H` exists (the
support of `F⁻¹H ⊆ [0,∞)` and of the shifted version must meet in `[0,−2a]`,
empty for `a ≥ 0`; at `a = 0` the meeting is the single point `{0}` and an `L²`
function supported there is zero). Hence

```text
model: carrier != {0}  <=>  log lambda < 0  <=>  lambda < 1,
```

exactly 1627's model verdict and exactly the `D⁺_BM(∅) = 0` threshold of
Prop 8.6(ii) at `Θ = 1` (nontrivial for `ã > 0`). The dictionary's *shape* and
*threshold normalization* are therefore pinned; only the letter-level
identification `Θ = m` vs `Θ = m̄` remains a convention flag, and either way the
class audit of §2 stands (`m̄` has poles in `ℂ₊`, so it is not inner either).

**Smirnov–Nevanlinna versus Hardy.** The SN form `Ker⁺T_U = {0} ⟺ γ = d + h̃`
concerns the *Smirnov–Nevanlinna* kernel. Our `γ` is a decreasing function
outside `[−1,1]` plus one compact bump (the increase `γ(−1) → γ(1) ≈ 14`), and
a single compact interval is short in the sense of (8.3)
(`|I|²/(1+dist²) = 4 < ∞`), so at the paper level the SN kernel of our symbol is
expected to be trivial. The base is therefore a **Hardy-only** phenomenon: any
witness must live in `H²(ℂ₊) \ N⁺` — precisely the gap between the Hardy and
Smirnov–Nevanlinna kernels, which is what the *big* multiplier theorem
(Theorem 8.5) addresses and what the missing retrieval covers. Diagnostic only,
not a verdict.

## 4. B4: the support-direction correction

1628 §3 stated `K = F⁻¹(m)` is supported on `[0,∞)` and that "the lower edge
of `U_m v` is controlled by the upper edge of `v`". The direction is wrong.
`m` is holomorphic in `ℂ₊` with all its poles in `ℂ₋`; the Paley–Wiener /
contour-closing dictionary therefore puts `K` on the **left** half-line:

```text
supp K subset (-inf, 0]      (formal / hyperfunction level: m is unbounded in C_+,
                              so K is not an L^2 function on either half-line;
                              model check m = e^{ia z}, a > 0: K = delta at -a/(2 pi) < 0)
==>  supp (U_m v) = supp (K * v) subset (-inf, sup supp v]:
     the UPPER edge of U_m v is inherited from the upper edge of v,
     and no lower edge is created at all.
```

Consequence, unchanged in substance from 1628 but now correctly derived:
B4's premise is the *upper* vanishing condition `supp(U_m v) ⊆ (−∞, −log λ'']`,
and for the committed columns `v` (supported on right half-lines `[c,∞)`,
`sup supp v = +∞`) support algebra yields nothing; the premise is a
**cancellation**, i.e. a statement about the zeros of `m` against `F v`, and it
shares the model-space entry of the carrier base. The committed confinement
brick (1575 §3.3) already extracts everything support algebra gives.

## 5. Verdict and boundaries

- The 1628 criterion redirect is **withdrawn**; law F40 filed (audit the model
  class, not only the hypotheses).
- `D⁺_BM(Λ(m)) = ∞` stands, but as a statement about the completeness of
  `{e^{iλ_n x}}`, not about the base.
- The carrier's Toeplitz form is now **exact and model-checked**: `m(−ξ)`
  symbol, shift `ã = 4π log(1/λ)`, threshold behaviour matching
  `D⁺_BM(∅) = 0` in the `m ≡ 1` model.
- The base is outside every classical criterion; if true it is a Hardy-only
  phenomenon (`H² \ N⁺`), consistent with 1627's finite-type obstruction and
  with the absence of any infinite-type construction. Base OPEN.
- B4: premise unchanged as a cancellation statement; support direction
  corrected.
- T4, S3, WO-S, WO-B, `StripDensity`, `EndpointMass(ε)`, T1, (★), `ρ5`,
  R4/(OB)/W1 and RH: unchanged and OPEN. No gap premise, `SourceRH`, or
  universal gate introduced.

## 6. Acceptance

No Lean brick this round (analytic record; nothing to elaborate). No build was
run and no module changed; the standing accepted modules remain
`Dev/SoninWindowTransport.lean` (1628, log `sonin_window_transport.log`) and
`Dev/SoninScaleMonotonicity.lean` (1626, log `sonin_scale_monotonicity2.log`).