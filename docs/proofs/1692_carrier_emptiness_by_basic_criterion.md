# 1692 — The committed carrier is EMPTY: the basic criterion's necessity face decides the base (Kolmogorov ceiling law F64); front-B base leg closed; canonical-system transfer void (explicit W/W̃, no de Branges realization); Mathlib Hardy gap confirmed

Date: 2026-09-19.

Status: proof record (paper level, hand-derived; the pivotal criteria
quoted verbatim from the primary source re-pinned today).  No uniform
bound is proved and RH is not claimed.  This record executes the "all
three steps" request of 1691 — and step 1's execution immediately
decided the base: **the committed carrier is {0}**.

Primary source (re-pinned this session, verbatim quotes below):
Makarov–Poltoratski, *Meromorphic inner functions, Toeplitz kernels and
the uncertainty principle*, Invent. Math. 180 (2010) 443–480,
arXiv:math/0702497, e-print `MIF2f.TEX` (extracted at
`/home/peter/rh/tmp/mp2010/mif2f.tex`, WSL side; `tmp/` is not
committed — all load-bearing lines are quoted verbatim in this record).

## 1. Verdict

```text
+------------------------------------------------------------------+
| THEOREM D.  For every lambda > 0 the committed symbol            |
|   Theta(xi) = e^{4 pi i (log lambda) xi} m(-xi),                 |
|   m(xi) = Gr(1/2 - 2 pi i xi)/Gr(1/2 + 2 pi i xi),  Gr = Gamma_R,|
| satisfies  N^p[e^{i gamma}] = {0}  for ALL p in (0, infinity],   |
| where gamma = arg Theta.  In particular the committed carrier    |
| (1629 normalization: H in H^2(C_+), Theta H in H^2(C_-)) is      |
| {0} — the carrier witness does NOT exist.                        |
+------------------------------------------------------------------+
```

Front-B's base leg is thereby CLOSED (negatively): the object that
F33 called "a witness input, never a theorem" has now been *decided*,
and the answer is negative.  The tower's WO legs lose their input; the
program's single remaining named open object is the global two-sided
finite-mass statement (the 1680 bone, machine-checkably equivalent to
RH).  Nothing about the gate, qw, or RH is claimed either way.

## 2. The phase facts (inputs)

Committed symbol and phase (1626 pin; 1683 exact formula, FD-verified
1e-13; re-verified today by `mpmath` at 30 dps):

```text
gamma(xi) = 4 pi (log lambda) xi + arg m(-xi)
gamma'(xi) = 4 pi log lambda - 2 pi log pi + 2 pi Re psi(1/4 + pi i xi)
```

Stirling (`psi(z) = log z + O(1/z)`, `Re psi(1/4 + pi i xi) =
log|1/4 + pi i xi| + O(xi^-2)`):

```text
gamma'(xi) = 4 pi log lambda + 2 pi log|xi| + O(xi^-2)      (|xi| -> inf)
gamma(xi)  = 2 pi (xi log xi - xi) + 4 pi (log lambda) xi + O(1)  (xi -> +inf)
```

The continuous branch is pinned by `gamma(0) = 0` (Theta(0) = m(0) = 1)
and `m(-xi) = conj m(xi)` on R, hence

```text
gamma is ODD:  gamma(-xi) = -gamma(xi)          (exact; mpmath diff 0)
```

Consequences used below: `gamma(xi) -> +inf` as `xi -> +inf`
superlinearly (`xi log xi`), `gamma(xi) -> -inf` as `xi -> -inf`, and
for every fixed lambda there is an explicit `X0(lambda)` with

```text
gamma(x) <= -pi |x| log|x|          (x <= -X0),
X0(lambda) = exp(2 + 4 |log lambda|)  up to the O(1) bookkeeping.
```

(For lambda = 0.1 the tail floor
`-2 pi t (log t - 1 + 2 log lambda)` matched the exact phase to 0.78
at t = 10^4 — an O(1) Stirling remainder; fold check: `gamma' = 0` at
`xi = +-lambda^-2`.)  Today's re-check also confirms the phase has TWO
stationary points, `+-xi0 = +-lambda^-2` (`gamma'` is even, `gamma` is
odd): increasing L-tail, decreasing middle, increasing R-tail.  The
1690/1691 fold analysis covered the `+xi0` block; `-xi0` is its odd
mirror.

## 3. The criteria, verbatim (MIF2f.TEX)

Conventions (lines 172–214, verbatim): `T_U : H^2 -> H^2`, `F |-> P_+(U F)`,
`H^2 = H^2(C_+)`, `P_+` the orthogonal projection;
`N[U] = ker T_U`; `N^+[U] = {F in NN^+ cap L^1_loc(R) : Ubar Fbar in NN^+}`;
`N^p[U] = N^+[U] cap L^p(R)`.

**The basic criterion** (the display labelled `basic`, lines 334–338,
verbatim):

> Suppose `gamma: R -> R` is a smooth function.  Then
> `N^+[e^{i gamma}] != 0` if and only if
> `gamma = -alpha + h~`
> for some smooth **increasing** function `alpha` and some
> `h in L^1_Pi`.

**Kolmogorov's estimate**, stated by the same paper immediately after
the criterion as a recalled property of the Hilbert transform
(equation labelled `kol`, verbatim):

> `Pi{|h~| > A} = o(1/A)`,  `A -> infinity`,

where `d Pi(t) = dt/(1+t^2)` is the Poisson measure and `h~` is the
Hilbert transform of `h` (Schwarz integral's boundary imaginary part;
singular integral `h~(x) = (1/pi) v.p. int [1/(x-t) + t/(1+t^2)] h(t) dt`).

## 4. Theorem D — proof

Identify the carrier first.  `H in H^2(C_+)` with `Theta H in
H^2(C_-)` means `P_+(Theta H) = 0`, i.e. `H in ker T_Theta = N[Theta]`;
and `N[Theta] = N^2[Theta] = N^+[Theta] cap H^2` (Smirnov: `H^2 =
NN^+ cap L^2` on both half-plane mirrors).  So it suffices to show
`N^+[e^{i gamma}] = {0}`.

Suppose `N^+[e^{i gamma}] != 0`.  By the basic criterion there are a
smooth increasing `alpha` and `h in L^1_Pi` with

```text
h~ = gamma + alpha.
```

Because `alpha` is increasing, it is bounded on each tail: `alpha(x)
<= alpha(-1) =: c2` for `x <= -1` and `alpha(x) >= alpha(1) =: c1`
for `x >= 1`.  On the left tail, with `gamma(x) <= -pi |x| log|x|`
for `x <= -X0` (Section 2),

```text
h~(x) = gamma(x) + alpha(x) <= -pi |x| log|x| + c2,
```

so for every `A > pi X0 log X0 + |c2|` the sublevel set `{h~ < -A}`
contains the half-line `(-inf, -Y(A)]`, where `Y(A) >= X0` is defined
by `pi Y log Y = A - |c2|`.  Hence

```text
Pi{|h~| > A}  >=  Pi{(-inf, -Y(A)]}
             =   integral_{Y(A)}^inf dt/(1+t^2)
            ~=   1/Y(A)
            =~   pi log A / A        (A -> inf).
```

But `pi log A / A` is NOT `o(1/A)` (ratio `pi log A -> inf`),
contradicting Kolmogorov's estimate.  Therefore
`N^+[e^{i gamma}] = {0}`, and `N^p[e^{i gamma}] = {0}` for all
`0 < p <= infinity` (each `N^p` embeds in `N^+`).  The right tail
gives the same contradiction symmetrically.  Since the tail growth
`2 pi xi log xi` dominates the linear term `4 pi (log lambda) xi` for
every fixed `lambda`, the conclusion is **uniform in lambda > 0`.
∎

The same argument with `gamma` replaced by `-gamma` (where the
increasing tails of `gamma` become decreasing, and the boundedness of
`alpha` switches tails) gives `N^+[e^{-i gamma}] = N^+[Theta-bar] =
{0}`; by the reflection bijection `F(xi) |-> conj F(-xi)` (legal
because `gamma` is odd) the `C_-`-mirror two-sided problem is the same
object as the carrier, so both orientations are dead.  Note this
avoids the epsilon-gap entirely: no `S^epsilon` twist is taken, and
Theorem A(i)-type statements (which hold only for `epsilon > 0`) are
not used.

Non-vacuity contrasts (the emptiness is a theorem about the committed
symbol, not a convention artifact):

```text
+--------------------------------------------------------------+
| test symbol                    | criterion reading | answer  |
+--------------------------------+-------------------+---------+
| m = 1, lambda < 1 (gamma       | alpha = -gamma    | N+ != 0 |
| linear decreasing)             | increasing, h~=0  | (1634's |
|                                |                   | witness)|
| m = 1, lambda > 1 (linear      | alpha impossible  | N+ = 0  |
| increasing)                    | on the tail       | = ker S |
| Blaschke factor b (arg bounded)| alpha = -arg b    | N+ != 0 |
|                                | increasing, h~=0  | (bmo2)  |
| committed m (gamma ~ xi log xi)| alpha impossible  | N+ = 0  |
|                                | (Kolmogorov)      | THEOREM |
+--------------------------------------------------------------+
```

## 5. Law F64 — the Kolmogorov ceiling on the phase

The proof used only: representation + monotone `alpha` + Kolmogorov.
Abstracting:

```text
LAW F64.  If N^+[e^{i gamma}] != 0, then Pi{|gamma| > A} = o(1/A).
```

Proof: `gamma = h~ - alpha`; `alpha` bounded on the tails; for `A`
large the set `{|gamma| > A}` outside a fixed compact is contained in
`{|h~| > A - C}`; the compact part is empty for large `A` since
`gamma` is locally bounded; apply (kol).  ∎

So a Toeplitz kernel can exist only for symbols whose argument is at
most *Kolmogorov-linear* — roughly `Pi`-distributionally `o(A)` in
measure `~ 1/A`, i.e. at most linear tail growth.  The committed
symbol's `xi log xi` phase (and a fortiori any faster growth) is
BANNED.  This is the same obstruction wearing its third hat:

```text
+--------------------------------------------------------------+
| one obstruction, three faces                                 |
+--------------------------------------------------------------+
| factorization face  | Theta = J S-bar^a with J meromorphic    |
|                     | inner: DEAD (F51 pole/zero certificate)|
| construction face   | p = 2 Hardy clause needs alpha = arg    |
|                     | of an inner function: DEAD (same poles) |
| necessity face      |Law F64: superlinear phase => N+ = {0}:  |
|                     | DECIDES the base negatively (this wave) |
+--------------------------------------------------------------+
```

**Law F65 (necessity-first audit).**  The 1631/1632 inventory priced
every tool by its *sufficiency* face ("can it construct a kernel at
p = 2?"); the p = 2 clause died with F51 and the whole family was
relegated.  But a criterion's *necessity* direction carries no class
hypotheses by construction — it is a decision tool, and here it
decides the single point of failure in five lines.  Standing rule:
before pricing a criterion "out of class", audit both faces
separately.

## 6. Consistency audit (all committed measurements agree)

```text
+--------------------------------------------------------------+
| committed fact                        | reading under Thm D  |
+---------------------------------------+----------------------+
| 1630 Toeplitz probe: sigma_min > 0    | 0 in the spectrum,   |
| at every section, decaying in lambda  | no kernel vector;    |
|                                       | approximable, never  |
|                                       | attained             |
| 1633: m(-xi) reads BELOW the          | the free shift has a |
| free-shift floor (focusing)           | kernel, the true     |
|                                       | symbol does not      |
| 1632: D_real/D_model -> 0.080 < 1     | real defect strictly |
|                                       | below the shift model|
| 1691 Thm C: fold block injective      | local echo of the    |
|                                       | global emptiness     |
| F63: no atom, continuous concen-      | empty kernel => no   |
| tration, no gap at 0                  | Clark-type atoms     |
| 1683 surrogate atom density -> 1      | inner-model artifact |
|                                       | (the 1682 trap law)  |
| 1684 ob-2b = Thm B (race)             | approximate face     |
|                                       | unchanged; the exact |
|                                       | face is now decided  |
| m = 1 model nontrivial (1634)         | linear phase; the    |
|                                       | emptiness is the     |
|                                       | Gamma-ratio's fault  |
+--------------------------------------------------------------+
```

No committed record asserted carrier nonemptiness; nothing needs
retraction.  Re-pricings only.

## 7. Consequences

```text
+------------------------------------------------------------------+
| object                          | status after today             |
+---------------------------------+--------------------------------+
| 1634 O1 (one-sided convolution  | CLOSED, negative: no h != 0 in |
| vanishing: carrier != 0)        | L^2(-inf,0] has K*h vanishing  |
|                                 | on (-inf, c)                   |
| F33 carrier witness input       | RESOLVED: the witness does not |
|                                 | exist (was: never a theorem)   |
| front-B base leg                | DEAD: the WO legs have no      |
|                                 | input object                   |
| Laguerre finite-section program | re-scoped: obligation 2's      |
| (1640)                          | defect -> 0 is the Thm B race  |
|                                 | (approximate solvability of an |
|                                 | EMPTY limit problem); as a     |
|                                 | carrier construction it is     |
|                                 | void; survives only as race/   |
|                                 | finite-section hygiene         |
| barrier table (1691 sec 3)      | the fold-split lane's KERNEL   |
|                                 | face is moot (decided); its    |
|                                 | live residue is the MASS face  |
| named open objects              | exactly ONE: the global        |
|                                 | two-sided finite-mass statement|
|                                 | = the 1680 bone = the gate     |
|                                 | <=> RH (1680 iff, no slack)    |
+------------------------------------------------------------------+
```

What Theorem D does NOT do: it says nothing about `qw`, the gate, or
RH; it does not produce the uniform annular bound; it closes a
*witness-input* question and thereby simplifies the map (map 044 owes
a redraw with front B removed: one lane, the bound).

## 8. Lane 1 — the fold-split branch dictionary (paper level)

With the verbatim BM machinery now pinned, the branch picture can be
stated exactly.  Orientation: MP's definitions run on phases with
`gamma(-inf) = +inf`, `gamma(+inf) = -inf` (decreasing); use
`Psi := -gamma`.  Then (Section 2 facts):

```text
Psi(-inf) = +inf,  Psi(+inf) = -inf            (BM( Psi) defined)
BM(Psi) = components of {x : Psi(x) != max_[x,inf) Psi}
        = {x : gamma(x) != min_[x,inf) gamma}
        = (-inf, xi0) u (xi0, inf)             (xi0 = lambda^-2;
                                                 xi0 itself is excluded)
```

The two intervals: the left one contains 0, so `d(l) = 0` (excluded
from every shortness sum); the right one has `d = xi0 >= 1` (for
`lambda <= 1`) and INFINITE length, so `d^{kappa-2} l^2 = inf`: the
shortness sum DIVERGES — `Psi` is not `(kappa)`-almost-decreasing for
any `kappa >= 0`; `BM(Psi)` is LONG.  (This refines 1630's Thm 8.5
audit, which examined a globally decreasing branch problem where the
sum was vacuous; on the FULL committed phase the family is long, so
Thm A(i)-type triviality is consistent with Theorem D — but Theorem D
is stronger: it needs no `kappa`, no twist, and no `epsilon`.)

The exact branch statements (what "branch completeness" says now):

```text
+------------------------------------------------------------------+
| branch          | kernel face                     | mass face    |
+-----------------+---------------------------------+--------------+
| L-tail, R-tail  | increasing argument: the side   | the tails are|
| (gamma incr.)   | that KILLS: F64 bans their      | where the    |
|                 | superlinear growth; no branch   | concentration|
|                 | kernel can exist                | mass must be |
|                 |                                 | FINITE (open)|
| M-middle        | d = 0 decreasing-argument       | surrogate    |
| (gamma decr.,   | problem on a FINITE interval,   | density-1    |
| finite dip      | BM-data = the single finite dip | object of    |
| Delta = -2      | Delta gamma; vacuous shortness  | 1683; atoms  |
| gamma(xi0))     | (1630's audit applies verbatim) | refuted (F63,|
|                 |                                 | Thm D)       |
| glue at +-xi0   | Thm A (normal form) + Thm B     | the fold's   |
|                 | (race) + Thm C (injectivity):   | continuous   |
|                 | the glue is COMPLETELY          | concentration|
|                 | described (1690/1691)           | is the whole |
|                 |                                 | game         |
+------------------------------------------------------------------+
```

So the fold-split lane's promised "branch-completeness -> mass
transfer" survives only as the mass face — and on the kernel face the
branch bookkeeping is moot, because Theorem D decides globally what
the branches could only have suggested locally.

## 9. Lane 2 — the canonical-system transfer is VOID (explicit W/W~)

The localization layer's residual gap ("true-measure AC on smooth
branches") had one named tool: lift the surrogate to a canonical
system via the MP dictionary.  The committed symbol has no such
realization.  First the new positive structure — an explicit entire
factorization.  With `Theta(z) = e^{2 pi i z (2 log lambda - log pi)}
Gamma(1/4 + pi i z)/Gamma(1/4 - pi i z)`:

```text
W(z)  := 1 / [ Gamma(1/4 + pi i z) Gamma(1/4 - pi i z) ]
W~(z) := e^{2 pi i z (2 log lambda - log pi)} / Gamma(1/4 - pi i z)^2

Theta = W~/W,   W, W~ ENTIRE,   W real on R and STRICTLY POSITIVE:
W(xi) = 1/|Gamma(1/4 + pi i xi)|^2 > 0,
W~(xi) = W(xi) e^{i gamma(xi)}   (|W~| = W on R),
zeros of W at +-i(n + 1/4)/pi, growth W(z) ~ e^{pi^2 y}|pi x|^{1/2}/(2 pi)
in C_+.
```

(`Gamma(1/4 +- pi i z)` are entire in `z` — the zeros of `1/Gamma` —
so both factors are entire; the `pi`-power bookkeeping: `Gr(1/2 + 2 pi
i z) = pi^{-1/4 - pi i z} Gamma(1/4 + pi i z)`.)  This is the exact
object behind the F51 certificate: the pole set
`{i(n + 1/4)/pi}` of `Theta` in `C_+` is the zero set of `W`.

Now the negative theorem:

```text
NO de Branges realization.  Every canonical-system symbol in the
MP/Toeplitz-kernel dictionary has the form E^#/E with E entire
(regular Hamiltonians) or meromorphic (singular Hamiltonians) and the
Hermite-Biehler sign Im(A conj B) of fixed sign on C_+ (E = A - iB,
A, B real); in either case the symbol is (meromorphic) INNER in C_+.
The committed Theta is not: it has poles in C_+ at i(n+1/4)/pi
(unbounded there) while DECAYING on the imaginary axis
(log|Theta(iy)| = 4 pi |log lambda| y - 2 pi y log y + O(y) -> -inf).
A function that both blows up (at interior points) and decays (along
the axis) admits no HB sign.  Hence gamma is the phase function of NO
canonical system, regular or singular.
```

Consequence for the ledger: the canonical-system transfer tool is
VOID for the committed symbol (same obstruction as F51/F40/1681, now
structural).  The localization residual gap must be attacked directly
on the 1682 trace functional `phi |-> tr(P0 M_phi P0)` — which exists
unconditionally — not via a spectral measure of a system that does
not exist.  The W/W~ factorization remains useful: it is the exact
entire-quotient presentation of the symbol and pins the zero/pole
geometry that any future tool must respect.

## 10. Lane 3 — Mathlib verdict (grep evidence)

WSL Mathlib tree (`/home/peter/rh/.lake/packages/mathlib/`, current):

```text
grep -rln 'Hardy' Mathlib/   -> only Algebra/ContinuedFractions/*
                                (name collisions, no Hardy space)
grep -rln -i 'privalov'      -> no matches
ls Mathlib/Analysis | grep -i -e hardy -e bergman -e smirnov
                             -> no matches
```

Verdict: Mathlib has NO half-plane Hardy-space framework and NO
boundary-uniqueness (Privalov/F.&M. Riesz) lemma.  The 1691 anchor
brick (`C1G9R1ChirpFoldAnchor`: exact shear identity +
frequency-ray vanishing, machine-checked at L^1) is the right
stopping point; the L^2 upgrade waits on an upstream framework and is
NOT retried blind.  (F64/Theorem D are paper-level: their inputs are
the published criterion + Kolmogorov estimate, quoted verbatim above;
no Lean brick is attempted this wave.)

## 11. Boundary

No uniform annular bound, no gate, no RH — the bone is, by the
machine-checked 1680 iff, exactly the endpoint gate, and completing it
IS proving RH.  Completed today: the carrier's exact face DECIDED
(negative, Theorem D, uniform in lambda), laws F64/F65, the
fold-split branch dictionary with the kernel face closed, the
canonical-system transfer ruled out with the explicit W/W~ factorization
pinned, and the Mathlib gap documented.  The single named open object
is unchanged and irreducible: the global two-sided finite-mass
statement.  RH is not claimed.
