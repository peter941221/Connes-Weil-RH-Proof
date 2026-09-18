# 1627 — The entire-`W` obligation: the elementary L² face, one proved obstruction, and two corrections

Date: 2026-09-18.

Status: route record (derivations + corrections). No Lean brick this round; the
1626 scale-monotonicity brick stands. The carrier base, T4, B4, S3 and RH stay
OPEN. RH is not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)).

## 1. The elementary L² face of the obligation (no H² layer needed)

With the conventions of [1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md)/[1626](1626_infrastructure_verdict_toeplitz_form_and_scale_monotonicity.md)
re-verified on `f(t) = e^{-t}1_{t>0}` (`Ff = 1/(1+2*pi*I*xi)`, pole in `C_+`):

```text
F(H^2(C_+)) = {FT supported on xi >= 0},   F(H^2(C_-)) = {FT supported on xi <= 0}.
```

Applying `F` to `(T)` (`EXISTS phi != 0, phi in H^2(C_+), m*phi in H^2(C_-)`,
1626 section 3) and writing `g := F phi` gives the *elementary* form

```text
(T')  EXISTS g != 0 in L2(R):   supp g subset [0, inf)   AND
                                supp (U_m g) subset (-inf, 0],
```

because `F(M_m phi) = (F M_m F^{-1})(F phi) = U_m g` with `U_m = F M_m F^{-1}`
the multiplier conjugate of [1622](1622_multiplier_conjugate_factorization_and_1621_erratum.md)
(committed in `Dev/SoninCarrierMultiplierConjugate.lean`). Using
`H = R ∘L U_m` and `supp (R w) subset [a,inf) <=> supp w subset (-inf,-a]`,
form `(T')` is exactly `V_arch(1) != {0}`, i.e. the carrier at `lambda = 1`:

```text
supp g subset [0, inf) and supp (U_m g) subset (-inf, 0]
   <=>  g in Radial(1) and H g in Radial(1).
```

So the carrier base has a face — `(T')` — stated entirely in the tree's
committed vocabulary (`Radial`, `H`, `U_m`), with no `H^2`/PW layer and no
analytic continuation. This *does not* make it easier: it makes it a question
about one Fourier-multiplier operator and two half-line supports.

## 2. Obstruction: no witness of finite exponential type

Claim: if an entire `W` satisfies the de Branges-pattern obligations of 1626
section 3, `W/A in H^2(C_+)` and `W/B in H^2(C_-)`, then `W` has **infinite
exponential type**. Proof in two steps.

```text
step 1 (pointwise exponential decay on R).
  |A(x)| = pi^{-1/4} |Gamma(1/4 - pi I x)| ~ (pi|x|)^{-1/4} e^{-pi^2 |x|/2}
  (Stirling, sigma = 1/4, T = -pi x).  W/A in H^2(C_+) gives boundary L2:
  INT |W|^2 rho^{-2} < inf with rho := |A|.  For |x| >= 2 and |t| in [|x|-1,|x|+1]
  one has rho(t)^2 <= rho(|x|-1)^2 (rho decreasing for t > 0), hence
  INT_{x-1}^{x+1} |W|^2 <= rho(|x|-1)^2 * C.
  Subharmonicity of |W|^2 at (x,0) with radius 1 and the line conditions at
  heights |s| <= 1 (weight (pi|t|)^{-2 pi s} <= 1 for |t| >= 1) give
      |W(x)|^2 <= (1/pi) INT_{B((x,0),1)} |W|^2
               <= rho(|x|-1)^2 * C * (pi (|x|+1))^{2 pi},
  i.e. |W(x)| <= C' e^{-pi^2 |x|/2} |x|^{pi - 1/4}: exponential decay.

step 2 (finite type + exponential decay on R => W = 0).
  W entire of exponential type tau with W|_R in L2 has, by Paley-Wiener,
  F W in L2 with COMPACT support in [-tau/2pi, tau/2pi].  Exponential decay
  |W(x)| <= C e^{-c|x|} with c = pi^2/2 > 0 makes F W analytic in the strip
  |Im xi| < c/(2 pi).  Compact support + analytic in a nonempty strip => F W = 0
  => W = 0.
```

Consequences:

- **Every band-limited / Paley–Wiener / finite-type candidate is excluded.**
  In particular no witness can be built from finite sums of exponentials, from
  the classical `H^2(C_+)` entire witnesses of 1626 section 6 (they have finite
  exponential type), or from any de Branges function of finite type.
- The witness must be of **infinite exponential type** (order `>= 2`, or order
  1 with infinite type). This matches the only candidate family currently on
  the table: products of two Weil/`Gamma` factors (1590), since
  `Gamma(1/4 - pi I z)` is already order-1 of infinite type (along the
  imaginary axis it grows like a factorial).
- Combining with section 1: `(T')` needs a *non-band-limited* `g` as well —
  if `g` were compactly supported then `F phi`... (that route is not the same
  statement; the obstruction above is about `W`, not `g`).

## 3. Correction 1 (to 1624): the carrier is a conjunction, and its scale dependence is real

1624 section 2 concluded that the threshold enters "only through a unimodular
modulation `e^{2 pi I c xi}`, which is absorbed by translating the vector", and
that therefore "the carrier base is exactly record 1003's `ker(T_m) != {0}`",
i.e. WO-B's producer premise and the carrier base are "one analytic object".
The modulation reading is correct for **one** condition on a fixed vector, and
it is correct for the B4 certificate (which is the single condition
`H v in Radial(lambda'')` on the committed column `v`). It does **not** lift to
the carrier, which is a **conjunction** of two conditions on the same vector:

```text
V_arch(lambda) != {0}   <=>   EXISTS g != 0:
    supp g subset [log lambda, inf)   AND   supp (U_m g) subset (-inf, -log lambda].
```

A single translation `T_c g = g(. + c)` moves the two half-lines in the *same*
direction (both endpoints shift by `c`), while the carrier's two levels must
move in *opposite* directions (`log lambda -> log lambda - c` on the left and
`-log lambda -> -log lambda - c` on the right). Concretely, in the model
`m = 1` (`U_m = id`) the two conditions read `supp g subset [a, inf)` and
`supp g subset (-inf, -a]` with `a = log lambda`, so

```text
V_arch(lambda) = {g : supp g subset [log lambda, -log lambda]}  (m = 1),
```

which is `{0}` exactly for `lambda >= 1` and nonzero for every `lambda < 1`.
So `V_arch` is **not** scale-independent, and one must not read the threshold
as pure modulation. (This is consistent with the 1626 monotonicity brick:
`V_arch(lambda') <= V_arch(lambda)` for `lambda <= lambda'`, with strict loss.)

Consequence for the route: **the B4 premise (a property of one committed
column) and the carrier base (an existence over all vectors) are adjacent but
distinct statements sharing the multiplier**; the "unification" headline of
1624 section 4 is withdrawn in its equivalence form. What survives: both are
Toeplitz-type conditions for the same symbol `m`, and a witness for the carrier
does produce a kernel element for the modulated symbol.

## 4. Correction 2 (erratum on a derivation drafted in this round): the `A B` product

While looking for a closed form, the identity

```text
A(z) B(z) = pi^{1/2} / sin(pi/4 - pi^2 I z)        (WRONG)
```

was drafted from the reflection formula for `Gamma`. It is **false**: at
`s = 1/2` it would give `Gamma_R(1/2)^2 = sqrt(2 pi) = 2.5066`, while

```text
Gamma_R(1/2) = pi^{-1/4} Gamma(1/4) = 3.625609908 / 1.331335363 = 2.723248,
Gamma_R(1/2)^2 = 7.4163      (both factors verified to 5 digits).
```

The slip: the product `Gamma_R(s) Gamma_R(1-s)` has `Gamma`-arguments `s/2` and
`(1-s)/2`, and `(1-s)/2 != 1 - s/2` in general, so no single reflection step
applies. The correct exact statements:

```text
A(z) B(z) = pi^{-1/2} Gamma(1/4 - pi I z) Gamma(1/4 + pi I z)      (exact, elementary)

1/(A B)  is ENTIRE, with zeros exactly at the poles of A and B,
         i.e. at +/- I (4k+1)/(4 pi), k >= 0                          (1/Gamma entire)

the correct reflection shape (other direction, verified at s = 1/2):
Gamma_R(s) Gamma_R(-s) = -2 pi / (s sin(pi s / 2)),
  check: Gamma_R(1/2) Gamma_R(-1/2) = 2.723248 * (-6.525616) = -17.771,
         -2 pi / (0.5 * sin(pi/4)) = -17.771   (agrees to 5 digits).
```

The entire function `pi^{1/2}/(Gamma(1/4-pi I z)Gamma(1/4 + pi I z))` is the
"product of two Weil factors" object named in 1590 — and it is **too large**:
`(1/(A B))/A` has modulus `rho^{-3}` on `R`, which grows like `e^{3 pi^2 |x|/2}`
and is not in `L^2`. So this natural candidate fails, consistent with the
finite-type obstruction of section 2 (this one is infinite type but fails the
line-norm bounds on the other side).

## 5. Makarov–Poltoratski status (item N1 of the round)

The applicable criterion is the MP injectivity theorem for unimodular
real-analytic symbols, formulated via **uniqueness sets for model spaces**
(Blaschke sets): literature quoted in 1626 section 4 (arXiv:1711.04511 section
2.3; arXiv:1511.08326). The *precise statement* of the criterion (the explicit
condition on the argument `gamma`) was not obtained this round — the survey
[1511.08326](https://arxiv.org/abs/1511.08326) states the structural results
(Hitt/Hayashi: `ker T_phi = g K_I`; Dyakonov: `ker T_psi = g b^{-1}(K_B INTER bH^2)`;
Hartmann–Sarason–Seip surjectivity) but the MP condition itself is in the
original 2005 paper, which was not retrieved. Status: pointer held, criterion
not explicitized.

## 6. Verdict and boundaries

- `(T')` is the cheapest *statement* of the carrier base known so far, and it
  needs no new layer.
- The finite-type obstruction is a genuine narrowing: the witness must be an
  infinite-type entire function. It does not decide `(T')`.
- Two corrections are filed: the carrier is scale-dependent and is a
  conjunction (1624's unification withdrawn in equivalence form); the drafted
  `A B` closed form is false, with the correct elementary forms recorded.
- The carrier base, T4, B4, S3, `EndpointMass(eps)`, T1, (star), `rho5`,
  R4/(OB)/W1 and RH are unchanged and open. No gap premise, `SourceRH`, or
  universal gate is introduced.

## 7. Acceptance

No build this round (no new Lean). The standing brick is 1626's
`Dev/SoninScaleMonotonicity.lean`, accepted at
`build-logs/sonin_scale_monotonicity2.log` (3319 jobs, zero `error:`, zero
`sorryAx`, five standard axiom prints).