# 1628 — The MP criterion's real form (shortness / BM density), the B4 single-column scalar form, the window transport brick, and a ledger erratum

Date: 2026-09-18.

Status: one accepted Lean brick (window transport, section 4) + route records
(sections 1–3, 5). The carrier base stays OPEN; the MP criterion is *located*
and its hypotheses audited but not satisfied by our symbol; RH is not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)).

## 1. The Makarov–Poltoratski criterion in its real form (item N5)

1626/1627 could only point at "the MP criterion for unimodular real-analytic
symbols; uniqueness sets for model spaces". The literature gate is now open,
and the criterion's actual shape is **not** a winding number and not a
uniqueness-set count: it is a **shortness condition on a set `Sigma(gamma)`
built from the argument**, with a Beurling–Malliavin-density reformulation.
Exact quotes (A. Hartmann, M. Mitkovski, "Kernels of Toeplitz operators",
<https://arxiv.org/abs/1511.08326>, section 8):

```text
failure of the shortness condition (eq. 8.3):
   SUM_n |I_n|^2 / (1 + dist(0, I_n)^2) = infinity

Theorem 8.4 ("little multiplier theorem", Makarov-Poltoratski):
  gamma real-analytic, of bounded variation, gamma' bounded from below.
  (i)  if Sigma(gamma) does NOT satisfy shortness, then for every eps > 0,
       gamma(x) + eps*x cannot be written as d + h~ (d decreasing, h in L^1(dPi));
  (ii) if Sigma(gamma) DOES satisfy shortness, then for every eps > 0,
       gamma(x) - eps*x can be written as d + h~.

Smirnov-Nevanlinna form: for U = e^(I*gamma),
  Ker^+ T_U = {0}  <=>  gamma = d + h~.

completeness/threshold form (section 8, BM density):
  inf{ a >= 0 : Ker T_{conj(S)^a Theta} != {0} } = D^+_BM(Lambda),
  the exterior Beurling-Malliavin density of the node sequence Lambda.
```

**Our symbol's class.** `m = A/B` is meromorphic on `C` with `|m| = 1` on `R`,
i.e. a **meromorphic inner function** — literally the class of MP's own title
("Meromorphic inner functions, Toeplitz kernels and the uncertainty
principle", Perspectives in Analysis, 2005; the paper itself was not
retrieved). The exact phase asymptotics, hand-derived from Stirling
(`arg Gamma(1/4 + I T) = -pi/8 + T log T - T + O(1/T)`, `T = pi*xi`) and now
carried to two terms:

```text
gamma(xi) = 2*pi*xi*log(pi) - 2*arg Gamma(1/4 + pi*I*xi)
          = -2*pi*xi*log|xi| + 2*pi*xi + (pi/4)*sgn(xi) + O(1/|xi|),
gamma'(xi) = -2*pi*log|xi| + O(1/|xi|)        (oddness of gamma is exact).
```

**Hypothesis audit — the criterion as quoted does NOT apply.** `gamma'` is
unbounded below (`-> -infinity`), so "`gamma'` bounded from below" fails;
`gamma` is unbounded, so "of bounded variation" fails too. The surveyed
polynomial-growth extension relaxes `|psi'| <= |x|^kappa`, which logarithmic
growth would satisfy, but not the unboundedness of `gamma` itself. So the
applicable frame is the **node-sequence / BM-density** form, and the honest
consequence is a redirection rather than a criterion met:

```text
node sequence  Lambda(m) = { xi : gamma(xi) in pi*Z },
counting       n(R) ~ 2|gamma(R)|/pi ~ 4*R*log R   (super-linear: spacing
               ~ 1/(2 log R) at height R),
threshold      the admissible scales of the carrier base should be
               { lambda : -log lambda > D^+_BM(Lambda(m)) }
               (normalization NOT verified; see caveats).
```

Both branches carry route meaning, and they point in opposite directions:

```text
+----------------------------------------+------------------------------------------------+
| D^+_BM(Lambda(m)) small (e.g. 0)       | kernel nontrivial for every positive shift:     |
|                                        | carrier nonempty at every lambda below the     |
|                                        | critical scale -> the base holds at the source |
| D^+_BM(Lambda(m)) large / infinite     | kernel trivial at every finite shift: the       |
|                                        | carrier is EMPTY at every scale -> the WO       |
|                                        | legs' base fails and the decomposition must be |
|                                        | revised                                        |
+----------------------------------------+------------------------------------------------+
```

This is a *single number* deciding the WO base. Caveats (explicit): the
mapping between the survey's `conj(S)^a Theta` picture and the tree's
scale `lambda` (equivalently the modulation `e^{2 pi I c xi}`, `c = log
lambda`) is not verified; `Sigma(gamma)` and the intervals `I_n` of 8.2/8.3
were not retrieved (only the failure form 8.3); the direction of the
threshold in the tree's normalization is inferred from the `m = 1` model
(`Lambda = empty`, density 0, `V_arch(lambda) != {0}` exactly for
`lambda < 1`, matching "kernel appears above the density" under
`a <-> -log lambda`). The 1626 scale-monotonicity brick is exactly the
qualitative shadow of this threshold theorem.

## 2. The infinite-type class has no constructive handle yet (item N6)

Two additions to 1627's finite-type obstruction, one independent and one
negative.

**Independent confirmation (Krasichkov–Tumarkin).** The classical criterion
for the existence of a nonzero entire function of exponential type `tau` with
`|f(x)| <= M(x)` on `R` is `INT (log M(x) - tau*|x|)/(1 + x^2) dx > -inf`.
For our obligation the real-axis ceiling is the profile `rho(x) ~
e^{-pi^2 |x|/2}` (1627 section 2, corrected in section 5 below), so for every
finite `tau` the integrand is `~ -(pi^2/2 + tau)|x|` and the integral is
`-infinity`: no finite-type witness exists. This reproduces 1627 section 2's
Paley–Wiener proof by a criterion that does not use the second half-plane
condition at all.

**Negative.** The only infinite-type objects on the table — reciprocal Gamma
products such as `1/(A B)` (the "product of two Weil factors" of record 1590)
— all fail the line-norm bounds (1627 section 4: `(1/(A B))/A` has modulus
`rho^{-3}` on `R`). No construction of an infinite-type witness is available,
and the criterion-level attack (section 1) is the only live lever: this is the
same conclusion as 1626 section 4's withdrawal of the cheap test, now with the
criterion actually in hand.

## 3. B4: the premise in single-column scalar form, and why support algebra cannot deliver it (item N4/B4)

**Committed content (quoted).** `Dev/C1G8R3StripConfinement.lean` header
(record 1575 section 3.3): for every operator `M` whose columns are supported
on the wider half-line, the radial defect is confined to the finite strip,
`(1 - E_lambda) M = (E_{lambda''} - E_lambda) M`, and "the consumer-facing
corollary is the signed B4 form of record 1599: under the Hardy wide-support
certificate `E_{lambda''} H M J = H M J`, the defect of the Hardy column is
exactly the finite strip projection, so the reflected half-line tail is a
finite-strip object and not an unbounded remainder." So the *consequence* of
B4's premise is committed and decidable; the premise itself is what is open.

**Scalar form of the premise.** With `v` the committed column and
`psi := F^{-1} v`, B4's premise is `H v in Radial(lambda'')`. By 1622's
`U_m u = R (H u)` this is `U_m v` supported in `(-inf, -log lambda'']`; by the
dictionary of 1626 section 2 (`supp w subset (-inf, c] <=> e^{2 pi I c xi}
(F w) in H^2(C_+)`) and `F(U_m v) = (m * psi)(-.)` this becomes

```text
(B4-scalar)   xi |-> e^{2 pi I (log lambda'') xi} * m(xi) * psi(xi)  in  H^2(C_+),
```

a **single explicit H²-membership condition for one explicit function** — the
same shape as 1624's certificate, but now stated per column. It is decidable
for each committed column once `psi = F^{-1} v` is written out (deferred: no
rig this round; the committed columns are built from Euler factors and
indicator windows, so `psi` is explicit in principle).

**Why support algebra cannot deliver it.** The kernel `K = F^{-1}(m)` has
`m` analytic in `C_+` with poles only in `C_-`; the analytic-continuation
dictionary therefore places `K` on the half-line `[0, inf)` (with the growth
caveat: `|m| ~ |x|^{2 pi y}` is not uniformly polynomial in `C_+`, so `K` is
at best an infinite-order / hyperfunction object). Then

```text
U_m v(t) = INT v(s) K(t + s) ds,     supp K subset [0, inf)
   ==> supp (U_m v) subset [ -sup supp v, inf ):   the LOWER support edge of
       U_m v is controlled by the UPPER support edge of v.
```

B4's premise is a *lower* vanishing condition, so no support hypothesis on `v`
can force it: like the carrier base, it is a **cancellation** statement, and it
shares the multiplier's model-space entry. This closes the "B4 might be paid
by support algebra" hope (the committed confinement already extracts
everything support algebra gives) and redirects B4 to the per-column scalar
form above.

## 4. The transport brick (item N4)

`ConnesWeilRH/Dev/SoninWindowTransport.lean` + audit, four declarations, no
`sorry`, standard axioms only:

```text
+------------------------------------------+------------------------------------------------+
| declaration                              | content                                        |
+------------------------------------------+------------------------------------------------+
| IsWindowWitness T u                      | u != 0, u and H u vanish outside (-T, T)        |
| mem_radialSupport_of_window              | log lambda <= -T  ==>  u in Radial(lambda)      |
| mem_fourierSupport_of_window             | log lambda <= -T  ==>  u in FourierSupport(lambda)|
| carrier_nontrivial_of_window_witness     | any window witness witnesses the carrier at     |
|                                          | every scale lambda <= exp(-T)                   |
+------------------------------------------+------------------------------------------------+
```

Meaning: the committed carrier is the **one-sided relaxation** of any
bounded-window (two-sided) Sonin problem — a window witness transports into
the tree for free, and (1626) spreads downward in `lambda`. This is the
direction of the 1623 mismatch made formal: the tree's obligation is *weaker*
than CCM's two-sided existence. It is not a step toward solving the base: the
proof uses only the window's lower edge, and no window witness is constructed
(law F33).

## 5. Erratum (numerically confirmed): the line-growth ledger carried spurious pi factors

The line profiles recorded in 1626 section 2 and used in 1627 section 2 were

```text
|m(x + I y)| ~ (pi*x)^{2 pi y},      |A(x + I y)| ~ rho(x) * (pi|x|)^{pi y}      (WRONG constants)
```

The `pi^{-s/2}` prefactor of `Gamma_R(s) = pi^{-s/2} Gamma(s/2)` contributes
`pi^{-pi y}`, which *cancels* the `pi^{pi y}` inside Stirling's
`(pi|T|)^{sigma - 1/2}`. The correct profiles are clean:

```text
|A(x + I y)| ~ sqrt(2) * |x|^{pi y - 1/4} * e^{-pi^2 |x| / 2},
|m(x + I y)| ~ |x|^{2 pi y},        rho(x) = |A(x)| ~ sqrt(2) |x|^{-1/4} e^{-pi^2 |x|/2}.
```

Numerical check (mpmath, `m = pi^{2 pi I xi} Gamma(1/4 - pi I xi) / Gamma(1/4 + pi I xi)`):

```text
|x|, y = 5, 0.3:      |m| = 20.796183      |x|^{2 pi y} = 20.774349   (0.1%)
                                          (pi|x|)^{2 pi y} = 179.73508  (8.6 x off)
|A(5)| direct = 1.8196985e-11    sqrt(2)*5^{-1/4}*e^{-pi^2*5/2} = 1.8196408e-11   (7 digits)
                                 with an extra pi^{-1/4}:       1.3667787e-11     (wrong)
```

Cross-check by hand: `|m| = |A(x+I y)|/|A(-x-I y)| = |x|^{pi y} rho / (|x|^{-pi y} rho) =
|x|^{2 pi y}` agrees, and Cauchy–Riemann gives `Re gamma'(x) = d/dy Im gamma(x+I y) =
-2 pi log|x|`, matching the Stirling derivative above. No qualitative conclusion of
1626/1627 changes (the exponential rate `e^{-pi^2 |x|/2}` and the polynomial order
are unaffected); the "neutral" line of the ledger moves from `|x| ~ 1/pi` to
`|x| ~ 1`, and the corrected formulas are cleaner. Law F39 filed.

## 6. Verdict and boundaries

- N5: criterion located, its real form quoted, our symbol's membership in the
  class confirmed, hypotheses **audited and found violated** as stated, and the
  obligation redirected to a single computable number (`D^+_BM` of the node
  sequence). Not settled; no verdict on the kernel.
- N6: independent confirmation of the finite-type obstruction; no constructive
  handle on the infinite-type class.
- B4: premise reduced to a per-column scalar H² condition; support algebra
  proved insufficient (cancellation, not support).
- N4: transport brick landed (this round's Lean).
- Erratum: ledger constants corrected and verified numerically.
- Carrier base, T4, B4, S3, WO-S, WO-B, `EndpointMass(eps)`, T1, (star), `rho5`,
  R4/(OB)/W1 and RH are unchanged and open. No gap premise, `SourceRH`, or
  universal gate is introduced.

## 7. Acceptance

Build log: `build-logs/sonin_window_transport.log`.
`Build completed successfully (3319 jobs)`; zero `error:` lines; zero
`sorryAx`; the three axiom prints (`mem_radialSupport_of_window`,
`mem_fourierSupport_of_window`, `carrier_nontrivial_of_window_witness`) all
resolve to exactly `[propext, Classical.choice, Quot.sound]`; no warning in
either new module. The 1626 monotonicity brick remains the standing accepted
module.