# Proof-717 transport-radial estimate: what the wall `(I-R)∘T†∘R` really is, and what a bound needs

Date: 2026-08-06
Status: math design notes — the missing analytic object, made concrete enough to
judge and (later) formalize or falsify. Not a Lean change.
Branch: `proof/gate3u-completed-readout`
RELATED: `811_route1_quantitative_closure.md`, `810_strong_route_index_survey.md`

## 1. Setup (all on the common logarithmic carrier `t = log λ`)

Let `H = cc20GlobalLogCrossingL2 = L²(ℝ, dt)` be the ambient space. Let

```
R   = radial-support (Sonin) projection:  (R f)(t) = f(t)·1_{t ≥ log λ}
S   = I − R                             :  (S f)(t) = f(t)·1_{t <  log λ}
```

Precisely `R f` is the star-projection onto
`{f : H | ∀ᵐ t, t < log λ → f(t) = 0}` (`CCM24LogRadialSupport.lean:48-58`).

The finite Euler transport is the ordered product over visible primes

```
T  = ∏_{p ∈ S} ( I − p^(−1/2) U_{log p} ),   (U_a f)(t) = f(t + a)
T† = ∏_{p ∈ S} ( I − p^(−1/2) U_{−log p} )  (each factor self-ish: U_a† = U_{−a})
```

The outer metric leakage is `M = T†∘D` with `D` the (radial, `R∘D = D`) dual
frame. Wall (open) operator = `W =  S ∘ T† ∘ R`.

## 2. Why `W ≠ 0` is real (mechanically)

Take a radial input `f = R f`, supported on `[logλ,∞)`. Apply one prime factor of
`T†`:

```
(I − p^(−1/2) U_{−log p}) f  (t) = f(t) − p^(−1/2) f(t + log p)
```

- Term `f(t)`: support `[logλ,∞)` — stays in `range(R)`, no `S` output.
- Term `−p^(−1/2) f(t+log p)`: shifts left by `log p`; its support is
  `[logλ − log p, ∞)`, which protrudes below `logλ` into the `S` region.

So `S(T† f)` collects `−p^(−1/2) f(t+log p)` on the strip
`t ∈ [logλ − log p, log λ)`. This is not zero unless `f` vanishes on that strip.
For a genuinely oscillatory/low-frequency radial `f`, that strip mass is
non-trivial. **This is exactly the off-Sonin defect**: T† drags radial mass from
just above `log λ` down past it.

## 3. What a closing estimate must control

Proposition (target): there is `C(λ,f-amplitude) ≤ 1` such that

```
‖ (I−R) ∘ T† ∘ R ‖ ≤ C(λ)   (operator norm on L²(space))
```

Needed to close Gate: `‖W‖` small enough that
`RightEnergy ≤ ‖leakage‖²·(fixedMajorant) ≤ majorant`.

### Decomposition of the wall across prime depth

For one prime this is a rank-one strip. Collapsing the product: expand `T†` as a
free (commuting) product of the `I − p^(−1/2) U_{−log p}`. Each

```
(I − p^(−1/2) U_{−log p}) f  =  f − p^(−1/2) U_{−log p} f ,
```

and the strip leakage from a single shift `−log p` is controlled by the
`L²(logλ−logp, logλ)` norm of `f`, i.e. the **tail of `f` in a `log p`-window
above `log λ`**. Summing over `p` is a Hardy-type inequality:
`Σ_p ∫_{a−log p}^{a} |f|² · p^(-1)` — a two-weight `L²` domination of the radial
tail against the full norm. The critical point is whether the coefficient
`p^{-1}` (from `|p^{-1/2}|²`) times the Bessel measure genuinely beats the
support overlap.

### The subtlety (honest)
- If `f` is supported on `[logλ,∞)` and shaved by exactly one prime, the
  overhang is `(log p)`-thick; its norm could be comparable to `‖f[..,a]‖`. This
  makes a *uniform* `C(λ)<1` **false** for arbitrary radial `f`.
- The rescue is that the **dual frame `D` is not arbitrary radial**: it is the
  canonical prolate/Sonin family, whose tail (`[logλ, logλ+log p]`) shrinks per
  the Sonin scale. That is exactly where the decay "lives": a **Sobolev decay
  of the radial basis** — not a general operator inequality.

## 4. Formal version needed (Candidate theorem — to judge not yet prove)

Let `D` be the normalized finite-Euler dual frame, `{e_k}` a Hilbert basis of
radial carrier with the Sonin decay `Σ‖' e_k‖²_{[logλ, logλ+δ]} shrink. Then

```
Σ_k ‖ (I−R)∘T†∘R e_k ‖²  ≤  Ω(λ,p; ‖D‖) 
```

for a decaying factor framed by the prolate tail. Combining with the
`tsum_normSq_precomp` machinery closes `RightEnergy` *without* requiring
`forward + M = 0`.

**This is the concrete new analytic theorem the whole front reduces to.**
Whether it is true is a statement about the Sonin-basis near-edge decay, i.e.
whether the prolate tails are thin enough that the shifted leak is square-squeezed.
That is testable numerically and falsifiable; it is not derivable from the
current library by Lean assembly.

## 5. Judgment & handoff

- The wall is a real spectral/leakage interaction: `T†` shifts radial mass left
  of `logλ`; `(I−R)` keeps exactly that mass.
- No library lemma forces it to `0`. A *bound* needs the radial-basis tail decay
  (Sobolev/prolate) — genuinely new analytic content.
- Next: numerically/dimensionally test `‖W‖` on the canonical prolate frame to
  see if a real `C<1` or `decay` exists, before committing to a Lean proof.
  This is the single gate the whole Proof-717 front depends on.

- RH status: because Gate-3U stays open, RH remains **conditional** on this wall
  estimate; the concrete-source/Dev layer is, per `812`/`813`, quarantined.
- Next safe move: numeric probe of `‖W‖` on the canonical prolate frame (not a
  Lean obligation yet); then decide whether to formalize the bound.

## 6. Numeric verdict (2026-08-06): the candidate wall theorem is FALSE

Run `814_wall_estimate_numeric_probe.py` (finite-section of `(I−R)∘T†∘R`).

| primes        | `‖W‖` (largest singval) |
|---------------|--------------------------|
| `{2}`         | `0.70711`               |
| `{2,3}`       | `1.30138`               |
| `{2,3,5}`     | `1.98716`               |

- Value is independent of `log λ` (0.0 / 1.0 gave identical numbers).
- On a decayed prolate-like radial carrier `e_k` (width shrinking with `k`),
  `‖W e_k‖` **does not decay**: it rises toward the flat `‖W‖` (`0.65→0.707`,
  `1.28→1.16`, ...).  The thinner the near-edge tail, the *more* it leaks.

Why this is decisive: one prime factor of `T†` reads `f(t) − p^(−1/2) f(t+logp)`;
the second term shifts radial mass left across `log λ`.  A carrier stacked right
at the wall loses almost its whole edge.  Same net effect accumulates over
`p → log (∏p)`.  So the §4 conjecture — square-squeeze by prolate tail decay —
is **numerically falsified**: `‖W‖` is genuinely `≥ 1` for more than one prime,
and serial decay is not square.

Verdict: Gate-3U cannot be closed via the §4 wall bound on the standard carrier;
that candidate theorem is dead.  The front must move to a *different* operator
side (e.g. forward `T`, a band-limited vs full-domain distinction, or a
radially-*weighted* `T†`), not keep stacking proofs on this wall.