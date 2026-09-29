# 2151–2153 — Exact finite-zero filter and scoped vertex screen

Date: 2026-09-29.

Status: exact finite-owner filter algebra; **NO PRODUCER GO**. The registered
`1e-3` sampled vertex-margin bar fails on the screened trial-162 shape family.
Neither result is a same-owner C3′ sign theorem or an RH claim.

## Entry contract

- Consumer: healthy `CompactLog` detector-specific `qw(g) >= 0`, via the exact
  semi-local gate and then `SourceRH`.
- Owner: the selected orbit detector for a hypothetical off-line zero `rho`,
  with its *complete* finite closed-ball source-zero owner and its actual
  support-derived visible prime-power set. The numerical model below has
  only 21 known positive-height zero positions; it is not that owner.
- Current assumptions: the already constructed compact smooth base and
  correction, their three nonzero correction target values, triple vanishing,
  and finiteness of the closed-ball zero set. No sign or RH premise is assumed.
- Construction choice replaced: the ill-conditioned 40-profile solve for
  omitted-zero pins. The filter gives an explicit compactly supported
  correction with zero Laplace values at **every** member of an arbitrary
  finite omitted-zero set while preserving all three nonzero target values.
  Its support increment is the smoothing width, independent of the zero
  count. Generic finite interpolation already exists formally in the
  project; this construction does not itself prove a new signed bound.
- Failure for a producer Go: no complete-owner signed gate and same-index
  spectral-tail margin. For the *numerical shape screen only*, the registered
  stop bar was relative vertex determinant margin `< 1e-3` or an unstable
  sign under rule/grid changes.

## Exact construction (paper proof)

Let `rho = beta + i gamma`, `beta > 1/2`, and put

```
T = {rho, 1 - conj(rho), rho + 1/2}.
```

These are the **three** nonzero correction targets in the 2143 model. Let
`Z` be any finite omitted-zero set disjoint from `T`; adding conjugates to
`Z` is allowed. For any `a > 0`, take an even, nonnegative, nonzero
`C_c^infty` bump `phi_a` supported in `[-a,a]`. With the project's Laplace
convention `L(f)(s) = integral f(x) exp(s x) dx`, define

```
q_Z(s) = product_{z in Z} (s-z)/(rho-z),
d_a(s) = L(phi_a(x) exp(-i gamma x))(s)
         / L(phi_a(x) exp(-i gamma x))(rho).
```

For each `t in T`, `q_Z(t) != 0`. All three targets have imaginary part
`gamma`, so `d_a(t)` is a quotient of strictly positive real integrals.
There is therefore a unique polynomial `h_Z` of degree at most two with
`h_Z(t) = 1/(q_Z(t)d_a(t))` on `T`. Set

```
R_Z(s) = q_Z(s) d_a(s) h_Z(s).
```

It follows by substitution that `R_Z(t)=1` for all three target nodes and
`R_Z(z)=0` for every `z in Z`. Multiplying an existing correction Laplace
transform by `R_Z` preserves its nonzero prescribed values; its already-zero
targets remain zero. In physical coordinates, multiplication by `q_Z h_Z`
is a finite constant-coefficient differential operator (the sign depends on
the Laplace derivative convention), and multiplication by `d_a` is
convolution with the carrier-centred bump up to its nonzero scalar
normalization. Derivatives do not enlarge compact support, so if the
original correction is supported in `[-A,A]`, the new one is supported in
`[-A-a,A+a]`, **independent of `|Z|`**. This proves the finite-owner
zero and support statements without a large interpolation solve.

This argument does not bound the derivative coefficients or the signed Weil
form. For the actual source-zero owner, `Z` and the resulting polynomial
depend on the hypothetical zero; uniform gate and tail estimates remain
the mathematical wall. This paper construction is not yet a Lean leaf.

## Numerical decision and instrument correction

The screen starts from record 2143 trial 162, `N=0`, `rho = 0.945 +
39.25244858548658 i`, and adds the 21 known positive-height zero positions
inside its formal ball and their conjugates. This is a model under-
approximation, not the complete abstract owner. The filter uses `a=1.0`;
the new support radius is `11.4`, and the complete prime-power book for that
support has 8755 entries, all evaluated. The third target `rho+1/2` was
initially missed by a linear normalizer; that reading was **withdrawn**.
The final artifacts use the quadratic three-target normalizer, with all
three filter target errors at floating-point scale.

The old `m=400` rule is untrustworthy after the polynomial filter: at
`xi=40` it reads filtered log10 weight `59.27`, while `m=1600` reads
`13.97`. Its apparent gate failure is an evaluator artifact. The corrected
paired filter's `a=1.0` vertex row has, on `[-20,20]` at `dxi=0.01`,

```
m=1600: C=4898.61322, B01=1.16298196e10, D=2.76103608e16,
        det=-2.25236743e14,  -det/B01^2=1.66530307e-6;
m=3200: C=4898.61447, B01=1.16298226e10, D=2.76103679e16,
        det=-2.25236843e14,  -det/B01^2=1.66530296e-6.
```

The `m=1600`, `dxi=0.005` row reproduces the sign and margin. This is a
sampled finite-window *vertex* gate; the same-index high-shell budget and
full-line integral certificate are open.

Record 2153 adds the exact-target-preserving null shape
`R_c(s)=R_Z(s)(1+c T_3(s)/M)`, where `T_3(s)` is the product of the three
target differences and `M` is its modulus at the mass peak. On the
registered real, imaginary, and two-dimensional coefficient grids, the
best vertex row occurs at `c=0.962 i`:

```
C=5.0900574, B01=1.21460893e7, D=2.89701987e13,
det=-6.75108837e10,  -det/B01^2=4.57615632e-4.
```

No row reaches the preregistered `1e-3` margin (`go_count=0`). This is a
**scoped numerical no-go for that null-shape grid and margin bar**, not a
global impossibility theorem for exact zero filters. Further coefficient
search on the same trial has no priority without a changed hypothesis and
a named same-index tail plan. The exact finite-zero construction above
survives this screen.

## Evidence and next proof obligation

The reproducible instruments and data are
`scripts/routea_polynomial_zero_filter_2151.py`,
`scripts/routea_paired_filter_vertex_verify_2152.py`,
`scripts/routea_paired_filter_nullshape_2153.py`, and their matching
`results/2151_*`, `results/2152_*`, `results/2153_*` JSON artifacts.
They were run through `scripts/run_resource_aware_task.sh`; logs are in
`build-logs/2151_*`, `2152_*`, and `2153_*`.

The record-2050 antibody script fired `GAP` on the words "margin" and
"tail" in this record. Its cited imported-theorem error-term exhibit does
not apply: the construction imports no theorem or error bound. The actual
gap is explicitly retained above, so this firing is vocabulary triage, not
a clearance verdict.

The next admissible producer claim must prove an actual-owner signed C3′
margin **and** the matching spectral tail (or prove `qw >= 0` directly).
The exact filter makes the zero constraints constructive with fixed support
increment; it does not shrink the signed producer premise by itself. It
also changes the correction
test, so its membership in the formal selected-owner correction family and
the corresponding detector-data fields must be proved before the B5
consumer can use it. The numeric model retains the 2143 floating
coefficients; high-node rule agreement is not an exact interpolation proof.
Evidence level: exact paper
algebra plus numerical screens, no Lean build or axiom audit.

## 2026-09-29 sign-orientation correction

Map 104 and proof record 1931 already formally establish: under a
hypothetical off-line zero, the *actual* healthy selected geometry has
`0 < ICgate(g.square)`, by its strict spectral-negative readback. The
negative vertex rows above belong to an auxiliary four-point span on an
incomplete numerical zero list at `N=0`. They do not give
`ICgate(g.square) <= 0` for that same healthy detector, nor do they close
the same-index spectral tail. The exact finite-zero filter is an alternative
construction formula, not a new signed premise or a route Go. The words
"construction GO" in this record's first draft are withdrawn.

## 2154 same-run pin repair

Record 2154 checks the most promising sampled null-shape row (`c=0.962 i`)
against its own `m=1600` target matrix before judging its sign. The
trial-162 base/correction target residuals are `2.615e-10` / `2.542e-11`;
a float least-squares repair makes them `1.78e-15` / `1.42e-14`.
Re-evaluating the full 8755-entry visible-prime gate in the same run moves
the determinant by only `6.43e-11` relative and leaves the sampled relative
vertex margin at `4.5761563e-4`. Thus this specific float pin error does
not explain the thin margin. The repair is not an exact coefficient
certificate, and the row still belongs to an incomplete numerical owner.
Evidence: `scripts/routea_paired_filter_pin_repair_2154.py`,
`results/2154_routea_paired_filter_pin_repair.json`, and
`build-logs/2154_paired_filter_pin_repair.log`.
