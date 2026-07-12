# 017 QW--Prolate Final Feasibility Verdict

Date: 2026-07-11

Result: rejected as a guaranteed executable route to unconditional RH.

This is not a theorem that the Connes spectral strategy is impossible. It is a
decision that plan 017 has no lower, quantitatively separated producer from
which its RH-closing approximation can currently be forced. The route is
logically valid, but its remaining central statements are the arithmetic
breakthrough rather than controlled consequences of prolate leakage.

## 1. The Valid Logical Bridge

For each support length `a`, let `A_a` be the self-adjoint operator associated
with the localized Weil form. If its lowest eigenvalue is simple and has an
even eigenfunction `xi_a`, then the Fourier transform of `xi_a` has only real
zeros. This is the continuous real-zero theorem:

```text
Connes--van Suijlekom
Quadratic Forms, Real Zeros and Echoes of the Spectral Action
https://arxiv.org/abs/2511.23257
Araki-final-oct25.tex:1366-1391
```

The explicit prolate proxy `k_a` has normalized Fourier--Mellin transform
converging to the Riemann Xi function on closed substrips:

```text
Connes--Consani--Moscovici
Zeta Spectral Triples
https://arxiv.org/abs/2511.22755
mc2arXiv.tex:1261-1269,1352-1383
```

Therefore a cofinal sequence of genuine simple-even ground states satisfying a
weighted approximation strong enough for compact-open convergence would imply
RH by Hurwitz. There is no logical defect in this implication.

## 2. The Lowest-Value Sign Is Exactly RH-Level

Suzuki proves that the lowest spectral value `lambda_a` is continuous in `a`,
is positive for sufficiently small `a`, and that failure of RH is equivalent
to the existence of some `a` with `lambda_a < 0`:

```text
Masatoshi Suzuki
Weil's quadratic form via the screw function
https://arxiv.org/abs/2606.09096
screwzelf_7.tex:439-450
```

Thus

```text
lambda_a >= 0 for every a > 0
              <=>
global Weil positivity
              <=>
RH.
```

Full-ground ownership and the sign of that ground are different statements.
Ownership alone does not imply RH. Ownership plus nonnegative ground values on
a cofinal family does, by support exhaustion. Plan 017 cannot use ground-state
positivity as a preliminary spectral estimate; that would import the final
arithmetic theorem.

## 3. Even-Simplicity Has Been Reduced, Not Proved

Suzuki proves positivity, simplicity, and evenness of the lowest eigenstate
only for sufficiently small intervals (`screwzelf_7.tex:469-483`). The
large-support regime needed for Xi approximation remains open.

The strongest 2026 structural reduction splits the pole term by parity:

```text
A_even = B_even + 2 |C><C|,
A_odd  = B_odd  - 2 |S><S|.
```

The pole-free operator has an unconditional Perron ground state for every
support length. After restoring the pole, full even-simplicity is equivalent
to

```text
lambda_0^even < lambda_0(B_odd)

and

<S,(B_odd-lambda_0^even)^(-1)S> < 1/2.
```

Sources:

```text
The pole term is the only obstruction to Perron structure...
https://zenodo.org/records/20682834
RIEMANN_pole_note_v3_13jun.tex:273-320,368-421

A scalar Herglotz criterion for the even-simplicity hypothesis...
https://zenodo.org/records/20694588
RIEMANN_herglotz_criterion.tex:191-280,337-356
```

The second source explicitly leaves the inequality open for general support.
Its numerical ledger also records that the margin below `1/2` is only of the
same order as

```text
lambda_0^odd - lambda_0^even.
```

See `RIEMANN_herglotz_criterion.tex:325-335`. This is a critically tuned
near-resonance, not a positivity inequality with a fixed safety margin.

The alternative Loewner/operator-monotone reduction does not cover the
arithmetic case. The arithmetic matrices lie in a doubly-critical finite-node
regime and the even/odd ordering is retained as an explicit conjecture:

```text
https://zenodo.org/records/20737111
RIEMANN_loewner_even_simplicity.tex:123-146,198-228
```

## 4. Why The Exact Poisson Defect Does Not Close The Gap

The first R1 calculation is genuine. It identifies the finite defects of the
two-mode proxy as

```text
point defect:       chi_0 - chi_2,
Fourier leakage:    1-chi_0^2 and 1-chi_2^2.
```

It also gives an exact lower-tail Poisson formula. See
`docs/proofs/017_qw_prolate_r1_first_verdict.md`.

But `QW_lambda` is an unbounded closed quadratic form with an archimedean
`log |t|` multiplier, pole evaluation, and finite-prime translations:

```text
https://arxiv.org/abs/2511.22755
mc2arXiv.tex:530-540,612-627
```

Therefore `L2` leakage does not control the `QW` form norm. Even if the
extended radical/tail identity is proved, it gives a small Rayleigh value, not
the relative projection estimate needed to distinguish one vector inside the
approximately `2*a^2` near-radical prolate cluster.

The exact Herglotz reduction shows why a soft estimate cannot suffice: the
quantity whose sign must be decided differs from its critical value by only
the minuscule even/odd spectral gap. The pole-note source states this directly:

```text
the Weil form is critically tuned;
no soft norm bound decides the sign.
```

Source: `RIEMANN_pole_note_v3_13jun.tex:426-433`.

## 5. The R4 Approximation Is Already An RH-Closing Property

Each simple-even ground-state transform has only real zeros. A locally uniform
limit of nonzero real-rooted entire functions belongs to the relevant
Laguerre--Polya closure and still has only real zeros. For Xi, membership in
that class is equivalent to RH. A representative source is:

```text
Karlheinz Grochenig
Schoenberg's Theory of Totally Positive Functions and the Riemann Zeta Function
https://arxiv.org/abs/2007.12889
```

Consequently the proposed estimate

```text
c_a FourierMellin(xi_a) -> Xi compact-open
```

is not an ordinary compactness theorem waiting after R1. It is the decisive
RH-closing assertion. The already proved convergence of the explicit proxy
`k_a` does not transfer to `xi_a` without a relative ground-state projection
estimate, and no such estimate is currently available.

## 6. Rejection Decision

```text
logical implication to RH:                 valid
exact prolate/Poisson defect calculation:  valid
general-support even-simplicity:           open, critically tuned
full growing-cluster transport:            absent
ground-state/proxy compact-open transfer:  absent and RH-closing
fixed quantitative margin:                 absent
guaranteed feasibility of plan 017:        rejected
```

Plan 017 therefore cannot be accepted under the project's feasibility rule
that the missing bridges must have a demonstrably lower producer and a
quantitative margin before route implementation begins.

The rejection applies to the current 017 mechanism and its claimed feasibility.
Future work could still prove the scalar Herglotz inequality or find an exact
arithmetic identity for the near-resonant gap. Either result would supply new
plan input; the present Poisson-leakage argument does not contain it.
