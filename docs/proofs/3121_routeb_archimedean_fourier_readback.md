# Actual powered-span archimedean Fourier readback (3121)

Status: FORMAL-PASS for complete Fourier readback and integrability.
No signed integral bound, gate sign or RH claim.

Owner: the actual rho-dependent powered source and four-point span in
3117/3119/3120, with its Hermitian square formed once. No stored carrier
or incomplete prime set replaces that owner.

Named premise: the actual archimedean term equals the sigma-weighted
full-line Fourier energy integral, with integrability and cycle-frequency
normalization. The consumer is the complete same-owner signed gate; the
prime channel was closed in 3120. Existing center-two Gamma readback is
not already this Fourier multiplier theorem.

Method: the existing paired physical Gamma profile series, single
Fourier/resolvent readback and a summable n^-2 majorant retaining the
first frequency moment. Completion requires an actual-family Lean theorem
and focused Linux ext4 source/audit build with exactly the standard axiom
trio. No external sign certificate or numerical experiment is authorized
by this entry.

Budget: one source/audit campaign, at most 20 minutes from implementation
start, 8 GiB peak resident memory and 2 GiB derived growth; at least 8 GiB
free disk. Stop if the infinite exchange or normalization cannot be proved
within that budget. Retain only verified scope and identify any remaining
gap. A formal readback alone supplies no signed gate bound.

Primary evidence: Mathlib v4.30 source; project
`C1XiCenterTwoGamma.integralOn_archimedeanIntegrand_eq_tsum`,
`C1XiCenterTwoPole.integral_fourierLaplace_div_vertical`, and the cycle
inversion and integrability theorems of 3120. These apply classical
Fourier and Gamma-function analysis; no novelty claim is made for them.

## Analytic construction

For a compact-log source g, let E(g,xi) be the squared complex norm of its
Mathlib Fourier transform at cycle frequency xi. Write c0 for
log(4*pi)+EulerGamma. The reciprocal series uses

```text
z(xi)    = 1/4 - pi*i*xi
r(n,xi)  = 1/(n+z(xi)) - 1/(n+1/2)

sigma(2*pi*xi) = c0 + Re(sum_n r(n,xi)).
```

The exact half-value of digamma and the existing half-anchored series
produce this identity. The real part of n+z(xi) is n+1/4, so no reciprocal
pole is crossed. Every frequency retains its own complex value; no
evenness of E is assumed.

The new source establishes the explicit majorant

```text
norm(r(n,xi))
  <= (1+pi*abs(xi))/((n+1/4)*(n+1/2)).
```

The first frequency moment integral of (1+pi*abs(xi))*E(g,xi) is finite
because the Fourier transform of g.square is a Schwartz function.
For n>=1, the denominator is at least n^2. This proves summability of
the integral of each reciprocal term's norm, not merely convergence at
each frequency. It therefore justifies the infinite sum/integral exchange
and proves integrability of the actual sigma-weighted energy.

For one index n, put a=2*n+1/2 and b=2*n+1. The existing full-line
Fourier/resolvent theorem, after the exact t=-2*pi*xi change of variable,
reads the term back to its positive-coordinate Gamma profile. That profile
is the paired expression

```text
exp(-a*y)*(g.square(y)+g.square(-y))
  - 2*exp(-b*y)*g.square(0).
```

Taking real parts preserves the Hermitian pairing. The two pieces are
kept together in the infinite series; splitting their separate divergent
series would invalidate the argument. The physical Gamma profile series
was already proved absolutely integrable in C1XiCenterTwoGamma.

## Complete same-owner target

The source proves these actual equalities, with all integrals over the
full real line and unit cycle-frequency measure:

```text
archimedeanTerm(g.square)
  = integral sigma(2*pi*xi)*E(g,xi) dxi

archimedeanTerm(g.square) + finitePrimeSum(g.square)
  = integral (sigma(2*pi*xi)+K(g,xi))*E(g,xi) dxi.
```

Here K(g,xi) is the signed cosine kernel over the actual complete
visible-prime set of g.square, with the exact von Mangoldt weights from
3120. The prime contribution is not truncated or bounded in absolute
value. The powered-family instance retains
norm(orbitMultiplier(rho,xi)-lambda)^2 and the actual source energy,
and proves integrability of that complete factored integrand.

These are the physical archimedean and prime terms defined by the
project. They do not identify the different Poisson-symbol contract of
3081 with qw, or reopen its pointwise-square producer. The earlier
angular-frequency normalization finding of 3094 remains valid.

## Consumer and boundary

On any same-owner triple-vanishing test, the existing consumer gives
qw(g)=-archimedeanTerm(g.square)-finitePrimeSum(g.square). Consequently
the required sign is still a signed integral inequality. An exact
representation and its integrability do not supply that inequality.

The audit checks the zero-frequency quarter point, the exact first
reciprocal value, pole avoidance, and failure of an everywhere-nonpositive
symbol claim even when the prime set is empty. That last guard is only
about the symbol: it does not assert nonzero energy at frequency zero.

No numerical model is evaluated or promoted to an exact conclusion.
The signed complete remainder/gate estimate, simultaneous gate/tail
coefficient and coverage of all hypothetical off-line source zeros remain
open. Route A remains the binding producer.

Reproduction in a Linux ext4 verification environment:

```text
python3 scripts/routeb_archimedean_fourier_readback_audit_3121.py
```

The source theorem `archimedean_eq_sigma_energy3121` has no extra analytic
premise. `complete_gate_readback3121` combines it with 3120's complete
prime readback. `poweredFamily_complete_gate_readback3121` and
`poweredFamily_complete_gate_integrable3121` instantiate the exact actual
family and its full complex multiplier.

Eighteen analytic declarations and four boundary declarations print
exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
The checker requires all 22 identifiers, the successful Lake footer and
ten parser controls, together with source provenance and resource checks.
No indexed 2664 certificate output is added; shared Dev outputs are retained.

The first checks exposed elaboration errors in real/complex coercions,
implicit measures, series multiplication and real-part integration. The
last mathematical compilation error was a missing use of the existing
`convolutionSquare_zero_im` theorem in a Hermitian profile identity. It was
fixed without a new assumption. The first passing Lake build and all
22 axiom checks completed before the implementation budget expired.
An outer command timeout then interrupted result-file finalization; the
checker was replayed against the unchanged cached proof outputs to finish
the provenance/resource receipt. That replay is not a second mathematics
campaign or an additional sign test.

The retained acceptance artifact is
`results/3121_routeb_archimedean_fourier_readback_audit.json`:

```text
Build completed successfully (3907 jobs).
audited leaves: 22 / 22
axioms on every leaf: [propext, Classical.choice, Quot.sound]
error / sorryAx: absent
parser controls: 10 / 10 pass
normalized source hashes: 21
cached receipt elapsed: 34.49 seconds
cached receipt peak resident memory: 834859008 bytes
cached receipt build-tree growth: 0 bytes
```

The preceding source/audit compilation took 85.80 seconds and peaked at
4091068 KiB resident memory, with cached dependencies. The smaller memory
reading above belongs to the cached acceptance replay. Source creation
to the first successful source/audit proof outputs took less than the
20-minute implementation budget; no further analytic target was opened.
The toolchain is Lean v4.30.0 and Mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Follow-up: unavoidable actual deficit (3122)

Record 3122 uses this exact physical density to prove integrability of
its credit and deficit, their signed Weil identity on triple-vanishing
tests, and a strictly positive deficit integral for every nonzero source.
The result is instantiated on the binding selected detector and actual
powered spans with nonzero coefficient. An actual zero Fourier value at
the origin coexists with that strict integral. Thus origin vanishing does
not remove the unfavourable band of this exact formula. The independent
credit-versus-deficit inequality remains unresolved.
