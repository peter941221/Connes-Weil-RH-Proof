# Actual powered-span prime Fourier readback (3120)

Status: FORMAL-PASS for exact prime-channel readback and integrability.
No signed remainder estimate, gate sign or RH claim.

Owner: the same powered family and four-point span of 3117/3119, with
the actual finite visible-prime remainder. The transform variable is the
ordinary Fourier cycle frequency, corresponding to Laplace parameter
-2*pi*i*xi. The complex owner need not have even Fourier energy.

Premise to remove: the unproved equality between the physical prime
remainder and its full-line Fourier kernel integral, including integrability
and normalization. Consumer: the signed remainder budget of 3119. The
archimedean multiplier, numerical quadrature error and full gate sign are
separate unresolved duties.

Completion: actual-owner exact readback without analytic hypotheses handed
to the consumer; complex modulus retained in the span multiplier; Linux ext4
Lake source/audit build with the standard axiom trio and boundary checks.

Budget: one analytic entry and audit, at most 20 minutes, 8 GiB RSS and
2 GiB additional derived output, with at least 8 GiB free Linux disk. No
prime enumeration, numerical sign search or cold certificate build. Stop
if the exact owner, full prime set or frequency convention cannot be retained.

Primary inputs: existing Schwartz Fourier inversion in Mathlib v4.30 and
the project source `C1XiArithmeticPrimePowerReadback`, the actual Hermitian
square law, and the exact signed remainder of 3119. This is an application
of classical Fourier analysis, with no novelty claim for those methods.

## Exact object and normalization

Write g for `poweredFamilyOwner3117 rho N nodes n`, the actual
rho-dependent compact-log source, and v for
`poweredFamilySpan3117 rho N nodes n lambda`, its four-point span. The
parameters N and nodes specify the interpolation correction, n specifies
the convolution power, and lambda is the real span coefficient. No stored
numerical carrier is substituted for this family.

For any compact-log source h, define T(h,xi) as its Mathlib Fourier
transform at cycle frequency xi and E(h,xi)=norm(T(h,xi))^2. The source
proves the following conversion and square identity:

```text
T(h,xi)        = laplaceAt(h, -2*pi*i*xi)
T(h.square,xi) = E(h,xi)

Re(h.square(x)) = integral cos(2*pi*xi*x) * E(h,xi) dxi
Re(h.square(0)) = integral E(h,xi) dxi.
```

All integrals are over the entire real line. Their integrability is
proved from the existing Schwartz Fourier transform. Here a Schwartz
function is a smooth function with sufficiently fast decay for inversion
and integration; compact-log tests already carry that structure. Taking
the real part of the complex inverse integral gives the cosine formula.
The energy of a complex h is not assumed to be even.

Cycle frequency includes 2*pi in the exponential, so its integration
measure has no additional factor. Record 3094 instead uses an angular
frequency with the 2*pi absorbed into the variable; that convention needs
the inverse factor 1/(2*pi). The two formulas do not conflict. This entry
does not reopen the failed Route A joint-density contract of 3094.

## Complete signed prime channel

Let L(q) be the von Mangoldt weight: log(p) when q is a positive power of
the prime p, and zero otherwise. For a finite integer set S, the actual
prime kernel is the real function

```text
K(S,xi) = sum_{q in S} (2*L(q)/sqrt(q)) * cos(2*pi*xi*log(q)).
```

This definition retains the sign of the cosine. The factor 2 comes from
the pair h.square(log(q)) and h.square(-log(q)), which are complex
conjugates. It does not come from doubling a positive-frequency integral.
`primeTerm_eq_cosine_integral3120` proves the identity for every natural
q, including zero, and `sum_primeTerms_eq_integral3120` sums it over S.

For cutoff M, choose S to be the actual visible-prime set of v.square,
filtered by q>M. The visible set contains precisely the project's
nonzero prime-power samples. No fixed log cutoff or support surrogate
replaces it. Define P(rho,xi) as `orbitMultiplier3120`, the complete
complex four-point annihilator multiplier. The formal result is:

```text
primeRemainder(v.square,M)
  = integral K(S,xi) * norm(P(rho,xi)-lambda)^2 * E(g,xi) dxi.
```

`poweredFamily_remainder_readback3120` proves this equation, and
`poweredFamily_remainder_integrable3120` proves that its actual factored
integrand is integrable. Both quantify over rho,N,nodes,n,lambda,M
without source-zero, energy-evenness or analytic premises. The complete
complex norm is retained, including its imaginary part. Separate source
theorems give the cutoff and complete-prime-sum readbacks.

The consumer remains the exact budget in 3119:

```text
same actual owner
       |
       v
fullGate = cutGate + primeRemainder
       |
       v
fullGate <= 0  iff  primeRemainder <= -cutGate
                             |
                             v
                   exact integral supplied here
                   its signed upper bound still open.
```

The equality removes the readback premise. It supplies no numerical value
or upper bound for that integral. A finite model band, even one with a
large negative contribution, cannot certify the complete integral.

## Boundary and rejection checks

The audit verifies unit cycle-mass normalization, energy integrability,
zero prime weight and term at q=0, an empty prime kernel and integral,
and the multiplier identity at lambda=0. It also proves
norm(i)^2=1 while Re(i)^2=0, guarding against dropping imaginary
contributions. The universal complex-owner inversion theorem uses neither
energy parity nor restriction to one frequency half-line.

All sixteen source theorems and eight boundary theorems have exactly
`[propext, Classical.choice, Quot.sound]` in the direct audit. No new
axiom, special-function certificate or floating-point input is introduced.

## Reproduction and remaining obligation

Run the bounded checker in a Linux ext4 verification environment:

```text
python3 scripts/routeb_prime_fourier_readback_audit_3120.py
```

It builds the source and audit modules with LEAN_NUM_THREADS=1, requires
all 24 exact identifiers and the successful Lake footer, rejects errors
and unsupported axioms, and runs ten parser acceptance/rejection controls.
It records normalized source hashes, the Mathlib revision, elapsed time,
peak resident memory and derived build-tree growth. A failed run replaces
the result status rather than preserving a stale PASS.

The accepted artifact is
`results/3120_routeb_prime_fourier_readback_audit.json`:

```text
Build completed successfully (3905 jobs).
audited declarations: 24
axioms on every leaf: [propext, Classical.choice, Quot.sound]
error / sorryAx: absent
parser controls: 10 / 10 pass
elapsed: 95.60 seconds
peak resident memory: 4116926464 bytes
derived build-tree growth: 4520162 bytes
normalized source hashes: 16
```

The toolchain is Lean v4.30.0 and Mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Most dependencies were cached.
Only shared Dev outputs are added; there is no indexed 2664 certificate
directory to prune. The first source checks exposed type-coercion,
implicit-measure and sum-rewrite elaboration errors. Those were fixed
before the passing direct and Lake audits; no assumption was added to
close them. No new numerical experiment is part of this record.

The remaining mathematical task is a signed estimate for the entire
actual remainder, together with the complete archimedean contribution
and a gate coefficient compatible with 3117's adaptive tail. An estimate
which throws away prime cancellation cannot discharge that task. Passing
the stored numerical gate cannot supply universal rho coverage. Route A
remains binding, and RH remains unproved.

## Follow-up: complete physical gate readback (3121)

Record 3121 proves the missing sigma-weighted archimedean equality and
integrability, then combines them with this complete prime channel on
the same actual powered span. Its full-line cycle-frequency integral
retains the complete complex multiplier and actual visible-prime set.
The signed integral inequality, gate/tail intersection and universal rho
coverage remain open. The distinct Poisson-symbol contract of 3081 is
not identified with this physical cosine-kernel formula.
