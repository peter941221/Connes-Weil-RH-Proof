# Same-owner signed prime-cut accounting (3119)

Status: FORMAL-PASS for exact signed accounting and finite coverage;
MODEL-DIAGNOSTIC for the numerical band. No full gate or RH claim.

Owner: the actual powered family of 3117 and, for the numerical decision,
the exact stored row-B node data of 2722F, re-seeded with poweredSeed as in
3110. The numerical point is not asserted to be a source zero.

Premise to remove: the implicit omission of prime powers above exp(10)
from the n=3 gate. The formal target is an exact signed cut-plus-remainder
identity on the actual span, with a proved support-based finite coverage
bound. No new RH exit or unsigned prime allowance is part of the target.

The bounded numerical question is whether the omitted band
10<log(q)<=12 has zero or negligible signed contribution at the stored
n=3, lambda=24 model, compared with its old gate margin. A same-run legacy
control precedes this decision. This is a diagnostic on finite frequency
quadrature, not a proof of the continuum omitted sum or its full tail.

Completion: focused Linux ext4 Lean source/audit build with the standard
axiom trio; signed numerical band with preserved owner and both frequency
signs; source provenance and boundary controls. Residual: full-line
readback and the uncomputed prime range remain open.

Budget: one analytic entry and its audit, at most 20 minutes and 8 GiB RSS;
one fixed numerical model with prime log cutoff at most 12, at most
10 minutes and 2 GiB RSS. At least 8 GiB free Linux space. No wider prime
enumeration or family scan. A failed legacy control licenses no verdict.
An unresolved full-prime remainder cannot be declared zero from a finite
band or a support upper bound.

## Formal signed accounting on the actual functions

For a compact-log formula test F and an integer cutoff M, the source defines:

```text
primeCut(F,M)       = sum_{q<=M} finitePrimeTerm(F,q)
primeRemainder(F,M) = sum_{visible q>M} finitePrimeTerm(F,q).
```

The first sum is over a finite integer range. Non-prime-powers and terms
outside the actual visible set contribute zero, as proved by
`primeCut_eq_visible_filter3119`. The second sum retains the actual visible
set of F, rather than a substituted support model. Both sums retain signs.
The canonical term is the project's von-Mangoldt-weighted physical sample
at log(q) and -log(q), with its factor 1/sqrt(q).

`finitePrimeSum_eq_cut_add_remainder3119` proves the exact decomposition.
For a source test g with its Hermitian square formed once, define cutGate
as the complete archimedean term plus primeCut. The gate then satisfies:

```text
fullGate(g) = cutGate(g,M) + primeRemainder(g.square,M)

fullGate(g)<=0
  iff primeRemainder(g.square,M) <= -cutGate(g,M).
```

`poweredFamily_full_gate3119` applies that identity to the actual
`poweredFamilySpan3117 rho N nodes n lambda`. `storedSpan_full_gate3119`
applies it to the exact stored powered-seed carrier of 3110, followed by
the four-point annihilator and the same span coefficient. There is no
hypothetical-zero premise in this accounting identity.

This is a missing-contribution interface, not a new positivity mechanism:
the signed remainder inequality still needs an independent proof. No
remainder domination is claimed from the identity itself.

## Complete finite coverage of the stored span

The stored source g has the existing open support bound (-55,55). The
annihilator has the corresponding proved closed bound [-55,55]. Widening
both to (-56,56) gives a common open support bound for the span. Its square
therefore has no visible prime power at or beyond exp(112).

The source proves, for every complex annihilator parameter and every real
coefficient:

```text
storedSpan_visible_prime_bound3119:
  every visible q <= ceil(exp(112))

storedSpan_remainder_at_complete_bound3119:
  primeRemainder(span.square, ceil(exp(112))) = 0

storedSpan_complete_prime_cut3119:
  finitePrimeSum(span.square) = primeCut(span.square, ceil(exp(112))).
```

This is a conservative finite coverage bound; it is not the exact support
or visible-prime endpoint, and it does not justify the old cutoff exp(10).
The integer bound is symbolic: no large prime book is generated. The
parameter rho here is not asserted to be a source zero.

Boundary checks prove that cutoff zero contributes zero, its remainder is
the full prime sum, and a successor cutoff includes exactly its new endpoint.
Scalar checks retain two elementary failure modes: nonzero summands can
cancel, and a negative truncated value does not determine the full sign.
These are not synthetic detector inputs.

## Bounded model decision

The numerical script reads the exact dyadic node and target-value capture
`results/2722f_rowB_capture_data.json`. Its 56 nodes and eight target nodes
match the stored Lean carrier data. It does not rebuild a different owner
from newly queried zeros. The parameter is the stored binary64 value of
0.55 + 21.022039638771556*i; it is not asserted to be a zeta zero.

The fixed convolution count is 3 and the span coefficient is 24. The old
prime book has 2532 prime powers. The additional band contains 12508 prime
powers, bringing the book through log(q)=12 to 15040. Both signs of the
frequency interval [-25,25] are retained.

The same-run baseline reproduces all C,b,D values of the committed 2032
row bitwise on both grids. For W the same model's squared transform and P
its four-point annihilator multiplier, the signed band is evaluated both
by three coefficients and directly on the assembled span:

```text
band(lambda) = band_D - 2*lambda*band_b + lambda^2*band_C
             = quadrature of bandKernel*(P-lambda)^2*W.
```

The direct calculation checks that the negative cross contribution is
retained. It is independent of regrouping the three coefficient sums,
although both evaluate the same finite quadrature model. An independent
simple prime generator checks the vectorized prime-power generator, and
an empty band contributes exactly zero.

The diagnostic result is:

```text
frequency step   seed nodes    old gate at 24     omitted band (10,12]
--------------   ----------   ----------------   --------------------
0.02             300          -1.177222430e11     -1.061786913e12
0.01             300          -1.177222430e11     -1.061786903e12
0.01             1200         -1.177222430e11     -1.061786903e12
```

The band has about 9.0194 times the magnitude of the old gate value. The
refined reading through log(q)=12 is about -1.179509146e12. Grid/rule
comparisons change the band by at most 9.36e-9 relative in these runs.
The seed-node increase changes the quadrature rule, rather than merely
repeating the same frequency grid.

Verdict: `MODEL-DIAGNOSTIC / OMITTED-BAND-EXCEEDS-OLD-MARGIN`.
An assumption that this omitted band is negligible is incompatible with
this controlled finite model. Its negative sign strengthens the truncated
model gate on this band. It does not establish the sign of the full
remaining prime contribution.

The numerical band is a finite-frequency quadrature value. No continuum
Fourier readback, certified frequency-tail remainder, exact special-function
value, or formal real-number sign certificate is inferred. A nonzero partial
band also does not prove that the aggregate remainder is nonzero: later
prime bands could cancel it. The formal scalar cancellation check guards
that distinction.

## Reproduction and acceptance

Run the formal checker in a Linux ext4 verification environment:

```text
python3 scripts/routeb_signed_prime_cut_audit_3119.py
```

It builds the source and audit modules with LEAN_NUM_THREADS=1, checks
fifteen exact declaration names and the successful Lake footer, rejects
errors and unsupported axioms, and records portable source hashes. Ten
format/rejection controls protect its log parser.

```text
Build completed successfully (3904 jobs).
all fifteen axiom footprints: [propext, Classical.choice, Quot.sound]
sorryAx: absent
elapsed: 78.90 seconds
peak resident memory: 4119408640 bytes
```

The result is `results/3119_routeb_signed_prime_cut_audit.json`. Most
dependencies were cached. No indexed 2664 certificate directory is part
of this entry, so its entry-local pruner does not apply; shared Dev outputs
are retained.

Run the bounded model diagnostic separately:

```text
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/routeb_prime_cut_probe_3119.py
```

Its artifact is `results/3119_routeb_prime_cut_probe.json`. All sixteen
controls pass. They cover capture identity, independent prime generation,
legacy bitwise reproduction, signed coefficient/direct-span agreement,
grid/rule stability, an empty band, finite outputs, unchanged sources and
resource limits. Failures propagate to the artifact status and exit code;
no verdict is issued after a control failure. No old artifact or engine
source is modified.

The final bounded model run takes about 2.84 seconds and peaks below
0.12 GiB RSS. Its eight source/data hashes and the formal audit's fourteen
source hashes use CRLF-to-LF normalization and are checked against the
publication blobs.

## Residual mathematical obligation

The old cutoff is now represented explicitly as a physical prime cut plus
a signed remainder on the actual span. A finite coverage bound is proved
for the stored span, and a controlled model shows why the omitted band
cannot simply be ignored. Neither result proves the complete gate sign.

The next required estimate is the signed contribution of all excluded
prime powers on the same actual function, together with the continuum
identification of any proposed Fourier computation. A bare absolute-value
allowance cannot be substituted for the needed prime cancellation. The
joint gate/tail coefficient and the eventual coverage of every hypothetical
right off-line source zero remain unresolved. Route A remains binding.

## Follow-up: exact prime-channel readback (3120)

Record 3120 closes the analytic equality and integrability premise for
this actual powered-family prime remainder. It uses cycle-frequency
Fourier inversion, the complete visible-prime set, and the full complex
four-point multiplier. It also gives the complete-prime-sum readback.

This does not promote the finite-frequency model values above to exact
real numbers. Frequency-tail and quadrature errors, the signed remainder
bound, the full archimedean/gate contribution and universal rho coverage
remain unresolved. Evidence:
`3120_routeb_prime_fourier_readback.md` and
`results/3120_routeb_prime_fourier_readback_audit.json`.
