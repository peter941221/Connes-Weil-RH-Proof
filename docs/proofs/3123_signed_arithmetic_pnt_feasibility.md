# Signed arithmetic feasibility on the actual detector (3123)

Status: PAPER-REVIEW COMPLETE; exact algebra controls pass. The imported
scalar error envelope does not supply a same-function sign estimate.
The actual weighted budget remains UNPRICED, not refuted. No RH claim.

## Question, owner and completion boundary

The functions are the binding selected healthy CompactLog detector and the
actual rho-dependent powered spans of 3117. Their complete physical prime
contributions are those of 3119-3121. A stored capture, a different source,
or a fixed prime book is not substituted for either function.

The candidate input is an unconditional prime number theorem error term.
The question is whether that input supplies the missing signed estimate,
rather than merely replacing it with a weighted autocorrelation obligation.
The consumer still needs the complete same-function gate, coordinated with
the same-function spectral tail in the powered-span case.

Completion is a paper-level derivation of the exact remainder estimate,
an audit of its endpoint convention and parameter dependence, and a decision
about what the imported theorem does and does not establish. A new Lean
entry is admissible only after an independent actual-function sign estimate
has been found. An error-envelope calculation alone is not such a sign.

Budget: one literature input and one symbolic feasibility calculation,
at most 30 minutes from 07:15 UTC on 2026-10-26, 2 GiB resident memory and
50 MiB derived output. No detector prime-book enumeration, frequency
quadrature, parameter scan, new certificate batch, or unchanged Lean rebuild.
Finite polynomial endpoint controls do not evaluate a detector. Stop at a surviving
unpriced signed correlation estimate; do not replace it with a positivity
assumption. Route A remains binding.

## Existing evidence to preserve

Records 215 and 220 already identify the continuous prime-number-theorem
main kernel and the signed Chebyshev discrepancy. Record 221 retains the
isolated target-orbit residue and its negative Weil contribution. These
are prior project analyses, not new mechanisms discovered in this review.
Their Q-root conventions are not silently transferred to the present source.

The exact current physical formula is `complete_gate_readback3121`, and
`qw_eq_credit_sub_deficit3122` is an identity, not an independent domination
estimate. The actual-family tail theorem is
`exists_eventual_powered_span_qw_neg3117`; the correction's necessary
inverse-gap cost is recorded in 3116.

## Exact current-source remainder and its cutoff endpoint

Fix one of the actual source tests g. Write F=g.convolutionSquare and
`C(b)=Re(F.test(b))`. This real autocorrelation measures overlap with a
translated copy of the same function; it can have either sign. Hermitian
symmetry gives `C(-b)=C(b)`. This does not require even Fourier energy.
Record 3120 proves, with the project's actual normalization,

```text
finitePrimeTerm(F,q) = 2*Lambda(q)/sqrt(q) * C(log(q)).
```

Here q runs over integers; Lambda(q)=log(p) when q=p^k for a prime p and
positive k, and is zero otherwise. Choose an integer M>=2 and X>M beyond
the support of F on the positive axis. Put T=log(X) and b0=log(M). Thus
`C(T)=0`; X is chosen for this function, not inherited from a stored row.

Let `psi(x)=sum_(q<=x) Lambda(q)` be the right-continuous Chebyshev counting
function, and `E(x)=psi(x)-x`. Define `f(x)=C(log(x))/sqrt(x)` for x>=M.
The signed prime remainder from 3119 is exactly

```text
R(g,M) = 2*sum_(M<q<=X) Lambda(q)*f(q)
       = 2*integral_(M,X] f(x) d psi(x).
```

Terms outside the actual visible set vanish; no contribution is omitted by
writing the sum over all integers in this interval. The Stieltjes integral
is an integral against a measure with a mass Lambda(q) at each prime power.
It therefore equals the displayed finite sum. Partial summation is ordinary
integration by parts for this step function, paired with the smooth f:

```text
R(g,M)
 = 2*integral_M^X f(x) dx
   + 2*f(X)*E(X) - 2*f(M)*E(M)
   - 2*integral_M^X E(x)*f'(x) dx.

f'(x) = x^(-3/2) * (C'(log(x)) - C(log(x))/2).
```

Using f(X)=0 and x=exp(b) gives the current-source formula

```text
R(g,M)
 = 2*integral_b0^T exp(b/2)*C(b) db
   - 2*E(M)/sqrt(M)*C(b0)
   - 2*integral_b0^T exp(-b/2)*E(exp(b))
                         * (C'(b)-C(b)/2) db.                 (1)
```

The lower endpoint uses psi(M), including the jump at M. The remainder
excludes q=M because the cut already includes it. Replacing psi(M) by its
left limit, including M a second time, or dropping the endpoint changes
the identity. If a larger X is chosen after C and C' vanish, all added
integrands and the upper endpoint are zero. A wider support upper bound
alone gives no lower bound on the integral in (1).

This is a paper derivation from the exact physical terms. It is not a new
Lean theorem. In particular it does not borrow the distinct Q-root Green
identity from 220 to assert a sign for the main integral of this source.

## The external estimate and the exact surviving budget

Johnston and Yang, arXiv:2204.01980v2, Theorem 1.1, equation (1.3), prove
the following unconditional estimate for all x>=2:

```text
abs(E(x)) <= x*H(log(x))
H(b) = (939/100)*b^(303/200)*exp(-(4137/5000)*sqrt(b)).
```

The decimal constants 9.39, 1.515 and 0.8274 are written as exact rationals
here. This is a cited literature input, not an axiom or a formal Lean
result. The paper uses proved zero-free/zero-density results and a finite
height verification; it does not assume the full Riemann hypothesis. The
version history identifies v2 as 20 April 2022. The bound and its threshold
were read in the versioned primary source:

https://arxiv.org/html/2204.01980v2

Set `W(b)=exp(b/2)*H(b)`. Equation (1) gives the valid paper allowance

```text
Rmain(g,M) = 2*integral_b0^T exp(b/2)*C(b) db

B(g,M) = 2*W(b0)*abs(C(b0))
         + 2*integral_b0^T W(b)*abs(C'(b)-C(b)/2) db

abs(R(g,M)-Rmain(g,M)) <= B(g,M).                       (2)
```

This takes absolute values only after retaining the cumulative prime
discrepancy E. It is different from summing absolute prime contributions,
but it still discards the sign of its final pairing with C'-C/2. It may be
useful on a function for which B has an independent, sufficiently small
bound; neither a successful price nor a failure of that price follows
without evaluating or bounding the actual weighted correlation.

For `Gcut(g,M)=archimedeanTerm(F)+primeCut(F,M)`, a sufficient acceptance
test for this particular envelope method would be

```text
Gcut(g,M) + Rmain(g,M) + B(g,M) <= 0.                   (3)
```

No independent proof of (3), or of a sufficiently sharp bound on B for the
selected detector or the actual powered span, is supplied by the imported
PNT theorem. Assuming (3) is not a new producer. The signed integral in
(1) is the unresolved arithmetic object if (2) is too expensive.

## What the error exponent actually says

Write r=303/200 and c=4137/5000. For every b>0,

```text
2*b*(log(W))'(b)
 = b + 2*r - c*sqrt(b)
 = (sqrt(b)-c/2)^2 + 285885231/100000000
 > 0.

b/2-c*sqrt(b) >= b/4-c^2.
```

Thus W increases and is unbounded. It is incorrect to read the decay in
the relative PNT error H as decay in the weighted allowance B. Equally,
growth of W alone is not a failure certificate for the actual test:
`C'-C/2` may be very small where W is large. An honest pricing decision
must examine their product. No endpoint value of W is multiplied by an
unidentified norm and declared to be the actual error.

There is also a precise scale-compatibility test. Fix any beta with
1/2<beta<1, and put a=1-beta>0. Completing a square gives

```text
-a*b+c*sqrt(b) = -a*(sqrt(b)-c/(2*a))^2 + c^2/(4*a)
              <= c^2/(4*a).

exp(beta*b) / (exp(b)*H(b))
 <= exp(c^2/(4*a)) / ((939/100)*b^r)
 -> 0 as b -> infinity.                              (4)
```

Consequently, an off-line exponential scale x^beta is not excluded by
this scalar PNT envelope at large x. More strongly, for b>=log(2), any
amplitude A0 satisfying

```text
abs(A0) <= (939/100)*(log(2))^r*exp(-c^2/(4*a))
```

makes `abs(A0*exp(beta*b)*cos(gamma*b)) <= exp(b)*H(b)` for every real
gamma. This is a scalar compatibility calculation. It is not an invented
prime-counting function, a claim that such a zeta zero exists, or a
counterexample using actual primes. It shows why the imported envelope
by itself cannot be treated as an exclusion of every beta>1/2. Additional
information about its pairing with the actual C is essential.

## Parameters and relation to the live routes

Equation (1) applies separately to the binding selected detector and to
each actual powered span, with that function's own C and support. In 3117,
increasing n changes both the function and the prime contribution. The
negative-qw tail theorem supplies no monotonicity or upper bound for B.
The symbolic stored support bound exp(112) is not assigned to arbitrary
rho-dependent constructions.

For delta=abs(Re(rho)-1/2)>0, t=Im(rho), delta<=1/16 and abs(t)>=1,
3116 already proves the necessary actual-correction cost

```text
C2 >= t^2*(1-4*delta)/(16*(2*pi)^2*delta).
```

This is a lower requirement, never an upper estimate for B or the tail.
A finite actual C2 upper bound may depend on rho, as permitted in 3117.
There is no evidence here for freezing C2, T, the prime cutoff or the
span coefficient as rho varies. The joint gate/tail and universal-zero
coverage duties remain open; no fixed coefficient floor is imposed as a
necessary condition on every possible successful coefficient sequence.

## Reproducible exact controls and evidence grade

Run in a Linux verification environment:

```text
python3 scripts/signed_arithmetic_pnt_feasibility_3123.py
```

The script uses Python Fraction arithmetic and independent formal log(p)
symbols. It compares a direct finite prime-power sum with piecewise exact
integration by parts on 21 polynomial-weight cases. These weights are
auxiliary algebra controls, not replacement detector functions. The cases
include a cutoff at a prime and at a prime power, repeated powers of 2,
vanishing/nonvanishing endpoints, an empty excluded prime band, and an
empty interval. Mutation controls require rejection of a missing endpoint,
the left-limit convention at the cutoff, duplicate inclusion of the cutoff
prime, and a missing Hermitian factor 2.

For example, on [2,3] with f(x)=(3-x)^2, the excluded-prime sum is zero,
since f(3)=0. The main integral is 2/3, the endpoint is 4-2*log(2), and
the signed derivative contribution is -14/3+2*log(2); they sum to zero.
The nonzero endpoint cannot be dropped. The script also checks the exact
square identities and positive rational remainder used above.

The retained receipt is
`results/3123_signed_arithmetic_pnt_feasibility.json`. It records the
individual controls, exact symbolic outputs and normalized hashes of the
script and cited project inputs. It does not certify the external PNT
theorem, the analytic derivation, an actual detector integral or a sign.
Those paper statements retain their stated evidence grade. No Lean source
changes or new axiom audits are involved; unchanged entries are not rebuilt.

The Linux ext4 run passes all 33 controls, including all 21 finite cases,
in about 0.004 seconds with 17039360 bytes of peak resident memory. Nine
normalized input hashes are retained. A separate isolated missing-input
test exits with code 1 and replaces an old PASS receipt with CONTROL-FAIL,
so an exception cannot leave stale successful evidence. No floating-point
special-function value or numerical detector sign enters these controls.

The initial mechanism-intake screen fired GAP on the words "error term".
The cited exponent/allowance exhibits 1590 and 1634 were reviewed. The
keyword firing is not evidence that B exceeds the actual margin. The
applicable older PNT analyses 215, 220 and 221 and the actual signed
physical remainder of 1939 were reviewed before making a route decision.

## Decision

```text
complete current-source partial summation:       PAPER-EXACT
cutoff and rational algebra controls:            EXACT-CONTROLS-PASS
Johnston-Yang PNT input:                         EXTERNAL, UNFORMALIZED
scalar envelope excludes off-line growth:        NO; scale compatible
actual weighted envelope budget (3):             UNPRICED
actual signed discrepancy-correlation estimate:  OPEN
same-function gate/tail intersection:            OPEN
RH:                                             UNPROVED
```

This review admits no new Lean campaign: there is no independent sign
estimate to formalize. It does not declare the weighted PNT method or
Route A/B impossible. The next mathematical input must control the actual
signed pairing in (1), or independently price (3), including its endpoint
and its rho dependence. Another identity, a wider finite prime band, or
growth of an envelope without its actual correlation factor cannot satisfy
that completion criterion.
