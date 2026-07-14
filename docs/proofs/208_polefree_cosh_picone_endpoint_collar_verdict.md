# Pole-Free Cosh-Picone And Endpoint-Collar Verdict

Date: 2026-07-13

Status: the global `C=cosh(x/2)` Picone/minimum-kernel lower bound is
rigorously negative at the center, and the positive endpoint collar of the
source potential shrinks like `exp(-4 sqrt(c))`. A detector translated into one
such collar is prime-free at the certified and asymptotic cutoffs, so Proof 113
precludes it from also being the required negative M4 detector. A two-collar
construction is not covered, but it has no determining theorem or same-object
finite-S read-off. RH remains unproved.

## 1. Result First

```text
pole-free jump-form identity:              accepted source theorem
global cosh-Picone complete-graph bound:   rejected by Arb
endpoint collar root formula:              exact in the last indicator cell
endpoint collar roots:                     Arb-certified
single translated collar detector:         prime-free / rejected by Proof 113
two-collar determining family:              not proved
new Lean owner:                             none
unconditional RH:                          unproved
```

The point is not merely that the first estimate is numerically weak. The exact
potential shows that the positive wall near an endpoint is logarithmic, while
the negative prime degree is of order `sqrt(c)`. The resulting support budget
collapses exponentially in `sqrt(c)`.

## 2. Source Form

Let `c=exp(2a)` and let

```text
A_tilde = A_a-W_(0,2).
```

The source proves, on the common closed form domain,

```text
<A_tilde v,v>
 = (1/2) integral integral J(x-y)|v(x)-v(y)|^2
   + sum_(q=p^m<=c) Lambda(q)/sqrt(q)
       integral |v(x+log q)-v(x)|^2
   + integral kappa_a(x)|v(x)|^2,

J(t)=exp(-|t|/2)/(1-exp(-2|t|)) > 0,

kappa_a(x)
 = -(1/2)log(a^2-x^2)-log(2*pi)-EulerGamma-m_1(x)
   -sum_(q=p^m<=c) Lambda(q)/sqrt(q) w_q(x).
```

Primary source: Zenodo 20682834, source file
`RIEMANN_pole_note_v3_13jun.tex`, lines 187-203 for the statement and lines
250-267 for the prime-degree and endpoint terms:

```text
https://zenodo.org/records/20682834
```

All jump terms are nonnegative. The only uncontrolled sign in this
representation is the potential.

## 3. Cosh-Picone Bound

Put

```text
C(x)=cosh(x/2),
v=C*u.
```

The jump-form ground-state transform has residual potential

```text
(A_tilde C)(x)/C(x),
```

and pole neutrality becomes `integral C^2 u=0`. Replacing the transformed
complete graph by its global minimum gives the candidate weighted gap

```text
gamma_C
 = (a+sinh(a))*exp(-a)
   / ((1-exp(-4a))*cosh(a/2)^2).
```

At the center the residual has the exact closed form

```text
(A_tilde C)(0)/C(0)
 = -a-log(1-exp(-a))-log(2*pi)-EulerGamma
   -sum_(q=p^m<=exp(a)) log(p)*(1+1/q).
```

Therefore one negative center value rejects this proposed global sufficient
bound. Arb proves:

```text
+--------+----------------------------------+
| c      | gamma_C+(A_tilde C)(0)/C(0)     |
+--------+----------------------------------+
| 5      | -2.990690444751712665240884...  |
| 13     | -5.318300030556374677296857...  |
| 29     | -8.774871191200052758035065...  |
| 53     | -11.45437533858752164140438...  |
| 100    | -13.89920329008409514888845...  |
| 1000   | -40.61814965700580065273259...  |
| 10000  | -105.0197385780121558718194...  |
+--------+----------------------------------+
```

The displayed Arb radii are below `2.1e-23`. This rejects only the
complete-graph minorant proof. It does not prove that the full jump geometry
cannot control the potential.

## 4. Exact Endpoint Cell

Write `x=a-d`. In the final indicator cell,

```text
0 < d < min(log 2, min_(q<c) log(c/q)),
```

the right translation indicator is zero for every prime power, the left
indicator is one exactly for `q<c`, and a possible endpoint event `q=c` is
absent away from the endpoint. Define

```text
F(t)=integral_0^t (J(s)-1/(2s)) ds,
M(c)=sum_(q=p^m<c) Lambda(q)/sqrt(q).
```

Then the potential is exactly

```text
kappa_a(a-d)
 = -(1/2)log(d(2a-d))-log(2*pi)-EulerGamma
   -F(d)-F(2a-d)-M(c).                         (E.1)
```

Differentiating (E.1) cancels all artificial singular pieces:

```text
d/dd kappa_a(a-d) = J(2a-d)-J(d) < 0,          (E.2)
```

because `J` is strictly decreasing and `0<d<a`. Hence the final cell contains
at most one root `d_c`, and `kappa_a(a-d)>=0` precisely on the endpoint side of
that root whenever the inner-cell value is negative.

The root equation is

```text
-log d_c
 = 2M(c)+log(2a-d_c)+2log(2*pi)+2*EulerGamma
   +2F(d_c)+2F(2a-d_c).                        (E.3)
```

Using the closed form for `F` from the source implementation,

```text
F(2a)=(1/2)log(2/a)+pi/4+o(1),
F(d_c)=o(1),
```

so

```text
-log d_c = 2M(c)+log 4+pi/2+2log(2*pi)+2*EulerGamma+o(1).
```

Partial summation and the unconditional prime number theorem give
`M(c)=2 sqrt(c)+o(sqrt(c))`. Thus

```text
d_c = exp(-4 sqrt(c)+o(sqrt(c))).               (E.4)
```

This is a scale identity, not a fitted empirical law.

## 5. Certified Collar Widths

Arb evaluates (E.1) at log-distances `y_c-1e-20` and `y_c+1e-20`, where
`y_c=-log d_c`. The two enclosures are respectively negative and positive,
with radii at most `3e-29` in the first run and `3e-33` in the second:

```text
+--------+----------------------------+----------------------+
| c      | d_c                        | -log(d_c)            |
+--------+----------------------------+----------------------+
| 5      | 1.329283940429747568e-4    |   8.925699965381... |
| 13     | 2.510661481147276381e-7    |  15.197549394229... |
| 29     | 1.806978651833889988e-10   |  22.434194732548... |
| 53     | 5.505941448088156319e-14   |  30.530363529453... |
| 100    | 1.305858704345913517e-18   |  41.179670838519... |
| 1000   | 1.307958144795467461e-56   | 128.676297954535... |
| 10000  | 1.313913040134127617e-175  | 402.679381535587... |
+--------+----------------------------+----------------------+
```

The stable implementation evaluates `d(2a-d)` directly. Forming
`a^2-(a-d)^2` loses about `-log10(d)` decimal digits and already gives a visible
error at `c=10000`.

## 6. Why The Single-Collar Detector Does Not Close RH

Translating one root into one endpoint collar preserves its convolution square
up to the standard translation cancellation. But its support diameter is at
most `d_c`. At every certified cutoff above, and asymptotically by (E.4),

```text
d_c < log 2.
```

Consequently its convolution square vanishes at every nonzero prime-log shift:

```text
F(log(p^m))=F(-log(p^m))=0.
```

It is a prime-free test. Proof 113 establishes on the same M4 complement that
every nonzero prime-free, pole-neutral Q-root has

```text
QW(g,g) >= ||xi||^2 > 0.
```

Therefore the translated collar root cannot also be the strict negative
detector required to exclude an off-critical zero. The positivity obtained
from the endpoint wall is positivity of a restricted test class already on the
sign-good side of the corrected CC20 identity.

This argument does not rule out support in both endpoint collars. Such a root
has a large convex hull and may create cross-correlations close to `2a`.
However, no checked theorem proves that the two-collar class is determining for
the zeta divisor, and no same-object finite-S trace formula identifies its
surviving top-edge correlations with the active crossing operator sum. It is a
new route, not a completion of the single-translation argument.

The existing fixed-window Yoshida API also does not repair the gap. It
interpolates a fixed finite node set in an arbitrary residual window and only
then chooses a convolution count. It does not prove the coupled estimate needed
when the allowed window itself shrinks as `exp(-4 sqrt(c))` while the nearby
zero radius grows.

## 7. Reproduction

The reconnaissance run needs `mpmath`; the interval run additionally needs
`python-flint`:

```text
python3 -B docs/proofs/208_polefree_cosh_picone_probe.py \
  --cutoff 5 13 29 53 --grid-size 81 --dps 80

python3 -B docs/proofs/208_polefree_cosh_picone_probe.py \
  --cutoff 5 13 29 53 --certify-only --arb-bits 768

python3 -B docs/proofs/208_polefree_cosh_picone_probe.py \
  --cutoff 100 1000 10000 --certify-only --arb-bits 1024
```

Related project evidence:

```text
docs/proofs/063_polefree_constraint_survivor.md
docs/proofs/064_polefree_antimax_rejection.md
docs/proofs/113_primefree_m4_negative_detector_impossible.md
ConnesWeilRH/Source/CC20YoshidaConvolution.lean
```

## 8. Verdict

```text
cosh/minimum-kernel proof: rejected
endpoint-wall scale: exp(-4 sqrt(c)+o(sqrt(c)))
single translated endpoint detector: prime-free and sign-incompatible
two-collar detector theorem: absent
finite-S semilocal sign gate: unchanged
unconditional RH: unproved
```
