# Proof 249: Global Critical-Line Contraction

Date: 2026-07-14

Status: good lower producer and a new detector-specific route, but not an RH
proof.  Exact resonance, orbit-value preservation, raw/centered coordinate
transport, critical-line transform contraction, and actual `L1` contraction
are axiom-clean in Lean.  Correct support accounting rejects Proof 248's
Fourier-grid correction.  The remaining decisive theorem is a quantitative
finite-S post-Q remainder bound with `p^(-m)`, rather than merely
`p^(-m/2)`, prime-power decay.  The Burnol all-zero identity and the
same-object semilocal trace identity are also not yet Lean theorems.

## 1. Result First

The active strategy can avoid a uniform sign theorem on the three-row
subspace.  A small complete finite-S remainder on the Yoshida detector from a
hypothetical off-critical zero suffices.

The new route is:

```text
hypothetical off-critical zero rho
             |
             v
resonant compact base, exactly one on the centered rho orbit
             |
             | convolution powers
             v
orbit contribution remains -2, while critical-line graph energy -> 0
             |
             v
detector-specific bound |E_S| < 1/2
             |
             v
positive semilocal trace gives WeilValue > -1/2
             |
             v
Burnol zero sum gives Re(WeilValue) < -7/4
             |
             v
contradiction
```

The constants `1/2` and `7/4` provide convenient margins.  Any two separated
bounds work.

## 2. DFT Rejection

Proof 248 originally generated the low Fourier rows from the correction
window alone.  That is not the support of the final test.  The exact Lean
support law is

```text
final support
  = (n + 1) copies of the base support
      + one correction support.
```

The source statement is
`UnscaledYoshidaSelectedOwner.lean:751-753`.  The corrected probe computes

```text
base_span       = (n + 1) * one_base_span
correction_span = chosen correction span
final_span      = base_span + correction_span
```

at `248_translated_bump_correction_probe.py:145-147`, then generates the
Fourier rows from `final_span`.

The self-consistent result is bad:

```text
+---+-------------+------+----------------+------------------+
| N | constraints | rank | residual       | full row rank    |
+---+-------------+------+----------------+------------------+
| 1 |          26 |   20 | 1.406          | false            |
| 2 |          40 |   29 | 1.408          | false            |
| 3 |          54 |   38 | 1.405          | false            |
| 4 |          66 |   45 | 1.401          | false            |
+---+-------------+------+----------------+------------------+
```

The default run remains rank deficient through `N=10`; the script refuses to
fit an assembled-tail slope at
`248_translated_bump_correction_probe.py:310`.

A separate 100-digit calculation of the exact exponential/Vandermonde core
gave minimum solution norms

```text
+---+------+----------------+-----------------------+
| N | rows | sigma_min      | minimum solution norm |
+---+------+----------------+-----------------------+
| 1 |   26 | 1.19e-18       | 8.19e17               |
| 2 |   40 | 2.94e-24       | 3.08e23               |
| 3 |   54 | 1.45e-30       | 3.96e29               |
| 4 |   66 | 1.05e-35       | 1.06e34               |
+---+------+----------------+-----------------------+
```

The proposed `0.04^N` contraction cannot pay that inverse growth.  A successor
needs a different support law.

## 3. Exact Resonant Contraction

Write the centered hypothetical zero as

```text
u = rho - 1/2 = delta + i gamma,
delta != 0.
```

Let a compact smooth seed `h` have bilateral Laplace transform `H` equal to
one on the complete centered orbit

```text
{+delta + i gamma, -delta + i gamma,
 +delta - i gamma, -delta - i gamma}.
```

Choose a translation `ell` satisfying

```text
ell * gamma = 2*pi*N
```

for an integer `N`, and define

```text
h_ell(x)
  = [h(x-ell) + h(x+ell)] / [2 cosh(ell*delta)].       (C.1)
```

Translation gives the exact transform

```text
H_ell(v)
  = H(v) cosh(ell*v) / cosh(ell*delta).                (C.2)
```

At each centered orbit point, the imaginary phase is an integral multiple of
`2*pi`, so

```text
H_ell(+/-delta +/- i gamma) = 1.                      (C.3)
```

On the complete imaginary axis,

```text
|H_ell(it)|
  <= ||h||_1 / cosh(ell*|delta|).                     (C.4)
```

The function itself satisfies the same bound:

```text
||h_ell||_1
  <= ||h||_1 / cosh(ell*|delta|).                     (C.5)
```

Since `delta != 0`, a sufficiently large resonant integer makes the right side
any prescribed `q` in `(0,1)`.  A zero close to the critical line requires a
large support span.  The bound still covers the complete `t` axis and adds no
Fourier control rows.

The raw source coordinate is recovered by

```text
raw(x)=exp(-x/2) h_ell(x).                             (C.6)
```

Multiplication by the existing half-density factor sends `(C.6)` back to
`h_ell`, so the selected source root sees the contraction on the
critical line `Re(s)=1/2`.

## 4. Reproducible Diagnostic

The probe implements `(C.1)--(C.4)`.  Its resonant-shift selection is at
`249_global_critical_contraction_probe.py:68-84`; the analytic contraction and
support accounting are at lines `133-143`.

Default synthetic zero `rho=0.4+14.134725...i`:

```text
centered_distance              = 1.000000000000e-01
resonant_shift                 = 1.644728525206e+01
support_span                   = 3.358771768469e+01
analytic_critical_contraction  = 4.587196890437e-01
sampled_critical_contraction   = 3.719603398958e-01
orbit_residual                 = 3.846e-16
```

Near-line synthetic zero `rho=0.499+14.134725...i`:

```text
centered_distance              = 1.000000000000e-03
resonant_shift                 = 1.604721615134e+03
support_span                   = 3.210136377448e+03
analytic_critical_contraction  = 4.760953636145e-01
sampled_critical_contraction   = 3.846282236041e-01
orbit_residual                 = 8.083e-16
```

These numbers verify the implementation and expose the support cost.  They do
not prove the finite-S estimate.

## 5. From `L1` Contraction to Graph-Energy Contraction

Let `c` be the centered finite correction, fixed after selecting the nearby
zero radius, and put

```text
g_n = h_ell^(convolution n+1) * c.                    (C.7)
```

Young's inequality and `(C.5)` give

```text
||g_n||_2 <= q^(n+1) ||c||_2.                         (C.8)
```

The Fourier form is stronger.  For each nonnegative Sobolev weight `w(t)`,

```text
integral w(t) |g_n_hat(t)|^2 dt
  <= q^(2n+2) integral w(t) |c_hat(t)|^2 dt.          (C.9)
```

The same exponential contraction holds in each fixed Sobolev graph
norm needed by the post-Q form.

For the genuine Q-root relation from Proof 217,

```text
g_n = (d/dx + 1/2) xi_n.
```

The inverse Fourier multiplier has norm at most `2`, hence

```text
||xi_n||_2 <= 2 ||g_n||_2.                            (C.10)
```

The correction norm may be large, but it is fixed before the final convolution
count.  Equations `(C.8)--(C.10)` still tend exponentially to zero.

## 6. Smallness Criterion

Let `P_S(F)` be the genuine positive semilocal trace and let `E_S(F)` be the
same-object post-Q remainder.  The required bookkeeping identity is

```text
WeilValue(F) = P_S(F) - E_S(F),
P_S(F) >= 0.                                           (C.11)
```

Proof 224 gives the mathematical direct-trace split
`R_a-R=(E_a-E)-(B_a-B_0)` at lines `96-102` and defines the exact
nested-complement term at lines `183-193`.  Proof 217 fixes the source/pre-root
ownership `g=(d/dx+1/2)xi`; its equations `(Q.1)--(Q.3)` show why the prime
form acts on `g` while the regular remainder acts on `xi`.

The old route tried to prove

```text
E_S(F) <= 0
```

for all vectors satisfying the route rows.  The new route needs the following
bound on detector `(C.7)`:

```text
|E_S(F_n)| < 1/2.                                     (C.12)
```

Then `(C.11)` gives

```text
Re(WeilValue(F_n)) > -1/2.                            (C.13)
```

Proof 238 makes the centered orbit contribution `-2`, cancels
the selected nearby zeros, and supplies a summable far-zero tail.  Choosing
that tail below `1/4`, the Burnol zero-side identity would give

```text
Re(WeilValue(F_n)) < -7/4,                            (C.14)
```

contradicting `(C.13)`.  A detector-specific norm estimate can replace the
stronger uniform sign theorem.

## 7. The Decisive Quantitative Gate

Let the final centered source root be supported in `[-B,B]`.  Its square can
see only prime powers with

```text
p^m <= exp(2B).                                       (C.15)
```

A sufficient finite-S theorem has the shape

```text
|E_S(F_n)|
  <= C (1+B)^d
       [sum_(p^m <= exp(2B)) m^r p^(-m)]
       ||g_n||_(H^s)^2.                               (C.16)
```

No prime number theorem is needed after the full `p^(-m)` gain.  Prime powers
form a subset of the positive integers, so the sum in `(C.16)` is bounded by

```text
sum_(k <= exp(2B)) (log_2 k)^r / k
  = O((1+B)^(r+1)).                                   (C.17)
```

The support radius in `(C.7)` grows linearly in `n`.  Combining
`(C.9)`, `(C.16)`, and `(C.17)` gives

```text
|E_S(F_n)| <= fixed_constant * polynomial(n) * q^(2n+2) -> 0.  (C.18)
```

This would close `(C.12)`.

The weaker decay is not enough.  Taking absolute operator norms with only
`p^(-m/2)` gives

```text
sum_(p <= exp(2B)) p^(-1/2),                          (C.19)
```

which has exponential support growth.  A Paley-Wiener contraction preserving
an evaluation at distance `|delta|<1/2` supplies exponential rate `|delta|`
per support radius.  The absolute `p^(-m/2)` majorant cannot close the route.

Proof 228 supplies the missing half-power for the endpoint chirp:

```text
Euler amplitude             p^(-m/2)
oscillatory operator norm   p^(-m/2)
product                     p^(-m).                   (C.20)
```

See `228_euler_chirp_operator_norm_compactness.md:153-165`.

Proof 229 estimates the cell interiors in Hilbert-Schmidt norm and keeps
`O(p^(-m/2))`; see lines `214-225`.  The next theorem must retain
their fast phase and prove the parameter-uniform Fourier-integral estimate

```text
|| integral_0^(log p)
     A_(p,m)(x-y,t)
     exp(2*pi*i*p^m*exp(x-y+t)) dt ||_(L2 -> L2)
  <= C poly(m) p^(-m).                                (C.21)
```

The proposed proof is a `TT*`/nonstationary-phase estimate after
`u=exp(x)`, `w=exp(-y)`.  The mixed phase becomes `p^m exp(t) u w`; the same
Plancherel mechanism as Proof 228 contributes
`p^(-m/2) exp(-t/2)`.  Proof 229's amplitude already contributes the other
`p^(-m/2)`, and the `t` integral is uniformly finite.  Graph inverses are
uniform because the existing Neumann ratio satisfies
`eta <= 2*sqrt(2)/3 < 1`.

This estimate is the route's current death test:

```text
+--------------------------------------+-------------------------------+
| quantitative verdict                 | route consequence             |
+--------------------------------------+-------------------------------+
| only p^(-m/2) after full dressing     | reject this contraction route |
| poly(m) p^(-m), polynomial in B       | detector smallness closes     |
| hidden exponential dependence on B   | reject unless rate is smaller |
+--------------------------------------+-------------------------------+
```

## 8. Lean Evidence

Production declarations:

```text
ConnesWeilRH/Source/CC20YoshidaCriticalContraction.lean
  line 32   translate
  line 50   laplaceAt_translate
  line 90   centeredPair
  line 114  laplaceAt_centeredPair
  line 155  exp_mul_I_eq_one_of_mul_eq_nat_two_pi
  line 165  centered_exponential_sum_eq_two_cosh_of_phase
  line 207  l1Mass_translate_eq
  line 216  l1Mass_centeredPair_le
  line 288  norm_laplaceAt_centeredPair_mul_I_le
  line 346  laplaceAt_centeredPair_eq_one_of_phase
  line 361  laplaceAt_centeredPair_eq_one_on_fourPointOrbit
  line 435  laplaceAt_rawOfCentered
  line 447  laplaceAt_rawOfCentered_critical
  line 458  norm_laplaceAt_raw_centeredPair_critical_le
```

The import-facing audit is

```text
ConnesWeilRH/Dev/CC20YoshidaCriticalContractionAudit.lean
```

The isolated WSL build completed `3498` jobs.  Each audited declaration
reported only

```text
propext
Classical.choice
Quot.sound
```

with no `sorryAx` or project axiom.

## 9. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/248_translated_bump_correction_probe.py

python3 -B docs/proofs/249_global_critical_contraction_probe.py

python3 -B docs/proofs/249_global_critical_contraction_probe.py \
  --target-real 0.499

flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CC20YoshidaCriticalContraction \
  ConnesWeilRH.Dev.CC20YoshidaCriticalContractionAudit
```

Primary source context:

```text
Burnol, On the Sonine Spaces associated by de Branges to the Fourier Transform
https://arxiv.org/pdf/math/0208121

Connes--Consani, Weil Positivity and Trace Formula, the Archimedean Place
https://arxiv.org/abs/2006.13771

Connes--Consani--Moscovici, Zeta Zeros and Prolate Wave Operators
https://arxiv.org/abs/2310.18423
```

Burnol supplies the archimedean Sonin evaluator kernel, and CCM24 supplies the
semilocal transport.  Neither source proves `(C.16)` or computes the Euler
metric kernel difference needed here; `(C.16)` is a new project obligation.

## 10. Route Judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| support-coupled translated-bump DFT repair     | rejected                 |
| exact resonant orbit preservation              | accepted in Lean         |
| global critical-line transform contraction     | accepted in Lean         |
| actual centered-pair L1 contraction            | accepted in Lean         |
| negative-owner integration                     | not yet assembled        |
| graph-energy contraction after powers          | mathematical consequence |
| detector-specific remainder strategy           | viable conditional route |
| full p^(-m) dressed FIO estimate                | open, decisive           |
| Burnol all-zero identity in Lean                | open                     |
| same-object finite-S trace identity in Lean     | open                     |
| RH                                              | unproved                 |
+------------------------------------------------+--------------------------+
```
