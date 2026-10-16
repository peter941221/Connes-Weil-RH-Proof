# Record 2708: exact same-owner joint acceptance contract

Status: SOURCE-ANCHORED PAPER REDUCTION; NO NEW LEAN THEOREM OR REOPENING.

Budget: one source/paper pass within 60 minutes, no numerical runs, no builds,
no generated Lean modules. Completion: state all owner/quantifier prerequisites,
the simultaneous inequalities, and the precise obstruction under the existing
tail method. The contract below completes that task, not its open inequalities.

## 1. Objects and dependencies

An owner is the actual function to which every estimate applies. Fix a genuine
source zero rho with Re(rho) > 1/2. A synthetic point is insufficient. Define:

```text
base, correction : compact-log test functions
n                : convolution count
g_n              : (selectedOwner base correction n).sourceTest
u_n              : fullFunctionalEquationOrbitAnnihilator g_n rho
lambda           : strictly positive real coefficient
v                : annihilatorDetectorSpanVector u_n g_n lambda
                   (the span u_n - lambda * g_n)
m                : xiMultiplicity(rho), positive zero multiplicity
s                : n0 in the shell-tail consumer, distinct from n
S_s              : the finite source-zero prefix in shells 0 through s
T                : high-frequency threshold
Cspec            : spectralMultiplicityConstant
K                : 3 + norm(rho)
C4, C2           : certified base/correction strip-decay constants
q                : certified base contraction bound above T
epsilon          : positive tail tolerance selected after compatibility holds
```

Use the exact captured/source definitions and their normalization. The four-point
construction is a candidate same-object contradiction for v, not an identity
between v and the original healthy detector g_n. The existing final consumer is
`riemannHypothesis_of_four_point_span_contradiction_producer`.

Quantifiers: for EVERY genuine right off-line source zero, produce such a test
and compatible parameters. Base/correction may depend on rho and a chosen
finite prefix. Their constants are then fixed before choosing n and lambda.
If the shell prefix is enlarged, its interpolation conditions must be rebuilt
or proved preserved; moving s to improve a factor is not free. Lambda may
depend on n. Constants need not be globally uniform in rho, but the argument
must work for every rho, including arbitrarily small positive Re(rho)-1/2.

## 2. Prerequisites before the two scalar inequalities

P1. g_n vanishes on the actual `cc20TripleFiniteVanishingSet` (three specified
evaluation points, not an assertion of third-order vanishing at one point).
The annihilator transport then supplies the same property for u_n and v.

P2. For every node w in `sourceFunctionalEquationOrbit rho`, the actual g_n
has `laplaceAt g_n (w - 1/2) = negativeSourceOrbitValue rho w`.
For each zero z in S_s outside that orbit, its convolution square has transform
zero at z-1/2. The prefix must contain rho. The formal transport then gives
the shell prefix bound `prefix(v.square) <= -m * lambda^2` after the finite-set
to-shell-prefix identification; that identification is still required.

P3. C4,C2 are nonnegative. The three strip bounds in
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q` hold for the exact
base and correction: base contraction by q above T, quartic base decay, and
quadratic correction decay. For geometric improvement in n one needs q < 1
(and q >= 0). The theorem itself only assumes q >= 0 and the supplied bounds.

P4. `T <= 2^(s+1)` and `2*abs(Im rho) <= 2^(s+1)`. The tail certificate is
on ALL z with Re(z) in [0,1], abs(Im z) >= T, >= 1, and >= 2*abs(Im rho).
It is not a sampled imaginary-axis bound or a one-sided finite-xi integral.

P5. Gate coefficients are the actual complete ICgate values for u_n,g_n.
Use their actual support-derived visible-prime domain and signed cancellation;
a truncated/fixed prime book or a different narrow-root test is not valid.

## 3. Exact gate inequality

Define real coefficients by the actual gate evaluations:

```text
D_n = ICgate(u_n.square)
B_n = ICgate(u_n.involution * g_n) + ICgate(g_n.involution * u_n)
C_n = ICgate(g_n.square)
```

Here `*` denotes convolution, not pointwise multiplication. The checked
parabola identity gives:

```text
G_n(lambda) = D_n - B_n*lambda + C_n*lambda^2 <= 0.       (G)
```

The support premise of `annihilator_span_gate_eq_parabola` must hold for both
functions. Together with P1, (G) implies `qw(v) >= 0`.

## 4. Tail inequality using the existing sufficient bound

The current q-based theorem produces the tail certificate if:

```text
L_n(lambda) = K^4 * (K^4 + abs(lambda))^2 * (2*pi)^12
              * (q^n * C4*C2)^2

L_n(lambda) < epsilon^2.                                (T1)
4 * epsilon^2 * Cspec * (3/4)^s < m*lambda^2.             (T2)
```

Under P2-P4, these give `qw(v) < 0`. The epsilon-free compatibility condition
is therefore:

```text
4*Cspec*(3/4)^s * L_n(lambda) < m*lambda^2.               (J)
```

This is equivalent to existence of positive epsilon satisfying T1,T2 when
m>0 and lambda>0: choose epsilon squared strictly between their nonnegative
lower and positive upper endpoints. This equivalence concerns this sufficient
tail method; failure of (J) does NOT establish failure of the actual tail.

## 5. A directly comparable pair of lambda ranges

For fixed n,s and the previously fixed owner/constants, set:

```text
A_n = [4*Cspec*(3/4)^s * K^4 * (2*pi)^12
        * (q^n*C4*C2)^2] / m
```

Since lambda>0, (J) becomes:

```text
A_n * (1 + K^4/lambda)^2 < 1.                            (R)
```

If A_n>=1, no positive lambda passes this certificate. If 0<A_n<1, (R)
is exactly:

```text
lambda > Ltail_n
Ltail_n = K^4 * sqrt(A_n) / (1 - sqrt(A_n)).
```

If A_n=0, every positive lambda passes this scalar compatibility check;
the owner/strip/prefix prerequisites still apply.

On the registered vertex branch ONLY, assume C_n>0, D_n>0, B_n>0 and
Delta_n = B_n^2 - 4*C_n*D_n >= 0. The positive gate interval is:

```text
Lminus_n = (B_n - sqrt(Delta_n)) / (2*C_n)
Lplus_n  = (B_n + sqrt(Delta_n)) / (2*C_n)

gate: lambda in [Lminus_n, Lplus_n]
tail: lambda in (Ltail_n, infinity)
joint acceptance: Lplus_n > Ltail_n.                    (I)
```

The gate interval is closed; the tail threshold is strict. The degenerate
Delta_n=0 case is allowed if its single positive coefficient exceeds Ltail_n.
Other D/B/C sign branches use (G) directly; they are not ruled out by this
vertex-branch formula. Passing at the vertex is sufficient, not necessary:
the tail factor decreases with positive lambda, so a non-vertex coefficient
inside the gate interval can pass when the vertex does not. This observation
does not evade recorded rows with A_n>=1, where NO coefficient can pass.

The exact obstruction comparison is now explicit:

```text
gate absent                -> no same-method candidate at that n
gate present, A_n >= 1     -> no lambda pays the existing tail bound
gate present, 0<A_n<1      -> compare Lplus_n with Ltail_n
nonempty intersection     -> scalar compatibility only; prove P1-P5
P1-P5 + intersection      -> existing consumers yield a contradiction
all genuine rho covered   -> final RH consumer applies
```

The map-103 P4b rows have no paired rows in their UNIT-PROXY convention;
their recorded gate rows have a proxy tail floor above budget, and later
closing rows lose the gate. P4b does not supply beta_s/m or certified strip
constants, so its proxy floor must not be identified with actual A_n. This remains a
scoped certificate obstruction, not a global impossibility result. No new
owner, new q bound, or improved analytic estimate has been supplied here.

## 6. Why coefficient scaling does not itself solve the gap

The existing 2174 consumer instead assumes a valid tail certificate at
`epsilon=lambda*eta` and accepts `4*eta^2*Cspec*(3/4)^s < m`. It genuinely
cancels lambda squared in the consumer. But setting eta=epsilon/lambda in
the old estimate simply reproduces (R); it gives no sharper bound. A useful
new proof must produce a stronger estimate for the actual function, not
rename the same constant. Its eta and T dependencies must be disclosed.

## 7. Outcome and next decision

The joint acceptance contract is now explicit. The open mathematical target
is an owner-matched gate interval intersecting an affordable tail range under
P1-P5, for the source-zero quantifiers. Record 2708 does not find a changed
hypothesis satisfying the reopening rule and does not authorize a scan,
entry campaign, or build. A subsequent candidate must identify which of
A_n, the gate interval, or the valid tail method changes and why the scoped
obstruction no longer applies. The scalar compatibility reduction above is
paper algebra only; it has not been added as a checked Lean theorem.

## Source anchors

- `C1FourPointSpanGateCertificate.lean`,
  `annihilator_span_gate_eq_parabola` and vertex-branch lemmas.
- `C1OrbitWindowSemiLocalGate.lean:57`, gate definition and nonnegativity bridge.
- `C1FourPointSpectralPrefixTransport.lean:330`, finite-prefix transport premises.
- `C1SpectralTailBound.lean:30`, full-strip FourthOrderSpectralTail definition.
- `C1FourPointHighShellTail.lean:666`, q-based sufficient tail theorem.
- `C1FourPointContradictionAssembly.lean:127`, tail-to-negativity consumer;
  `:154`, coefficient-scaled consumer; `:253`, quantified RH consumer.
- `docs/map/103_four_point_same_span_three_cut_campaign.md`, P4b scoped outcome.
