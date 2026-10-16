# Record 2709: use the existing high-shell separation in the geometric bound

Status: PAPER CANDIDATE + OLD-ROW SENSITIVITY; NO FAMILY REOPENING.

Named change: replace the height-blind geometric majorant in
`fullOrbit_span_multiplier_norm_le_height_pow_four` by a bound using the
ALREADY REQUIRED `2*abs(Im rho) <= abs(Im z)` in FourthOrderSpectralTail.
Owner, lambda, signed gate and support-derived prime domain stay unchanged.
Budget: source/paper derivation and one standard-library arithmetic pass over
2033's stored rows; no new integrals, no gate scan, no Lean build. Stop if no
registered gate row has a unit-proxy scalar compatibility improvement sufficient
to pass. A passing sensitivity row does not reopen the family: actual complete
owner, directed decay bounds, shell s and multiplicity m are still required.

## Derivation

Assume Re(rho),Re(z) in [0,1], y=abs(Im z)>=1 and
2*abs(Im rho)<=y. Every orbit point w in
{rho, conjugate(rho), 1-rho, 1-conjugate(rho)} has real part in [0,1] and
abs(Im w)<=y/2. Therefore:

```text
abs(Re(w-z)) <= 1 <= y
abs(Im(w-z)) <= 3*y/2
norm(w-z)^2 <= (13/4)*y^2
```

Set d=169/16. For P(z)=product_w(w-z), multiplicativity of the complex norm
gives `norm(P(z)) <= d*y^4`. Also the two spectral distances satisfy
`norm(z-rho)^2 * norm((1-conjugate(z))-rho)^2 <= d*y^4`.
Reflection preserves the strip and y. For positive lambda:

```text
norm(P(z)-lambda) <= (d+lambda)*y^4
```

Combining with the existing raw-square twelfth-order estimate gives the new
sufficient weighted tail budget:

```text
Lnew = d*(d+lambda)^2*(2*pi)^12*(q^n*C4*C2)^2
```

instead of `K^4*(K^4+lambda)^2*(2*pi)^12*(q^n*C4*C2)^2`.
This is a paper proof of a stronger geometric bound under the extra shell
separation already present in the FINAL tail interface. It does not replace
the old intermediate theorem, which lacks that hypothesis, for arbitrary z.
It has not been checked in Lean. Source-zero strip membership must be proved
when instantiating it.

## Scope correction to 2708

The 2033 P4b artifact uses the UNIT PROXY beta_s/m=1 and sampled decay constants,
not actual shell acceptance or a certified global bound. Its tau_inf is not
2708's actual A_n without supplying beta_s/m. The statements that those rows
have A_n>=1 must be read as proxy statements only. This candidate retains that
proxy for an honest same-row comparison; no source-zero conclusion follows.

## Controls and limits

`scripts/high_shell_geometry_sensitivity_2709.py` lifts each stored binary64
input as an exact rational and recomputes OLD and NEW prices in one pass.
It checks the recomputed old price against the stored tau reading as a
diagnostic of conventions, and gates new<=old on each registered gate row.
Exact rational arithmetic validates operations on the stored inputs, not the
truth of those inputs. The script reports no producer GO even if a proxy row
passes. The old P4b obstruction remains binding for its old named estimate.

Before pricing, the mechanism intake screen must be run on this sketch; fired
classes require checking their cited exhibits, not automatic acceptance or
rejection. This candidate is a geometric norm estimate rather than an identity
split claiming positivity or a P-only owner substitution.

## Recorded outcome

The intake screen fired zero classes. The WSL arithmetic pass completed with
16 registered gate rows, old-price replay differences below 1e-10, and
new<=old on every row. Three unit-proxy rows pass:

```text
gamma                owner N   convolution n   old proxy        new proxy
30.424876125859512    3         3               510701261.0823   0.2351626652
30.424876125859512    4         3               560491649.8489   0.2687424461
30.424876125859512    5         3               623222132.7652   0.3052795390
```

The improvement is about 2.0-2.2 billion times on these stored rows. It is an
algebraic sensitivity result, not measured new analytic accuracy. The sampled
C4/C2 values, under-approximate owner and synthetic source point are not
upgraded to certificates by this calculation. Source hash, all rows, controls,
and false producer/reopening/RH flags are in
`results/2709_high_shell_geometry_sensitivity.json`.

The bounded diagnostic therefore warrants investigating this stronger geometric
lemma and the directed complete-owner tail input, but does not satisfy the
binding complete-owner reopening gate. Do not launch the frozen-family scan or
the matrix/cell campaign on the strength of these three rows.
