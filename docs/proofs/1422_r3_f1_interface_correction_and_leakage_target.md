# 1422 - R3-F1 interface correction and the leakage target

Date: 2026-09-14.

Status: `FORMAL-SOURCE AUDIT / PROJECT CANDIDATE`; this record corrects the
route interpretation of record 1421.  It does not claim RH and does not claim
that F0 is solved.

## 1. The correction

Record 1421 proves on paper the following genuine geometric statement for the
archimedean Sonin space:

```text
u in S_lambda, a > 0
  => || P_S T_(-n*a) u || -> 0.
```

The actual R3-F0 source-leg question from record 1420 is different.  The
finite G8 trace is built from the cutoff factor on the ambient carrier,
precomposed with the source inclusion:

```text
J† B_n† G_S B_n J.
```

Its proposed limit therefore requires control of

```text
G_S^(1/2) B_infinity J,
```

not merely of a source-projected translation.  The committed source confirms
that `sourceInclusion` is the subtype inclusion into the ambient global
carrier (`CCM24FiniteSGramResponse.lean:41-43`), while the G8 cutoff pair
places the full boundary operator before the G8 middle kernel
(`C1G8AdjointShearGram.lean:440-454`).  No output `sourceSoninProjection` is
present in that source-leg definition.

Therefore the implication

```text
pointwise Sonin antiresonance -> F0 Hilbert--Schmidt
```

is invalid as stated.  The ambient component can still carry translated
energy, and the G8 middle operator has not been proved to annihilate it.

## 2. The corrected two-channel target

The new mathematical target is to establish an exact source/ambient split:

```text
B_infinity J
  = P_S B_infinity J + (I - P_S) B_infinity J.
```

The two pieces have different obligations.

### Channel S: compressed Sonin part

If `B_infinity` has a translation or integral-translation representation
compatible with the committed `T_b`, then record 1421 can control the
source-projected part through a tail estimate.  The desired collective
statement is a source-basis energy bound of the form

```text
sum_k || G_S^(1/2) P_S B_infinity J(e_k) ||^2 < infinity.
```

This is still stronger than pointwise convergence, but it is now attached to
the correct factor.

### Channel L: Sonin leakage

The complementary term is

```text
(I - P_S) B_infinity J.
```

It must be controlled by a new boundary/commutator inequality, for example a
factorization through the existing prolate remainder or through a trace-class
boundary crossing:

```text
sum_k || G_S^(1/2) (I - P_S) B_infinity J(e_k) ||^2 < infinity.
```

The old radial identities
`radialComplement_comp_negativeTranslation_comp_radialSupport_eq_zero` and
`radialSupport_comp_positiveTranslation_comp_radialComplement_eq_zero` only
give triangularity for one-sided translations.  They do not yet provide this
G8 global source-leg bound.  The leakage channel is therefore the real new
R3 obstruction exposed by the correction.

## 3. Why this correction is useful

It sharply separates two previously conflated statements:

```text
Sonin geometry kills source-projected translation tails       VALID
Sonin geometry makes the ambient G8 source leg trace-class    NOT SHOWN
```

The first is a genuine new lemma.  The second is exactly the F0 problem.  A
future proof may use the first only after exhibiting the required projection
factorization; otherwise it must estimate the ambient leakage directly.

This also gives a clean falsifier.  If one can produce an orthonormal source
sequence `(e_k)` for which

```text
sum_k ||G_S^(1/2) (I - P_S) B_infinity J(e_k)||^2 = infinity,
```

then the current ordinary-trace G8 route fails at F0 even though the
pointwise antiresonance lemma is true.

## 4. Corrected verdict

```text
record 1421 pointwise geometric lemma       PAPER-GREEN
direct F0 closure from that lemma           REJECTED (interface mismatch)
compressed channel S                         OPEN, conditional on factorization
ambient leakage channel L                    OPEN, decisive
F0 Hilbert--Schmidt limit                    OPEN
G8SameOwnerReadbackData                      NOT CONSTRUCTED
RH                                          NOT CLAIMED
```

The next admissible R3 move is not another generic convergence assumption.  It
is to derive, from the actual G8 definitions, either the missing projection
factorization or a trace-ideal estimate for Channel L.  Until that is done,
the route is still RH-reachable in logic but analytically open.
