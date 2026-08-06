# Proof-717: the outer channel `(I−R)∘D` is numerically non-zero; the sole escape is the Sonin-band intersection

Date: 2026-08-06
Status: new-math verdict — the outer channel of the metric wall is **numerically
decided**: it does not vanish on the full radial carrier and exceeds 1 for more
than one prime. This leaves exactly one way Gate-3U can still close (band-limited
Sonin intersection), now stated precisely.
Branch: `proof/gate3u-completed-readout`
RELATED: `814_wall_estimate_math_design.md`, `815_rh_route_conditional_boundary.md`

## 1. The object and the proven identity we lean on

On the carrier, the metric dual coframe is (`CCM24FiniteSCoframeResponse.lean:37,43,52`):

```
D = finiteEulerMetricCoframe = T†∘(T∘J∘G⁻¹),    J†∘D = id  (proven)
```

Guard/endpoint equivalence (`CCM24FiniteSEndpointContractionGuard.lean:245`,
channel-split `CCM24FiniteSPhysicalCancellationChannelSplit.lean:84-101`):

```
forward + physicalLeakage = 0  ⟺  OuterCh + BandCh = 0
OuterCh = (I−R)∘D
BandCh  = forward + (R−R₀)∘D
```

with `(I−R)`, `R`, `R−R₀` (source Sonin band) mutually orthogonal projections.
So the two channels live in mutually orthogonal ambient subspaces, and

```
OuterCh + BandCh = 0  ⟺  OuterCh = 0  AND  BandCh = 0        (Pythagoras)
```

## 2. New numeric fact: `(I−R)∘D` is nonzero (fidelity-verified)

`815_outer_channel_small_probe.py` builds the true metric coframe, validates the
construction by checking the **proven** identity `J†∘D = id`, then measures the
outer channel on the standard radial carrier. On a small well-conditioned grid
the fidelity is exact:

```
primes   ||J† D|| (must be 1)   ||(I−R)∘D|| outer channel
 {2}         1.0000                 0.79 – 0.92     (< 1)
 {2,3}       1.0000                 1.29 – 1.55     (> 1)
 {2,3,5}     1.0000                 1.56 – 1.63     (> 1)
```

`||(I−R)∘D|| > 1` for more than one prime, independent of `log λ`. Because the
construction passes the exact biorthogonality checks, this is a definitive
statement: **the outer channel is not zero on the full radial carrier**, and on
that carrier the outer channel alone already has norm > 1.

## 3. The precise escape: only the band-limited Sonin carrier can save it

Since `OuterCh` and `BandCh` are orthogonal, the only way the cancellation can
hold is if the metric coframe maps the **true source Sonin carrier** back into
radial support, so `(I−R)∘D` vanishes there:

```
D |_{sourceSoninCarrier}  ⊆  range(R)
    ⟺  (I−R)∘D·u = 0  for every u in the true Sonin carrier (log radial ∩ Fourier band-limited)
```

The grid probe tests the **all-of-radial** carrier, which is *too big*: it
includes high-frequency radial functions that the true Sonin carrier (band-limited
into the Fourier interval) excludes.  So the numeric non-vanishing on the big
carrier does **not** contradict Gate-3U *provided* the band-limited/band notion
cut those frequencies.  This is precisely the genuine new-math content: whether
the metric coframe `D` compresses into radial support **on the Fourier/Sonin-band
carrier**.

## 4. Second probe: the band-limited Sonin carrier does NOT rescue it

`816_outer_channel_sonin_carrier_probe.py` builds the outer channel action
`Du = T†∘(P u)` (P = projector onto col-span of the frame `A=range(T∘J)`) and
measures the fraction of mass leaking below `log λ` (the radial complement), on
band-limited radial carriers.

Two band-limited models (`(1−r²)³` smooth bump; sinc localized by Gaussian),
width/frequency varied, gave:

```
outer/full on band-limited carriers:
 {2}:  0.24–0.48      {2,3}:  0.26–0.38      {2,3,5}:  0.31–0.42
```

The leaked fraction never heads to 0 as the carrier becomes more band-limited
(narrower or lower-frequency): it saturates at a level 0.24–0.48, logλ-independent.
So band-limiting into radial ∩ Fourier-support does **not** push the outer channel
to zero.

Caveat (honest): smooth bumps and Gaussian-windowed sinc are *approximate*
band-limited/Prolate functions, not the exact prolate spheroidal wave functions
of the true Sonin space. So this is strong evidence, not a proof, that the outer
channel survives band-limiting. Rigor would require the actual prolate family.

## 5. Verdict: the hard bone does not break by outer-channel band-limiting

Stack of evidence, all consistent:

- OuterCh needs `=0` for Gate-3U (orthogonality), and `‖(I−R)∘D‖>1` on the full
  radial carrier (fidelity-verified).
- On band-limited carriers the outer fracture stays 24–48% — non-vanishing.
- Because `(I−R)∘(T·J)=0` has *no* analogue for `(I−R)∘(T·T·J·G⁻¹)`: the Gram
  inverse `G⁻¹` mixes frequencies and the composition does not re-preserve radial
  support. `T†` merely shifts left by `log p`; the extra `G⁻¹` has no
  radial-support welfare.

So the **numeric outer-channel verdict is negative for Gate-3U**: this route's
whole-gate equality `forward + physicalLeakage = 0` fails to close via the outer
channel on the tested carriers, including band-limited ones. The remaining hope
(if any) is that the outer channel cancels only on the *exact* prolate carrier,
which this numeric does not reach; or that the Gate's data (finite-S primes of
*arithmetic* type, not the toy 2,3,5) has additional structure not visible here.

> Discipline: this is a numeric falsification of the outer-channel *estimate*, not
> a Lean refutation and not a proof of RH. It re-casts 815's open identity as:
> the outer channel does not vanish on the broad carriers; the last hope is the
> exact prolate / arithmetic-prime structure.