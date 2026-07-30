# Proof 611: antiresonant response split

## Result

Proof 611 applies one and the same supplied Bone 1 readout to both radial
pieces before estimating them:

```text
reducedRow * newFrame
  = interiorResponse + boundaryResponse.
```

This preserves the signed response.  It does not introduce separate source
rows or discard cancellation before the split.

## Uniform boundary decay

For a response factor with bound `B`,

```text
||boundaryResponse(p,S)||
  <= 2 B * primeEulerAmbientLossScale(p)
  <= 2 B * sqrt(q_p).
```

The ambient-loss scale tends to zero along the arithmetic primes.  Therefore,
for every moving suffix sequence `S(n)`, a supplied family-uniform factor
forces

```text
||boundaryResponse(p_n, S(n))|| -> 0,

||reducedRow(p_n,S(n)) * newFrame(S(n))
    - interiorResponse(p_n,S(n))|| -> 0.
```

## Interpretation

```text
+----------------------+------------------------------------------+
| channel              | status after Proof 611                   |
+----------------------+------------------------------------------+
| radial boundary      | uniformly negligible if Bone 1 factor    |
| radial interior      | carries the unresolved antiresonance     |
| response factor      | still not constructed                    |
+----------------------+------------------------------------------+
```

The next source theorem must control the radial-interior response using the
actual Sonin/Fourier constraint and compact detector support.  A lower bound
for the ambient half-line shift alone is unavailable.

## Boundary of the result

The boundary decay is conditional on a supplied family-uniform response
factor.  It is a localization of the hard obligation, not a construction of
that factor.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH
remain open.

## Verification

```text
focused source build: 3382 jobs, PASS
import-facing audit:  PASS
audited declarations: 8
axioms: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3879 jobs, PASS
full repository build:  3960 jobs, PASS
```
