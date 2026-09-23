# 042 — G8 diagonal-energy operator bridge audit

Status: supporting interface audit, compressed 2026-09-23. The formal
factorizations and no-gos below remain useful; S3 and B4 are open. RH is not
claimed.

Consumer: conditional healthy-owner G8 readback in [012]. This is not an
active producer lane under the current core-progress gate.

## Exact operators

Let

```text
C = rootConvolution(owner)
J = sourceInclusion(scale)
P = sourceSoninProjection(scale)
E = radialSupportProjection(scale).
```

Every actual G8 metric coframe factors through `J`:

```text
survivor:  scalar * J * sourceSide
boundary:  finite sum of M_p * J * N_p.
```

This factorization is formal in
`C1G8R3SurvivorCoframeBridge.lean` and
`C1G8R3BoundaryOutputFactorizationBridge.lean`.

The earlier selected-root leakage theorem controls an operator with left
factor `I - P`. It does not control the full G8 diagonal because the missing
`P` component is precisely the in-Sonin signal, and boundary terms contain an
additional ambient factor `M_p`.

## Survivor work order WO-S

| Brick | Content | Status |
|---|---|---|
| S1 | survivor coframe factors as `scalar * J * sourceSide` | FORMAL |
| S2 | orthogonal IN/OUT split; OUT controlled by existing leakage result | FORMAL |
| S3 | source-compressed IN energy `sum ||J† C J e_i||^2` | OPEN |

The finite source-side Schur operator is formally invertible, so S3 is
equivalent to the bare source-compressed square-sum; no frame conditioning is
left to exploit. The projected-root endpoint and Hardy/prolate normal forms
are bookkeeping equivalents, not estimates.

## Boundary work order WO-B

| Brick | Content | Status |
|---|---|---|
| B1 | each boundary output factors as `M_p * J * N_p` | FORMAL |
| B2 | per-output IN/OUT and radial/internal-gap split | FORMAL |
| B3 | actual-column radial-boundary estimate | FORMAL |
| B4 | composite internal-gap / commutator-root square-sum | OPEN |

The finite-output consumers and conditional total trace limit are already
wired. B4, not another output-summation wrapper, is the remaining boundary
analysis.

## Formal shortcut no-gos

1. The unprojected ambient leakage operator is not Hilbert–Schmidt on any
   Hilbert basis when the selected source Laplace value is nonzero.
2. The full ambient band-root has the same obstruction. Therefore neither can
   replace the source-compressed gate.
3. The corresponding full-basis Hardy off-diagonal estimate is impossible at
   unit scale under the same nonzero condition.
4. The source-prolate pullback
   `J† * sourceProlateFactor * J` used by an earlier boundary shortcut is
   identically zero.
5. Fixed-window compact-kernel Hilbert–Schmidt bounds grow with the window and
   do not supply a uniform annular trace bound.

These are scoped no-gos for the shortcuts, not for S3/B4 themselves.
Representative formal evidence lives in
`C1G8R3HilbertSchmidtOrthonormalObstruction.lean`,
`C1G8R3GateAmbientNormalForm.lean`,
`C1G8R3InternalProlateGapEnergy.lean`, and paired audits; proof records
1488--1512, 1614--1615, 1653--1655, and 1704--1707 preserve the chronology.

## Stop rules

- Do not infer full energy from the OUT leakage half.
- Do not drop the source/Sonin compression.
- Do not move an ambient factor through `C`, `P`, or `E` without a proved
  commutation law.
- Do not replace trace class by Hilbert–Schmidt.
- Do not add another conditional cutoff/readback theorem while S3 or B4 is
  merely restated.
- Stop any proof that assumes the desired `qw` sign, `SourceRH`, or universal
  positivity.

## Reuse criterion

This lane may be reactivated only if a new theorem proves a quantitative part
of S3 or B4 on the actual selected owner. A coordinate normalization or
equivalent square-sum statement alone is not enough.
