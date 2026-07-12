# 091 Ambient Compact Square Transport Pass

Date: 2026-07-12

## Lean evidence

The WSL-verified probe `ConnesWeilRH/Dev/SchwartzAmbientOwnerProbe.lean` now
proves:

```text
ambientConvolution f.test g.test = (f.convolution g).test
```

for every `CompactLogTest f g`. The proof uses:

```text
SchwartzMap.convolution_apply
CompactLogTest.convolution_apply
MeasureTheory.convolution_def
```

and closes by reflexivity after the two continuous multiplication maps are
identified. The earlier Fourier product theorem and the ambient complex-vector
carrier theorem remain passing in the same probe.

## Consequence

The ambient Schwartz carrier and compact-log witness do not disagree on the
convolution square at the function level. The Xi/M4 finite linear combination
can therefore be represented in the ambient carrier without reverting to the
invalid additive toy convolution.

## Remaining gate

The unresolved bridge is now strictly downstream:

```text
same ambient square
  -> CC20 trace amplitude / K_I form
  -> CCM25 finite-prime and pole read-off
  -> one source QW value
```

No route theorem is accepted until those read-offs are proved for the same
encoded square.

