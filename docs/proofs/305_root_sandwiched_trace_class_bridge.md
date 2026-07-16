# Proof 305: root-sandwiched trace-class bridge

Date: 2026-07-16

Status: the finite-window trace-class producer is now an axiom-clean Lean
object. The source identification with the continuous CC20 quantized
commutator, the moving `E/R/K_prol` equality, and Gate 3U remain open.

## What changed

`ConnesWeilRH/Source/CC20Concrete/RootSandwichedTrace.lean` introduces the
actual finite-window sandwich

```text
K_(left,right)(y,x)
  = conjugate(leftRoot(y)) * K(y,x) * rightRoot(x).
```

For any continuous kernel `K` on the compact source window, the module builds
the corresponding `L2` operator and packages two such factors as a genuine
`A†B` owner. The generic continuous-kernel theorem from
`ContinuousKernelHilbertSchmidt` supplies the square-summability and diagonal
integrability; no stored trace-class premise or `sorry` is used.

The named declarations are:

```text
cc20WindowRootSandwichedKernel
cc20WindowRootToLp
cc20WindowRootSandwichedOperator
cc20WindowRootSandwichedPairData
cc20WindowRootSandwichedPairData_traceProduct_isTraceClass
cc20WindowRootSandwichedPairData_trace_eq_integral
cc20WindowRootSandwichedResponse
cc20WindowRootSandwichedResponse_eq_integral_sub_residue
```

The response keeps the source atom explicit:

```text
response
  = trace(A†B)
      - 2 * inner(rightRoot, leftRoot).
```

The root pairing is also read back as the actual Haar integral, so the `-2`
term is not hidden in a continuous diagonal kernel.

## Why this is the right first owner

The trace route has two different analytic objects:

```text
regular branch       continuous kernel on a finite carrier -> A†B trace
distributional atom  -2 Dirac_0                   -> -2 <rightRoot,leftRoot>
```

Putting the atom into the ordinary divided-difference kernel would conflate a
distribution with a continuous function. Proofs 302--304 already reject that
shortcut. The new response definition keeps both terms in one signed scalar
while preserving the legal factorization of the regular part.

The concrete specialization
`cc20WindowRootSandwichedRegularPairData` uses the existing CC20 regular
kernel. It is a producer for the trace-class side only. It does **not** say
that this regular kernel is the off-diagonal source commutator

```text
([H,f])(s,t) = i / pi * (f(s)-f(t))/(s-t),
```

which is the remaining source theorem from CC20 Appendix E (arXiv:2006.13771):

```text
https://arxiv.org/abs/2006.13771
```

## Lean evidence

The import-facing audit is
`ConnesWeilRH/Dev/RootSandwichedTraceAudit.lean`. In the isolated WSL2
verification mirror:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.RootSandwichedTrace

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.RootSandwichedTraceAudit \
             ConnesWeilRH.Source.CC20Concrete
```

The audit reports only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, no project axiom, and no hidden no-argument trace
premise. The full default target also passes in the same mirror (`3586`
jobs) after refreshing the stale `CC20YoshidaNearZeros.olean` dependency.

## Finite guard

`305_root_sandwiched_trace_probe.py` checks the corresponding finite matrix
ledger. It verifies the `A†B` trace against both the diagonal series and the
row-wise kernel pairing, then checks that the explicit residue is nonzero and
that deleting it changes the complete scalar. This is an algebraic guard, not
a continuous source proof.

Example commands (WSL2):

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/305_root_sandwiched_trace_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/305_root_sandwiched_trace_probe.py \
  --size 48 --support-radius 4 --seed 2305
```

Expected invariant shape:

```text
A†B trace readback error       < 1e-14
kernel row pairing error       < 1e-14
root atom readback error       = 0
residue omission gap           > 0
RH                             UNPROVED
```

## Remaining hard bone

The next theorem must provide a `ContinuousMap` kernel witness for the
root-sandwiched CC20 divided difference and identify its complete scalar with
the moving outer, second-support, and prolate branches:

```text
root-sandwiched [H,f] response
  = regular divided-difference A†B trace
      - 2 <rightRoot,leftRoot>
  = moving E/R response + second-support branch + K_prol branch.
```

Only after this equality may compact support be used for a signed estimate. Do
not use a raw translated projection trace, split the three physical branches
by absolute value, or delete the prolate/residue terms. Gate 3U, the
finite-`S` sign, Burnol's identity, and RH remain unproved.
