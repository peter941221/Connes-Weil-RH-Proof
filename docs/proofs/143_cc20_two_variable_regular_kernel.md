# CC20 Two-Variable Regular Kernel

Date: 2026-07-12

Status: accepted measurable symmetric kernel candidate; Hilbert-Schmidt and
source-action identities remain open.

## Objects

`RegularKernel.lean` defines positive multiplicative coordinates and

```text
ratioRadius(u,v) = max(u/v,v/u)
```

with proofs that it is continuous, symmetric, at least one, and equals one
exactly on the diagonal.

The ordinary kernel uses the finite regular diagonal value

```text
8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2
```

and the proved non-diagonal `Q(delta)` formula elsewhere. Lean proves the
resulting two-variable kernel measurable and symmetric, with separate
diagonal and off-diagonal read-offs.

## Verification

The isolated WSL2 ext4 build and `RegularKernelAudit.lean` pass. The audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Domain correction

A ratio-only kernel cannot be Hilbert-Schmidt on the entire positive Haar
plane because common scaling leaves the kernel unchanged and contributes an
infinite center variable. CC20 uses the fixed compact domain
`sqrt(I) x sqrt(I)` for `I` contained in `(1/2,2)`. The next integrability
theorem must be stated on that restricted domain, not globally.

## Remaining gate

The finite diagonal value is currently a source-backed extension value. Its
limit equality with the non-diagonal formula still needs a Lean proof before
continuity and compact-domain boundedness can be used. After that, the fixed
interval kernel square is integrable by compactness.

## Route judgment

```text
two-variable measurable symmetric kernel: accepted candidate
diagonal limit theorem: open
fixed-interval square integrability: open
source kernel-action identity: open
RH: unproved
```
