# Stoquastic Weil Gauge Rejection

Date: 2026-07-12

Status: diagonal sign or phase gauges cannot turn even the smallest tested
exact cutoff-free Weil matrices into stoquastic Hamiltonians or graph
Laplacians. Arb certifies frustrated positive triangles at `(c,N)=(13,2)` and
`(13,4)`. This rejects the proposed Perron--Frobenius lower proof mechanism;
it does not challenge the certified positivity of those finite matrices.

## 1. Proposed Lower Mechanism

Let `Q_(c,N)` be the exact real symmetric finite Weil matrix from the
Guinand--Weil dictionary. The candidate was:

```text
find a diagonal unitary D such that
  (D* Q_(c,N) D)_(i,j) <= 0 for i != j;

then identify the result with a graph-Laplacian or stoquastic Hamiltonian
whose ground-state sign follows from a lower Perron--Frobenius theorem.
```

This would be useful only if the gauge and diagonal lower bound followed from
the explicit entries without assuming matrix positivity.

## 2. Exact Gauge Obstruction

For three nonzero off-diagonal entries, the cyclic product

```text
Q_(i,j) Q_(j,k) Q_(k,i)
```

is invariant under every diagonal unitary gauge. If all three transformed
entries were real and nonpositive, their product would be negative. Therefore
one positive triangle product is a complete obstruction.

For a real matrix this is the standard signed-graph switching condition. It
also covers arbitrary diagonal phases, not only `+1/-1`, because the three
vertex phases cancel in the cyclic product.

## 3. Certified Results

The probe loads `anc/arb_ldlt_certify.py` directly from the official arXiv
source package for arXiv:2607.02828. Every entry sign is decided by an Arb
interval; a sign interval containing zero aborts the run.

At `(c,N)=(13,2)`, dimension five:

```text
undetermined off-diagonal signs = 0
tested nonzero triangles        = 10
frustrated triangles            = 10
```

The first witness is

```text
Q_(0,1) = +0.0482615006491741318...
Q_(1,2) = +0.0457203442394000540...
Q_(2,0) = +0.0469909224442870929...
```

At `(c,N)=(13,4)`, dimension nine:

```text
undetermined off-diagonal signs = 0
tested nonzero triangles        = 84
frustrated triangles            = 84
```

The first witness is again strictly positive on every edge:

```text
Q_(0,1) = +0.0711327036909206765...
Q_(1,2) = +0.0547708321116810782...
Q_(2,0) = +0.0629517679013008774...
```

The same source matrix at `(13,2)` was independently rerun through interval
LDL and certified positive definite, with midpoint smallest eigenvalue
`2.97351877410148e-9`. Thus the result is not a negative-eigenvalue discovery;
it separates ordinary matrix positivity from stoquastic sign structure.

## 4. Reproduction

Fetch and unpack the official source bundle in WSL2:

```text
curl -L https://export.arxiv.org/e-print/2607.02828 -o source.tar
tar -xf source.tar
```

Then run, with `python-flint` and `mpmath` available:

```text
python3 -B docs/proofs/051_stoquastic_weil_probe.py \
  --upstream anc/arb_ldlt_certify.py --c 13 --N 2 --prec 512

python3 -B docs/proofs/051_stoquastic_weil_probe.py \
  --upstream anc/arb_ldlt_certify.py --c 13 --N 4 --prec 768
```

## 5. Why Sign Reversal Does Not Repair The Route

Since the tested off-diagonal entries are positive, `alpha I-Q` has negative
off-diagonal entries. Perron--Frobenius information for that matrix controls
the largest eigenvalue of `Q`, not the smallest eigenvalue whose nonnegativity
is required. Choosing `alpha` large enough to make `alpha I-Q` positive merely
asks for an upper spectral bound and does not prove `Q>=0`.

Likewise, allowing a general dense change of basis is not a lower structure:
diagonalizing `Q` or using its Cholesky factor already requires the desired
positive spectral information. The rejected claim is specifically that the
explicit Fourier/Galerkin basis hides a graph-energy proof removable by local
phase switching.

## 6. Verdict

```text
exact cutoff-free matrix owner: retained
finite Arb positivity evidence: retained
diagonal gauge to stoquastic form: rejected
graph-Laplacian lower proof: rejected
general positive factorization: still the RH-level sign problem
new Lean owner: none
unconditional RH: unproved
```

Sources:

```text
https://arxiv.org/abs/2607.02828
https://export.arxiv.org/e-print/2607.02828
docs/proofs/043_cutoff_free_weil_spectrum_probe.py
docs/proofs/044_cutoff_free_weil_cancellation_verdict.md
```
