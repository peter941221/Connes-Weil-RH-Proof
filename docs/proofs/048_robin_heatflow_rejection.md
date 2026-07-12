# Robin And Heat-Flow Rejection

Date: 2026-07-12

Status: both candidate routes are rejected as lower unconditional RH
producers. The Robin lane requires a sign estimate at exactly the
zero-sensitive square-root scale. The generic de Bruijn heat-flow lane only
transports an already known zero strip forward and cannot reach time zero
without an RH-level input. No Lean route owner is authorized.

## 1. Robin / Colossally Abundant Lane

Put

```text
G(n) = sigma(n)/(n log log n),
T(n) = (exp(gamma) log log n - sigma(n)/n) sqrt(log n).
```

Robin's theorem already gives the exact route judgment:

```text
RH <=> G(n) < exp(gamma) for every n > 5040,
```

and it is enough to check the colossally abundant numbers. Restricting the
consumer to that subsequence therefore does not make the missing sign a lower
theorem.

The quantitative asymptotics show why standard prime-distribution estimates do
not supply the sign. Ramanujan's conditional CA estimates, as quoted and
proved in Musin (2020), give under RH

```text
1.393 < T(n) < 1.558
```

for every sufficiently large CA number. Thus the expected absolute deficit
in `sigma(n)/n` is only

```text
Theta(1/sqrt(log n)).
```

On the other hand, Robin's oscillation theorem says that if RH is false and
`theta` is the supremum of the real parts of the nontrivial zeros, then for
every `b` with

```text
1 - theta < b < 1/2
```

there are infinitely many `n` with

```text
G(n) > exp(gamma) * (1 + c/(log n)^b).
```

The exponent boundary `1/2` is therefore not an artifact of a weak estimate;
it is precisely where an off-critical zero changes the sign scale.

Let `x` denote the prime scale, with `x` comparable to `log n` on CA numbers.
The classical zero-free-region PNT error has the qualitative size

```text
exp(-c sqrt(log x)).
```

It is asymptotically much larger than the required CA margin `x^(-1/2)`:

```text
exp(-c sqrt(log x)) / x^(-1/2)
  = exp((log x)/2 - c sqrt(log x)) -> infinity.
```

Consequently a proof that keeps only this unconditional error cannot determine
Robin's strict sign. Any successful arithmetic lane needs a new cancellation
theorem at the square-root scale without assuming a zero-free half-plane beyond
`Re(s)=1/2`; that is the unresolved mathematical owner, not an elementary CA
enumeration or Mertens-product bound.

## 2. De Bruijn--Newman Heat-Flow Lane

For the standard deformation

```text
H_t(z) = integral exp(t u^2) Phi(u) cos(zu) du,
```

the de Bruijn theorem contracts a known zero strip under forward flow. In the
polynomial form quoted by Branden--Chasse, if the starting zeros lie in
`|Im z| <= mu`, then applying `exp(-lambda D^2)` puts the resulting zeros in

```text
|Im z| <= sqrt(max(mu^2 - 2 lambda, 0)).
```

This proves real zeros only after positive heat time has consumed the known
strip width. It cannot be reversed: the inverse heat operator amplifies high
frequencies and is not a real-zero preserver. At time zero, the formula reaches
width zero only when the input width is already `mu=0`, which is RH.

The available stronger kernel conditions also fail as an escape:

```text
+--------------------------+----------------------------------------------+
| proposed lower input     | route judgment                               |
+--------------------------+----------------------------------------------+
| positivity/log concavity | too weak; controls only low-order variation  |
| PF_infinity              | impossible for the non-Gaussian Xi kernel    |
| PF_r for r >= 5          | excluded by a certified negative PF5 minor   |
| forward strip contraction| gives t>0 real zeros, not Lambda <= 0        |
| backward heat transport  | does not preserve real-rootedness            |
+--------------------------+----------------------------------------------+
```

Rodgers--Tao proves `Lambda >= 0`; RH is exactly `Lambda <= 0`. Rephrasing the
missing direction as a kernel inequality is useful only if that inequality is
proved from strictly lower data. PF infinity, all-time Jensen hyperbolicity,
or real-rootedness at `t=0` are not such data.

## 3. Route Decision

```text
Robin / CA:
  rejected as a lower producer;
  missing owner = unconditional square-root-scale signed cancellation.

de Bruijn--Newman:
  rejected as a generic heat-flow producer;
  missing owner = a new time-zero kernel theorem weaker than real-rootedness.

unconditional RH:
  not proved.
```

## 4. Primary Sources

```text
Guy Robin, Grandes valeurs de la fonction somme des diviseurs et
hypothese de Riemann, J. Math. Pures Appl. 63 (1984), 187--213.

Oleg R. Musin, Ramanujan's Theorem and Highest Abundant Numbers,
Arnold Mathematical Journal 6 (2020), 119--130.
https://doi.org/10.1007/s40598-020-00136-w

Petter Branden and Matthew Chasse,
Classification Theorems for Operators Preserving Zeros in a Strip.
https://arxiv.org/abs/1402.2795

Brad Rodgers and Terence Tao,
The de Bruijn--Newman constant is non-negative.
https://arxiv.org/abs/1801.05914

Wojciech Michalowski,
On the Polya Frequency Order of the de Bruijn--Newman Kernel.
https://arxiv.org/abs/2602.20313
```
