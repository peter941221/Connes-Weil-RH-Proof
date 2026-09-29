# 2250 — Per-node count uniformity of the owner-count brick

Date: 2026-09-30

Consumer: the per-node half of the 2246 L2 transfer — "the per-node
uniformity of the screen charges remains open, so the transferred-charge
number is a reading". This record closes the COUNT half of that uniformity
at the chosen candidate, node by node.

Verdict: **landed (count side)**. At every one of the 30 construction
nodes the family-height window count is bounded by `<= 8`
unconditional and by the exact enumerated count `<= 2` under the
Platt-Trudgian import; the three real-axis pins count exactly `0`.

## The per-node windows

Node geometry from the 2103 construction at
`rho = 0.945 + 39.25244858548658 i`: 21 true in-ball critical-line zeros
(heights `gamma_1 .. gamma_21`), 3 targets at `+gamma`, 2 conjugate orbit
pins at `-gamma`, 3 real-axis pins, 1 non-zero kill pin
(`27.67032193035704`, audited in 2245). Each node carries its family
width `a = SCALE * width` (r81 width plan, else the `2.2` fallback), and
the family-height window is `[||h| - a|, |h| + a]` (mirrored to `|h|`;
conjugation maps a negative-height family onto the same positive
ordinates). The count is window-framed, not cumulative:

```text
count <= (theta(T+) - theta(T-))/pi + S_up(T+) + S_up(T-)
```

with `S_up` the Trudgian 2014 bound (valid `T >= e`); below the first
ordinate `gamma_1 = 14.134725141734693790` no zero exists (exact), so a
sub-`gamma_1` edge contributes nothing.

## Numbers

```text
worst node (bound)      node 26: h = 72.0671576744819, a = 1.76,
                        window [70.3071576744819, 73.82715767448191],
                        count <= 8, enumerated 1
densest window          node 1: h = +39.25244858548658, a = 1.84,
                        window [37.412448585486589, 41.09244858548658],
                        count <= 7, enumerated 2 (gamma_6 and gamma_7)
bound histogram         0: 3 (real pins), 3: 1, 6: 1, 7: 21, 8: 4
enumerated histogram    0: 5, 1: 17, 2: 8
ball window (owner)     T+ = 82.51907238937719, T- = 4.014175218404013,
                        count <= 26, enumerated 21  (bitwise the 2245 values)
identity check          N(T) = (theta + Phi)/pi at T = 81.09737502024937,
                        residual -4.276423536147513e-50, 21 ordinates found
```

The ball-window row reproduces the committed 2245 stress row exactly
(`owner_count_upper_2014 = 26`, `zeros_enumerated = 21`, asserted in the
script). The per-node transfer ratios `count/62` therefore run with worst
case `8/62 = 0.12903225806451613` (unconditional) and
`2/62 = 0.03225806451612903` (imported), against the ball-window ratios
`26/62` and `21/62`.

## What this closes and what it does not

Closed: the count side of L2 per node — every construction node has an
explicit family-window count, uniformly below the ball-window count, with
the worst-node constants registered in the artifact.

Not closed: the CHARGE side of the transfer (per-node charge `<=`
uniform per-node budget `tail/62`) is untouched here; the family window
is the height reach of the node's own interpolation family, not an owner
membership statement; the Trudgian and Platt-Trudgian inputs are cited
external theorems (the 2252 Lean brick formalizes the downstream
arithmetic, not these imports); no producer GO, no gate sign change, no
RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_pernode_count_2250.py`;
- artifact: `results/2250_pernode_count_uniformity.json`;
- machinery: `scripts/routea_weighted_zero_owner_count_brick_2245.py`
  (Hardy-Z scan, phase identity, Trudgian bounds).