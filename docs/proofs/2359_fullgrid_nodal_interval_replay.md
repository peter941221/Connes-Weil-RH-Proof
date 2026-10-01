# 2359 - Full-grid directed nodal interval replay

日期：2026-10-01。

## Scope

The 2242 directed MPFR interval evaluator was run on the producer's full
240001-point physical grid at the binding `sigma=-0.5`. The points are split
into fixed spans of 20001; each worker preserves increasing node order and
the parent combines span sums in increasing span order.

This is a full-grid replay of pointwise interval magnitudes, not yet a
certificate. The parent accumulation allowance, the composite-trapezoid
remainder, and identity with the original 2303 coordinate construction remain
separate obligations.

## Reproducible command

```text
source /home/peter/rh/.venv-flint/bin/activate
python scripts/routea_nodal_interval_fullgrid_2359.py \
  --nodes 240001 --sigma -0.5 --workers 12 --span 20001
```

The committed result records the full-grid readings and source hashes. The
full run gives:

```text
base_M0 = 2.6867143296475375
base_D2 = 8606.21439765069
corr_M0 = 90.78788225375501
corr_D2 = 125446.71132157727
min product = 337039.47691483964
```

The 1001-node sequential/12-worker control is bitwise equal in all four
integrals and in the min-product. The full-grid result is not imported into
Lean and does not alter the strip pin or the producer.

The readings agree with the stored 2303 point row at `sigma=-0.5` to the
displayed floating precision. This is a strong evaluator control, but it is
not yet a theorem: the pointwise interval-to-function identity,
directed accumulation allowance, trapezoid remainder, and coordinate identity
remain open.
