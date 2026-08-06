# Proof-717 / Gate-3U: 820 — no Sobolev-type decay of the outer channel (track-b negative)

Date: 2026-08-06
Status: analytic-scale negative — the outer-channel leak does NOT decay with
either grid resolution or radial-cutoff depth.  There is no Sobolev/decay
mechanism keeping `(I−R)∘D` inside radial support on the derivative scale.  This
is the analytic content that would be needed for Lean route-1 (815 §5), and it
is absent.  Ditches the "improvement under Sobolev" hope, not the gate itself.
Branch: `proof/gate3u-completed-readout`
RELATED: `815_rh_route_conditional_boundary.md`, `816`, `817`, `818`, `819`

## 1. What this tests (track-b: the analytic mechanism)

815 §5 listed two Lean-shaped closures. Route-1 is a *decay / boundedness*
statement:
  "show `(I−R)∘D` maps the source Sonin carrier into radial support with a
   controlled estimate", the Sobolev-flavoured version being "the operator does
   not push probability/mass from radial support into the outer complement on a
   scale that I can control by narrowing support."

If such an analytic mechanism existed, the measured quantity
    Outer(u) = ‖D(u)‖_{t<logλ} / ‖D(u)‖
would DECREASE as (a) we resolve the boundary finer (so u is a cleaner localised
probe), or (b) we deepen the radial cutoff (push logλ inward), both being proxy
for "high-frequency/decay control".

## 2. Result — completely flat; no decay

`820_outer_decay_sobolev_scale_probe.py`, single boundary probe `u = e_{car[0]}`
(delta just inside the radial support), on the metric coframe.

```
                outer = ‖D(u)_below‖ / ‖D(u)‖
{2}     scale 1→8 :   0.2784, 0.2794, 0.2794, 0.2794        (flat / +0.001 over 8x res)
        cutoff 0→-1.5: 0.2776 until 0.2776                   (flat in depth)
{2,3}   scale 1→8 :   0.3743, 0.3748, ... 0.3748,             (flat / +0.0005)
        cutoff 0→-1.5:  0.3735 ...                             (flat)
{2,3,5} scale 1→8 :   0.3440 ... 0.3961                       (RISES with res!)
        cutoff 0→-1.5: 0.3440 ... 0.3283                      (only -0.016 at depth)
```

Interpretation: the leak is **O(1), essentially independent** of the resolution
scale and of the radial cutoff depth.  For `{2,3,5}` it grows slightly under
refinement (0.344 -> 0.396) — the discretisation is not hiding a decay; it's
exposing more leak.  There is **no** Sobolev / decay / mollifier scale at which
`(I−R)∘D` goes to zero.

## 3. How this is honest / binds track-b

- This avoids the 818/819 failure mode (no R0, no Q0, no subspace
  intersection): it is a direct, self-similar, radial-scale sweep of the very
  object route-1 is about.
- It is not a proof of RH and not a Lean refutation.  It is a measurement of the
  *derivative-scale geometry* of D's action: D does not respect radial support
  improvement under refinement.
- Combined with 815/816/817 (exact-Slepian) this is a unified picture: the outer
  channel leaks a fixed O(1) fraction at every analytic scale we can reach
  (prime count 1,2,3; logλ 0,1; grid scale x1..x8; radial depth 0..-1.5;
  band-limited, Slepian and prolate-type).  No mechanism, Sobolev or otherwise,
  has produced a vanishing outer channel.

## 4. Consequence

Ditches the "outer channel via a Sobolev/decay lemma" route-1: the numerics say
there is no such scale.  The remaining live possibilities for Gate-3U are (a) the
truly arithmetic finite-S prime structure beyond toy {2,3,5}, or (b) a fully
exact analytic prolate/Sonin-frame transport computation that the grid (818/819)
cannot reach.  Both are ahead of what this probe family can reach.

## 5. Files

- `820_outer_decay_sobolev_scale_probe.py` (this run)
- This verdict.

Nuance: the raw outer norm itself stays ~0.35–0.57 in absolute; the flat
*fraction* is the honest invariant — a decay estimate in 815 would be a
statement about that fraction, and there is none.