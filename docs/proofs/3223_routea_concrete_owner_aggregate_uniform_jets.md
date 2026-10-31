# 3223: Route A aggregate with uniform jet bounds

Status: verified conditional aggregate adapter.

The 3223 theorem applies the fixed 40960-cell Taylor aggregate while supplying
the concrete-owner second-, fourth-, and sixth-derivative arrays from 3220 and
3222. Its only remaining per-cell premise is:

```text
weightedExternal3201 (...) (record2680Center3212 index)
  <= valueUpper index
```

for every `index < 40960`.

This is an interface reduction only. It does not prove that the resulting
finite sum is negative, because the conservative uniform derivative bounds may
be too large for the observed cancellation margin. A final producer proof must
replace them with cell-local bounds or prove that the uniform budget still
fits.

Verification: WSL2 ext4, Lean `4.30.0`, focused build and axioms audit. The
audited adapter uses exactly:

```text
[propext, Classical.choice, Quot.sound]
```
