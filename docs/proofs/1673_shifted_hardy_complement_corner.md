# 1673 — Shifted-Hardy fixed-half-line reduction

The moving archimedean Fourier-support projection at unit scale has an exact
fixed-half-line normal form.  For every real shift `b`, conjugating it by the
global logarithmic translation gives

```text
T_(2b) Q_0 T_(-2b) = K_b P_+ K_b,
```

where `P_+` is the fixed positive-half-line projection and `K_b` is the
shifted Hardy involution.  The pointwise identity is proved first; the
operator identity is then obtained by extensionality.  This avoids the large
uncontrolled simplifier expansion of the direct operator proof.

The reduction is exact and axiom-clean.  It supplies the fixed-coordinate
owner for the remaining complement-corner estimate, but does not yet provide
the required trace or Hilbert–Schmidt bound and does not prove RH.
