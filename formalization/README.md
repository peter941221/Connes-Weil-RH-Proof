# Formalization

This directory records the Lean 4 formalization plan and readiness notes.

The active Lake scaffold now lives at the repository root:

```text
lakefile.toml
lean-toolchain
ConnesWeilRH.lean
ConnesWeilRH/
```

Use the segmented target for current route work:

```text
lake build ConnesWeilRH
```

The route scaffold is source-conditional. It names the CCM24, CCM25, and CC20
source interfaces and checks the route composition, but it does not yet
formalize the source-paper analytic proofs.

Before changing Lean interfaces, read:

```text
formalization/lean-readiness.md
docs/audits/source-reread-v0.2.md
docs/audits/lean-source-interface-map.md
docs/audits/lean-segment-build.md
```

For route edits, build the smallest affected segment first, then run
`lake build ConnesWeilRH` and record the final axiom audit. Major milestone
commits should be GPG-signed before they are pushed.
