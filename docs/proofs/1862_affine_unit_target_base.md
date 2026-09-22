# 1862 - Explicit affine unit-target base

Date: 2026-09-23.

Status: Formally verified in Lean; base producer packaging.

`exists_affine_base_with_unit_targets_and_quadratic_decay` packages the
actual finite-node base used by the healthy orbit route as an affine
right-inverse correction with target value `1` at every selected node. It
exports support, all finite Laplace target equations, and the uniform
quadratic vertical-tail bound in one owner.

The coefficient-weighted seminorm budget is still a separate quantitative
obligation. No positivity or RH conclusion is asserted.

Verification: WSL focused build `affine-base-1862b.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and standard three-axiom audit output.
