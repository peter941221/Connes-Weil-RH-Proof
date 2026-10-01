# 2395 — directed term construction path audit

Date: 2026-10-02.

A source-level AST audit, bound to the 2385 evaluator hashes, confirms that
the worker's directed branch uses the interval kernel, constructs the point
norm and exponential weight in MPFR, converts the MPFR point term to binary64
with RNDU, and accumulates that converted term with RNDU. The diagnostic
`math.hypot` branch remains only in the separate diagnostic assignment and is
not used by the directed accumulator path.

This is code-path evidence only. It does not prove the underlying MPFR
point-box enclosure theorem or import termwise dominance into Lean.
