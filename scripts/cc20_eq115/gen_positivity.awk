#!/usr/bin/awk -f
BEGIN {
  print "/-"
  print "Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved."
  print "Released under Apache 2.0 license as described in the file LICENSE."
  print "-/"
  print ""
  print "import ConnesWeilRH.Dev.C1CC20Eq115Table"
  print "import Mathlib.Tactic.IntervalCases"
  print ""
  print "/-!"
  print "# Positivity of every extracted equation-(115) coefficient"
  print ""
  print "The published equation-(115) coefficient table `cc20Eq115CoefficientQ` is a"
  print "machine-transcribed 1732-branch rational `ite` chain.  This leaf is generated"
  print "from that chain: for each branch index it records the branch value as a"
  print "definitional equation (kernel `rfl` descends the ite chain and never inspects"
  print "the subtype bound proof), and the quantified positivity then follows from a"
  print "single `interval_cases` sweep that rewrites the matching branch equation and"
  print "closes the resulting rational literal comparison with `norm_num`."
  print ""
  print "Three routes were rejected by measurement (companion record docs/proofs/1047):"
  print "`norm_num [cc20Eq115CoefficientQ]` per case blows the whnf heartbeat budget"
  print "(measured failure after 1613 s); kernel `decide` cannot evaluate ANY"
  print "comparison of rational division literals in this toolchain"
  print "(`Rat.instDecidableLt` is stuck at the externalized `Rat.blt`); and per-case"
  print "`simp only [cc20Eq115CoefficientQ]` rebuilds the whole 1732-node chain in"
  print "every goal, which is quadratic in the chain length (measured > 45 min and"
  print "killed for the full sweep).  Case GENERATION itself (`interval_cases` on the"
  print "decomposed `ℕ`) was measured at 0.3 s for all 1732 cases, so the assembly"
  print "sweep is cheap; only the per-case chain rebuild had to go."
  print ""
  print "This feeds the (gamma) Bessel-coercivity brick, whose perturbed summands"
  print "only lower the defect form when the coefficients `d_n` are nonnegative."
  print ""
  print "Reference: equation (115) of <https://arxiv.org/html/2006.13771>; companion"
  print "records docs/proofs/1046, docs/proofs/1047."
  print "-/"
  print ""
  print "namespace ConnesWeilRH"
  print "namespace Source"
  print "namespace C1CC20Eq115CoefficientPositivity"
  print ""
  print "open C1CC20Eq115Table"
  print ""
  print "-- The machine-generated ite chain nests far deeper than the defaults sized"
  print "-- for hand-written proofs."
  print "set_option maxRecDepth 30000"
  print "-- The assembly sweep rewrites through 1732 branch equations per goal."
  print "set_option maxHeartbeats 20000000"
  print ""
  names = ""
  count = 0
}

/^def cc20Eq115CoefficientQ/ { inside = 1; next }

inside && /^  if n\.val = [0-9]+ then \([0-9]+ : ./ {
  line = $0
  sub(/^  if n\.val = /, "", line)
  K = line; sub(/ then.*/, "", K)
  v = line; sub(/^.*then \(/, "", v); sub(/ : .*/, "", v)
  d = line; sub(/^.*\) \//, "", d); sub(/ else$/, "", d)
  emit(K, v, d)
  next
}

inside && /^  \([0-9]+ : / {
  line = $0
  v = line; sub(/^  \(/, "", v); sub(/ : .*/, "", v)
  d = line; sub(/^.*\) \//, "", d)
  emit(count, v, d)
  finish()
  exit
}

function emit(K, v, d) {
  nm = "cc20Eq115CoefficientQ_branch_" K
  printf "/-- Branch %d of the coefficient chain is the literal %s/%s. -/\n", K, v, d
  printf "theorem %s : ∀ (p : %s < 1732), cc20Eq115CoefficientQ ⟨%s, p⟩ = (%s : ℚ) / %s :=\n  fun p => by rfl\n\n", nm, K, K, v, d
  if (names == "") names = nm; else names = names ", " nm
  count = K + 1
}

function finish() {
  print "/-- Every branch of the equation-(115) coefficient chain is strictly"
  print "positive: 1732 rational literals, each one a positive fraction. -/"
  print "theorem cc20Eq115CoefficientQ_pos :"
  print "    ∀ n : Fin 1732, (0 : ℚ) < cc20Eq115CoefficientQ n := by"
  print "  intro n"
  print "  cases n with"
  print "  | mk k hk =>"
  printf "      interval_cases k <;> (simp only [%s]; norm_num)\n", names
  print ""
  print "/-- The real form of every published equation-(115) coefficient is"
  print "nonnegative. -/"
  print "theorem cc20Eq115Coefficient_nonneg :"
  print "    ∀ n : Fin 1732, 0 ≤ cc20Eq115Coefficient n := by"
  print "  intro n"
  print "  rw [cc20Eq115Coefficient]"
  print "-- Term-level mod_cast lifts the source relation as-is and needs a"
  print "-- known strict target: weaken the goal to < first via le_of_lt."
  print "  apply le_of_lt"
  print "  exact mod_cast (cc20Eq115CoefficientQ_pos n)"
  print ""
  print "end C1CC20Eq115CoefficientPositivity"
  print "end Source"
  print "end ConnesWeilRH"
}
