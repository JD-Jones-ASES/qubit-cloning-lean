module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `QubitCloning.`, `_private.QubitCloning.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "QubitCloning." || label.startsWith "_private.QubitCloning." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 180 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 180"
  for n in [`QubitCloning.proj_pauliVec, `QubitCloning.pauliVec_unit, `QubitCloning.sixAvg_le,
      `QubitCloning.exists_unit_min_le, `QubitCloning.sixAvg_ge_third,
      `QubitCloning.exists_sixAvg_eq_third, `QubitCloning.bh_isChannel, `QubitCloning.bh_trace,
      `QubitCloning.bh_traceSecond, `QubitCloning.bh_traceFirst, `QubitCloning.bh_fidelity,
      `QubitCloning.bh_sixAvg, `QubitCloning.eq_bh_of_sixAvg, `QubitCloning.eq_bh_of_forall,
      `QubitCloning.isGreatest_cloning_fidelity, `QubitCloning.asym_bound,
      `QubitCloning.asym_bound_forall, `QubitCloning.asym_isChannel,
      `QubitCloning.asym_traceSecond, `QubitCloning.asym_traceFirst,
      `QubitCloning.asym_fidelity, `QubitCloning.asym_equality,
      `QubitCloning.eq_asym_of_equality, `QubitCloning.bhChannel_eq_asymChannel,
      `QubitCloning.tradeoff_sqrt, `QubitCloning.tradeoff_forall,
      `QubitCloning.tradeoff_attained, `QubitCloning.tradeoff_full_sqrt,
      `QubitCloning.signed_asym_bound, `QubitCloning.eq_asym_of_signed_equality,
      `QubitCloning.clone_anticlone_bound, `QubitCloning.clone_anticlone_attained,
      `QubitCloning.eq_clone_anticlone_of_equality,
      `QubitCloning.sixAvg₁_le_of_sixAvg₂_eq_third,
      `QubitCloning.sixAvg₂_le_of_sixAvg₁_eq_third, `QubitCloning.floor_companion_attained,
      `QubitCloning.kraus_span_stability] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
