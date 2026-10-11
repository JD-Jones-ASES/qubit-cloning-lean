# Verification

All twenty-seven statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
controls, the definition and statement checks, the standard-library replay of every identity behind the compared
statements, the metadata check, the module-resolution check, the elaboration check and Palomar's core-notation audit of
the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run
on the tree of the final commit (the counts are printed by verify.py); a build log is evidence for that tree only.
Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no
`definition_names`: a name there is a definition hole whose value the Solution supplies; the twenty definitions here are
fully specified in the Challenge, so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `proj_pauliVec` — Each Pauli eigenstate is the projector onto its unit vector | QubitCloning/States.lean |
| 2 | `pauliVec_unit` — The six vectors are unit vectors | QubitCloning/States.lean |
| 3 | `sixAvg_le` — Gisin–Massar's bound in the six-state form: for every channel the mean single-clone fidelity, averaged over the six Pauli eigenstates, is at most `5/6` | QubitCloning/Form.lean |
| 4 | `exists_unit_min_le` — No channel clones every pure state with both fidelities above `5/6`: some unit vector has `min (F₁, F₂) ≤ 5/6` | QubitCloning/Form.lean |
| 5 | `sixAvg_ge_third` — The six-state average of either clone's fidelity is at least `1/3` for every channel (the universal-NOT bound in average form: no channel anti-clones better than the universal NOT) | QubitCloning/Form.lean |
| 6 | `exists_sixAvg_eq_third` — The floor `1/3` is attained: the universal NOT on the first clone with a maximally mixed second clone | QubitCloning/BH.lean |
| 7 | `bh_isChannel` — The Bužek–Hillery map is a channel: it has a Kraus family | QubitCloning/BH.lean |
| 8 | `bh_trace` — The Bužek–Hillery map preserves the trace | QubitCloning/BH.lean |
| 9 | `bh_traceSecond` — The first marginal of the Bužek–Hillery channel is the depolarizing map `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1` | QubitCloning/BH.lean |
| 10 | `bh_traceFirst` — The second marginal of the Bužek–Hillery channel is the same depolarizing map | QubitCloning/BH.lean |
| 11 | `bh_fidelity` — Any Kraus family of the Bužek–Hillery channel clones every pure state with both fidelities `5/6` | QubitCloning/BH.lean |
| 12 | `bh_sixAvg` — Its six-state averages are `5/6` and `5/6` | QubitCloning/BH.lean |
| 13 | `eq_bh_of_sixAvg` — Equality in the bound forces the channel: a channel whose six-state mean fidelity is `5/6` is the Bužek–Hillery channel as a map | QubitCloning/Unique.lean |
| 14 | `eq_bh_of_forall` — A channel cloning every pure state with both fidelities at least `5/6` is the Bužek–Hillery channel | QubitCloning/Unique.lean |
| 15 | `isGreatest_cloning_fidelity` — `5/6` is the greatest worst-case common fidelity of a universal `1 → 2` qubit cloner: the greatest `t` for which some channel has `t ≤ F₁(ψ)` and `t ≤ F₂(ψ)` for every unit `ψ` | QubitCloning/Unique.lean |
| 16 | `asym_bound` — The asymmetric cloning bound: for every channel and all weights `a, b ≥ 0`, `a b ≤ a (a + 2b) (1 − F̄₁) + b (2a + b) (1 − F̄₂)` | QubitCloning/AsymForm.lean |
| 17 | `asym_bound_forall` — The same bound for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then `a b ≤ a (a + 2b) (1 − f₁) + b (2a + b) (1 − f₂)` | QubitCloning/AsymForm.lean |
| 18 | `asym_isChannel` — The asymmetric cloner is a channel for every `(a, b) ≠ (0, 0)` | QubitCloning/Asym.lean |
| 19 | `asym_traceSecond` — Its first marginal is the depolarizing map with shrinking factor `1 − b²/(a² + ab + b²)` | QubitCloning/Asym.lean |
| 20 | `asym_traceFirst` — Its second marginal is the depolarizing map with shrinking factor `1 − a²/(a² + ab + b²)` | QubitCloning/Asym.lean |
| 21 | `asym_fidelity` — Any Kraus family of the asymmetric cloner clones every pure state with fidelities `1 − b²/(2(a² + ab + b²))` and `1 − a²/(2(a² + ab + b²))` | QubitCloning/Asym.lean |
| 22 | `asym_equality` — The asymmetric cloner attains the bound with equality at its own weights | QubitCloning/Asym.lean |
| 23 | `eq_asym_of_equality` — Uniqueness of the asymmetric optimum: for `a, b > 0`, a channel with equality in the bound at the weights `(a, b)` is the asymmetric cloner `Λ_{a,b}` as a map | QubitCloning/AsymUnique.lean |
| 24 | `bhChannel_eq_asymChannel` — The Bužek–Hillery channel is the symmetric member `a = b` of the family | QubitCloning/BH.lean |
| 25 | `tradeoff_sqrt` — The trade-off in square-root form (Scarani–Iblisdir–Gisin–Acín 2005, Eq. (23)): `F̄₁ + F̄₂ − 3/2 ≤ √((1 − F̄₁)(1 − F̄₂))` for every channel | QubitCloning/Tradeoff.lean |
| 26 | `tradeoff_forall` — The trade-off for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then `f₁ + f₂ − 3/2 ≤ √((1 − f₁)(1 − f₂))` | QubitCloning/Tradeoff.lean |
| 27 | `tradeoff_attained` — The asymmetric cloners with `a, b ≥ 0` lie on the trade-off curve: equality in the square-root form (the curve of Niu–Griffiths 1998, Eq. (6.29)) | QubitCloning/Tradeoff.lean |

## What is checked

- **The build.** `lake build` of `QubitCloning`, `Challenge`, `Solution` and `Test` at Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`; every file has a `module` header; the lakefile sets no options.
- **The axiom audit.** `Test/Axioms.lean` walks every constant of the environment named under `QubitCloning.`,
  `_private.QubitCloning.` and `_private.Solution.` (193 constants at the final commit, floor 60) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `QubitCloning/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  requires identical output, and prints every compared theorem's type with Palomar's `core_notation_audit.lean`
  (47 rows: the twenty-seven theorems and the twenty definitions, exit 0).
- **The replay.** `scripts/check_cloning.py` (standard library only, Gaussian rationals, 582 checks, `VERDICT: PASS`,
  also under `python -O`): the six states as projectors; the six-state sums as quadratic forms `6Wᵢ = 1 + Ωᵢ` by
  polarization; the symmetric certificate `5·1 − 12W ⪰ 0` with its exact LDL, its kernel `span{v₁, v₂}`, the six-term
  sum of squares as a form identity, the sharpness of `5`, and the trace-preservation solve `(1/6, 2/3, 0)`; the
  Bužek–Hillery channel, its marginals on the basis matrices, its Choi matrix and its fidelities; the asymmetric family at
  eight rational points of the conic (channel, marginals, fidelities, equality, the certificate's LDL, kernel and
  sharpness, the trace-preservation solve), its agreement with the Bužek–Hillery channel at the symmetric point, the
  largest-eigenvalue formula at non-conic weights, the universal-NOT witness, and the polynomial sum of squares of the
  asymmetric certificate on a 4 × 4 grid of weights.
- **Metadata.** `formalization.yaml` parses, its title is within 300 characters, its `status.main_results` and
  `alignment` list the compared theorems in `comparator.json`'s order with every status `proved`, and it validates
  against the registry's v0.4 schema (fetched, not vendored).

## What is not checked

The equivalence of finite Kraus families with completely positive trace-preserving maps; the equality of the six-state
and Bloch-sphere averages; the registry's own Comparator and NanoDa replay (run at registration); the mathematics of
the papers beyond the statements formalized; significance or priority.
