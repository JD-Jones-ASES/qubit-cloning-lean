# Verification

All forty-four statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and its
controls, the definition and statement checks, the standard-library replays of every identity behind the compared
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
| 28 | `tradeoff_full_sqrt` — For every channel, `3(F̄₁ + F̄₂) − 7/2 ≤ √((3F̄₁ − 1)(3F̄₂ − 1))`: the full-range trade-off, which also binds where a clone's average fidelity is below `1/2`, where the square-root form is vacuous | QubitCloning/FullTradeoff.lean |
| 29 | `signed_asym_bound` — For every channel and all real `a, b` with `(2a + b)(a + 2b) ≥ 0`, `ab ≤ a(a + 2b)(1 − F̄₁) + b(2a + b)(1 − F̄₂)`: the bound `asym_bound` with `0 ≤ a`, `0 ≤ b` replaced by `(2a + b)(a + 2b) ≥ 0` | QubitCloning/Signed.lean |
| 30 | `eq_asym_of_signed_equality` — For real `a, b ≠ 0` with `(2a + b)(a + 2b) > 0`, a channel with equality in the signed bound at `(a, b)` is `Λ_{a,b}` as a map | QubitCloning/Signed.lean |
| 31 | `clone_anticlone_bound` — For every channel, `3F̄₁ − 5F̄₂ ≤ 1` (the signed bound at the weights `(3, −1)`) | QubitCloning/Signed.lean |
| 32 | `clone_anticlone_attained` — `Λ_{3,−1}` is a two-operator channel with the average fidelities `(13/14, 5/14)`, where `3F̄₁ − 5F̄₂ = 1` | QubitCloning/Signed.lean |
| 33 | `eq_clone_anticlone_of_equality` — A channel with `3F̄₁ − 5F̄₂ = 1` is `Λ_{3,−1}` as a map | QubitCloning/Signed.lean |
| 34 | `sixAvg₁_le_of_sixAvg₂_eq_third` — If the second clone attains the universal-NOT floor, the first clone's average fidelity is at most `5/6` | QubitCloning/FullTradeoff.lean |
| 35 | `sixAvg₂_le_of_sixAvg₁_eq_third` — If the first clone attains the universal-NOT floor, the second clone's average fidelity is at most `5/6` | QubitCloning/FullTradeoff.lean |
| 36 | `floor_companion_attained` — `Λ_{2,−1}` is a two-operator channel with `F̄₁ = 5/6` and `F̄₂ = 1/3`, and with `F₁(ψ) = 5/6`, `F₂(ψ) = 1/3` on every unit `ψ`: the universal-NOT floor on the second clone with `5/6` on the first | QubitCloning/Signed.lean |
| 37 | `kraus_span_stability` — If `(F̄₁ + F̄₂)/2 ≥ 5/6 − ε`, there are coefficients `xᵢ, yᵢ` with `Σᵢ ‖Kᵢ − xᵢV₁ − yᵢV₂‖² ≤ 6ε`: every Kraus family of a near-optimal channel is near the Bužek–Hillery Kraus space | QubitCloning/Stability.lean |
| 38 | `tradeoff_full_attained` — Along the asymmetric family with `(2a + b)(a + 2b) ≥ 0` the full-range trade-off is an equality: both sides equal `(2a + b)(a + 2b)/(2(a² + ab + b²))` | QubitCloning/FullEquality.lean |
| 39 | `eq_asym_of_tradeoff_full_equality` — Equality in the full-range trade-off away from the perfect-clone points `(1, 1/2)` and `(1/2, 1)` forces a member of the asymmetric family with both weights nonzero and `(2a + b)(a + 2b) ≥ 0`: the boundary arc of the region is the family | QubitCloning/FullEquality.lean |
| 40 | `eq_asym_of_floor₂` — The companion of the universal-NOT floor on the second clone is unique: `F̄₁ = 5/6` and `F̄₂ = 1/3` force `Λ_{2,−1}` as a map | QubitCloning/FullEquality.lean |
| 41 | `eq_asym_of_floor₁` — The companion of the universal-NOT floor on the first clone is unique: `F̄₁ = 1/3` and `F̄₂ = 5/6` force `Λ_{−1,2}` as a map | QubitCloning/FullEquality.lean |
| 42 | `sixAvg₂_eq_half_of_sixAvg₁_eq_one` — A perfect first clone on average forces the second output's average fidelity to be `1/2` | QubitCloning/FullEquality.lean |
| 43 | `sixAvg₁_eq_half_of_sixAvg₂_eq_one` — A perfect second clone on average forces the first output's average fidelity to be `1/2` | QubitCloning/FullEquality.lean |
| 44 | `channel_stability` — If the six-state mean fidelity is at least `5/6 − ε`, the channel is within Frobenius distance `200 √ε ‖ρ‖_F` of the Bužek–Hillery channel on every input `ρ` | QubitCloning/ChannelStability.lean |

## What is checked

- **The build.** `lake build` of `QubitCloning`, `Challenge`, `Solution` and `Test` at Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`; every file has a `module` header; the lakefile sets no options.
- **The axiom audit.** `Test/Axioms.lean` walks every constant of the environment named under `QubitCloning.`,
  `_private.QubitCloning.` and `_private.Solution.` (298 constants at the final commit, floor 180) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `QubitCloning/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  every compared theorem's type from the Challenge and the Solution, and requires identical output, and prints every compared theorem's type with Palomar's `core_notation_audit.lean`
  (64 rows: the forty-four theorems and the twenty definitions, exit 0).
- **The replay.** `scripts/check_cloning.py` (standard library only, Gaussian rationals, 582 checks, `VERDICT: PASS`,
  also under `python -O`): the six states as projectors; the six-state sums as quadratic forms `6Wᵢ = 1 + Ωᵢ` by
  polarization; the symmetric certificate `5·1 − 12W ⪰ 0` with its rational LDL, its kernel `span{v₁, v₂}`, the six-term
  sum of squares as a form identity, that `5` cannot be lowered, and the trace-preservation solve `(1/6, 2/3, 0)`; the
  Bužek–Hillery channel, its marginals on the basis matrices, its Choi matrix and its fidelities; the asymmetric family at
  eight rational points of the conic (channel, marginals, fidelities, equality, the certificate's LDL, kernel and
  least constant, the trace-preservation solve), its agreement with the Bužek–Hillery channel at the symmetric point, the
  largest-eigenvalue formula at non-conic weights, the universal-NOT witness, and the polynomial sum of squares of the
  asymmetric certificate on a 4 × 4 grid of weights.
- **The extension replay.** `scripts/check_extensions.py` (standard library only, rational arithmetic, 66 checks,
  `VERDICT: PASS`, also under `python -O`): the Gram identity of `FullTradeoff.lean` and the signed certificate as
  coefficient matrices (the latter in each of `a²`, `ab`, `b²`), with the signed form positive semidefinite where
  `(2a + b)(a + 2b) ≥ 0` and not elsewhere at sample weights; the projection onto `span{V₁, V₂}`, the coercivity identity
  and its gap `2`; the signed channels at rational weights (complete positivity and trace preservation, the six-state
  averages, the full-range bound and its equality); the point `(13/14, 5/14)`; the nonsingular trace-preservation
  equations; the distance `6ε` and the Frobenius distance to the Bužek–Hillery output at `|0⟩⟨0|` along `Λ_{1+t,1−t}`; and perturbed inputs that the checks must reject.
- **Metadata.** `formalization.yaml` parses, its title is within 300 characters, and its `status.main_results` and
  `alignment` list the compared theorems in `comparator.json`'s order with every status `proved`. verify.py validates
  it against the registry's v0.4 schema only when a copy is present at `scripts/formalization.schema.json`, and none is
  shipped; the yaml of the final commit was validated separately against the fetched v0.4 schema, with 0 errors.

## What is not checked

The equivalence of finite Kraus families with completely positive trace-preserving maps; the equality of the six-state
and Bloch-sphere averages; the registry's own Comparator and NanoDa replay (run at registration); the realization of
every point of the full-range region; the trace-norm and diamond-norm forms of the stability; the mathematics of the
papers beyond the statements formalized; significance.
