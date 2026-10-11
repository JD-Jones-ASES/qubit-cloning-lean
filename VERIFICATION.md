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
| 1 | `proj_pauliVec` — One qubit: the index type `Fin 2`. -/ abbrev Q : Type := Fin 2 /-- Two qubits, the first clone then the second: the index type `Fin 2 × Fin 2`. -/ abbrev QQ : Type := Fin 2 × Fin 2 /-- The action of a Kraus family on a one-qubit matrix: `ρ ↦ Σᵢ Kᵢ ρ Kᵢᴴ`. -/ def krausApply {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ := ∑ i, K i * ρ * (K i)ᴴ /-- A channel from one qubit to two: a finite Kraus family with `Σᵢ Kᵢᴴ Kᵢ = 1` (trace preservation; complete positivity is built into the Kraus form). -/ def IsChannel {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : Prop := ∑ i, (K i)ᴴ * K i = 1 /-- The partial trace over the second clone: `(a, b) ↦ Σ_k M (a, k) (b, k)`. -/ def traceSecond (M : Matrix QQ QQ ℂ) : Matrix Q Q ℂ := Matrix.of fun a b => ∑ k, M (a, k) (b, k) /-- The partial trace over the first clone: `(a, b) ↦ Σ_k M (k, a) (k, b)`. -/ def traceFirst (M : Matrix QQ QQ ℂ) : Matrix Q Q ℂ := Matrix.of fun a b => ∑ k, M (k, a) (k, b) /-- The projector `ψ ψ†` onto a vector. -/ def proj (ψ : Q → ℂ) : Matrix Q Q ℂ := Matrix.vecMulVec ψ (star ψ) /-- The fidelity of the pure state `ρ = ψψ†` with a state `σ`: `Re Tr(ρ σ) = ⟨ψ|σ|ψ⟩`. -/ def fidelity (ρ σ : Matrix Q Q ℂ) : ℝ := (Matrix.trace (ρ * σ)).re /-- The first clone's fidelity on the pure input `ψ`. -/ def F₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ψ : Q → ℂ) : ℝ := fidelity (proj ψ) (traceSecond (krausApply K (proj ψ))) /-- The second clone's fidelity on the pure input `ψ`. -/ def F₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ψ : Q → ℂ) : ℝ := fidelity (proj ψ) (traceFirst (krausApply K (proj ψ))) /-- The six Pauli eigenstates as density matrices `(1 ± σ)/2`: `0, 1` the `σ_z` eigenstates `|0⟩, |1⟩`; `2, 3` the `σ_x` eigenstates `|±⟩`; `4, 5` the `σ_y` eigenstates `|±i⟩`. -/ def pauliState : Fin 6 → Matrix Q Q ℂ := ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![1 / 2, 1 / 2; 1 / 2, 1 / 2], !![1 / 2, -1 / 2; -1 / 2, 1 / 2], !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2], !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]] /-- The six Pauli eigenstates as unit vectors: `|0⟩, |1⟩, (|0⟩ ± |1⟩)/√2, (|0⟩ ± i|1⟩)/√2`. -/ def pauliVec : Fin 6 → (Q → ℂ) := ![![1, 0], ![0, 1], ![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹], ![(Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹], ![(Real.sqrt 2 : ℂ)⁻¹, Complex.I * (Real.sqrt 2 : ℂ)⁻¹], ![(Real.sqrt 2 : ℂ)⁻¹, -(Complex.I * (Real.sqrt 2 : ℂ)⁻¹)]] /-- The six-state average of the first clone's fidelity. -/ def sixAvg₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : ℝ := (∑ s, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s)))) / 6 /-- The six-state average of the second clone's fidelity. -/ def sixAvg₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : ℝ := (∑ s, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s)))) / 6 /-- Bužek–Hillery's first operator: `V₁|0⟩ = 2|00⟩`, `V₁|1⟩ = |01⟩ + |10⟩`. -/ def bhV₁ : Matrix QQ Q ℂ := Matrix.of fun x i => if x = (0, 0) ∧ i = 0 then 2 else if (x = (0, 1) ∨ x = (1, 0)) ∧ i = 1 then 1 else 0 /-- Bužek–Hillery's second operator: `V₂|0⟩ = (|01⟩ + |10⟩)/2`, `V₂|1⟩ = |11⟩`. -/ def bhV₂ : Matrix QQ Q ℂ := Matrix.of fun x i => if (x = (0, 1) ∨ x = (1, 0)) ∧ i = 0 then 1 / 2 else if x = (1, 1) ∧ i = 1 then 1 else 0 /-- The Bužek–Hillery channel as a map: `ρ ↦ (1/6) V₁ ρ V₁ᴴ + (2/3) V₂ ρ V₂ᴴ` (Bužek–Hillery 1996; the Kraus operators are `V₁/√6` and `√(2/3) V₂`). -/ def bhChannel (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ := (1 / 6 : ℂ) • (bhV₁ * ρ * bhV₁ᴴ) + (2 / 3 : ℂ) • (bhV₂ * ρ * bhV₂ᴴ) /-- The asymmetric cloner's first operator: `A₀|0⟩ = (a + b)|00⟩`, `A₀|1⟩ = a|10⟩ + b|01⟩`. -/ def asymA₀ (a b : ℝ) : Matrix QQ Q ℂ := Matrix.of fun x i => if x = (0, 0) ∧ i = 0 then ((a + b : ℝ) : ℂ) else if x = (1, 0) ∧ i = 1 then (a : ℂ) else if x = (0, 1) ∧ i = 1 then (b : ℂ) else 0 /-- The asymmetric cloner's second operator: `A₁|0⟩ = a|01⟩ + b|10⟩`, `A₁|1⟩ = (a + b)|11⟩`. -/ def asymA₁ (a b : ℝ) : Matrix QQ Q ℂ := Matrix.of fun x i => if x = (0, 1) ∧ i = 0 then (a : ℂ) else if x = (1, 0) ∧ i = 0 then (b : ℂ) else if x = (1, 1) ∧ i = 1 then ((a + b : ℝ) : ℂ) else 0 /-- The asymmetric cloning channel with weights `a, b` (not both zero), as a map: `ρ ↦ (A₀ ρ A₀ᴴ + A₁ ρ A₁ᴴ) / (2(a² + ab + b²))` (the optimal asymmetric cloner of Niu–Griffiths 1998 and Cerf 1998 in these coordinates; `a = b` is the Bužek–Hillery channel; the Kraus operators are `A₀, A₁` divided by `√(2(a² + ab + b²))`). -/ def asymChannel (a b : ℝ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ := ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ)⁻¹ : ℂ) • (asymA₀ a b * ρ * (asymA₀ a b)ᴴ + asymA₁ a b * ρ * (asymA₁ a b)ᴴ) /-! ## The six states -/ /-- Each Pauli eigenstate is the projector onto its unit vector | QubitCloning/States.lean |
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
  `_private.QubitCloning.` and `_private.Solution.` (197 constants at the final commit, floor 60) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `QubitCloning/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  requires identical output, and prints every compared theorem's type with Palomar's `core_notation_audit.lean`
  (47 rows: the twenty-seven theorems and the twenty definitions, exit 0).
- **The replay.** `scripts/check_cloning.py` (standard library only, Gaussian rationals, 583 checks, `VERDICT: PASS`,
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
