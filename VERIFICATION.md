# Verification

All thirty-seven statements of Challenge.lean have proofs. The consultation checked the additions with the
unmodified, pinned Lean frontend at trust level 0 through a Lake script. The normal Lean CLI cannot start in
this environment because executable-path discovery is denied. Consequently, this review does not claim a fresh
normal `lake build`, an upstream CI run, or the registry's own Comparator/NanoDa run. The exact completed checks,
including source/replay checks, the axiom audit and elaboration comparisons, are recorded in
[REVIEW_VALIDATION.md](REVIEW_VALIDATION.md). The original repository's verification claim applies to its original
tree; a validation log is evidence only for the source tree and execution path it actually checked.

The standard reproducible command is `python scripts/verify.py --fetch-cache`; it must end with `VERIFY: PASS`
in a normal Lean environment. `.github/workflows/verify.yml` supplies that upstream gate. The source-only
`--skip-build` mode checks no Lean proof and reports that limitation explicitly.

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

| 28 | `tradeoff_full_sqrt` — Necessary full-range average-fidelity inequality | QubitCloning/FullTradeoff.lean |
| 29 | `signed_asym_bound` — Homogeneous bound when `(2a+b)(a+2b) ≥ 0` | QubitCloning/Signed.lean |
| 30 | `eq_asym_of_signed_equality` — Signed equality uniqueness for positive product and nonzero parameters | QubitCloning/Signed.lean |
| 31 | `clone_anticlone_bound` — `3F̄₁ − 5F̄₂ ≤ 1` | QubitCloning/Signed.lean |
| 32 | `clone_anticlone_attained` — Two-Kraus attainment of `(13/14,5/14)` | QubitCloning/Signed.lean |
| 33 | `eq_clone_anticlone_of_equality` — Unique extremizer `Λ_{3,−1}` of the signed support | QubitCloning/Signed.lean |
| 34 | `sixAvg₁_le_of_sixAvg₂_eq_third` — `F̄₂ = 1/3` implies `F̄₁ ≤ 5/6` | QubitCloning/Signed.lean |
| 35 | `sixAvg₂_le_of_sixAvg₁_eq_third` — The floor-companion bound with outputs exchanged | QubitCloning/Signed.lean |
| 36 | `floor_companion_attained` — Two-Kraus attainment of `(5/6,1/3)` on every pure input | QubitCloning/Signed.lean |
| 37 | `kraus_span_stability` — Total squared distance to the optimal Kraus span is at most `6ε` | QubitCloning/Stability.lean |

## What the standard verifier checks

- **The build.** `lake build` of `QubitCloning`, `Challenge`, `Solution` and `Test` at Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`; every file has a `module` header; the lakefile sets no options.
- **The axiom audit.** `Test/Axioms.lean` walks every constant of the environment named under `QubitCloning.`,
  `_private.QubitCloning.` and `_private.Solution.` (237 constants in this update; 193 at the original commit; floor 180) and fails on
  any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `decide +kernel`.
- **The source guard** (`scripts/check-source.py`, exercised by `scripts/check_source_guard.py`): no `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `set_option` or debug option outside comments and strings in the
  development, the Solution and the Test; no control bytes in the scripts.
- **Statements.** `scripts/check_definitions.py` compares every definition block of Challenge.lean with
  `QubitCloning/Defs.lean` character for character and the imports; `scripts/check_statements.py` compares every theorem
  header of Challenge.lean with Solution.lean; verify.py prints every definition with `pp.all` from both modules and
  requires identical output, and prints every compared theorem's type with Palomar's `core_notation_audit.lean`
  (57 rows: the thirty-seven theorems and the twenty definitions).
- **The replay.** `scripts/check_cloning.py` (standard library only, Gaussian rationals, 582 checks, `VERDICT: PASS`,
  also under `python -O`): the six states as projectors; the six-state sums as quadratic forms `6Wᵢ = 1 + Ωᵢ` by
  polarization; the symmetric certificate `5·1 − 12W ⪰ 0` with its exact LDL, its kernel `span{v₁, v₂}`, the six-term
  sum of squares as a form identity, the sharpness of `5`, and the trace-preservation solve `(1/6, 2/3, 0)`; the
  Bužek–Hillery channel, its marginals on the basis matrices, its Choi matrix and its fidelities; the asymmetric family at
  eight rational points of the conic (channel, marginals, fidelities, equality, the certificate's LDL, kernel and
  sharpness, the trace-preservation solve), its agreement with the Bužek–Hillery channel at the symmetric point, the
  largest-eigenvalue formula at non-conic weights, the universal-NOT witness, and the polynomial sum of squares of the
  asymmetric certificate on a 4 × 4 grid of weights.
- **The extension replay.** `scripts/check_extensions.py` adds 62 exact rational checks, also under isolated
  ordinary and optimized Python: every coefficient of the Gram, signed-SOS, projection and coercivity identities;
  signed-domain and sharpness examples; direct six-state fidelities of the signed extremizers; and deliberate
  perturbations that the checks must reject. These supplement the 582 original checks.
- **Metadata.** `formalization.yaml` parses, its title is within 300 characters, its `status.main_results` and
  `alignment` list the compared theorems in `comparator.json`'s order with every status `proved`, and it validates
  against the registry's v0.4 schema when `scripts/formalization.schema.json` is present. Local schema validation
  is conditional on that file and the `jsonschema` package. The new CI workflow explicitly installs the validators
  and fetches the official `v0.4.schema.json`, making that gate mandatory there. The consult independently validated
  the final metadata against the official v0.4 schema.

## What is not checked

The equivalence of finite Kraus families with completely positive trace-preserving maps; the equality of the six-state
and Bloch-sphere averages; the registry's own Comparator and NanoDa replay (run at registration); general sufficiency of the full-range
region; the handwritten Choi/diamond bounds and sharpness in STABILITY.md; the mathematics of
the papers beyond the statements formalized; significance or priority.
