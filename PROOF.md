# The proofs

A Kraus operator `K : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ` has entries `K (a, b) r` (input `r`, first clone `a`, second
clone `b`); `‖K‖² = Σ |K x i|²`; `uⱼ(K) = K (0, j) 0 + K (1, j) 1` and `vⱼ(K) = K (j, 0) 0 + K (j, 1) 1` (`j = 0, 1`) are
the pairings of `vec K` with `|00j⟩ + |11j⟩` and `|0j0⟩ + |1j1⟩`. The six Pauli eigenstates are the density matrices
`(1 ± σ)/2` (`pauliState`); every six-state sum below is a quadratic form in the sixteen real and imaginary parts of
the eight entries, and every identity is closed by `ring` after unfolding (the exact replay is `scripts/check_cloning.py`).

1. **The ground floor** (`QubitCloning/States.lean`). `fidelity (proj ψ) σ = Re (ψ† σ ψ)`; the Kraus action, the
   partial traces and the fidelity are additive, so `sixAvgᵢ K = Σᵢ sixAvgᵢ ![K i]` (`st_sixAvg₁_eq_sum`,
   `st_sixAvg₂_eq_sum`); `proj (pauliVec s) = pauliState s` (`proj_pauliVec`: the four equatorial vectors carry `(√2)⁻¹`,
   whose square is `1/2`) and the six vectors are unit (`pauliVec_unit`), so `F₁ K (pauliVec s)` is the `s`-th six-state
   term (`st_F₁_pauliVec`) and a pointwise lower bound on the six vectors bounds the average (`st_le_sixAvg₁`); the trace
   of `Σ Kᵢᴴ Kᵢ = 1` gives `Σᵢ ‖Kᵢ‖² = 2` for a channel (`st_isChannel_normSq_sum`); for a unit `ψ` and real `c, d`,
   `fidelity (proj ψ) (c • proj ψ + d • Tr(proj ψ) • 1) = c + d` (`st_fidelity_depolarized`).
2. **The symmetric certificate** (`Form.lean`). For one Kraus operator, `6 · sixAvg₁ ![K] = ‖K‖² + Σⱼ |uⱼ(K)|²` and
   `6 · sixAvg₂ ![K] = ‖K‖² + Σⱼ |vⱼ(K)|²` (`form_six_one`, `form_six_two`: the six-state average of `ψ̄ψ̄† ⊗ ψψ†` over
   the octahedron is `(1 + Ω)/6`, Gisin–Massar's and Fiurášek–Filip–Cerf's averaged operator, written out). The
   six-term sum of squares (`form_sos`): `5 ‖K‖² − 6 (sixAvg₁ + sixAvg₂) ![K] = |k₀₀₀ − k₁₀₁ − k₁₁₀|² + 2|k₀₀₁ − k₁₁₁/2|²
   + 2|k₀₁₀ − k₁₁₁/2|² + 3|k₀₁₁|² + 3|k₁₀₀|² + |k₁₀₁ − k₁₁₀|²` (`k_{rab} = K (a, b) r`; the exact LDL of `5·1 − 12W`, whose
   kernel is `span{vec V₁, vec V₂}`). Summing over the family and using `Σ ‖Kᵢ‖² = 2`: `6 (sixAvg₁ + sixAvg₂) ≤ 10`, i.e.
   `(F̄₁ + F̄₂)/2 ≤ 5/6` (`sixAvg_le`); the squares in `form_six_one` give `F̄ᵢ ≥ 2/6 = 1/3` (`sixAvg_ge_third`); if every
   six-state mean exceeded `5/6` so would the average, so some `pauliVec s` has `min(F₁, F₂) ≤ 5/6` (`exists_unit_min_le`).
3. **The Bužek–Hillery channel** (`BH.lean`). `bhChannel ρ = (1/6) V₁ ρ V₁ᴴ + (2/3) V₂ ρ V₂ᴴ` is the Kraus action of
   `![(√6)⁻¹ • V₁, 2(√6)⁻¹ • V₂]`, and `(1/6) V₁ᴴV₁ + (2/3) V₂ᴴV₂ = 1` entrywise (`bh_isChannel`); both marginals are
   `(2/3) ρ + (1/6) Tr(ρ)·1` by the four entries (`bh_traceSecond`, `bh_traceFirst`; `bh_trace`), so `F₁ = F₂ = 2/3 + 1/6
   = 5/6` on every unit `ψ` by `st_fidelity_depolarized` (`bh_fidelity`, `bh_sixAvg`). `asymA₀ 1 1 = V₁`, `asymA₁ 1 1 =
   2 V₂` and `(2 · 3)⁻¹ · 4 = 2/3` give `bhChannel = asymChannel 1 1` (`bhChannel_eq_asymChannel`). The floor is attained
   by the six Kraus operators `(√6)⁻¹ σ ⊗ |j⟩` (`σ ∈ {X, XZ, Z}`, `XZ = −iY`, the phase dropping out; `j ∈ {0, 1}`): the first marginal is `(1/3)(XρX + YρY
   + ZρZ) = (2/3) Tr(ρ)·1 − (1/3) ρ`, whose fidelity with each Pauli state is `1/3` (`exists_sixAvg_eq_third`).
4. **Uniqueness of the symmetric optimum** (`Unique.lean`). Equality `(F̄₁ + F̄₂)/2 = 5/6` forces the total of the
   nonnegative squares of `form_sos` over the family to vanish, so each `Kᵢ` has `Kᵢ (1,1) 0 = Kᵢ (0,0) 1 = 0`,
   `Kᵢ (0,1) 1 = Kᵢ (1,0) 1`, `Kᵢ (0,0) 0 = 2 Kᵢ (0,1) 1`, `Kᵢ (0,1) 0 = Kᵢ (1,0) 0 = Kᵢ (1,1) 1 / 2`: `Kᵢ = xᵢ • V₁ + yᵢ • V₂`
   with `xᵢ = Kᵢ (0,1) 1`, `yᵢ = Kᵢ (1,1) 1`. The channel equation reads, with `V₁ᴴV₁ = diag(4, 2)`, `V₂ᴴV₂ = diag(1/2, 1)`,
   `V₁ᴴV₂ = E₁₀`: `Σ x̄ᵢ yᵢ = 0`, `4X + Y/2 = 1`, `2X + Y = 1` (`X = Σ|xᵢ|²`, `Y = Σ|yᵢ|²`), so `X = 1/6`, `Y = 2/3`, and
   `Σᵢ Kᵢ ρ Kᵢᴴ = X V₁ρV₁ᴴ + Y V₂ρV₂ᴴ` (`eq_bh_of_sixAvg`). Pointwise bounds `F₁, F₂ ≥ 5/6` on every unit vector give
   averages `≥ 5/6`, hence `= 5/6` (`eq_bh_of_forall`). `5/6` is attained (`bh_isChannel`, `bh_fidelity`) and no `t`
   above it is, by `exists_unit_min_le` (`isGreatest_cloning_fidelity`).
5. **The asymmetric certificate** (`AsymForm.lean`). The identity, polynomial in `a, b` with no side condition
   (`af_sos`): `(2a + b)(a + 2b) ‖K‖² − a(a + 2b) Σⱼ |uⱼ|² − b(2a + b) Σⱼ |vⱼ|² = (1/3) Σⱼ |(a + 2b) uⱼ − (2a + b) vⱼ|²
   + (2a + b)(a + 2b) (|k₀₁₁|² + |k₁₀₀|² + |k₀₀₀ − k₁₁₀ − k₁₀₁|²/3 + |k₁₁₁ − k₀₀₁ − k₀₁₀|²/3)` — on each clone-index
   block the operator `a(a + 2b) ũⱼũⱼ† + b(2a + b) ṽⱼṽⱼ†` (`⟨ũ, ṽ⟩ = 1`, norms `2`) has top eigenvalue `(2a + b)(a + 2b)`
   with eigenvector `a ũⱼ + b ṽⱼ` and bottom eigenvalue `3ab` with eigenvector `(a + 2b) ũⱼ − (2a + b) ṽⱼ`, and the four
   written vectors span the orthogonal complement. With `af_weighted_eq` (the sums of `form_six_one`, `form_six_two`) and
   `Σ ‖Kᵢ‖² = 2`, dropping the squares for `a, b ≥ 0` gives `6 (a(a + 2b) F̄₁ + b(2a + b) F̄₂) ≤ 6 (a² + 3ab + b²)`, i.e.
   `ab ≤ a(a + 2b)(1 − F̄₁) + b(2a + b)(1 − F̄₂)` (`asym_bound`); with worst-case fidelities through `st_le_sixAvg₁/₂`
   (`asym_bound_forall`). This is Fiurášek–Filip–Cerf's largest-eigenvalue bound at `d = 2` for the weights
   `(a(a + 2b), b(2a + b))`, where the square root of their eigenvalue formula is `a² + ab + b²`.
6. **The family** (`Asym.lean`). `A₀ᴴA₀ + A₁ᴴA₁ = 2(a² + ab + b²)·1` (`as_gram`), so `asymChannel a b` is the Kraus action
   of `![c • A₀, c • A₁]`, `c = (√(2(a² + ab + b²)))⁻¹`, when `a² + ab + b² ≠ 0` (`asym_isChannel`); the marginals by the
   four entries (`asym_traceSecond`, `asym_traceFirst`), the fidelities by `st_fidelity_depolarized` (`asym_fidelity`),
   and the six-state averages `1 − b²/2s`, `1 − a²/2s` satisfy `a(a + 2b)·b²/2s + b(2a + b)·a²/2s = ab` (`asym_equality`).
7. **Uniqueness of the asymmetric optimum** (`AsymUnique.lean`). For `a, b > 0`, equality in `asym_bound` forces every
   square of `af_sos` to vanish for every `Kᵢ`: `Kᵢ (1,1) 0 = Kᵢ (0,0) 1 = 0`, `Kᵢ (0,0) 0 = Kᵢ (1,0) 1 + Kᵢ (0,1) 1`,
   `Kᵢ (1,1) 1 = Kᵢ (0,1) 0 + Kᵢ (1,0) 0`, `(a + 2b) uⱼ = (2a + b) vⱼ`; these leave the span of `vec A₀ = (a + b)|000⟩ +
   a|110⟩ + b|101⟩` and `vec A₁ = a|001⟩ + b|010⟩ + (a + b)|111⟩`, so `Kᵢ = xᵢ • A₀ + yᵢ • A₁`. The channel equation with
   `A₀ᴴA₀ = diag((a + b)², a² + b²)`, `A₁ᴴA₁ = diag(a² + b², (a + b)²)`, `A₀ᴴA₁ = 2ab E₁₀` gives `Σ x̄ᵢ yᵢ = 0` and
   `X = Y = (2(a² + ab + b²))⁻¹`, hence `Σᵢ Kᵢ ρ Kᵢᴴ = asymChannel a b ρ` (`eq_asym_of_equality`).
8. **The square-root form** (`Tradeoff.lean`). If `ab ≤ a(a + 2b) D₁ + b(2a + b) D₂` for all `a, b ≥ 0` then `D₁, D₂ ≥ 0`
   (`(a, b) = (1, 0), (0, 1)`) and `1/2 ≤ D₁ + D₂ + √(D₁D₂)`: with `g = √(D₁D₂)`, `a = √(2D₂)`, `b = √(2D₁)` the bound reads
   `2g ≤ 4g² + 4g(D₁ + D₂)`, which for `g > 0` is the claim; for `g = 0`, say `D₁ = 0`, the bound at `(1, t)` gives
   `1 ≤ (2 + t) D₂` for every `t > 0`, so `D₂ ≥ 1/2` (`tr_of_bounds`). Applied to `asym_bound` and `asym_bound_forall` with
   `Dᵢ = 1 − F̄ᵢ` resp. `1 − fᵢ` this is `tradeoff_sqrt` and `tradeoff_forall`. Along the family with `a, b ≥ 0`, both
   sides equal `ab/(2s)` (`tradeoff_attained`).
