# ARCH — the module map of `qubit-cloning-lean` (desk, 2026-10-11; stripped before registration)

The pinned statements are `Challenge.lean` (read-only for lanes); the definitions are restated in
`QubitCloning/Defs.lean` (read-only). Each module below holds the `_internal` twins of its Challenge theorems and the
desk's pinned helpers, all `sorry` in the skeleton; `Solution.lean` closes every Challenge theorem by its twin. The
desk's exact replay of every identity is the bench's `probe.py` (583 checks, PROBE: PASS; its sections H1–H5' are
cited below). Conventions: a Kraus operator `K : Matrix QQ Q ℂ` has entries `K (a, b) r` = `k_{r a b}` (input `r`,
first clone `a`, second clone `b`); `‖K‖² = Σ_{x, i} normSq (K x i)`; `uⱼ(K) = K (0, j) 0 + K (1, j) 1` and
`vⱼ(K) = K (j, 0) 0 + K (j, 1) 1` (`j = 0, 1`) are the pairings with `|00j⟩ + |11j⟩` and `|0j0⟩ + |1j1⟩`.

## §1 States (lane `states`) — the ground floor, imported by everyone
`fidelity (proj ψ) σ = Re (ψ† σ ψ)` (`st_fidelity_proj`); additivity of `krausApply` over the family, of the partial
traces and of the fidelity (`st_*_sum`, `st_*_smul`); `sixAvgᵢ K = Σᵢ sixAvgᵢ ![K i]` (`st_sixAvg₁_eq_sum`,
`st_sixAvg₂_eq_sum`); `F₁ K (pauliVec s)` is the `s`-th six-state term (`st_F₁_pauliVec`), via
`proj_pauliVec : proj (pauliVec s) = pauliState s` (the four equatorial vectors carry `(√2)⁻¹`; the projector entries
are `(√2)⁻¹ · conj((√2)⁻¹) = 1/2`, `Real.mul_self_sqrt`, `Complex.ofReal_inv`, `Complex.normSq`); `pauliVec_unit`;
pointwise lower bounds on the six vectors bound the averages (`st_le_sixAvg₁/₂`: average of six terms each `≥ f`);
`Σᵢ ‖Kᵢ‖² = 2` for a channel (`st_isChannel_normSq_sum`: take the trace of `Σ Kᵢᴴ Kᵢ = 1`,
`Matrix.trace_mul_comm`-free: `(Kᴴ K) i i = Σ_x conj (K x i) K x i`, `Complex.normSq_eq_conj_mul_self`);
`fidelity (proj ψ) (c • proj ψ + d • Tr(proj ψ) • 1) = c + d` for unit `ψ` (`st_fidelity_depolarized`:
`proj ψ * proj ψ = proj ψ` from `ψ† ψ = 1`, `Tr (proj ψ) = 1`).

## §2 Form (lane `form`) — the symmetric certificate
`form_six_one`, `form_six_two`: for one Kraus operator the six-state sums are `‖K‖² + Σⱼ |uⱼ|²` and `‖K‖² + Σⱼ |vⱼ|²`
(probe H1: `6 Wᵢ = 1 + Ωᵢ`). Route: unfold `sixAvg₁`, `pauliState`, `krausApply`, `traceSecond`, `fidelity`, `trace`,
`mul_apply` with `Fin.sum_univ_two`, `Fintype.sum_prod_type`, `Matrix.of_apply`, `Matrix.cons_val_*`; the result is a
real polynomial identity in the sixteen real and imaginary parts (`Complex.ext_iff`, `Complex.normSq_apply`,
`Complex.add_re`, `Complex.mul_re`, `Complex.I_re`, …), closed by `ring`. `form_sos`: the six-term sum of squares
(probe H2) — `6 (sixAvg₁ + sixAvg₂) ![K] = 5 ‖K‖² − SOS(K)`; the same expansion, or `form_six_one + form_six_two` and
`ring`/`linear_combination`. Then `sixAvg_le`: sum `form_sos` over `i` with `st_sixAvg₁_eq_sum`, drop the squares
(`Complex.normSq_nonneg`, `Finset.sum_nonneg`), use `st_isChannel_normSq_sum`. `sixAvg_ge_third`: from
`form_six_one` summed, the squares are `≥ 0` and `Σ ‖Kᵢ‖² = 2`. `exists_unit_min_le`: if every six-state term of
`(F₁ + F₂)/2` exceeded `5/6` the average would (`Finset.exists_le_of_sum_le` or a direct `by_contra` with
`Finset.sum_lt_sum`); take `ψ = pauliVec s` with `pauliVec_unit`, `st_F₁_pauliVec`, `st_F₂_pauliVec`.

## §3 BH (lane `bh`) — the Bužek–Hillery channel and the universal-NOT witness
`bh_isChannel`: `K = ![((Real.sqrt 6)⁻¹ : ℂ) • bhV₁, (2 * (Real.sqrt 6)⁻¹ : ℂ) • bhV₂]` (`4/6 = 2/3`); `Σ Kᴴ K = (1/6) V₁ᴴV₁ + (4/6) V₂ᴴV₂ = 1` by `ext i j; fin_cases`,
`simp [bhV₁, bhV₂, Matrix.mul_apply, Fintype.sum_prod_type]`, `Real.mul_self_sqrt`; `krausApply K ρ = bhChannel ρ`
by the same scalar facts (`(√6)⁻¹ · conj (√6)⁻¹ = 1/6`). `bh_traceSecond`/`bh_traceFirst` (probe H3): `ext a b;
fin_cases a <;> fin_cases b; simp [bhChannel, traceSecond, bhV₁, bhV₂, Matrix.mul_apply, Fintype.sum_prod_type,
Matrix.one_apply, Matrix.trace]; ring`. `bh_trace` from either marginal (`Matrix.trace_fin_two`) or directly.
`bh_fidelity`: rewrite `F₁ K ψ` through `hK`, `bh_traceSecond`, `st_fidelity_depolarized` with `c = 2/3`, `d = 1/6`.
`bh_sixAvg`: each six-state term is `5/6` (`pauliState s = proj (pauliVec s)` and `bh_fidelity`, or directly). `bhChannel_eq_asymChannel`:
`asymA₀ 1 1 = bhV₁`, `asymA₁ 1 1 = 2 • bhV₂` (`ext; fin_cases; simp`), and `(2·3)⁻¹ · 4 = 2/3`.
`exists_sixAvg_eq_third` (probe: the NOT floor witness): `r = 6`, `K (σ, j) = (√6)⁻¹ • (σ ⊗ |j⟩)` for `σ ∈ {X, Y, Z}`,
`j ∈ {0, 1}`, i.e. `K (σ,j) (a, b) i = (√6)⁻¹ · σ a i · [b = j]`; `Σ Kᴴ K = (1/6) Σ_σ Σ_j σᴴ σ = (1/6) · 3 · 2 · 1 = 1`;
`sixAvg₁ = 1/3` because the first marginal is `(1/3)(XρX + YρY + ZρZ) = (2/3) Tr(ρ) 1 − (1/3) ρ`, whose fidelity with
each Pauli state is `2/3 − 1/3 = 1/3`; or compute the six terms directly (`fin_cases s`, `simp`, `norm_num`).

## §4 Unique (lane `unique`) — uniqueness of the symmetric optimum
`eq_bh_of_sixAvg`: from `sixAvg_le`'s proof with equality: `Σᵢ SOS(Kᵢ) = 0`, so every square of every `Kᵢ` vanishes
(`Finset.sum_eq_zero_iff_of_nonneg`, `Complex.normSq_eq_zero`): `Kᵢ (1,1) 0 = 0`, `Kᵢ (0,0) 1 = 0`,
`Kᵢ (0,1) 1 = Kᵢ (1,0) 1`, `Kᵢ (0,0) 0 = 2 Kᵢ (0,1) 1`, `Kᵢ (0,1) 0 = Kᵢ (1,1) 1 / 2 = Kᵢ (1,0) 0`; hence
`Kᵢ = xᵢ • bhV₁ + yᵢ • bhV₂` with `xᵢ = Kᵢ (0,1) 1`, `yᵢ = Kᵢ (1,1) 1` (`ext; fin_cases; simp [bhV₁, bhV₂]`). Then
`IsChannel K` reads `Σ |xᵢ|² · diag(4, 2) + Σ |yᵢ|² · diag(1/2, 1) + (Σ xᵢ conj yᵢ) E₁₀ + c.c. = 1` (probe H2: the Gram
blocks `V₁ᴴV₁ = diag(4,2)`, `V₂ᴴV₂ = diag(1/2,1)`, `V₁ᴴV₂ = E₁₀`), so `Σ xᵢ conj yᵢ = 0`, `Σ|xᵢ|² = 1/6`, `Σ|yᵢ|² = 2/3`;
expand `krausApply K ρ = Σᵢ (xᵢ V₁ + yᵢ V₂) ρ (xᵢ V₁ + yᵢ V₂)ᴴ` (`Finset.sum_add_distrib`, `Finset.smul_sum`,
`Matrix.smul_mul`, `Matrix.mul_smul`, `conjTranspose_smul`) into `bhChannel ρ`. `eq_bh_of_forall`: `st_le_sixAvg₁/₂`
with `f = 5/6` and `sixAvg_le` give equality. `isGreatest_cloning_fidelity`: membership by `bh_isChannel` and
`bh_fidelity`; the upper bound: `t ≤ F₁, F₂` on the unit vector of `exists_unit_min_le` gives `t ≤ min ≤ 5/6`.

## §5 AsymForm (lane `asymform`) — the asymmetric certificate
`af_sos` (probe H5'): an identity of real polynomials in `a, b` and the sixteen real/imaginary parts, closed by the
expansion of §2 and `ring` (no hypothesis). `af_weighted_eq`: sum `form_six_one`, `form_six_two` over `i` with
`st_sixAvg₁_eq_sum`, `st_isChannel_normSq_sum`. `asym_bound`: `af_sos` summed over `i` (every term on the right `≥ 0`
for `a, b ≥ 0`: `mul_nonneg`, `Complex.normSq_nonneg`), `af_weighted_eq`, `st_isChannel_normSq_sum`, then
`nlinarith`/`linarith` from `6(a(a+2b) F̄₁ + b(2a+b) F̄₂) ≤ 6(a² + 3ab + b²)`. `asym_bound_forall`: `asym_bound` with
`st_le_sixAvg₁/₂` and `a(a+2b), b(2a+b) ≥ 0` (`mul_le_mul_of_nonneg_left`).

## §6 Asym (lane `asym`) — the family
`as_gram` (probe H4: `A₀ᴴA₀ + A₁ᴴA₁ = 2(a² + ab + b²) 1`): `ext; fin_cases; simp [asymA₀, asymA₁, mul_apply,
Fintype.sum_prod_type]; ring`. `asym_isChannel`: `K = ![c • A₀, c • A₁]` with `c = (Real.sqrt (2(a² + ab + b²)))⁻¹`
(the radicand is positive: `a² + ab + b² = (a + b/2)² + 3b²/4 ≥ 0`, nonzero by `h`), `Real.mul_self_sqrt`. The
marginals (probe H4): `ext a' b'; fin_cases; simp [asymChannel, asymA₀, asymA₁, traceSecond, …]; field_simp; ring`
(the scalar `(2 s)⁻¹` with `s ≠ 0`). `asym_fidelity`: through `hK`, the marginals and `st_fidelity_depolarized`.
`asym_equality`: the six-state averages are `1 − b²/(2s)` and `1 − a²/(2s)` (each six-state term by the marginals,
`pauliState s = proj (pauliVec s)` or `st_fidelity_depolarized` on `pauliVec s` through `st_F₁_pauliVec`), then
`field_simp; ring`.

## §7 AsymUnique (lane `asymunique`) — uniqueness of the asymmetric optimum
From `af_sos` summed with equality (as in §5): every square vanishes, so for each `i`: `Kᵢ (1,1) 0 = Kᵢ (0,0) 1 = 0`,
`Kᵢ (0,0) 0 = Kᵢ (1,0) 1 + Kᵢ (0,1) 1`, `Kᵢ (1,1) 1 = Kᵢ (0,1) 0 + Kᵢ (1,0) 0`, and `(a + 2b) uⱼ = (2a + b) vⱼ` for
`j = 0, 1`; hence `Kᵢ = xᵢ • asymA₀ a b + yᵢ • asymA₁ a b`: `vec A₀ = (a+b)|000⟩ + a|110⟩ + b|101⟩`,
`vec A₁ = a|001⟩ + b|010⟩ + (a+b)|111⟩`; the five vanishing conditions plus `(a+2b)(k₀₀ⱼ + k₁₁ⱼ) =
(2a+b)(k₀ⱼ₀ + k₁ⱼ₁)` leave the two-dimensional span (probe H5: kernel dimension 2 for `a, b > 0`); take
`xᵢ = Kᵢ (1,0) 1 / a` and `yᵢ = Kᵢ (0,1) 0 / a`, check the eight entries by `field_simp`/`linear_combination` from the
conditions. Then `IsChannel K` with `A₀ᴴA₀ = diag((a+b)², a² + b²)`, `A₁ᴴA₁ = diag(a² + b², (a+b)²)`, `A₀ᴴA₁ = 2ab E₁₀`:
`Σ xᵢ conj yᵢ = 0`, `X = Y = 1/(2s)` (`(X − Y) · 2ab = 0`, `X · 2s = 1`), and the expansion gives `asymChannel a b ρ`.

## §8 Tradeoff (lane `tradeoff`) — the square-root form (Scarani–Iblisdir–Gisin–Acín 2005, Eq. (23))
`tr_of_bounds`: `a = 1, b = 0` gives `0 ≤ D₁`; `a = 0, b = 1` gives `0 ≤ D₂`. If `1/2 ≤ D₁ + D₂` done
(`Real.sqrt_nonneg`). Else with `g = √(D₁ D₂)` and `a = √(2 D₂)`, `b = √(2 D₁)`: `a² = 2D₂`, `b² = 2D₁`, `ab = 2g`
(`Real.sqrt_mul`, `Real.sq_sqrt`, `Real.mul_self_sqrt`), the bound reads `2g ≤ 4D₁D₂ + 4g(D₁ + D₂) = 4g² + 4g(D₁ + D₂)`
(`Real.sq_sqrt` for `g² = D₁D₂`); if `0 < g` divide; if `g = 0` then `D₁ D₂ = 0`, say `D₁ = 0`, and `a = 1, b = t`
gives `t ≤ t(2 + t) D₂` for every `t > 0`, so `1 ≤ (2 + t) D₂`; with `D₂ < 1/2` the choice `t = (1 − 2D₂)/(2D₂)` (if
`D₂ > 0`; `D₂ = 0` is `1 ≤ 0`) contradicts. `tradeoff_sqrt`: `tr_of_bounds` on `asym_bound` with `Dᵢ = 1 − sixAvgᵢ K`
and `Real.le_sqrt`-free rearrangement. `tradeoff_forall`: the same on `asym_bound_forall`. `tradeoff_attained`:
`asym_equality`-type values: with `F̄₁ = 1 − b²/(2s)`, `F̄₂ = 1 − a²/(2s)` (from `asym_fidelity` on the six vectors
or directly), the left side is `(s − a² − b²)/(2s) = ab/(2s)` and `√((b²/2s)(a²/2s)) = ab/(2s)` for `a, b ≥ 0`
(`Real.sqrt_eq_iff`, `s > 0`).
