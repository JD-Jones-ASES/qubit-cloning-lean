module

public import QubitCloning.Form
public import QubitCloning.BH

/-!
# Unique

Uniqueness of the symmetric optimum and the `IsGreatest` form (ARCH.md §4). Lane `unique`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `un_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- One Kraus operator obeys the symmetric bound: `6 (sixAvg₁ + sixAvg₂) ![K] ≤ 5 ‖K‖²` (the sum of squares of
`form_sos` is nonnegative). -/
theorem un_sos_le (K : Matrix QQ Q ℂ) :
    6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) ≤ 5 * ∑ x, ∑ i, Complex.normSq (K x i) := by
  have hs := form_sos K
  have a₁ := Complex.normSq_nonneg (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1)
  have a₂ := Complex.normSq_nonneg (K (0, 1) 0 - K (1, 1) 1 / 2)
  have a₃ := Complex.normSq_nonneg (K (1, 0) 0 - K (1, 1) 1 / 2)
  have a₄ := Complex.normSq_nonneg (K (1, 1) 0)
  have a₅ := Complex.normSq_nonneg (K (0, 0) 1)
  have a₆ := Complex.normSq_nonneg (K (0, 1) 1 - K (1, 0) 1)
  linarith

/-- The kernel of the symmetric certificate: an operator whose six squares vanish is `x V₁ + y V₂` with
`x = K (0,1) 1`, `y = K (1,1) 1`. -/
theorem un_kraus_eq (K : Matrix QQ Q ℂ) (h₁ : K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1 = 0)
    (h₂ : K (0, 1) 0 - K (1, 1) 1 / 2 = 0) (h₃ : K (1, 0) 0 - K (1, 1) 1 / 2 = 0) (h₄ : K (1, 1) 0 = 0)
    (h₅ : K (0, 0) 1 = 0) (h₆ : K (0, 1) 1 - K (1, 0) 1 = 0) :
    K = K (0, 1) 1 • bhV₁ + K (1, 1) 1 • bhV₂ := by
  ext ⟨a, b⟩ i
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [bhV₁, bhV₂] <;>
    first
    | linear_combination h₁ - h₆
    | linear_combination h₂
    | linear_combination h₃
    | linear_combination h₄
    | linear_combination h₅
    | linear_combination -h₆

/-- Equality in the one-operator bound forces `K = x V₁ + y V₂`. -/
theorem un_sos_zero (K : Matrix QQ Q ℂ)
    (h : 6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) = 5 * ∑ x, ∑ i, Complex.normSq (K x i)) :
    K = K (0, 1) 1 • bhV₁ + K (1, 1) 1 • bhV₂ := by
  have hs := form_sos K
  have a₁ := Complex.normSq_nonneg (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1)
  have a₂ := Complex.normSq_nonneg (K (0, 1) 0 - K (1, 1) 1 / 2)
  have a₃ := Complex.normSq_nonneg (K (1, 0) 0 - K (1, 1) 1 / 2)
  have a₄ := Complex.normSq_nonneg (K (1, 1) 0)
  have a₅ := Complex.normSq_nonneg (K (0, 0) 1)
  have a₆ := Complex.normSq_nonneg (K (0, 1) 1 - K (1, 0) 1)
  apply un_kraus_eq K
  · exact Complex.normSq_eq_zero.1 (by linarith)
  · exact Complex.normSq_eq_zero.1 (by linarith)
  · exact Complex.normSq_eq_zero.1 (by linarith)
  · exact Complex.normSq_eq_zero.1 (by linarith)
  · exact Complex.normSq_eq_zero.1 (by linarith)
  · exact Complex.normSq_eq_zero.1 (by linarith)

/-- The Gram entry `(0,0)` of `x V₁ + y V₂`: `4 |x|² + |y|²/2`. -/
theorem un_gram₀₀ (x y : ℂ) :
    ((x • bhV₁ + y • bhV₂)ᴴ * (x • bhV₁ + y • bhV₂)) 0 0 = 4 * (star x * x) + star y * y / 2 := by
  have h₂ : (starRingEnd ℂ) 2 = 2 := map_ofNat (starRingEnd ℂ) 2
  simp [Matrix.mul_apply, Fintype.sum_prod_type, bhV₁, bhV₂, h₂]
  ring

/-- The Gram entry `(1,1)` of `x V₁ + y V₂`: `2 |x|² + |y|²`. -/
theorem un_gram₁₁ (x y : ℂ) :
    ((x • bhV₁ + y • bhV₂)ᴴ * (x • bhV₁ + y • bhV₂)) 1 1 = 2 * (star x * x) + star y * y := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, bhV₁, bhV₂]
  ring

/-- The Gram entry `(1,0)` of `x V₁ + y V₂`: `conj x · y`. -/
theorem un_gram₁₀ (x y : ℂ) :
    ((x • bhV₁ + y • bhV₂)ᴴ * (x • bhV₁ + y • bhV₂)) 1 0 = star x * y := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, bhV₁, bhV₂]
  ring

/-- The Gram entry `(0,1)` of `x V₁ + y V₂`: `conj y · x`. -/
theorem un_gram₀₁ (x y : ℂ) :
    ((x • bhV₁ + y • bhV₂)ᴴ * (x • bhV₁ + y • bhV₂)) 0 1 = star y * x := by
  have h₂ : (starRingEnd ℂ) 2 = 2 := map_ofNat (starRingEnd ℂ) 2
  simp [Matrix.mul_apply, Fintype.sum_prod_type, bhV₁, bhV₂, h₂]
  ring

/-- The conjugation by a two-term operator expands into four terms. -/
theorem un_expand (a b : ℂ) (A B : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    (a • A + b • B) * ρ * (a • A + b • B)ᴴ =
      (a * star a) • (A * ρ * Aᴴ) + (a * star b) • (A * ρ * Bᴴ) + (b * star a) • (B * ρ * Aᴴ)
        + (b * star b) • (B * ρ * Bᴴ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul]
  rw [mul_comm (star a) a, mul_comm (star a) b, mul_comm (star b) a, mul_comm (star b) b]
  abel

/-- A channel spanned by `V₁, V₂` is the Bužek–Hillery channel: trace preservation fixes the weights. -/
theorem un_eq_bh_of_span {r : ℕ} (x y : Fin r → ℂ) (hK : IsChannel fun i => x i • bhV₁ + y i • bhV₂)
    (ρ : Matrix Q Q ℂ) : krausApply (fun i => x i • bhV₁ + y i • bhV₂) ρ = bhChannel ρ := by
  simp only [IsChannel] at hK
  have g₀₀ := congrFun (congrFun hK 0) 0
  have g₁₁ := congrFun (congrFun hK 1) 1
  have g₁₀ := congrFun (congrFun hK 1) 0
  have g₀₁ := congrFun (congrFun hK 0) 1
  simp only [Matrix.sum_apply, un_gram₀₀, un_gram₁₁, un_gram₁₀, un_gram₀₁, Matrix.one_apply_eq,
    Matrix.one_apply_ne (one_ne_zero : (1 : Q) ≠ 0), Matrix.one_apply_ne (zero_ne_one : (0 : Q) ≠ 1)]
    at g₀₀ g₁₁ g₁₀ g₀₁
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at g₀₀
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at g₁₁
  have hX' : ∑ i, star (x i) * x i = 1 / 6 := by linear_combination (g₀₀ - g₁₁ / 2) / 3
  have hY' : ∑ i, star (y i) * y i = 2 / 3 := by linear_combination g₁₁ - 2 * (g₀₀ - g₁₁ / 2) / 3
  have hX : ∑ i, x i * star (x i) = 1 / 6 := by
    rw [← hX']; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hY : ∑ i, y i * star (y i) = 2 / 3 := by
    rw [← hY']; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hXY : ∑ i, x i * star (y i) = 0 := by
    rw [← g₀₁]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hYX : ∑ i, y i * star (x i) = 0 := by
    rw [← g₁₀]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [krausApply, un_expand, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [hX, hY, hXY, hYX]
  simp only [zero_smul, add_zero, bhChannel]

/-- The converse of the weight computation: a family `x V₁ + y V₂` with `Σ|xᵢ|² = 1/6`, `Σ|yᵢ|² = 2/3` and
`Σ conj xᵢ yᵢ = 0` is a channel. -/
theorem un_isChannel_of_span {r : ℕ} (x y : Fin r → ℂ) (hX : ∑ i, star (x i) * x i = 1 / 6)
    (hY : ∑ i, star (y i) * y i = 2 / 3) (hXY : ∑ i, star (x i) * y i = 0) :
    IsChannel fun i => x i • bhV₁ + y i • bhV₂ := by
  have hYX : ∑ i, star (y i) * x i = 0 := by
    have h := congrArg star hXY
    rw [star_sum, star_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', star_star, mul_comm]
  unfold IsChannel
  refine Matrix.ext fun a b => ?_
  rw [Matrix.sum_apply]
  revert a b
  simp only [Fin.forall_fin_two, un_gram₀₀, un_gram₁₁, un_gram₁₀, un_gram₀₁, Matrix.one_apply_eq,
    Matrix.one_apply_ne (one_ne_zero : (1 : Q) ≠ 0), Matrix.one_apply_ne (zero_ne_one : (0 : Q) ≠ 1)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hX, hY]
    norm_num
  · exact hYX
  · exact hXY
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hX, hY]
    norm_num

/-- The Bužek–Hillery map has a two-operator Kraus family, `(√6)⁻¹ V₁` and `2 (√6)⁻¹ V₂` (the statement of
`bh_isChannel_internal`, proved here from `un_isChannel_of_span` and `un_eq_bh_of_span`). -/
theorem un_bh_isChannel :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = bhChannel ρ := by
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hc : star (((Real.sqrt 6)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 6)⁻¹ : ℝ) : ℂ) = 1 / 6 := by
    rw [← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, h6]
    push_cast
    norm_num
  have hd : star (((2 * (Real.sqrt 6)⁻¹ : ℝ)) : ℂ) * ((2 * (Real.sqrt 6)⁻¹ : ℝ) : ℂ) = 2 / 3 := by
    have h : (2 * (Real.sqrt 6)⁻¹) * (2 * (Real.sqrt 6)⁻¹) = (2 / 3 : ℝ) := by
      rw [show (2 * (Real.sqrt 6)⁻¹) * (2 * (Real.sqrt 6)⁻¹) = 4 * (Real.sqrt 6 * Real.sqrt 6)⁻¹ by ring, h6]
      norm_num
    rw [← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, h]
    push_cast
    ring
  have hK : IsChannel fun i => ![(((Real.sqrt 6)⁻¹ : ℝ) : ℂ), 0] i • bhV₁
      + ![0, ((2 * (Real.sqrt 6)⁻¹ : ℝ) : ℂ)] i • bhV₂ := by
    apply un_isChannel_of_span
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, mul_zero, add_zero]
      exact hc
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, zero_mul, zero_add]
      exact hd
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, mul_zero, zero_mul,
        add_zero]
  exact ⟨_, hK, un_eq_bh_of_span _ _ hK⟩

/-- Equality in the bound forces the channel: a channel whose six-state mean fidelity is `5/6` is the
Bužek–Hillery channel as a map. -/
theorem eq_bh_of_sixAvg_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : (sixAvg₁ K + sixAvg₂ K) / 2 = 5 / 6) : ∀ ρ, krausApply K ρ = bhChannel ρ := by
  have hS : ∑ i, (5 * ∑ x, ∑ j, Complex.normSq (K i x j) - 6 * (sixAvg₁ ![K i] + sixAvg₂ ![K i])) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← st_sixAvg₁_eq_sum, ← st_sixAvg₂_eq_sum, st_isChannel_normSq_sum K hK]
    linarith
  have hnn : ∀ i ∈ Finset.univ,
      (0 : ℝ) ≤ 5 * ∑ x, ∑ j, Complex.normSq (K i x j) - 6 * (sixAvg₁ ![K i] + sixAvg₂ ![K i]) :=
    fun i _ => sub_nonneg.2 (un_sos_le (K i))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS
  have hform : ∀ i, K i = K i (0, 1) 1 • bhV₁ + K i (1, 1) 1 • bhV₂ := fun i =>
    un_sos_zero (K i) (by linarith [hz i (Finset.mem_univ i)])
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin r → ℂ, K = fun i => x i • bhV₁ + y i • bhV₂ :=
    ⟨fun i => K i (0, 1) 1, fun i => K i (1, 1) 1, funext hform⟩
  exact un_eq_bh_of_span x y hK

/-- A channel cloning every pure state with both fidelities at least `5/6` is the Bužek–Hillery channel. -/
theorem eq_bh_of_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → 5 / 6 ≤ F₁ K ψ ∧ 5 / 6 ≤ F₂ K ψ) :
    ∀ ρ, krausApply K ρ = bhChannel ρ := by
  have h₁ := st_le_sixAvg₁ K (5 / 6) fun ψ hψ => (h ψ hψ).1
  have h₂ := st_le_sixAvg₂ K (5 / 6) fun ψ hψ => (h ψ hψ).2
  have hle := sixAvg_le_internal K hK
  exact eq_bh_of_sixAvg_internal K hK (by linarith)

/-- `5/6` is the greatest worst-case common fidelity of a universal `1 → 2` qubit cloner: the greatest `t`
for which some channel has `t ≤ F₁(ψ)` and `t ≤ F₂(ψ)` for every unit `ψ`. -/
theorem isGreatest_cloning_fidelity_internal :
    IsGreatest {t : ℝ | ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → t ≤ F₁ K ψ ∧ t ≤ F₂ K ψ} (5 / 6) := by
  constructor
  · obtain ⟨K, hK, hmap⟩ := un_bh_isChannel
    exact ⟨2, K, hK, fun ψ hψ =>
      ⟨(bh_fidelity_internal K hmap ψ hψ).1.ge, (bh_fidelity_internal K hmap ψ hψ).2.ge⟩⟩
  · rintro t ⟨r, K, hK, ht⟩
    obtain ⟨ψ, hψ, hmin⟩ := exists_unit_min_le_internal K hK
    exact le_trans (le_min (ht ψ hψ).1 (ht ψ hψ).2) hmin

end QubitCloning
