module

public import QubitCloning.AsymForm
public import QubitCloning.Asym

/-!
# Tradeoff

the square-root form of the trade-off from the homogeneous bound (ARCH.md §8). Lane `tradeoff`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `tr_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The degenerate case of Cerf's form: if `1 ≤ (2 + t) D` for every `t > 0`, then `1/2 ≤ D`. -/
theorem tr_zero_case (D : ℝ) (h : ∀ t : ℝ, 0 < t → 1 ≤ (2 + t) * D) : 1 / 2 ≤ D := by
  by_contra hlt
  rw [not_le] at hlt
  rcases lt_or_ge 0 D with hD | hD
  · have ht : 0 < (1 - 2 * D) / (2 * D) := div_pos (by linarith) (by linarith)
    have h1 := h ((1 - 2 * D) / (2 * D)) ht
    have e : (2 + (1 - 2 * D) / (2 * D)) * D = D + 1 / 2 := by
      field_simp
      ring
    linarith
  · have h1 := h 1 one_pos
    linarith

/-- The real lemma behind Cerf's form: if `a b ≤ a (a + 2b) D₁ + b (2a + b) D₂` for all `a, b ≥ 0`, then
`D₁, D₂ ≥ 0` and `1/2 ≤ D₁ + D₂ + √(D₁ D₂)`. -/
theorem tr_of_bounds (D₁ D₂ : ℝ)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ a * (a + 2 * b) * D₁ + b * (2 * a + b) * D₂) :
    0 ≤ D₁ ∧ 0 ≤ D₂ ∧ 1 / 2 ≤ D₁ + D₂ + Real.sqrt (D₁ * D₂) := by
  have h1 : 0 ≤ D₁ := by
    have := h 1 0 zero_le_one le_rfl
    linarith
  have h2 : 0 ≤ D₂ := by
    have := h 0 1 le_rfl zero_le_one
    linarith
  refine ⟨h1, h2, ?_⟩
  by_cases hs : 1 / 2 ≤ D₁ + D₂
  · linarith [Real.sqrt_nonneg (D₁ * D₂)]
  rw [not_le] at hs
  have hg0 : 0 ≤ Real.sqrt (D₁ * D₂) := Real.sqrt_nonneg _
  have hgg : Real.sqrt (D₁ * D₂) * Real.sqrt (D₁ * D₂) = D₁ * D₂ :=
    Real.mul_self_sqrt (mul_nonneg h1 h2)
  have ha2 : Real.sqrt (2 * D₂) * Real.sqrt (2 * D₂) = 2 * D₂ := Real.mul_self_sqrt (by linarith)
  have hb2 : Real.sqrt (2 * D₁) * Real.sqrt (2 * D₁) = 2 * D₁ := Real.mul_self_sqrt (by linarith)
  have hab : Real.sqrt (2 * D₂) * Real.sqrt (2 * D₁) = 2 * Real.sqrt (D₁ * D₂) := by
    rw [← Real.sqrt_mul (by linarith), show 2 * D₂ * (2 * D₁) = 2 ^ 2 * (D₁ * D₂) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have key := h (Real.sqrt (2 * D₂)) (Real.sqrt (2 * D₁)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  generalize Real.sqrt (2 * D₂) = a at key ha2 hab
  generalize Real.sqrt (2 * D₁) = b at key hb2 hab
  generalize Real.sqrt (D₁ * D₂) = g at hg0 hgg hab ⊢
  have e : a * (a + 2 * b) * D₁ + b * (2 * a + b) * D₂ = 4 * (g * g) + 4 * g * (D₁ + D₂) := by
    linear_combination D₁ * ha2 + (2 * D₁ + 2 * D₂) * hab + D₂ * hb2 - 4 * hgg
  have key' : 2 * g ≤ 4 * (g * g) + 4 * g * (D₁ + D₂) := by linarith
  by_cases hg : 0 < g
  · nlinarith
  · have hg' : g = 0 := le_antisymm (not_lt.mp hg) hg0
    subst hg'
    have hz : D₁ * D₂ = 0 := by linarith
    rcases mul_eq_zero.mp hz with hD | hD
    · have : 1 / 2 ≤ D₂ := by
        refine tr_zero_case D₂ (fun t ht => ?_)
        have := h 1 t zero_le_one ht.le
        rw [hD] at this
        nlinarith
      linarith
    · have : 1 / 2 ≤ D₁ := by
        refine tr_zero_case D₁ (fun t ht => ?_)
        have := h t 1 ht.le zero_le_one
        rw [hD] at this
        nlinarith
      linarith

/-- The trade-off in Cerf's form: `F̄₁ + F̄₂ − 3/2 ≤ √((1 − F̄₁)(1 − F̄₂))` for every channel. -/
theorem tradeoff_sqrt_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 ≤ Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := by
  have := (tr_of_bounds (1 - sixAvg₁ K) (1 - sixAvg₂ K)
    (fun a b ha hb => asym_bound_internal K hK a b ha hb)).2.2
  linarith

/-- The trade-off for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`f₁ + f₂ − 3/2 ≤ √((1 − f₁)(1 − f₂))`. -/
theorem tradeoff_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (f₁ f₂ : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    f₁ + f₂ - 3 / 2 ≤ Real.sqrt ((1 - f₁) * (1 - f₂)) := by
  have := (tr_of_bounds (1 - f₁) (1 - f₂)
    (fun a b ha hb => asym_bound_forall_internal K hK a b ha hb f₁ f₂ h)).2.2
  linarith

/-- The asymmetric cloner's six-state averages: `F̄₁ = 1 − b²/(2(a² + ab + b²))` and
`F̄₂ = 1 − a²/(2(a² + ab + b²))`. -/
theorem tr_sixAvg_asym {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      sixAvg₂ K = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
  have h1 : ∀ s : Fin 6, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) =
      1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := fun s => by
    rw [← st_F₁_pauliVec K s]
    exact (asym_fidelity_internal a b h K hK (pauliVec s) (pauliVec_unit_internal s)).1
  have h2 : ∀ s : Fin 6, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) =
      1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := fun s => by
    rw [← st_F₂_pauliVec K s]
    exact (asym_fidelity_internal a b h K hK (pauliVec s) (pauliVec_unit_internal s)).2
  constructor
  · rw [sixAvg₁, Finset.sum_congr rfl (fun s _ => h1 s)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · rw [sixAvg₂, Finset.sum_congr rfl (fun s _ => h2 s)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

/-- The asymmetric cloners with `a, b ≥ 0` lie on the trade-off curve: equality in Cerf's form. -/
theorem tradeoff_attained_internal {r : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 = Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := by
  obtain ⟨hS1, hS2⟩ := tr_sixAvg_asym a b h K hK
  have hs : 0 < a ^ 2 + a * b + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  rw [hS1, hS2]
  have e1 : (1 - (1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)))) *
      (1 - (1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)))) = (a * b / (2 * (a ^ 2 + a * b + b ^ 2))) ^ 2 := by
    ring
  rw [e1, Real.sqrt_sq (div_nonneg (mul_nonneg ha hb) (by linarith))]
  have hc : (2 * (a ^ 2 + a * b + b ^ 2)) * (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero h)
  linear_combination (-1 / 2 : ℝ) * hc

/-! ## Extras for the neighbouring modules (exact statements of their pins, from black boxes) -/

/-- `st_le_sixAvg₁` from `st_F₁_pauliVec` and `pauliVec_unit_internal`. -/
theorem tr_le_sixAvg₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₁ K ψ) : f ≤ sixAvg₁ K := by
  have hs : ∀ s ∈ (Finset.univ : Finset (Fin 6)),
      f ≤ fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) := fun s _ => by
    rw [← st_F₁_pauliVec K s]
    exact h _ (pauliVec_unit_internal s)
  have := Finset.card_nsmul_le_sum _ _ _ hs
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  rw [sixAvg₁]
  linarith

/-- `st_le_sixAvg₂` from `st_F₂_pauliVec` and `pauliVec_unit_internal`. -/
theorem tr_le_sixAvg₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₂ K ψ) : f ≤ sixAvg₂ K := by
  have hs : ∀ s ∈ (Finset.univ : Finset (Fin 6)),
      f ≤ fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := fun s _ => by
    rw [← st_F₂_pauliVec K s]
    exact h _ (pauliVec_unit_internal s)
  have := Finset.card_nsmul_le_sum _ _ _ hs
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  rw [sixAvg₂]
  linarith

/-- `asym_bound_forall_internal` from `asym_bound_internal` and `st_le_sixAvg₁/₂`. -/
theorem tr_asym_bound_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (f₁ f₂ : ℝ) (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    a * b ≤ a * (a + 2 * b) * (1 - f₁) + b * (2 * a + b) * (1 - f₂) := by
  have h1 := st_le_sixAvg₁ K f₁ (fun ψ hψ => (h ψ hψ).1)
  have h2 := st_le_sixAvg₂ K f₂ (fun ψ hψ => (h ψ hψ).2)
  have hB := asym_bound_internal K hK a b ha hb
  have c1 : 0 ≤ a * (a + 2 * b) := by positivity
  have c2 : 0 ≤ b * (2 * a + b) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 c1, mul_le_mul_of_nonneg_left h2 c2]

/-- `asym_fidelity_internal` from the two marginals (`asym_traceSecond_internal`, `asym_traceFirst_internal`) and
`st_fidelity_depolarized`. -/
theorem tr_asym_fidelity {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    F₁ K ψ = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      F₂ K ψ = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
  constructor
  · rw [F₁, hK, asym_traceSecond_internal a b h, st_fidelity_depolarized ψ hψ]
    generalize a ^ 2 + a * b + b ^ 2 = s
    ring
  · rw [F₂, hK, asym_traceFirst_internal a b h, st_fidelity_depolarized ψ hψ]
    generalize a ^ 2 + a * b + b ^ 2 = s
    ring

/-- `asym_equality_internal` from the six-state averages of the family (`tr_sixAvg_asym`). -/
theorem tr_asym_equality {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := by
  obtain ⟨hS1, hS2⟩ := tr_sixAvg_asym a b h K hK
  rw [hS1, hS2]
  have hc : (2 * (a ^ 2 + a * b + b ^ 2)) * (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero h)
  linear_combination (-(a * b)) * hc

/-- `asym_traceSecond_internal` by the entrywise computation (ARCH §6). -/
theorem tr_asym_traceSecond (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceSecond (asymChannel a b ρ) =
      ((1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  have hC : ((a : ℂ) ^ 2 + a * b + b ^ 2) ≠ 0 := by exact_mod_cast h
  have hv : ((a : ℂ) ^ 2 + a * b + b ^ 2) * ((a : ℂ) ^ 2 + a * b + b ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hC
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymChannel, traceSecond, asymA₀, asymA₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Matrix.conjTranspose_apply]
  · linear_combination (ρ 0 0) * hv
  · linear_combination (ρ 0 1) * hv
  · linear_combination (ρ 1 0) * hv
  · linear_combination (ρ 1 1) * hv

/-- `asym_traceFirst_internal` by the entrywise computation (ARCH §6). -/
theorem tr_asym_traceFirst (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceFirst (asymChannel a b ρ) =
      ((1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  have hC : ((a : ℂ) ^ 2 + a * b + b ^ 2) ≠ 0 := by exact_mod_cast h
  have hv : ((a : ℂ) ^ 2 + a * b + b ^ 2) * ((a : ℂ) ^ 2 + a * b + b ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hC
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymChannel, traceFirst, asymA₀, asymA₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Matrix.conjTranspose_apply]
  · linear_combination (ρ 0 0) * hv
  · linear_combination (ρ 0 1) * hv
  · linear_combination (ρ 1 0) * hv
  · linear_combination (ρ 1 1) * hv

/-- `as_gram`: `A₀ᴴ A₀ + A₁ᴴ A₁ = 2(a² + ab + b²) · 1`. -/
theorem tr_as_gram (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₀ a b + (asymA₁ a b)ᴴ * asymA₁ a b =
      ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  all_goals ring

/-- `asym_isChannel_internal`: the Kraus family `A₀, A₁` scaled by `(√(2(a² + ab + b²)))⁻¹`. -/
theorem tr_asym_isChannel (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  have hs0 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg b]
  have hne : 2 * (a ^ 2 + a * b + b ^ 2) ≠ 0 := mul_ne_zero two_ne_zero h
  have hc2 : (Real.sqrt (2 * (a ^ 2 + a * b + b ^ 2)))⁻¹ * (Real.sqrt (2 * (a ^ 2 + a * b + b ^ 2)))⁻¹ =
      (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by linarith)]
  generalize (Real.sqrt (2 * (a ^ 2 + a * b + b ^ 2)))⁻¹ = c at hc2
  have hcC : star (c : ℂ) * (c : ℂ) = ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, hc2, Complex.ofReal_inv]
  have hcC' : (c : ℂ) * star (c : ℂ) = ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ)⁻¹ := by
    rw [mul_comm, hcC]
  refine ⟨![(c : ℂ) • asymA₀ a b, (c : ℂ) • asymA₁ a b], ?_, ?_⟩
  · unfold IsChannel
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [← smul_add, tr_as_gram, smul_smul, hcC', inv_mul_cancel₀ (by exact_mod_cast hne), one_smul]
  · intro ρ
    unfold krausApply asymChannel
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [hcC, ← smul_add]

/-- `st_fidelity_depolarized`: `fidelity (proj ψ) (c • proj ψ + d • Tr(proj ψ) • 1) = c + d` for a unit `ψ`. -/
theorem tr_fidelity_depolarized (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (c d : ℝ) :
    fidelity (proj ψ) ((c : ℂ) • proj ψ + (d : ℂ) • Matrix.trace (proj ψ) • (1 : Matrix Q Q ℂ)) = c + d := by
  have hP : proj ψ * proj ψ = proj ψ := by
    rw [proj, Matrix.vecMulVec_mul_vecMulVec, hψ, one_smul]
  have htr : Matrix.trace (proj ψ) = 1 := by
    rw [proj, Matrix.trace_vecMulVec, dotProduct_comm, hψ]
  rw [fidelity, htr, one_smul, Matrix.mul_add, Matrix.mul_smul, hP, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr]
  simp

/-- `proj_pauliVec_internal`: each Pauli eigenstate is the projector onto its unit vector. -/
theorem tr_proj_pauliVec (s : Fin 6) : proj (pauliVec s) = pauliState s := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast
    ring
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp [proj, pauliVec, pauliState, Matrix.vecMulVec_apply, Complex.conj_ofReal]
  all_goals first
    | linear_combination h2
    | linear_combination (-1 : ℂ) * h2
    | linear_combination Complex.I * h2
    | linear_combination (-Complex.I) * h2
    | linear_combination h2 - ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * Complex.I_sq

/-- `pauliVec_unit_internal`: the six vectors are unit vectors (the trace of `pauliState s` is `1`). -/
theorem tr_pauliVec_unit (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 := by
  rw [dotProduct_comm, ← Matrix.trace_vecMulVec]
  show Matrix.trace (proj (pauliVec s)) = 1
  rw [tr_proj_pauliVec]
  fin_cases s <;> simp [pauliState, Matrix.trace, Fin.sum_univ_two] <;> norm_num

/-- `st_F₁_pauliVec`: the first clone's fidelity on the six vectors is the six-state term. -/
theorem tr_F₁_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₁ K (pauliVec s) = fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) := by
  rw [F₁, tr_proj_pauliVec]

/-- `st_F₂_pauliVec`: the second clone's fidelity on the six vectors is the six-state term. -/
theorem tr_F₂_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₂ K (pauliVec s) = fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := by
  rw [F₂, tr_proj_pauliVec]

/-- `st_fidelity_proj`: the fidelity of a projector with `σ` is `Re (ψ† σ ψ)`. -/
theorem tr_fidelity_proj (ψ : Q → ℂ) (σ : Matrix Q Q ℂ) :
    fidelity (proj ψ) σ = (star ψ ⬝ᵥ (σ *ᵥ ψ)).re := by
  rw [fidelity, proj, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

/-- `st_krausApply_eq_sum`. -/
theorem tr_krausApply_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply K ρ = ∑ i, krausApply ![K i] ρ := by
  simp [krausApply]

/-- `st_traceSecond_sum`. -/
theorem tr_traceSecond_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceSecond (∑ i ∈ s, M i) = ∑ i ∈ s, traceSecond (M i) := by
  ext a b
  simp only [traceSecond, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- `st_traceFirst_sum`. -/
theorem tr_traceFirst_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceFirst (∑ i ∈ s, M i) = ∑ i ∈ s, traceFirst (M i) := by
  ext a b
  simp only [traceFirst, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- `st_traceSecond_smul`. -/
theorem tr_traceSecond_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceSecond (c • M) = c • traceSecond M := by
  ext a b
  simp only [traceSecond, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- `st_traceFirst_smul`. -/
theorem tr_traceFirst_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceFirst (c • M) = c • traceFirst M := by
  ext a b
  simp only [traceFirst, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- `st_fidelity_sum`. -/
theorem tr_fidelity_sum {ι : Type} (s : Finset ι) (ρ : Matrix Q Q ℂ) (σ : ι → Matrix Q Q ℂ) :
    fidelity ρ (∑ i ∈ s, σ i) = ∑ i ∈ s, fidelity ρ (σ i) := by
  simp only [fidelity, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- `st_sixAvg₁_eq_sum`. -/
theorem tr_sixAvg₁_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₁ K = ∑ i, sixAvg₁ ![K i] := by
  simp only [sixAvg₁, ← Finset.sum_div]
  congr 1
  simp only [fun ρ => tr_krausApply_eq_sum K ρ, tr_traceSecond_sum, tr_fidelity_sum]
  exact Finset.sum_comm

/-- `st_sixAvg₂_eq_sum`. -/
theorem tr_sixAvg₂_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₂ K = ∑ i, sixAvg₂ ![K i] := by
  simp only [sixAvg₂, ← Finset.sum_div]
  congr 1
  simp only [fun ρ => tr_krausApply_eq_sum K ρ, tr_traceFirst_sum, tr_fidelity_sum]
  exact Finset.sum_comm

/-- `st_isChannel_normSq_sum`: the trace of `Σ Kᵢᴴ Kᵢ = 1`. -/
theorem tr_isChannel_normSq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) = 2 := by
  have ht := congrArg Matrix.trace hK
  rw [Matrix.trace_sum, Matrix.trace_one] at ht
  have e : ∀ i, Matrix.trace ((K i)ᴴ * K i) = ((∑ x, ∑ j, Complex.normSq (K i x j) : ℝ) : ℂ) := by
    intro i
    rw [Finset.sum_comm]
    simp [Matrix.trace, Matrix.mul_apply, Complex.normSq_eq_conj_mul_self]
  simp only [e] at ht
  exact_mod_cast ht

end QubitCloning
