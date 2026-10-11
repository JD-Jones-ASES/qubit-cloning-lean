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

end QubitCloning
