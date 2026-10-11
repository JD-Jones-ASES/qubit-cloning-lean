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

/-- The real lemma behind Cerf's form: if `a b ≤ a (a + 2b) D₁ + b (2a + b) D₂` for all `a, b ≥ 0`, then
`D₁, D₂ ≥ 0` and `1/2 ≤ D₁ + D₂ + √(D₁ D₂)`. -/
theorem tr_of_bounds (D₁ D₂ : ℝ)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ a * (a + 2 * b) * D₁ + b * (2 * a + b) * D₂) :
    0 ≤ D₁ ∧ 0 ≤ D₂ ∧ 1 / 2 ≤ D₁ + D₂ + Real.sqrt (D₁ * D₂) := sorry

/-- The trade-off in Cerf's form: `F̄₁ + F̄₂ − 3/2 ≤ √((1 − F̄₁)(1 − F̄₂))` for every channel. -/
theorem tradeoff_sqrt_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 ≤ Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := sorry

/-- The trade-off for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`f₁ + f₂ − 3/2 ≤ √((1 − f₁)(1 − f₂))`. -/
theorem tradeoff_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (f₁ f₂ : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    f₁ + f₂ - 3 / 2 ≤ Real.sqrt ((1 - f₁) * (1 - f₂)) := sorry

/-- The asymmetric cloners with `a, b ≥ 0` lie on the trade-off curve: equality in Cerf's form. -/
theorem tradeoff_attained_internal {r : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 = Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := sorry

end QubitCloning
