module

public import QubitCloning.States

/-!
# Asym

The asymmetric family: channel, marginals, fidelities, equality (ARCH.md §6). Lane `asym`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `as_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- `A₀ᴴ A₀ + A₁ᴴ A₁ = 2(a² + ab + b²) · 1`. -/
theorem as_gram (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₀ a b + (asymA₁ a b)ᴴ * asymA₁ a b =
      ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • (1 : Matrix Q Q ℂ) := sorry

/-- The asymmetric cloner is a channel for every `(a, b) ≠ (0, 0)`. -/
theorem asym_isChannel_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = asymChannel a b ρ := sorry

/-- Its first marginal is the depolarizing map with shrinking factor `1 − b²/(a² + ab + b²)`. -/
theorem asym_traceSecond_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceSecond (asymChannel a b ρ) =
      ((1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Its second marginal is the depolarizing map with shrinking factor `1 − a²/(a² + ab + b²)`. -/
theorem asym_traceFirst_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceFirst (asymChannel a b ρ) =
      ((1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Any Kraus family of the asymmetric cloner clones every pure state with fidelities
`1 − b²/(2(a² + ab + b²))` and `1 − a²/(2(a² + ab + b²))`. -/
theorem asym_fidelity_internal {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    F₁ K ψ = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      F₂ K ψ = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := sorry

/-- The asymmetric cloner attains the bound with equality at its own weights. -/
theorem asym_equality_internal {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := sorry

end QubitCloning
