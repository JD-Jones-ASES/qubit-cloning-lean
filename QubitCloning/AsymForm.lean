module

public import QubitCloning.Form

/-!
# AsymForm

The asymmetric certificate: the polynomial sum of squares (ARCH.md §5). Lane `asymform`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `af_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The asymmetric certificate, polynomial in the weights (the desk's `probe.py`, H5'): with
`uⱼ = K (0, j) 0 + K (1, j) 1` and `vⱼ = K (j, 0) 0 + K (j, 1) 1`,
`(2a + b)(a + 2b) ‖K‖² − a(a + 2b) Σⱼ |uⱼ|² − b(2a + b) Σⱼ |vⱼ|²
  = (1/3) Σⱼ |(a + 2b) uⱼ − (2a + b) vⱼ|² + (2a + b)(a + 2b) (|K (1,1) 0|² + |K (0,0) 1|²
    + |K (0,0) 0 − K (1,0) 1 − K (0,1) 1|²/3 + |K (1,1) 1 − K (0,1) 0 − K (1,0) 0|²/3)`. -/
theorem af_sos (a b : ℝ) (K : Matrix QQ Q ℂ) :
    (2 * a + b) * (a + 2 * b) * ∑ x, ∑ i, Complex.normSq (K x i)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K (0, j) 0 + K (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K (j, 0) 0 + K (j, 1) 1) =
      (1 / 3) * ∑ j, Complex.normSq (((a + 2 * b : ℝ) : ℂ) * (K (0, j) 0 + K (1, j) 1)
          - ((2 * a + b : ℝ) : ℂ) * (K (j, 0) 0 + K (j, 1) 1))
        + (2 * a + b) * (a + 2 * b) * (Complex.normSq (K (1, 1) 0) + Complex.normSq (K (0, 0) 1)
          + Complex.normSq (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1) / 3
          + Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) / 3) := sorry

/-- The weighted six-state sums of a channel, in the certificate's terms. -/
theorem af_weighted_eq {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) :
    6 * (a * (a + 2 * b) * sixAvg₁ K + b * (2 * a + b) * sixAvg₂ K) =
      2 * (a * (a + 2 * b) + b * (2 * a + b))
        + ∑ i, (a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
          + b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := sorry

/-- The asymmetric cloning bound: for every channel and all weights `a, b ≥ 0`,
`a b ≤ a (a + 2b) (1 − F̄₁) + b (2a + b) (1 − F̄₂)`. -/
theorem asym_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := sorry

/-- The same bound for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`a b ≤ a (a + 2b) (1 − f₁) + b (2a + b) (1 − f₂)`. -/
theorem asym_bound_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (f₁ f₂ : ℝ) (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    a * b ≤ a * (a + 2 * b) * (1 - f₁) + b * (2 * a + b) * (1 - f₂) := sorry

end QubitCloning
