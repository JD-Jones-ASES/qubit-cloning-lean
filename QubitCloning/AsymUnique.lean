module

public import QubitCloning.AsymForm
public import QubitCloning.Asym

/-!
# AsymUnique

Uniqueness of the asymmetric optimum (ARCH.md §7). Lane `asymunique`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `au_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- Uniqueness of the asymmetric optimum: for `a, b > 0`, a channel with equality in the bound at the weights
`(a, b)` is the asymmetric cloner `Λ_{a,b}` as a map. -/
theorem eq_asym_of_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := sorry

end QubitCloning
