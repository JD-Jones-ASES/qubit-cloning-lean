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

/-- Equality in the bound forces the channel: a channel whose six-state mean fidelity is `5/6` is the
Bužek–Hillery channel as a map. -/
theorem eq_bh_of_sixAvg_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : (sixAvg₁ K + sixAvg₂ K) / 2 = 5 / 6) : ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- A channel cloning every pure state with both fidelities at least `5/6` is the Bužek–Hillery channel. -/
theorem eq_bh_of_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → 5 / 6 ≤ F₁ K ψ ∧ 5 / 6 ≤ F₂ K ψ) :
    ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- `5/6` is the greatest worst-case common fidelity of a universal `1 → 2` qubit cloner: the greatest `t`
for which some channel has `t ≤ F₁(ψ)` and `t ≤ F₂(ψ)` for every unit `ψ`. -/
theorem isGreatest_cloning_fidelity_internal :
    IsGreatest {t : ℝ | ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → t ≤ F₁ K ψ ∧ t ≤ F₂ K ψ} (5 / 6) := sorry

end QubitCloning
