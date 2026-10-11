module

public import QubitCloning.States

/-!
# BH

The Bužek–Hillery channel and the universal-NOT witness (ARCH.md §3). Lane `bh`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `bh_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The Bužek–Hillery map is a channel: it has a Kraus family. -/
theorem bh_isChannel_internal :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- The Bužek–Hillery map preserves the trace. -/
theorem bh_trace_internal (ρ : Matrix Q Q ℂ) : Matrix.trace (bhChannel ρ) = Matrix.trace ρ := sorry

/-- The first marginal of the Bužek–Hillery channel is the depolarizing map `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1`. -/
theorem bh_traceSecond_internal (ρ : Matrix Q Q ℂ) :
    traceSecond (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- The second marginal of the Bužek–Hillery channel is the same depolarizing map. -/
theorem bh_traceFirst_internal (ρ : Matrix Q Q ℂ) :
    traceFirst (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Any Kraus family of the Bužek–Hillery channel clones every pure state with both fidelities `5/6`. -/
theorem bh_fidelity_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ)
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 5 / 6 := sorry

/-- Its six-state averages are `5/6` and `5/6`. -/
theorem bh_sixAvg_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ) :
    sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 5 / 6 := sorry

/-- The Bužek–Hillery channel is the symmetric member `a = b` of the family. -/
theorem bhChannel_eq_asymChannel_internal (ρ : Matrix Q Q ℂ) : bhChannel ρ = asymChannel 1 1 ρ := sorry

/-- The floor `1/3` is attained: the universal NOT on the first clone with a maximally mixed second clone. -/
theorem exists_sixAvg_eq_third_internal :
    ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧ sixAvg₁ K = 1 / 3 := sorry

end QubitCloning
