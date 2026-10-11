module

public import QubitCloning.Defs

/-!
# States

The six states, linearity of the pieces, the vector form of the fidelity (ARCH.md §1). Lane `states`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `st_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The fidelity of a projector with `σ` is the quadratic form `Re (ψ† σ ψ)`. -/
theorem st_fidelity_proj (ψ : Q → ℂ) (σ : Matrix Q Q ℂ) :
    fidelity (proj ψ) σ = (star ψ ⬝ᵥ (σ *ᵥ ψ)).re := sorry

/-- `krausApply` is additive in the Kraus family: the sum over the family of the one-operator maps. -/
theorem st_krausApply_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply K ρ = ∑ i, krausApply ![K i] ρ := sorry

/-- The partial traces are additive. -/
theorem st_traceSecond_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceSecond (∑ i ∈ s, M i) = ∑ i ∈ s, traceSecond (M i) := sorry

theorem st_traceFirst_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceFirst (∑ i ∈ s, M i) = ∑ i ∈ s, traceFirst (M i) := sorry

/-- The partial traces commute with scalars. -/
theorem st_traceSecond_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceSecond (c • M) = c • traceSecond M := sorry

theorem st_traceFirst_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceFirst (c • M) = c • traceFirst M := sorry

/-- The fidelity is additive in its second argument. -/
theorem st_fidelity_sum {ι : Type} (s : Finset ι) (ρ : Matrix Q Q ℂ) (σ : ι → Matrix Q Q ℂ) :
    fidelity ρ (∑ i ∈ s, σ i) = ∑ i ∈ s, fidelity ρ (σ i) := sorry

/-- The six-state averages are sums over the Kraus family of the one-operator averages. -/
theorem st_sixAvg₁_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₁ K = ∑ i, sixAvg₁ ![K i] := sorry

theorem st_sixAvg₂_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₂ K = ∑ i, sixAvg₂ ![K i] := sorry

/-- The clone fidelities on the six vectors are the six-state terms. -/
theorem st_F₁_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₁ K (pauliVec s) = fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) := sorry

theorem st_F₂_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₂ K (pauliVec s) = fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := sorry

/-- Pointwise lower bounds on the six vectors bound the averages. -/
theorem st_le_sixAvg₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₁ K ψ) : f ≤ sixAvg₁ K := sorry

theorem st_le_sixAvg₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₂ K ψ) : f ≤ sixAvg₂ K := sorry

/-- A channel's Kraus operators have squared Frobenius norms summing to `2`. -/
theorem st_isChannel_normSq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) = 2 := sorry

/-- The fidelity of a projector with a depolarized copy of itself: `fidelity (proj ψ) (c • proj ψ + d • Tr(proj ψ) • 1) = c + d` for a unit `ψ` and real `c, d`. -/
theorem st_fidelity_depolarized (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (c d : ℝ) :
    fidelity (proj ψ) ((c : ℂ) • proj ψ + (d : ℂ) • Matrix.trace (proj ψ) • (1 : Matrix Q Q ℂ)) = c + d := sorry

/-- Each Pauli eigenstate is the projector onto its unit vector. -/
theorem proj_pauliVec_internal (s : Fin 6) : proj (pauliVec s) = pauliState s := sorry

/-- The six vectors are unit vectors. -/
theorem pauliVec_unit_internal (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 := sorry

end QubitCloning
