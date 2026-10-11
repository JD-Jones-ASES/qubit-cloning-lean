module

public import QubitCloning.States

/-!
# Form

The symmetric certificate: the per-Kraus identities and the six-term sum of squares (ARCH.md §2). Lane `form`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `form_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The one-operator six-state sums as quadratic forms (`6 W₁ = 1 + Ω₁`): with `k_{r a b} = K (a, b) r`,
`6 · sixAvg₁ ![K] = Σ |K x i|² + Σⱼ |K (0, j) 0 + K (1, j) 1|²`. -/
theorem form_six_one (K : Matrix QQ Q ℂ) :
    6 * sixAvg₁ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (0, j) 0 + K (1, j) 1) := sorry

/-- `6 · sixAvg₂ ![K] = Σ |K x i|² + Σⱼ |K (j, 0) 0 + K (j, 1) 1|²` (`6 W₂ = 1 + Ω₂`). -/
theorem form_six_two (K : Matrix QQ Q ℂ) :
    6 * sixAvg₂ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (j, 0) 0 + K (j, 1) 1) := sorry

/-- The symmetric certificate: the six-term sum of squares (the desk's `probe.py`, H2). -/
theorem form_sos (K : Matrix QQ Q ℂ) :
    6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) =
      5 * ∑ x, ∑ i, Complex.normSq (K x i)
        - (Complex.normSq (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1) + 2 * Complex.normSq (K (0, 1) 0 - K (1, 1) 1 / 2)
          + 2 * Complex.normSq (K (1, 0) 0 - K (1, 1) 1 / 2) + 3 * Complex.normSq (K (1, 1) 0)
          + 3 * Complex.normSq (K (0, 0) 1) + Complex.normSq (K (0, 1) 1 - K (1, 0) 1)) := sorry

/-- Gisin–Massar's bound in the six-state form: for every channel the mean single-clone fidelity, averaged
over the six Pauli eigenstates, is at most `5/6`. -/
theorem sixAvg_le_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    (sixAvg₁ K + sixAvg₂ K) / 2 ≤ 5 / 6 := sorry

/-- No channel clones every pure state with both fidelities above `5/6`: some unit vector has
`min (F₁, F₂) ≤ 5/6`. -/
theorem exists_unit_min_le_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∃ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ min (F₁ K ψ) (F₂ K ψ) ≤ 5 / 6 := sorry

/-- The six-state average of either clone's fidelity is at least `1/3` for every channel (the universal-NOT
bound in average form: no channel anti-clones better than the universal NOT). -/
theorem sixAvg_ge_third_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    1 / 3 ≤ sixAvg₁ K ∧ 1 / 3 ≤ sixAvg₂ K := sorry

end QubitCloning
