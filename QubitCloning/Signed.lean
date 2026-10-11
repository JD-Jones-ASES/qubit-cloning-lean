module

public import QubitCloning.AsymUnique

/-!
# Signed

The asymmetric bound and its equality case for real weights with `(2a + b)(a + 2b) ≥ 0`, the inequality `3F̄₁ − 5F̄₂ ≤ 1` with its unique optimum `Λ_{3,−1}`, and the floor companion `Λ_{2,−1}`. Every public theorem is the `_internal` twin of a Challenge statement (header verbatim).
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- For every channel and all real `a, b` with `(2a + b)(a + 2b) ≥ 0`,
`ab ≤ a(a + 2b)(1 − F̄₁) + b(2a + b)(1 − F̄₂)`: the bound `asym_bound` without the sign conditions on the
weights. -/
theorem signed_asym_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ)
    (hP : 0 ≤ (2 * a + b) * (a + 2 * b)) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) :=
  af_bound_of_nonneg K hK a b hP

/-- For real `a, b ≠ 0` with `(2a + b)(a + 2b) > 0`, a channel with equality in the signed bound at `(a, b)`
is `Λ_{a,b}` as a map. -/
theorem eq_asym_of_signed_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (hP : 0 < (2 * a + b) * (a + 2 * b))
    (ha : a ≠ 0) (hb : b ≠ 0) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  -- the certificate's right-hand side, operator by operator
  obtain ⟨R, hR⟩ : ∃ R : Fin r → ℝ, ∀ i, R i =
      (1 / 3) * ∑ j, Complex.normSq (((a + 2 * b : ℝ) : ℂ) * (K i (0, j) 0 + K i (1, j) 1)
          - ((2 * a + b : ℝ) : ℂ) * (K i (j, 0) 0 + K i (j, 1) 1))
        + (2 * a + b) * (a + 2 * b) * (Complex.normSq (K i (1, 1) 0) + Complex.normSq (K i (0, 0) 1)
          + Complex.normSq (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1) / 3
          + Complex.normSq (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0) / 3) := ⟨_, fun i => rfl⟩
  have hsos : ∀ i, (2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1) = R i := by
    intro i
    rw [hR i]
    exact af_sos a b (K i)
  have hRnn : ∀ i ∈ Finset.univ, 0 ≤ R i := by
    intro i _
    rw [hR i]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _))
      (mul_nonneg hP.le (add_nonneg (add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
        (div_nonneg (Complex.normSq_nonneg _) (by norm_num))) (div_nonneg (Complex.normSq_nonneg _) (by norm_num))))
  have e1 : ∑ i, R i = (2 * a + b) * (a + 2 * b) * ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j)
      - ∑ i, (a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
          + b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsos i]
    ring
  have e2 := st_isChannel_normSq_sum K hK
  have e3 := af_weighted_eq K hK a b
  have hsum : ∑ i, R i = 0 := by
    linear_combination e1 + (2 * a + b) * (a + 2 * b) * e2 + e3 - 6 * h
  have hR0 : ∀ i, R i = 0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg hRnn).mp hsum i (Finset.mem_univ i)
  -- each operator lies in the span of `A₀, A₁`
  have hdec : ∀ i, K i = (K i (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K i (0, 1) 0 / (a : ℂ)) • asymA₁ a b := by
    intro i
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := au_conditions a b hP (K i) (by rw [← hR i]; exact hR0 i)
    exact au_kraus_eq a b ha (K i) c1 c2 c3 c4 c5 c6
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin r → ℂ, ∀ i, K i = x i • asymA₀ a b + y i • asymA₁ a b := ⟨_, _, hdec⟩
  exact au_eq_asym_of_span a b ha hb K hK x y hxy

/-- For every channel, `3F̄₁ − 5F̄₂ ≤ 1` (the signed bound at the weights `(3, −1)`). -/
theorem clone_anticlone_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    3 * sixAvg₁ K - 5 * sixAvg₂ K ≤ 1 := by
  have h := signed_asym_bound_internal K hK 3 (-1) (by norm_num)
  linarith

/-- `Λ_{3,−1}` is a two-operator channel with the average fidelities `(13/14, 5/14)`, where
`3F̄₁ − 5F̄₂ = 1`. -/
theorem clone_anticlone_attained_internal :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ sixAvg₁ K = 13 / 14 ∧ sixAvg₂ K = 5 / 14 := by
  obtain ⟨K, hK, hmap⟩ := asym_isChannel_internal 3 (-1) (by norm_num)
  refine ⟨K, hK, ?_, ?_⟩
  · have h := as_sixAvg₁ 3 (-1) (by norm_num) K hmap
    norm_num at h
    exact h
  · have h := as_sixAvg₂ 3 (-1) (by norm_num) K hmap
    norm_num at h
    exact h

/-- A channel with `3F̄₁ − 5F̄₂ = 1` is `Λ_{3,−1}` as a map. -/
theorem eq_clone_anticlone_of_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 3 * sixAvg₁ K - 5 * sixAvg₂ K = 1) :
    ∀ ρ, krausApply K ρ = asymChannel 3 (-1) ρ := by
  apply eq_asym_of_signed_equality_internal K hK 3 (-1) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- `Λ_{2,−1}` is a two-operator channel with `F̄₁ = 5/6` and `F̄₂ = 1/3`, and with `F₁(ψ) = 5/6`,
`F₂(ψ) = 1/3` on every unit `ψ`: the universal-NOT floor on the second clone with `5/6` on the first. -/
theorem floor_companion_attained_internal :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 1 / 3 ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 1 / 3 := by
  obtain ⟨K, hK, hmap⟩ := asym_isChannel_internal 2 (-1) (by norm_num)
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · have h := as_sixAvg₁ 2 (-1) (by norm_num) K hmap
    norm_num at h
    exact h
  · have h := as_sixAvg₂ 2 (-1) (by norm_num) K hmap
    norm_num at h
    exact h
  · intro ψ hψ
    have h := asym_fidelity_internal 2 (-1) (by norm_num) K hmap ψ hψ
    norm_num at h
    exact h

end QubitCloning
