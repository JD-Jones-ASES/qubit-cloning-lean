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
          + Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) / 3) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The weighted six-state sums of a channel, in the certificate's terms. -/
theorem af_weighted_eq {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) :
    6 * (a * (a + 2 * b) * sixAvg₁ K + b * (2 * a + b) * sixAvg₂ K) =
      2 * (a * (a + 2 * b) + b * (2 * a + b))
        + ∑ i, (a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
          + b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
  have h1 : 6 * sixAvg₁ K = ∑ i, (∑ x, ∑ j, Complex.normSq (K i x j)
      + ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)) := by
    rw [st_sixAvg₁_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => form_six_one (K i))
  have h2 : 6 * sixAvg₂ K = ∑ i, (∑ x, ∑ j, Complex.normSq (K i x j)
      + ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    rw [st_sixAvg₂_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => form_six_two (K i))
  have hN := st_isChannel_normSq_sum K hK
  rw [Finset.sum_add_distrib] at h1 h2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (a * (a + 2 * b)) * h1 + (b * (2 * a + b)) * h2
    + (a * (a + 2 * b) + b * (2 * a + b)) * hN

/-- The asymmetric cloning bound: for every channel and all weights `a, b ≥ 0`,
`a b ≤ a (a + 2b) (1 − F̄₁) + b (2a + b) (1 − F̄₂)`. -/
theorem asym_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := by
  have hN := st_isChannel_normSq_sum K hK
  have hW := af_weighted_eq K hK a b
  have hab : 0 ≤ (2 * a + b) * (a + 2 * b) := mul_nonneg (by linarith) (by linarith)
  have hS : 0 ≤ ∑ i, ((2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    apply Finset.sum_nonneg
    intro i _
    rw [af_sos a b (K i)]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
    · refine mul_nonneg hab ?_
      have h3 : (0 : ℝ) < 3 := by norm_num
      exact add_nonneg (add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
        (div_nonneg (Complex.normSq_nonneg _) h3.le)) (div_nonneg (Complex.normSq_nonneg _) h3.le)
  have hS' : ∑ i, ((2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) =
      (2 * a + b) * (a + 2 * b) * ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j)
        - ∑ i, (a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
          + b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hS', hN] at hS
  linarith

/-- The same bound for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`a b ≤ a (a + 2b) (1 − f₁) + b (2a + b) (1 − f₂)`. -/
theorem asym_bound_forall_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (f₁ f₂ : ℝ) (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    a * b ≤ a * (a + 2 * b) * (1 - f₁) + b * (2 * a + b) * (1 - f₂) := by
  have hf₁ : f₁ ≤ sixAvg₁ K := st_le_sixAvg₁ K f₁ (fun ψ hψ => (h ψ hψ).1)
  have hf₂ : f₂ ≤ sixAvg₂ K := st_le_sixAvg₂ K f₂ (fun ψ hψ => (h ψ hψ).2)
  have hA : 0 ≤ a * (a + 2 * b) := mul_nonneg ha (by linarith)
  have hB : 0 ≤ b * (2 * a + b) := mul_nonneg hb (by linarith)
  have e₁ := mul_le_mul_of_nonneg_left hf₁ hA
  have e₂ := mul_le_mul_of_nonneg_left hf₂ hB
  have hb' := asym_bound_internal K hK a b ha hb
  linarith

end QubitCloning
