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
      ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

/-- The weight `a² + ab + b²` is positive once it is nonzero. -/
theorem as_pos (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) : 0 < a ^ 2 + a * b + b ^ 2 :=
  lt_of_le_of_ne (by nlinarith [sq_nonneg (a + b / 2), sq_nonneg b]) (Ne.symm h)

/-- The asymmetric cloner is a channel for every `(a, b) ≠ (0, 0)`. -/
theorem asym_isChannel_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  have h2 : 0 < 2 * (a ^ 2 + a * b + b ^ 2) := by linarith [as_pos a b h]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * c = (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ :=
    ⟨(Real.sqrt (2 * (a ^ 2 + a * b + b ^ 2)))⁻¹, by rw [← mul_inv, Real.mul_self_sqrt h2.le]⟩
  have hcC : (c : ℂ) * (c : ℂ) = (((2 * (a ^ 2 + a * b + b ^ 2))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hc]
  have hstar : star (c : ℂ) = (c : ℂ) := by simp
  refine ⟨![(c : ℂ) • asymA₀ a b, (c : ℂ) • asymA₁ a b], ?_, ?_⟩
  · unfold IsChannel
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstar]
    rw [← smul_add, as_gram, smul_smul, hcC, ← Complex.ofReal_mul, inv_mul_cancel₀ h2.ne',
      Complex.ofReal_one, one_smul]
  · intro ρ
    unfold krausApply asymChannel
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstar]
    rw [← smul_add, hcC]
    push_cast
    rfl

/-- `1 − x/S` over the common denominator `2S`. -/
theorem as_one_sub (x S : ℝ) (hS : S ≠ 0) : 1 - x / S = (2 * S - 2 * x) * (2 * S)⁻¹ := by
  field_simp

/-- `1 − x/S + x/(2S) = 1 − x/(2S)`. -/
theorem as_half (x S : ℝ) (hS : S ≠ 0) : 1 - x / S + x / (2 * S) = 1 - x / (2 * S) := by
  field_simp
  ring

/-- The weighted identity behind the equality case: `ab = a(a+2b)·b²/(2s) + b(2a+b)·a²/(2s)`. -/
theorem as_weights (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    a * b = a * (a + 2 * b) * (1 - (1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)))) +
      b * (2 * a + b) * (1 - (1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)))) := by
  have h2 : 2 * (a ^ 2 + a * b + b ^ 2) ≠ 0 := mul_ne_zero two_ne_zero h
  rw [sub_sub_cancel, sub_sub_cancel, mul_div_assoc', mul_div_assoc', ← add_div,
    eq_div_iff h2]
  ring

/-- Its first marginal is the depolarizing map with shrinking factor `1 − b²/(a² + ab + b²)`. -/
theorem asym_traceSecond_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceSecond (asymChannel a b ρ) =
      ((1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ := ⟨_, rfl⟩
  have e0 : (((2 * (a ^ 2 + a * b + b ^ 2) : ℝ)⁻¹ : ℂ)) = (t : ℂ) := by simp [ht]
  have e1 : (1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) =
      (2 * (a ^ 2 + a * b + b ^ 2) - 2 * b ^ 2) * t := by rw [ht, as_one_sub _ _ h]
  have e2 : (b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) = b ^ 2 * t := by rw [ht, div_eq_mul_inv]
  unfold asymChannel
  rw [e0, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, traceSecond, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace] <;> ring

/-- Its second marginal is the depolarizing map with shrinking factor `1 − a²/(a² + ab + b²)`. -/
theorem asym_traceFirst_internal (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceFirst (asymChannel a b ρ) =
      ((1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ := ⟨_, rfl⟩
  have e0 : (((2 * (a ^ 2 + a * b + b ^ 2) : ℝ)⁻¹ : ℂ)) = (t : ℂ) := by simp [ht]
  have e1 : (1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) =
      (2 * (a ^ 2 + a * b + b ^ 2) - 2 * a ^ 2) * t := by rw [ht, as_one_sub _ _ h]
  have e2 : (a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) = a ^ 2 * t := by rw [ht, div_eq_mul_inv]
  unfold asymChannel
  rw [e0, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, traceFirst, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace] <;> ring

/-- Any Kraus family of the asymmetric cloner clones every pure state with fidelities
`1 − b²/(2(a² + ab + b²))` and `1 − a²/(2(a² + ab + b²))`. -/
theorem asym_fidelity_internal {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    F₁ K ψ = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      F₂ K ψ = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
  constructor
  · unfold F₁
    rw [hK, asym_traceSecond_internal a b h, st_fidelity_depolarized ψ hψ]
    exact as_half _ _ h
  · unfold F₂
    rw [hK, asym_traceFirst_internal a b h, st_fidelity_depolarized ψ hψ]
    exact as_half _ _ h

/-- The first six-state average of any Kraus family of the asymmetric cloner. -/
theorem as_sixAvg₁ {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
  have hterm : ∀ s : Fin 6,
      fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) =
        1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
    intro s
    rw [← st_F₁_pauliVec K s]
    exact (asym_fidelity_internal a b h K hK (pauliVec s) (pauliVec_unit_internal s)).1
  unfold sixAvg₁
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The second six-state average of any Kraus family of the asymmetric cloner. -/
theorem as_sixAvg₂ {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₂ K = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
  have hterm : ∀ s : Fin 6,
      fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) =
        1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := by
    intro s
    rw [← st_F₂_pauliVec K s]
    exact (asym_fidelity_internal a b h K hK (pauliVec s) (pauliVec_unit_internal s)).2
  unfold sixAvg₂
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The asymmetric cloner attains the bound with equality at its own weights. -/
theorem asym_equality_internal {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := by
  rw [as_sixAvg₁ a b h K hK, as_sixAvg₂ a b h K hK]
  exact as_weights a b h

/-! ### Extras for the neighbouring lanes (`tradeoff`, `asymunique`) -/

end QubitCloning
