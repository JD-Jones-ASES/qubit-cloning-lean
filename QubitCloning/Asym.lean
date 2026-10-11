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

/-- The asymmetric cloners lie on the trade-off curve (the statement of `tradeoff_attained_internal`, proved here
from `as_sixAvg₁`, `as_sixAvg₂`): `F̄₁ + F̄₂ − 3/2 = ab/(2s) = √((1 − F̄₁)(1 − F̄₂))`. -/
theorem as_tradeoff_attained {r : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 = Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := by
  rw [as_sixAvg₁ a b h K hK, as_sixAvg₂ a b h K hK]
  have hs := as_pos a b h
  generalize hS : a ^ 2 + a * b + b ^ 2 = S at hs h ⊢
  have key : (1 - (1 - b ^ 2 / (2 * S))) * (1 - (1 - a ^ 2 / (2 * S))) = (a * b / (2 * S)) ^ 2 := by
    ring
  rw [key, Real.sqrt_sq (div_nonneg (mul_nonneg ha hb) (by linarith))]
  field_simp
  subst hS
  ring

/-- The Gram block `A₀ᴴ A₀ = diag((a + b)², a² + b²)`. -/
theorem as_gram₀₀ (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₀ a b = !![(((a + b) ^ 2 : ℝ) : ℂ), 0; 0, ((a ^ 2 + b ^ 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

/-- The Gram block `A₀ᴴ A₁ = 2ab E₁₀`. -/
theorem as_gram₀₁ (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₁ a b = !![0, 0; ((2 * a * b : ℝ) : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  ring

/-- The Gram block `A₁ᴴ A₀ = 2ab E₀₁`. -/
theorem as_gram₁₀ (a b : ℝ) :
    (asymA₁ a b)ᴴ * asymA₀ a b = !![0, ((2 * a * b : ℝ) : ℂ); 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  ring

/-- The Gram block `A₁ᴴ A₁ = diag(a² + b², (a + b)²)`. -/
theorem as_gram₁₁ (a b : ℝ) :
    (asymA₁ a b)ᴴ * asymA₁ a b = !![((a ^ 2 + b ^ 2 : ℝ) : ℂ), 0; 0, (((a + b) ^ 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

/-- The second half of the uniqueness of the asymmetric optimum (ARCH.md §7): for `a, b ≠ 0`, a channel whose
Kraus operators lie in the span of `A₀, A₁` is the asymmetric cloner as a map. -/
theorem as_eq_asymChannel_of_span {r : ℕ} (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (x y : Fin r → ℂ) (hxy : ∀ i, K i = x i • asymA₀ a b + y i • asymA₁ a b) (hK : IsChannel K) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  unfold IsChannel at hK
  have E : (∑ i, star (x i) * x i) • ((asymA₀ a b)ᴴ * asymA₀ a b) +
      (∑ i, star (x i) * y i) • ((asymA₀ a b)ᴴ * asymA₁ a b) +
      (∑ i, star (y i) * x i) • ((asymA₁ a b)ᴴ * asymA₀ a b) +
      (∑ i, star (y i) * y i) • ((asymA₁ a b)ᴴ * asymA₁ a b) = 1 := by
    rw [← hK]
    simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxy i]
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul]
    module
  rw [as_gram₀₀, as_gram₀₁, as_gram₁₀, as_gram₁₁] at E
  generalize hX : ∑ i, star (x i) * x i = X at E
  generalize hZ : ∑ i, star (x i) * y i = Z at E
  generalize hW : ∑ i, star (y i) * x i = W at E
  generalize hY : ∑ i, star (y i) * y i = Y at E
  have e00 := congrFun (congrFun E 0) 0
  have e11 := congrFun (congrFun E 1) 1
  have e10 := congrFun (congrFun E 1) 0
  have e01 := congrFun (congrFun E 0) 1
  simp at e00 e11
  simp [ha, hb] at e10 e01
  have hab : (2 * (a : ℂ) * (b : ℂ)) ≠ 0 := by simp [ha, hb]
  have hXY0 : (X - Y) * (2 * (a : ℂ) * (b : ℂ)) = 0 := by linear_combination e00 - e11
  have hXY : X - Y = 0 := (mul_eq_zero.mp hXY0).resolve_right hab
  have hX2 : X * (2 * ((a : ℂ) ^ 2 + (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2)) = 1 := by
    linear_combination e00 + ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * hXY
  intro ρ
  have hkr : krausApply K ρ =
      (∑ i, x i * star (x i)) • (asymA₀ a b * ρ * (asymA₀ a b)ᴴ) +
      (∑ i, x i * star (y i)) • (asymA₀ a b * ρ * (asymA₁ a b)ᴴ) +
      (∑ i, y i * star (x i)) • (asymA₁ a b * ρ * (asymA₀ a b)ᴴ) +
      (∑ i, y i * star (y i)) • (asymA₁ a b * ρ * (asymA₁ a b)ᴴ) := by
    unfold krausApply
    simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxy i]
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul]
    module
  have c1 : ∑ i, x i * star (x i) = X :=
    (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans hX
  have c2 : ∑ i, x i * star (y i) = 0 :=
    (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans (hW.trans e01)
  have c3 : ∑ i, y i * star (x i) = 0 :=
    (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans (hZ.trans e10)
  have c4 : ∑ i, y i * star (y i) = X :=
    (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans (hY.trans (sub_eq_zero.mp hXY).symm)
  rw [hkr, c1, c2, c3, c4, zero_smul, zero_smul, add_zero, add_zero, ← smul_add]
  unfold asymChannel
  congr 1
  rw [eq_inv_of_mul_eq_one_left hX2]
  simp

end QubitCloning
