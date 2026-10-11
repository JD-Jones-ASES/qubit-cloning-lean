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

/-- The Gram blocks of the asymmetric family: `A₀ᴴA₀ = diag((a + b)², a² + b²)`. -/
theorem au_gram₀₀ (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₀ a b = !![((a : ℂ) + b) ^ 2, 0; 0, (a : ℂ) ^ 2 + (b : ℂ) ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- `A₁ᴴA₁ = diag(a² + b², (a + b)²)`. -/
theorem au_gram₁₁ (a b : ℝ) :
    (asymA₁ a b)ᴴ * asymA₁ a b = !![(a : ℂ) ^ 2 + (b : ℂ) ^ 2, 0; 0, ((a : ℂ) + b) ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- `A₀ᴴA₁ = 2ab E₁₀`. -/
theorem au_gram₀₁ (a b : ℝ) :
    (asymA₀ a b)ᴴ * asymA₁ a b = !![0, 0; 2 * (a : ℂ) * b, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- `A₁ᴴA₀ = 2ab E₀₁`. -/
theorem au_gram₁₀ (a b : ℝ) :
    (asymA₁ a b)ᴴ * asymA₀ a b = !![0, 2 * (a : ℂ) * b; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymA₀, asymA₁, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The Gram matrix of a two-term combination. -/
theorem au_expand_gram (P R : Matrix QQ Q ℂ) (x y : ℂ) :
    (x • P + y • R)ᴴ * (x • P + y • R) =
      (star x * x) • (Pᴴ * P) + (star x * y) • (Pᴴ * R) + (star y * x) • (Rᴴ * P)
        + (star y * y) • (Rᴴ * R) := by
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul]
  module

/-- The conjugation by a two-term combination. -/
theorem au_expand_kraus (P R : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) (x y : ℂ) :
    (x • P + y • R) * ρ * (x • P + y • R)ᴴ =
      (x * star x) • (P * ρ * Pᴴ) + (x * star y) • (P * ρ * Rᴴ) + (y * star x) • (R * ρ * Pᴴ)
        + (y * star y) • (R * ρ * Rᴴ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul]
  module

/-- The vanishing of the certificate's right-hand side for one operator gives the six linear conditions. -/
theorem au_conditions (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (K : Matrix QQ Q ℂ)
    (h : (1 / 3) * ∑ j, Complex.normSq (((a + 2 * b : ℝ) : ℂ) * (K (0, j) 0 + K (1, j) 1)
          - ((2 * a + b : ℝ) : ℂ) * (K (j, 0) 0 + K (j, 1) 1))
        + (2 * a + b) * (a + 2 * b) * (Complex.normSq (K (1, 1) 0) + Complex.normSq (K (0, 0) 1)
          + Complex.normSq (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1) / 3
          + Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) / 3) = 0) :
    K (1, 1) 0 = 0 ∧ K (0, 0) 1 = 0 ∧ K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1 = 0 ∧
      K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0 = 0 ∧
      ((a + 2 * b : ℝ) : ℂ) * (K (0, 0) 0 + K (1, 0) 1) - ((2 * a + b : ℝ) : ℂ) * (K (0, 0) 0 + K (0, 1) 1) = 0 ∧
      ((a + 2 * b : ℝ) : ℂ) * (K (0, 1) 0 + K (1, 1) 1) - ((2 * a + b : ℝ) : ℂ) * (K (1, 0) 0 + K (1, 1) 1) = 0 := by
  rw [Fin.sum_univ_two] at h
  have hP : 0 < (2 * a + b) * (a + 2 * b) := by positivity
  have n1 := Complex.normSq_nonneg (K (1, 1) 0)
  have n2 := Complex.normSq_nonneg (K (0, 0) 1)
  have n3 := Complex.normSq_nonneg (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1)
  have n4 := Complex.normSq_nonneg (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0)
  have n5 := Complex.normSq_nonneg (((a + 2 * b : ℝ) : ℂ) * (K (0, 0) 0 + K (1, 0) 1)
    - ((2 * a + b : ℝ) : ℂ) * (K (0, 0) 0 + K (0, 1) 1))
  have n6 := Complex.normSq_nonneg (((a + 2 * b : ℝ) : ℂ) * (K (0, 1) 0 + K (1, 1) 1)
    - ((2 * a + b : ℝ) : ℂ) * (K (1, 0) 0 + K (1, 1) 1))
  set S := Complex.normSq (K (1, 1) 0) + Complex.normSq (K (0, 0) 1)
    + Complex.normSq (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1) / 3
    + Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) / 3 with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact add_nonneg (add_nonneg (add_nonneg n1 n2) (div_nonneg n3 (by norm_num))) (div_nonneg n4 (by norm_num))
  have hPS : 0 ≤ (2 * a + b) * (a + 2 * b) * S := mul_nonneg hP.le hS0
  have hPS0 : (2 * a + b) * (a + 2 * b) * S = 0 := by linarith
  have hS00 : S = 0 := by
    rcases mul_eq_zero.mp hPS0 with h' | h'
    · exact absurd h' (ne_of_gt hP)
    · exact h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.normSq_eq_zero.mp (by linarith)
  · exact Complex.normSq_eq_zero.mp (by linarith)
  · exact Complex.normSq_eq_zero.mp (by linarith)
  · exact Complex.normSq_eq_zero.mp (by linarith)
  · exact Complex.normSq_eq_zero.mp (by linarith)
  · exact Complex.normSq_eq_zero.mp (by linarith)

/-- The six linear conditions force the operator into the span of `A₀, A₁`. -/
theorem au_kraus_eq (a b : ℝ) (ha : a ≠ 0) (K : Matrix QQ Q ℂ) (c1 : K (1, 1) 0 = 0) (c2 : K (0, 0) 1 = 0)
    (c3 : K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1 = 0) (c4 : K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0 = 0)
    (c5 : ((a + 2 * b : ℝ) : ℂ) * (K (0, 0) 0 + K (1, 0) 1) - ((2 * a + b : ℝ) : ℂ) * (K (0, 0) 0 + K (0, 1) 1) = 0)
    (c6 : ((a + 2 * b : ℝ) : ℂ) * (K (0, 1) 0 + K (1, 1) 1) - ((2 * a + b : ℝ) : ℂ) * (K (1, 0) 0 + K (1, 1) 1) = 0) :
    K = (K (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K (0, 1) 0 / (a : ℂ)) • asymA₁ a b := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  push_cast at c5 c6
  have h01 : K (0, 1) 1 = K (1, 0) 1 / (a : ℂ) * (b : ℂ) := by
    rw [div_mul_eq_mul_div, eq_div_iff ha']
    linear_combination (-1 / 3 : ℂ) * c5 + (1 / 3 : ℂ) * ((b : ℂ) - a) * c3
  have h00 : K (0, 0) 0 = K (1, 0) 1 / (a : ℂ) * ((a : ℂ) + b) := by
    rw [div_mul_eq_mul_div, eq_div_iff ha']
    linear_combination (a : ℂ) * c3 + (-1 / 3 : ℂ) * c5 + (1 / 3 : ℂ) * ((b : ℂ) - a) * c3
  have h10 : K (1, 0) 0 = K (0, 1) 0 / (a : ℂ) * (b : ℂ) := by
    rw [div_mul_eq_mul_div, eq_div_iff ha']
    linear_combination (-1 / 3 : ℂ) * c6 + (1 / 3 : ℂ) * ((b : ℂ) - a) * c4
  have h11 : K (1, 1) 1 = K (0, 1) 0 / (a : ℂ) * ((a : ℂ) + b) := by
    rw [div_mul_eq_mul_div, eq_div_iff ha']
    linear_combination (a : ℂ) * c4 + (-1 / 3 : ℂ) * c6 + (1 / 3 : ℂ) * ((b : ℂ) - a) * c4
  ext x i
  rcases x with ⟨p, q⟩
  fin_cases p <;> fin_cases q <;> fin_cases i <;>
    simp [asymA₀, asymA₁, h00, h01, h10, h11, c1, c2, ha']

/-- Uniqueness of the asymmetric optimum: for `a, b > 0`, a channel with equality in the bound at the weights
`(a, b)` is the asymmetric cloner `Λ_{a,b}` as a map. -/
theorem eq_asym_of_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  have hP : 0 < (2 * a + b) * (a + 2 * b) := by positivity
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
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := au_conditions a b ha hb (K i) (by rw [← hR i]; exact hR0 i)
    exact au_kraus_eq a b ha.ne' (K i) c1 c2 c3 c4 c5 c6
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin r → ℂ, ∀ i, K i = x i • asymA₀ a b + y i • asymA₁ a b := ⟨_, _, hdec⟩
  -- trace preservation in the coordinates `x, y`
  have hK' : (∑ i, star (x i) * x i) • ((asymA₀ a b)ᴴ * asymA₀ a b)
      + (∑ i, star (x i) * y i) • ((asymA₀ a b)ᴴ * asymA₁ a b)
      + (∑ i, star (y i) * x i) • ((asymA₁ a b)ᴴ * asymA₀ a b)
      + (∑ i, star (y i) * y i) • ((asymA₁ a b)ᴴ * asymA₁ a b) = 1 := by
    have hK1 := hK
    unfold IsChannel at hK1
    rw [← hK1]
    simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxy i, au_expand_gram]
  rw [au_gram₀₀, au_gram₀₁, au_gram₁₀, au_gram₁₁] at hK'
  obtain ⟨X, hXd⟩ : ∃ X : ℂ, (∑ i, star (x i) * x i) = X := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : ℂ, (∑ i, star (y i) * y i) = Y := ⟨_, rfl⟩
  obtain ⟨Z₁, hZ₁d⟩ : ∃ Z : ℂ, (∑ i, star (x i) * y i) = Z := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂d⟩ : ∃ Z : ℂ, (∑ i, star (y i) * x i) = Z := ⟨_, rfl⟩
  rw [hXd, hYd, hZ₁d, hZ₂d] at hK'
  have e00 : X * ((a : ℂ) + b) ^ 2 + Y * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) = 1 := by
    have := congrArg (fun M => M 0 0) hK'
    simp [-mul_eq_zero] at this
    linear_combination this
  have e11 : X * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) + Y * ((a : ℂ) + b) ^ 2 = 1 := by
    have := congrArg (fun M => M 1 1) hK'
    simp [-mul_eq_zero] at this
    linear_combination this
  have e10 : Z₁ * (2 * (a : ℂ) * b) = 0 := by
    have := congrArg (fun M => M 1 0) hK'
    simp [-mul_eq_zero] at this
    linear_combination this
  have e01 : Z₂ * (2 * (a : ℂ) * b) = 0 := by
    have := congrArg (fun M => M 0 1) hK'
    simp [-mul_eq_zero] at this
    linear_combination this
  have h2ab : (2 * (a : ℂ) * b) ≠ 0 := by
    have : (2 * a * b : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hXY : X = Y := by
    have h' : (X - Y) * (2 * (a : ℂ) * b) = 0 := by
      linear_combination e00 - e11
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' h2ab
  have hXc : X * ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) = 1 := by
    push_cast
    linear_combination e00 + ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * hXY
  have hX : X = ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hXc
  have hZ1 : Z₁ = 0 := by
    rcases mul_eq_zero.mp e10 with h'' | h''
    · exact h''
    · exact absurd h'' h2ab
  have hZ2 : Z₂ = 0 := by
    rcases mul_eq_zero.mp e01 with h'' | h''
    · exact h''
    · exact absurd h'' h2ab
  have sxx : (∑ i, x i * star (x i)) = ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ)⁻¹ := by
    rw [← hX, ← hXd]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have syy : (∑ i, y i * star (y i)) = ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ)⁻¹ := by
    rw [← hX, hXY, ← hYd]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have sxy : (∑ i, x i * star (y i)) = 0 := by
    rw [← hZ2, ← hZ₂d]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have syx : (∑ i, y i * star (x i)) = 0 := by
    rw [← hZ1, ← hZ₁d]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- the action
  intro ρ
  have hexp : krausApply K ρ =
      (∑ i, x i * star (x i)) • (asymA₀ a b * ρ * (asymA₀ a b)ᴴ)
      + (∑ i, x i * star (y i)) • (asymA₀ a b * ρ * (asymA₁ a b)ᴴ)
      + (∑ i, y i * star (x i)) • (asymA₁ a b * ρ * (asymA₀ a b)ᴴ)
      + (∑ i, y i * star (y i)) • (asymA₁ a b * ρ * (asymA₁ a b)ᴴ) := by
    unfold krausApply
    simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxy i, au_expand_kraus]
  rw [hexp, sxx, sxy, syx, syy, zero_smul, zero_smul, add_zero, add_zero, asymChannel, smul_add]

end QubitCloning
