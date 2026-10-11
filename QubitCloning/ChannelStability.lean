module

public import QubitCloning.Stability
public import QubitCloning.BH
public import QubitCloning.AsymUnique

/-!
# Quantitative uniqueness of the optimum as a channel

If the six-state mean fidelity of a channel is at least `5/6 - ε`, then on every input `ρ` its output is within
Frobenius distance `200 √ε ‖ρ‖_F` of the Bužek–Hillery output. Each Kraus operator splits as `Kᵢ = Pᵢ + Rᵢ`, with
`Pᵢ = sb_project Kᵢ` in the span of `bhV₁, bhV₂` and `Σᵢ ‖Rᵢ‖² ≤ 6ε` (`sb_channel_coercivity`); trace
preservation fixes the coefficients of the `Pᵢ` up to the error matrix `E = Σᵢ (PᵢᴴRᵢ + RᵢᴴPᵢ + RᵢᴴRᵢ)`, and
submultiplicativity of the Frobenius norm bounds every remaining term. The route gives the constant `78√3 < 136`.
Every helper is prefixed `cs_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix
open scoped Matrix.Norms.Frobenius

/-! ## The Frobenius norm -/

/-- The Frobenius norm as the square root of the sum of squared moduli. -/
theorem cs_norm_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

theorem cs_norm_sq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [cs_norm_eq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _)

/-- An entry is bounded by the Frobenius norm. -/
theorem cs_entry_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (a : m) (b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h : ‖A a b‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [cs_norm_sq, ← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (A a b) ≤ ∑ j, Complex.normSq (A a j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (A a j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
      _ ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
          Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (A i j))
            (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  nlinarith [norm_nonneg (A a b), norm_nonneg A]

theorem cs_norm_mul3 {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) (C : Matrix n p ℂ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))

theorem cs_norm_add5 {M : Type*} [SeminormedAddCommGroup M] (a b c d e : M) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

/-- One conjugated term `c • (A ρ Bᴴ)`. -/
theorem cs_term (c : ℂ) (A B : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) (s k : ℝ) (hc : ‖c‖ ≤ s)
    (hk : ‖A‖ * ‖B‖ ≤ k) : ‖c • (A * ρ * Bᴴ)‖ ≤ s * k * ‖ρ‖ := by
  rw [norm_smul]
  have h1 : ‖A * ρ * Bᴴ‖ ≤ k * ‖ρ‖ :=
    calc ‖A * ρ * Bᴴ‖ ≤ ‖A‖ * ‖ρ‖ * ‖Bᴴ‖ := cs_norm_mul3 _ _ _
      _ = ‖A‖ * ‖B‖ * ‖ρ‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
      _ ≤ k * ‖ρ‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  calc ‖c‖ * ‖A * ρ * Bᴴ‖ ≤ s * (k * ‖ρ‖) :=
        mul_le_mul hc h1 (norm_nonneg _) ((norm_nonneg _).trans hc)
    _ = s * k * ‖ρ‖ := by ring

/-! ## The Bužek–Hillery operators -/

theorem cs_norm_V₁ : ‖bhV₁‖ ^ 2 = 6 := by
  rw [cs_norm_sq]
  simp [bhV₁, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  norm_num

theorem cs_norm_V₂ : ‖bhV₂‖ ^ 2 = 3 / 2 := by
  rw [cs_norm_sq]
  simp [bhV₂, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  norm_num

theorem cs_V₁V₂ : ‖bhV₁‖ * ‖bhV₂‖ ≤ 3 := by
  have h : (‖bhV₁‖ * ‖bhV₂‖) ^ 2 = 9 := by
    rw [mul_pow, cs_norm_V₁, cs_norm_V₂]; norm_num
  nlinarith [mul_nonneg (norm_nonneg bhV₁) (norm_nonneg bhV₂)]

/-- `V₁ᴴV₁ = diag(4, 2)`. -/
theorem cs_G₁₁ : bhV₁ᴴ * bhV₁ = !![4, 0; 0, 2] := by
  rw [bh_V₁_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bhV₁] <;> norm_num

/-- `V₁ᴴV₂ = E₁₀`. -/
theorem cs_G₁₂ : bhV₁ᴴ * bhV₂ = !![0, 0; 1, 0] := by
  rw [bh_V₁_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bhV₁, bhV₂]
  norm_num

/-- `V₂ᴴV₁ = E₀₁`. -/
theorem cs_G₂₁ : bhV₂ᴴ * bhV₁ = !![0, 1; 0, 0] := by
  rw [bh_V₂_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bhV₁, bhV₂]
  norm_num

/-- `V₂ᴴV₂ = diag(1/2, 1)`. -/
theorem cs_G₂₂ : bhV₂ᴴ * bhV₂ = !![1 / 2, 0; 0, 1] := by
  rw [bh_V₂_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bhV₂]
  norm_num

/-! ## One Kraus operator: the projection and the remainder -/

/-- The remainder `R = K - P` after the projection onto the span of `bhV₁, bhV₂`. -/
def cs_R (K : Matrix QQ Q ℂ) : Matrix QQ Q ℂ := K - sb_project K

/-- The Gram cross terms `PᴴR + RᴴP + RᴴR`. -/
def cs_U (K : Matrix QQ Q ℂ) : Matrix Q Q ℂ :=
  (sb_project K)ᴴ * cs_R K + (cs_R K)ᴴ * sb_project K + (cs_R K)ᴴ * cs_R K

/-- The conjugation cross terms `PρRᴴ + RρPᴴ + RρRᴴ`. -/
def cs_T (K : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ :=
  sb_project K * ρ * (cs_R K)ᴴ + cs_R K * ρ * (sb_project K)ᴴ + cs_R K * ρ * (cs_R K)ᴴ

theorem cs_split (K : Matrix QQ Q ℂ) : sb_project K + cs_R K = K := by
  simp [cs_R]

theorem cs_gram_term (K : Matrix QQ Q ℂ) :
    Kᴴ * K = (sb_x K * star (sb_x K)) • (bhV₁ᴴ * bhV₁) + (sb_y K * star (sb_x K)) • (bhV₁ᴴ * bhV₂)
      + (sb_x K * star (sb_y K)) • (bhV₂ᴴ * bhV₁) + (sb_y K * star (sb_y K)) • (bhV₂ᴴ * bhV₂)
      + cs_U K := by
  have h : (sb_project K + cs_R K)ᴴ * (sb_project K + cs_R K) =
      (sb_project K)ᴴ * sb_project K + cs_U K := by
    simp only [cs_U, conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [cs_split] at h
  rw [h, sb_project, au_expand_gram, mul_comm (star (sb_x K)) (sb_x K),
    mul_comm (star (sb_x K)) (sb_y K), mul_comm (star (sb_y K)) (sb_x K),
    mul_comm (star (sb_y K)) (sb_y K)]

theorem cs_kraus_term (K : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    K * ρ * Kᴴ = (sb_x K * star (sb_x K)) • (bhV₁ * ρ * bhV₁ᴴ)
      + (sb_x K * star (sb_y K)) • (bhV₁ * ρ * bhV₂ᴴ)
      + (sb_y K * star (sb_x K)) • (bhV₂ * ρ * bhV₁ᴴ)
      + (sb_y K * star (sb_y K)) • (bhV₂ * ρ * bhV₂ᴴ) + cs_T K ρ := by
  have h : (sb_project K + cs_R K) * ρ * (sb_project K + cs_R K)ᴴ =
      sb_project K * ρ * (sb_project K)ᴴ + cs_T K ρ := by
    simp only [cs_T, conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [cs_split] at h
  rw [h, sb_project, au_expand_kraus]

/-- `‖K‖² = ‖P‖² + ‖R‖²` entrywise: the projection is orthogonal. -/
theorem cs_pyth (K : Matrix QQ Q ℂ) :
    ∑ z, ∑ i, Complex.normSq (K z i) =
      ∑ z, ∑ i, Complex.normSq (sb_project K z i) + sb_distanceSq K := by
  simp [sb_distanceSq, sb_project, sb_x, sb_y, bhV₁, bhV₂,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im]
  ring

theorem cs_R_sq (K : Matrix QQ Q ℂ) : ‖cs_R K‖ ^ 2 = sb_distanceSq K := by
  rw [cs_norm_sq, sb_distanceSq]
  simp only [cs_R, Matrix.sub_apply]

theorem cs_norm_pyth (K : Matrix QQ Q ℂ) :
    ‖K‖ ^ 2 = ‖sb_project K‖ ^ 2 + ‖cs_R K‖ ^ 2 := by
  rw [cs_norm_sq K, cs_norm_sq (sb_project K), cs_R_sq]
  exact cs_pyth K

theorem cs_U_norm (K : Matrix QQ Q ℂ) :
    ‖cs_U K‖ ≤ 2 * ‖sb_project K‖ * ‖cs_R K‖ + ‖cs_R K‖ ^ 2 := by
  have h1 := Matrix.frobenius_norm_mul (sb_project K)ᴴ (cs_R K)
  have h2 := Matrix.frobenius_norm_mul (cs_R K)ᴴ (sb_project K)
  have h3 := Matrix.frobenius_norm_mul (cs_R K)ᴴ (cs_R K)
  rw [Matrix.frobenius_norm_conjTranspose] at h1 h2 h3
  have h4 := norm_add_le ((sb_project K)ᴴ * cs_R K + (cs_R K)ᴴ * sb_project K)
    ((cs_R K)ᴴ * cs_R K)
  have h5 := norm_add_le ((sb_project K)ᴴ * cs_R K) ((cs_R K)ᴴ * sb_project K)
  rw [cs_U]
  nlinarith [h1, h2, h3, h4, h5]

theorem cs_T_norm (K : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    ‖cs_T K ρ‖ ≤ ‖ρ‖ * (2 * ‖sb_project K‖ * ‖cs_R K‖ + ‖cs_R K‖ ^ 2) := by
  have h1 := cs_norm_mul3 (sb_project K) ρ (cs_R K)ᴴ
  have h2 := cs_norm_mul3 (cs_R K) ρ (sb_project K)ᴴ
  have h3 := cs_norm_mul3 (cs_R K) ρ (cs_R K)ᴴ
  rw [Matrix.frobenius_norm_conjTranspose] at h1 h2 h3
  have h4 := norm_add_le (sb_project K * ρ * (cs_R K)ᴴ + cs_R K * ρ * (sb_project K)ᴴ)
    (cs_R K * ρ * (cs_R K)ᴴ)
  have h5 := norm_add_le (sb_project K * ρ * (cs_R K)ᴴ) (cs_R K * ρ * (sb_project K)ᴴ)
  rw [cs_T]
  nlinarith [h1, h2, h3, h4, h5]

/-! ## The family: sums over the Kraus index -/

/-- The cross-term budget `S = Σᵢ (2‖Pᵢ‖‖Rᵢ‖ + ‖Rᵢ‖²)`. -/
def cs_S {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : ℝ :=
  ∑ i, (2 * ‖sb_project (K i)‖ * ‖cs_R (K i)‖ + ‖cs_R (K i)‖ ^ 2)

theorem cs_gram_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    ∑ i, (K i)ᴴ * K i = (∑ i, sb_x (K i) * star (sb_x (K i))) • (bhV₁ᴴ * bhV₁)
      + (∑ i, sb_y (K i) * star (sb_x (K i))) • (bhV₁ᴴ * bhV₂)
      + (∑ i, sb_x (K i) * star (sb_y (K i))) • (bhV₂ᴴ * bhV₁)
      + (∑ i, sb_y (K i) * star (sb_y (K i))) • (bhV₂ᴴ * bhV₂) + ∑ i, cs_U (K i) := by
  rw [Finset.sum_congr rfl (fun i _ => cs_gram_term (K i))]
  simp only [Finset.sum_add_distrib, Finset.sum_smul]

theorem cs_kraus_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply K ρ = (∑ i, sb_x (K i) * star (sb_x (K i))) • (bhV₁ * ρ * bhV₁ᴴ)
      + (∑ i, sb_x (K i) * star (sb_y (K i))) • (bhV₁ * ρ * bhV₂ᴴ)
      + (∑ i, sb_y (K i) * star (sb_x (K i))) • (bhV₂ * ρ * bhV₁ᴴ)
      + (∑ i, sb_y (K i) * star (sb_y (K i))) • (bhV₂ * ρ * bhV₂ᴴ) + ∑ i, cs_T (K i) ρ := by
  rw [krausApply, Finset.sum_congr rfl (fun i _ => cs_kraus_term (K i) ρ)]
  simp only [Finset.sum_add_distrib, Finset.sum_smul]

/-- The difference from the Bužek–Hillery map, term by term. -/
theorem cs_delta_eq {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply K ρ - bhChannel ρ =
      ((∑ i, sb_x (K i) * star (sb_x (K i))) - 1 / 6) • (bhV₁ * ρ * bhV₁ᴴ)
        + (∑ i, sb_x (K i) * star (sb_y (K i))) • (bhV₁ * ρ * bhV₂ᴴ)
        + (∑ i, sb_y (K i) * star (sb_x (K i))) • (bhV₂ * ρ * bhV₁ᴴ)
        + ((∑ i, sb_y (K i) * star (sb_y (K i))) - 2 / 3) • (bhV₂ * ρ * bhV₂ᴴ)
        + ∑ i, cs_T (K i) ρ := by
  rw [cs_kraus_sum, bhChannel]
  module

/-- Trace preservation solved for the four coefficients. -/
theorem cs_trace_solve (X Y Z W : ℂ) (E : Matrix Q Q ℂ)
    (h : X • (bhV₁ᴴ * bhV₁) + W • (bhV₁ᴴ * bhV₂) + Z • (bhV₂ᴴ * bhV₁) + Y • (bhV₂ᴴ * bhV₂) + E = 1) :
    X - 1 / 6 = (E 1 1 - 2 * E 0 0) / 6 ∧ Y - 2 / 3 = (2 * E 0 0 - 4 * E 1 1) / 3 ∧
      Z = -E 0 1 ∧ W = -E 1 0 := by
  rw [cs_G₁₁, cs_G₁₂, cs_G₂₁, cs_G₂₂] at h
  have h00 : X * 4 + W * 0 + Z * 0 + Y * (1 / 2) + E 0 0 = 1 := by
    simpa using congrArg (fun M : Matrix Q Q ℂ => M 0 0) h
  have h11 : X * 2 + W * 0 + Z * 0 + Y * 1 + E 1 1 = 1 := by
    simpa using congrArg (fun M : Matrix Q Q ℂ => M 1 1) h
  have h01 : X * 0 + W * 0 + Z * 1 + Y * 0 + E 0 1 = 0 := by
    simpa using congrArg (fun M : Matrix Q Q ℂ => M 0 1) h
  have h10 : X * 0 + W * 1 + Z * 0 + Y * 0 + E 1 0 = 0 := by
    simpa using congrArg (fun M : Matrix Q Q ℂ => M 1 0) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 3 : ℂ) * h00 - (1 / 6 : ℂ) * h11
  · linear_combination (-2 / 3 : ℂ) * h00 + (4 / 3 : ℂ) * h11
  · linear_combination h01
  · linear_combination h10

/-- The coefficients are within the error budget of their Bužek–Hillery values. -/
theorem cs_coef_bounds (X Y Z W : ℂ) (E : Matrix Q Q ℂ) (s : ℝ) (hE : ‖E‖ ≤ s)
    (h : X • (bhV₁ᴴ * bhV₁) + W • (bhV₁ᴴ * bhV₂) + Z • (bhV₂ᴴ * bhV₁) + Y • (bhV₂ᴴ * bhV₂) + E = 1) :
    ‖X - 1 / 6‖ ≤ s / 2 ∧ ‖Y - 2 / 3‖ ≤ 2 * s ∧ ‖Z‖ ≤ s ∧ ‖W‖ ≤ s := by
  obtain ⟨eX, eY, eZ, eW⟩ := cs_trace_solve X Y Z W E h
  have e00 := (cs_entry_le E 0 0).trans hE
  have e11 := (cs_entry_le E 1 1).trans hE
  have e01 := (cs_entry_le E 0 1).trans hE
  have e10 := (cs_entry_le E 1 0).trans hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eX, norm_div, Complex.norm_ofNat]
    have h1 := norm_sub_le (E 1 1) (2 * E 0 0)
    rw [norm_mul, Complex.norm_ofNat] at h1
    linarith
  · rw [eY, norm_div, Complex.norm_ofNat]
    have h1 := norm_sub_le (2 * E 0 0) (4 * E 1 1)
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at h1
    linarith
  · rw [eZ, norm_neg]; exact e01
  · rw [eW, norm_neg]; exact e10

/-- The channel bound in terms of the cross-term budget: `‖Λρ - Λ_BH ρ‖ ≤ 13 S ‖ρ‖`. -/
theorem cs_delta_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (ρ : Matrix Q Q ℂ) :
    ‖krausApply K ρ - bhChannel ρ‖ ≤ 13 * cs_S K * ‖ρ‖ := by
  have hK' : ∑ i, (K i)ᴴ * K i = 1 := hK
  have hES : ‖∑ i, cs_U (K i)‖ ≤ cs_S K :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => cs_U_norm (K i))
  have hTS : ‖∑ i, cs_T (K i) ρ‖ ≤ ‖ρ‖ * cs_S K := by
    rw [cs_S, Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => cs_T_norm (K i) ρ)
  obtain ⟨nX, nY, nZ, nW⟩ :=
    cs_coef_bounds _ _ _ _ _ _ hES ((cs_gram_sum K).symm.trans hK')
  have t1 := cs_term _ bhV₁ bhV₁ ρ _ 6 nX (by nlinarith [cs_norm_V₁])
  have t2 := cs_term _ bhV₁ bhV₂ ρ _ 3 nZ cs_V₁V₂
  have t3 := cs_term _ bhV₂ bhV₁ ρ _ 3 nW (by rw [mul_comm]; exact cs_V₁V₂)
  have t4 := cs_term _ bhV₂ bhV₂ ρ _ (3 / 2) nY (by nlinarith [cs_norm_V₂])
  rw [cs_delta_eq]
  refine (cs_norm_add5 _ _ _ _ _).trans ?_
  linarith

/-- The budget against the distance to the Kraus span: `S ≤ 3√2 · √D`. -/
theorem cs_S_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    cs_S K ≤ 3 * Real.sqrt 2 * Real.sqrt (∑ i, sb_distanceSq (K i)) := by
  have hsumR : ∑ i, ‖cs_R (K i)‖ ^ 2 = ∑ i, sb_distanceSq (K i) :=
    Finset.sum_congr rfl fun i _ => cs_R_sq (K i)
  have hsumK : ∑ i, ‖K i‖ ^ 2 = 2 := by
    rw [← st_isChannel_normSq_sum K hK]
    exact Finset.sum_congr rfl fun i _ => cs_norm_sq (K i)
  have hsum : ∑ i, ‖sb_project (K i)‖ ^ 2 + ∑ i, ‖cs_R (K i)‖ ^ 2 = 2 := by
    rw [← Finset.sum_add_distrib, ← hsumK]
    exact Finset.sum_congr rfl fun i _ => (cs_norm_pyth (K i)).symm
  have hcs : ∑ i, ‖sb_project (K i)‖ * ‖cs_R (K i)‖ ≤
      Real.sqrt (∑ i, ‖sb_project (K i)‖ ^ 2) * Real.sqrt (∑ i, ‖cs_R (K i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hS : cs_S K =
      2 * ∑ i, ‖sb_project (K i)‖ * ‖cs_R (K i)‖ + ∑ i, ‖cs_R (K i)‖ ^ 2 := by
    rw [cs_S, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hp0 : 0 ≤ ∑ i, ‖sb_project (K i)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq0 : 0 ≤ ∑ i, ‖cs_R (K i)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← hsumR, hS]
  have h1 : Real.sqrt (∑ i, ‖sb_project (K i)‖ ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (∑ i, ‖cs_R (K i)‖ ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 := Real.mul_self_sqrt hq0
  have hq := Real.sqrt_nonneg (∑ i, ‖cs_R (K i)‖ ^ 2)
  have h4 := mul_le_mul_of_nonneg_right h1 hq
  have h5 := mul_le_mul_of_nonneg_right h2 hq
  linarith

/-! ## The theorem -/

/-- If the six-state mean fidelity is at least `5/6 − ε`, the channel is within Frobenius distance
`200 √ε ‖ρ‖_F` of the Bužek–Hillery channel on every input `ρ`. -/
theorem channel_stability_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (ε : ℝ)
    (hε : 5 / 6 - ε ≤ (sixAvg₁ K + sixAvg₂ K) / 2) (ρ : Matrix Q Q ℂ) :
    Real.sqrt (∑ x, ∑ y, Complex.normSq ((krausApply K ρ - bhChannel ρ) x y)) ≤
      200 * Real.sqrt ε * Real.sqrt (∑ i, ∑ j, Complex.normSq (ρ i j)) := by
  rw [← cs_norm_eq (krausApply K ρ - bhChannel ρ), ← cs_norm_eq ρ]
  have hD := sb_channel_coercivity K hK
  have hD6 : ∑ i, sb_distanceSq (K i) ≤ 6 * ε := by linarith
  have h1 := cs_delta_le K hK ρ
  have h2 := cs_S_le K hK
  have h3 : Real.sqrt (∑ i, sb_distanceSq (K i)) ≤ Real.sqrt 6 * Real.sqrt ε := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
    exact Real.sqrt_le_sqrt hD6
  have h4 : Real.sqrt 2 * Real.sqrt 6 ≤ 7 / 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_le_left (by norm_num)]
    norm_num
  have hn := norm_nonneg ρ
  have he := Real.sqrt_nonneg ε
  have hs2 := Real.sqrt_nonneg 2
  have hS' : cs_S K ≤ 3 * Real.sqrt 2 * (Real.sqrt 6 * Real.sqrt ε) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  calc ‖krausApply K ρ - bhChannel ρ‖ ≤ 13 * cs_S K * ‖ρ‖ := h1
    _ ≤ 13 * (3 * Real.sqrt 2 * (Real.sqrt 6 * Real.sqrt ε)) * ‖ρ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS' (by norm_num)) hn
    _ = 39 * (Real.sqrt 2 * Real.sqrt 6) * Real.sqrt ε * ‖ρ‖ := by ring
    _ ≤ 39 * (7 / 2) * Real.sqrt ε * ‖ρ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) he) hn
    _ ≤ 200 * Real.sqrt ε * ‖ρ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) he) hn

end QubitCloning
