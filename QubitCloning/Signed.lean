module

public import QubitCloning.AsymUnique

/-!
# Signed asymmetric bounds

The polynomial certificate applies whenever `(2a + b)(a + 2b) ≥ 0`, even when one
fidelity coefficient is negative. This yields cloning-versus-anticloning bounds for
six-state averages. Such signed objectives do not inherit the worst-case corollary
of the nonnegative-weight bound. The equality map is unique when the product is
positive and both parameters are nonzero.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The asymmetric certificate bounds a signed fidelity objective whenever its
complement coefficient `(2a + b)(a + 2b)` is nonnegative. -/
theorem signed_asym_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ)
    (hP : 0 ≤ (2 * a + b) * (a + 2 * b)) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := by
  have hN := st_isChannel_normSq_sum K hK
  have hW := af_weighted_eq K hK a b
  have hS : 0 ≤ ∑ i, ((2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    apply Finset.sum_nonneg
    intro i _
    rw [af_sos a b (K i)]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
    · refine mul_nonneg hP ?_
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

/-- Vanishing of the signed certificate gives its six linear kernel conditions
whenever the complement coefficient is positive. -/
theorem sg_conditions (a b : ℝ) (hP : 0 < (2 * a + b) * (a + 2 * b)) (K : Matrix QQ Q ℂ)
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

/-- For nonzero parameters and positive complement coefficient, equality in the
signed bound forces the asymmetric channel as a map, including mixed-sign parameters. -/
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
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := sg_conditions a b hP (K i) (by rw [← hR i]; exact hR0 i)
    exact au_kraus_eq a b ha (K i) c1 c2 c3 c4 c5 c6
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
    have : (2 * a * b : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ha) hb
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

/-- A sharp cloning-versus-anticloning inequality: `3 F̄₁ − 5 F̄₂ ≤ 1`. -/
theorem clone_anticlone_bound_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    3 * sixAvg₁ K - 5 * sixAvg₂ K ≤ 1 := by
  have h := signed_asym_bound_internal K hK 3 (-1) (by norm_num)
  linarith

/-- The mixed-sign asymmetric channel at `(3, -1)` attains the fidelity pair
`(13/14, 5/14)`, and therefore the sharp bound `3 F̄₁ − 5 F̄₂ ≤ 1`. -/
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

/-- The channel attaining `3 F̄₁ − 5 F̄₂ = 1` is uniquely `Λ_{3,-1}`. -/
theorem eq_clone_anticlone_of_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 3 * sixAvg₁ K - 5 * sixAvg₂ K = 1) :
    ∀ ρ, krausApply K ρ = asymChannel 3 (-1) ρ := by
  apply eq_asym_of_signed_equality_internal K hK 3 (-1) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- If the second clone attains the universal-NOT floor, the first clone's average
fidelity is at most `5/6`. -/
theorem sixAvg₁_le_of_sixAvg₂_eq_third_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₂ K = 1 / 3) : sixAvg₁ K ≤ 5 / 6 := by
  by_contra hbad
  let d : ℝ := sixAvg₁ K - 5 / 6
  have hd : 0 < d := by dsimp [d]; linarith
  let b : ℝ := (3 / 2) * d - 1 / 2
  have hP : 0 ≤ (2 * 1 + b) * (1 + 2 * b) := by
    dsimp only [b]
    nlinarith [sq_nonneg d]
  have hb := signed_asym_bound_internal K hK 1 b hP
  have hF : sixAvg₁ K = 5 / 6 + d := by dsimp only [d]; ring
  rw [h, hF] at hb
  dsimp only [b] at hb
  nlinarith [mul_pos hd hd]

/-- If the first clone attains the universal-NOT floor, the second clone's average
fidelity is at most `5/6`. -/
theorem sixAvg₂_le_of_sixAvg₁_eq_third_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₁ K = 1 / 3) : sixAvg₂ K ≤ 5 / 6 := by
  by_contra hbad
  let d : ℝ := sixAvg₂ K - 5 / 6
  have hd : 0 < d := by dsimp [d]; linarith
  let a : ℝ := (3 / 2) * d - 1 / 2
  have hP : 0 ≤ (2 * a + 1) * (a + 2 * 1) := by
    dsimp only [a]
    nlinarith [sq_nonneg d]
  have ha := signed_asym_bound_internal K hK a 1 hP
  have hF : sixAvg₂ K = 5 / 6 + d := by dsimp only [d]; ring
  rw [h, hF] at ha
  dsimp only [a] at ha
  nlinarith [mul_pos hd hd]

/-- The mixed-sign channel at `(2, -1)` simultaneously reaches the universal-NOT
floor on its second output and the sharp companion fidelity `5/6` on its first,
both in six-state average and on every pure input. -/
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
