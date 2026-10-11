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
    fidelity (proj ψ) σ = (star ψ ⬝ᵥ (σ *ᵥ ψ)).re := by
  unfold fidelity proj
  congr 1
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, mulVec,
    Fin.sum_univ_two, Pi.star_apply]
  ring

/-- `(√2)⁻¹` in `ℂ` is the cast of a real number whose square is `1/2`. -/
theorem st_sqrt_two_inv :
    (Real.sqrt 2 : ℂ)⁻¹ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ∧
      (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  refine ⟨by push_cast; rfl, ?_⟩
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Each Pauli eigenstate is the projector onto its unit vector (the lane's working copy of the pin). -/
theorem st_proj_pauliVec (s : Fin 6) : proj (pauliVec s) = pauliState s := by
  obtain ⟨e, hv⟩ := st_sqrt_two_inv
  generalize (Real.sqrt 2)⁻¹ = v at hv e
  ext a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
    simp [proj, pauliVec, pauliState, Matrix.vecMulVec_apply, e] <;> linarith

/-- The six vectors are unit vectors (the lane's working copy of the pin). -/
theorem st_pauliVec_unit (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 := by
  obtain ⟨e, hv⟩ := st_sqrt_two_inv
  generalize (Real.sqrt 2)⁻¹ = v at hv e
  fin_cases s <;> apply Complex.ext <;>
    simp [pauliVec, dotProduct, Fin.sum_univ_two, e] <;> linarith

/-- `krausApply` is additive in the Kraus family: the sum over the family of the one-operator maps. -/
theorem st_krausApply_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply K ρ = ∑ i, krausApply ![K i] ρ := by
  unfold krausApply
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero]

/-- The partial traces are additive. -/
theorem st_traceSecond_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceSecond (∑ i ∈ s, M i) = ∑ i ∈ s, traceSecond (M i) := by
  ext a b
  simp only [traceSecond, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

theorem st_traceFirst_sum {ι : Type} (s : Finset ι) (M : ι → Matrix QQ QQ ℂ) :
    traceFirst (∑ i ∈ s, M i) = ∑ i ∈ s, traceFirst (M i) := by
  ext a b
  simp only [traceFirst, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- The partial traces commute with scalars. -/
theorem st_traceSecond_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceSecond (c • M) = c • traceSecond M := by
  ext a b
  simp only [traceSecond, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem st_traceFirst_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceFirst (c • M) = c • traceFirst M := by
  ext a b
  simp only [traceFirst, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The fidelity is additive in its second argument. -/
theorem st_fidelity_sum {ι : Type} (s : Finset ι) (ρ : Matrix Q Q ℂ) (σ : ι → Matrix Q Q ℂ) :
    fidelity ρ (∑ i ∈ s, σ i) = ∑ i ∈ s, fidelity ρ (σ i) := by
  simp only [fidelity, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- The six-state averages are sums over the Kraus family of the one-operator averages. -/
theorem st_sixAvg₁_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₁ K = ∑ i, sixAvg₁ ![K i] := by
  unfold sixAvg₁
  simp_rw [st_krausApply_eq_sum K, st_traceSecond_sum, st_fidelity_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem st_sixAvg₂_eq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    sixAvg₂ K = ∑ i, sixAvg₂ ![K i] := by
  unfold sixAvg₂
  simp_rw [st_krausApply_eq_sum K, st_traceFirst_sum, st_fidelity_sum]
  rw [Finset.sum_comm, Finset.sum_div]

/-- The clone fidelities on the six vectors are the six-state terms. -/
theorem st_F₁_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₁ K (pauliVec s) = fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) := by
  unfold F₁
  rw [st_proj_pauliVec]

theorem st_F₂_pauliVec {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (s : Fin 6) :
    F₂ K (pauliVec s) = fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := by
  unfold F₂
  rw [st_proj_pauliVec]

/-- Pointwise lower bounds on the six vectors bound the averages. -/
theorem st_le_sixAvg₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₁ K ψ) : f ≤ sixAvg₁ K := by
  have h6 : ∀ s ∈ (Finset.univ : Finset (Fin 6)),
      f ≤ fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) := by
    intro s _
    rw [← st_F₁_pauliVec]
    exact h _ (st_pauliVec_unit s)
  have hs := Finset.sum_le_sum h6
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  push_cast at hs
  unfold sixAvg₁
  linarith

theorem st_le_sixAvg₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (f : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f ≤ F₂ K ψ) : f ≤ sixAvg₂ K := by
  have h6 : ∀ s ∈ (Finset.univ : Finset (Fin 6)),
      f ≤ fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := by
    intro s _
    rw [← st_F₂_pauliVec]
    exact h _ (st_pauliVec_unit s)
  have hs := Finset.sum_le_sum h6
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  push_cast at hs
  unfold sixAvg₂
  linarith

/-- `Aᴴ A` has trace `‖A‖²`, as a complex number. -/
theorem st_trace_conjTranspose_mul_self (A : Matrix QQ Q ℂ) :
    Matrix.trace (Aᴴ * A) = ((∑ x, ∑ j, Complex.normSq (A x j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- A channel's Kraus operators have squared Frobenius norms summing to `2`. -/
theorem st_isChannel_normSq_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) = 2 := by
  have h1 := congrArg Matrix.trace hK
  rw [Matrix.trace_sum, Matrix.trace_one] at h1
  simp only [st_trace_conjTranspose_mul_self] at h1
  have h3 : ((∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h1]
    simp
  exact_mod_cast h3

/-- The fidelity of a projector with a depolarized copy of itself: `fidelity (proj ψ) (c • proj ψ + d • Tr(proj ψ) • 1) = c + d` for a unit `ψ` and real `c, d`. -/
theorem st_fidelity_depolarized (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (c d : ℝ) :
    fidelity (proj ψ) ((c : ℂ) • proj ψ + (d : ℂ) • Matrix.trace (proj ψ) • (1 : Matrix Q Q ℂ)) = c + d := by
  rw [st_fidelity_proj]
  have hn : star (ψ 0) * ψ 0 + star (ψ 1) * ψ 1 = 1 := by
    simpa only [dotProduct, Fin.sum_univ_two, Pi.star_apply] using hψ
  have e00 : (1 : Matrix Q Q ℂ) 0 0 = 1 := Matrix.one_apply_eq 0
  have e11 : (1 : Matrix Q Q ℂ) 1 1 = 1 := Matrix.one_apply_eq 1
  have e01 : (1 : Matrix Q Q ℂ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have e10 : (1 : Matrix Q Q ℂ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have key : star ψ ⬝ᵥ (((c : ℂ) • proj ψ + (d : ℂ) • Matrix.trace (proj ψ) • (1 : Matrix Q Q ℂ)) *ᵥ ψ)
      = ((c : ℂ) + d) * (star (ψ 0) * ψ 0 + star (ψ 1) * ψ 1) ^ 2 := by
    simp only [dotProduct, mulVec, proj, Matrix.trace_fin_two, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.smul_apply, Fin.sum_univ_two, Pi.star_apply, smul_eq_mul, e00, e11, e01, e10]
    ring
  rw [key, hn]
  simp

/-- Each Pauli eigenstate is the projector onto its unit vector. -/
theorem proj_pauliVec_internal (s : Fin 6) : proj (pauliVec s) = pauliState s := st_proj_pauliVec s

/-- The six vectors are unit vectors. -/
theorem pauliVec_unit_internal (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 := st_pauliVec_unit s

/-! ## Extras for the neighbouring modules -/

/-- A depolarizing first marginal fixes the first clone's fidelity on every unit vector. -/
theorem st_F₁_of_marginal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (c d : ℝ)
    (hm : ∀ ρ, traceSecond (krausApply K ρ) = (c : ℂ) • ρ + (d : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ))
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₁ K ψ = c + d := by
  unfold F₁
  rw [hm]
  exact st_fidelity_depolarized ψ hψ c d

/-- A depolarizing second marginal fixes the second clone's fidelity on every unit vector. -/
theorem st_F₂_of_marginal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (c d : ℝ)
    (hm : ∀ ρ, traceFirst (krausApply K ρ) = (c : ℂ) • ρ + (d : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ))
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₂ K ψ = c + d := by
  unfold F₂
  rw [hm]
  exact st_fidelity_depolarized ψ hψ c d

/-- A depolarizing first marginal fixes the first six-state average. -/
theorem st_sixAvg₁_of_marginal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (c d : ℝ)
    (hm : ∀ ρ, traceSecond (krausApply K ρ) = (c : ℂ) • ρ + (d : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ)) :
    sixAvg₁ K = c + d := by
  have h : ∀ s, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) = c + d := by
    intro s
    rw [← st_F₁_pauliVec]
    exact st_F₁_of_marginal K c d hm _ (st_pauliVec_unit s)
  unfold sixAvg₁
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- A depolarizing second marginal fixes the second six-state average. -/
theorem st_sixAvg₂_of_marginal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (c d : ℝ)
    (hm : ∀ ρ, traceFirst (krausApply K ρ) = (c : ℂ) • ρ + (d : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ)) :
    sixAvg₂ K = c + d := by
  have h : ∀ s, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) = c + d := by
    intro s
    rw [← st_F₂_pauliVec]
    exact st_F₂_of_marginal K c d hm _ (st_pauliVec_unit s)
  unfold sixAvg₂
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `z̄ z = |z|²` with `star`. -/
theorem st_star_mul_self (z : ℂ) : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem st_one_apply_00 : (1 : Matrix Q Q ℂ) 0 0 = 1 := Matrix.one_apply_eq 0

theorem st_one_apply_11 : (1 : Matrix Q Q ℂ) 1 1 = 1 := Matrix.one_apply_eq 1

theorem st_one_apply_01 : (1 : Matrix Q Q ℂ) 0 1 = 0 := Matrix.one_apply_ne (by decide)

theorem st_one_apply_10 : (1 : Matrix Q Q ℂ) 1 0 = 0 := Matrix.one_apply_ne (by decide)

/-- The six Pauli eigenstates form a 2-design: `Σₛ ρₛ(a, b) ρₛ(c, d) = δ_ab δ_cd + δ_ad δ_cb`. -/
theorem st_pauliState_design (a b c d : Q) :
    ∑ s, pauliState s a b * pauliState s c d =
      (1 : Matrix Q Q ℂ) a b * (1 : Matrix Q Q ℂ) c d + (1 : Matrix Q Q ℂ) a d * (1 : Matrix Q Q ℂ) c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> apply Complex.ext <;>
    simp [pauliState, Fin.sum_univ_six] <;> norm_num

/-- One Kraus operator: `krausApply ![A] ρ = A ρ Aᴴ`. -/
theorem st_krausApply_single (A : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply ![A] ρ = A * ρ * Aᴴ := by
  simp only [krausApply, Fin.sum_univ_one, Matrix.cons_val_zero]

/-- The first-clone overlap of one Kraus operator as a quadratic form in `ρ`. -/
theorem st_trace_traceSecond_single (A : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    Matrix.trace (ρ * traceSecond (A * ρ * Aᴴ)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ρ a b * ρ c d * ∑ k, A (b, k) c * star (A (a, k) d) := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, traceSecond, Matrix.of_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The second-clone overlap of one Kraus operator as a quadratic form in `ρ`. -/
theorem st_trace_traceFirst_single (A : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    Matrix.trace (ρ * traceFirst (A * ρ * Aᴴ)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ρ a b * ρ c d * ∑ k, A (k, b) c * star (A (k, a) d) := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, traceFirst, Matrix.of_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The one-operator six-state sum of the first clone (the statement of `form_six_one`), by the 2-design. -/
theorem st_six_one (K : Matrix QQ Q ℂ) :
    6 * sixAvg₁ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (0, j) 0 + K (1, j) 1) := by
  have hc : ∑ s, Matrix.trace (pauliState s * traceSecond (K * pauliState s * Kᴴ)) =
      ∑ x, ∑ i, star (K x i) * K x i + ∑ j, star (K (0, j) 0 + K (1, j) 1) * (K (0, j) 0 + K (1, j) 1) := by
    simp only [st_trace_traceSecond_single]
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib, ← Finset.sum_mul, st_pauliState_design,
      st_one_apply_00, st_one_apply_01, st_one_apply_10, st_one_apply_11, Fintype.sum_prod_type, star_add]
    ring
  have e : 6 * sixAvg₁ ![K] = (∑ s, Matrix.trace (pauliState s * traceSecond (K * pauliState s * Kᴴ))).re := by
    unfold sixAvg₁
    simp only [st_krausApply_single, Complex.re_sum, fidelity]
    ring
  rw [e, hc]
  simp only [st_star_mul_self, Complex.add_re, Complex.re_sum, Complex.ofReal_re]

/-- The one-operator six-state sum of the second clone (the statement of `form_six_two`), by the 2-design. -/
theorem st_six_two (K : Matrix QQ Q ℂ) :
    6 * sixAvg₂ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (j, 0) 0 + K (j, 1) 1) := by
  have hc : ∑ s, Matrix.trace (pauliState s * traceFirst (K * pauliState s * Kᴴ)) =
      ∑ x, ∑ i, star (K x i) * K x i + ∑ j, star (K (j, 0) 0 + K (j, 1) 1) * (K (j, 0) 0 + K (j, 1) 1) := by
    simp only [st_trace_traceFirst_single]
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib, ← Finset.sum_mul, st_pauliState_design,
      st_one_apply_00, st_one_apply_01, st_one_apply_10, st_one_apply_11, Fintype.sum_prod_type, star_add]
    ring
  have e : 6 * sixAvg₂ ![K] = (∑ s, Matrix.trace (pauliState s * traceFirst (K * pauliState s * Kᴴ))).re := by
    unfold sixAvg₂
    simp only [st_krausApply_single, Complex.re_sum, fidelity]
    ring
  rw [e, hc]
  simp only [st_star_mul_self, Complex.add_re, Complex.re_sum, Complex.ofReal_re]

end QubitCloning
