module

public import QubitCloning.States

/-!
# BH

The Bužek–Hillery channel and the universal-NOT witness (ARCH.md §3). Lane `bh`.
Every public theorem of this module is the `_internal` twin of a Challenge statement (header verbatim) or a desk-pinned helper; helpers of this lane are prefixed `bh_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-! ## Scalars -/

/-- A real number is fixed by the star of `ℂ`. -/
theorem bh_star_ofReal (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

/-- `(√6)⁻¹ · (√6)⁻¹ = 1/6`. -/
theorem bh_sqrt6_inv_sq : (Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹ = (1 / 6 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

/-- The Kraus scalar `(√6)⁻¹` of `V₁`. -/
def bh_c₁ : ℂ := (((Real.sqrt 6)⁻¹ : ℝ) : ℂ)

/-- The Kraus scalar `2 (√6)⁻¹ = √(2/3)` of `V₂`. -/
def bh_c₂ : ℂ := ((2 * (Real.sqrt 6)⁻¹ : ℝ) : ℂ)

theorem bh_c₁_mul_star : bh_c₁ * star bh_c₁ = (1 / 6 : ℂ) := by
  rw [bh_c₁, bh_star_ofReal, ← Complex.ofReal_mul, bh_sqrt6_inv_sq]
  norm_num

theorem bh_star_c₁_mul : star bh_c₁ * bh_c₁ = (1 / 6 : ℂ) := by
  rw [mul_comm, bh_c₁_mul_star]

theorem bh_c₂_mul_star : bh_c₂ * star bh_c₂ = (2 / 3 : ℂ) := by
  rw [bh_c₂, bh_star_ofReal, ← Complex.ofReal_mul,
    show (2 * (Real.sqrt 6)⁻¹) * (2 * (Real.sqrt 6)⁻¹) = 4 * ((Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹) by ring,
    bh_sqrt6_inv_sq]
  norm_num

theorem bh_star_c₂_mul : star bh_c₂ * bh_c₂ = (2 / 3 : ℂ) := by
  rw [mul_comm, bh_c₂_mul_star]

/-! ## Kraus pairs and scaled families -/

/-- The map of a scaled pair of Kraus operators. -/
theorem bh_krausApply_pair (c d : ℂ) (A B : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    krausApply ![c • A, d • B] ρ = (c * star c) • (A * ρ * Aᴴ) + (d * star d) • (B * ρ * Bᴴ) := by
  simp only [krausApply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (star c) c, mul_comm (star d) d]

/-- The Gram sum of a scaled pair of Kraus operators. -/
theorem bh_gram_pair (c d : ℂ) (A B : Matrix QQ Q ℂ) :
    ∑ i, (![c • A, d • B] i)ᴴ * ![c • A, d • B] i = (star c * c) • (Aᴴ * A) + (star d * d) • (Bᴴ * B) := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm c (star c), mul_comm d (star d)]

/-! ## The partial traces are linear -/

theorem bh_traceSecond_smul (c : ℂ) (M : Matrix QQ QQ ℂ) : traceSecond (c • M) = c • traceSecond M := by
  ext a b
  simp only [traceSecond, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]

theorem bh_traceSecond_add (M N : Matrix QQ QQ ℂ) :
    traceSecond (M + N) = traceSecond M + traceSecond N := by
  ext a b
  simp [traceSecond, Finset.sum_add_distrib]

/-! ## The Bužek–Hillery operators are real -/

theorem bh_V₁_conjTranspose : bhV₁ᴴ = bhV₁ᵀ := by
  ext i x
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, bhV₁, Matrix.of_apply]
  split_ifs <;> simp

theorem bh_V₂_conjTranspose : bhV₂ᴴ = bhV₂ᵀ := by
  ext i x
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, bhV₂, Matrix.of_apply]
  split_ifs <;> simp

/-! ## The Bužek–Hillery channel -/

/-- The Bužek–Hillery map is a channel: it has a Kraus family. -/
theorem bh_isChannel_internal :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = bhChannel ρ := by
  refine ⟨![bh_c₁ • bhV₁, bh_c₂ • bhV₂], ?_, ?_⟩
  · rw [IsChannel, bh_gram_pair, bh_star_c₁_mul, bh_star_c₂_mul, bh_V₁_conjTranspose, bh_V₂_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bhV₁, bhV₂] <;> norm_num
  · intro ρ
    rw [bh_krausApply_pair, bh_c₁_mul_star, bh_c₂_mul_star]
    rfl

/-- The first marginal of the Bužek–Hillery channel is the depolarizing map `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1`. -/
theorem bh_traceSecond_internal (ρ : Matrix Q Q ℂ) :
    traceSecond (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  rw [bhChannel, bh_V₁_conjTranspose, bh_V₂_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [traceSecond, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, bhV₁, bhV₂] <;> ring

/-- The second marginal of the Bužek–Hillery channel is the same depolarizing map. -/
theorem bh_traceFirst_internal (ρ : Matrix Q Q ℂ) :
    traceFirst (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  rw [bhChannel, bh_V₁_conjTranspose, bh_V₂_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [traceFirst, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, bhV₁, bhV₂] <;> ring

/-- The Bužek–Hillery map preserves the trace. -/
theorem bh_trace_internal (ρ : Matrix Q Q ℂ) : Matrix.trace (bhChannel ρ) = Matrix.trace ρ := by
  have h : Matrix.trace (bhChannel ρ) = Matrix.trace (traceSecond (bhChannel ρ)) := by
    simp only [Matrix.trace, traceSecond, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
  rw [h, bh_traceSecond_internal]
  simp only [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  ring

/-- Any Kraus family of the Bužek–Hillery channel clones every pure state with both fidelities `5/6`. -/
theorem bh_fidelity_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ)
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 5 / 6 := by
  have h := st_fidelity_depolarized ψ hψ (2 / 3) (1 / 6)
  have e₁ : ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) := by norm_num
  have e₂ : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
  rw [e₁, e₂] at h
  constructor
  · rw [F₁, hK, bh_traceSecond_internal, h]
    norm_num
  · rw [F₂, hK, bh_traceFirst_internal, h]
    norm_num

/-- Its six-state averages are `5/6` and `5/6`. -/
theorem bh_sixAvg_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ) :
    sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 5 / 6 := by
  have h₁ : ∀ s, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) = 5 / 6 := by
    intro s
    rw [← proj_pauliVec_internal s]
    exact (bh_fidelity_internal K hK (pauliVec s) (pauliVec_unit_internal s)).1
  have h₂ : ∀ s, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) = 5 / 6 := by
    intro s
    rw [← proj_pauliVec_internal s]
    exact (bh_fidelity_internal K hK (pauliVec s) (pauliVec_unit_internal s)).2
  constructor
  · simp only [sixAvg₁, h₁, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · simp only [sixAvg₂, h₂, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

theorem bh_asymA₀_one : asymA₀ 1 1 = bhV₁ := by
  ext ⟨a, b⟩ i
  fin_cases a <;> fin_cases b <;> fin_cases i <;> norm_num [asymA₀, bhV₁]

theorem bh_asymA₁_one : asymA₁ 1 1 = (2 : ℂ) • bhV₂ := by
  ext ⟨a, b⟩ i
  fin_cases a <;> fin_cases b <;> fin_cases i <;> norm_num [asymA₁, bhV₂]

theorem bh_star_two : star (2 : ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, bh_star_ofReal]

/-- The Bužek–Hillery channel is the symmetric member `a = b` of the family. -/
theorem bhChannel_eq_asymChannel_internal (ρ : Matrix Q Q ℂ) : bhChannel ρ = asymChannel 1 1 ρ := by
  rw [asymChannel, bh_asymA₀_one, bh_asymA₁_one, bhChannel]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, bh_star_two]
  congr 1 <;> congr 1 <;> norm_num

/-! ## The universal-NOT witness -/

/-- Pauli `X`. -/
def bh_pauliX : Matrix Q Q ℂ := !![0, 1; 1, 0]

/-- `XZ = -i Y`, Pauli `Y` up to the phase `-i` (the phase drops out of `σ ρ σᴴ`), written over the reals. -/
def bh_pauliXZ : Matrix Q Q ℂ := !![0, -1; 1, 0]

/-- Pauli `Z`. -/
def bh_pauliZ : Matrix Q Q ℂ := !![1, 0; 0, -1]

/-- The operator `σ ⊗ |j⟩`: apply `σ` to the first clone and prepare the second clone in `|j⟩`. -/
def bh_tk (σ : Matrix Q Q ℂ) (j : Q) : Matrix QQ Q ℂ :=
  Matrix.of fun x i => if x.2 = j then σ x.1 i else 0

/-- The six operators `σ ⊗ |j⟩`, `σ ∈ {X, XZ, Z}`, `j ∈ {0, 1}`. -/
def bh_notP : Fin 6 → Matrix QQ Q ℂ :=
  ![bh_tk bh_pauliX 0, bh_tk bh_pauliX 1, bh_tk bh_pauliXZ 0, bh_tk bh_pauliXZ 1,
    bh_tk bh_pauliZ 0, bh_tk bh_pauliZ 1]

/-- The universal NOT on the first clone with a maximally mixed second clone: `K m = (√6)⁻¹ • (σ ⊗ |j⟩)`. -/
def bh_notKraus (m : Fin 6) : Matrix QQ Q ℂ := bh_c₁ • bh_notP m

theorem bh_notP_0 : bh_notP 0 = bh_tk bh_pauliX 0 := rfl
theorem bh_notP_1 : bh_notP 1 = bh_tk bh_pauliX 1 := rfl
theorem bh_notP_2 : bh_notP 2 = bh_tk bh_pauliXZ 0 := rfl
theorem bh_notP_3 : bh_notP 3 = bh_tk bh_pauliXZ 1 := rfl
theorem bh_notP_4 : bh_notP 4 = bh_tk bh_pauliZ 0 := rfl
theorem bh_notP_5 : bh_notP 5 = bh_tk bh_pauliZ 1 := rfl

theorem bh_tk_gram (σ : Matrix Q Q ℂ) (j : Q) : (bh_tk σ j)ᴴ * bh_tk σ j = σᴴ * σ := by
  fin_cases j <;> ext i l <;>
    simp [bh_tk, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bh_tk_traceSecond (σ : Matrix Q Q ℂ) (j : Q) (ρ : Matrix Q Q ℂ) :
    traceSecond (bh_tk σ j * ρ * (bh_tk σ j)ᴴ) = σ * ρ * σᴴ := by
  fin_cases j <;> ext a b <;>
    simp [bh_tk, traceSecond, Matrix.mul_apply, Fin.sum_univ_two]

theorem bh_notKraus_isChannel : IsChannel bh_notKraus := by
  have h : ∀ m, (bh_notKraus m)ᴴ * bh_notKraus m = (1 / 6 : ℂ) • ((bh_notP m)ᴴ * bh_notP m) := by
    intro m
    simp only [bh_notKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      bh_c₁_mul_star]
  rw [IsChannel, Finset.sum_congr rfl (fun m _ => h m), ← Finset.smul_sum]
  simp only [Fin.sum_univ_six, bh_notP_0, bh_notP_1, bh_notP_2, bh_notP_3, bh_notP_4, bh_notP_5, bh_tk_gram]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [bh_pauliX, bh_pauliXZ, bh_pauliZ]

/-- The first marginal of the universal-NOT witness: `ρ ↦ (2/3) Tr(ρ)·1 − (1/3) ρ`. -/
theorem bh_not_traceSecond (ρ : Matrix Q Q ℂ) :
    traceSecond (krausApply bh_notKraus ρ) =
      ((-1 / 3 : ℝ) : ℂ) • ρ + ((2 / 3 : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := by
  have h : ∀ m, bh_notKraus m * ρ * (bh_notKraus m)ᴴ = (1 / 6 : ℂ) • (bh_notP m * ρ * (bh_notP m)ᴴ) := by
    intro m
    simp only [bh_notKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      bh_star_c₁_mul]
  rw [krausApply, Finset.sum_congr rfl (fun m _ => h m), ← Finset.smul_sum, bh_traceSecond_smul]
  simp only [Fin.sum_univ_six, bh_notP_0, bh_notP_1, bh_notP_2, bh_notP_3, bh_notP_4, bh_notP_5,
    bh_traceSecond_add, bh_tk_traceSecond]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    smul_eq_mul, Matrix.trace_fin_two]
  fin_cases a <;> fin_cases b <;> simp [bh_pauliX, bh_pauliXZ, bh_pauliZ] <;> ring

/-- The floor `1/3` is attained: the universal NOT on the first clone with a maximally mixed second clone. -/
theorem exists_sixAvg_eq_third_internal :
    ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧ sixAvg₁ K = 1 / 3 := by
  refine ⟨6, bh_notKraus, bh_notKraus_isChannel, ?_⟩
  have h : ∀ s, fidelity (pauliState s) (traceSecond (krausApply bh_notKraus (pauliState s))) = 1 / 3 := by
    intro s
    rw [bh_not_traceSecond, ← proj_pauliVec_internal s,
      st_fidelity_depolarized (pauliVec s) (pauliVec_unit_internal s)]
    norm_num
  simp only [sixAvg₁, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end QubitCloning
