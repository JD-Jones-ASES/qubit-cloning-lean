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

/-- The fidelity trace for one Kraus operator and the first clone, entrywise. -/
theorem form_trace_two (K : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    Matrix.trace (ρ * traceSecond (krausApply ![K] ρ)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ρ a b * ρ c d * ∑ k, K (b, k) c * star (K (a, k) d) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, traceSecond, krausApply, Fin.sum_univ_one,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The fidelity trace for one Kraus operator and the second clone, entrywise. -/
theorem form_trace_one (K : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    Matrix.trace (ρ * traceFirst (krausApply ![K] ρ)) =
      ∑ a, ∑ b, ∑ c, ∑ d, ρ a b * ρ c d * ∑ k, K (k, b) c * star (K (k, a) d) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, traceFirst, krausApply, Fin.sum_univ_one,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The six Pauli states form a 2-design: `Σₛ ρₛ ⊗ ρₛ = 1 + SWAP`, entrywise. -/
theorem form_design (a b c d : Q) :
    ∑ s, pauliState s a b * pauliState s c d =
      (if a = b ∧ c = d then 1 else 0) + (if a = d ∧ c = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_succ, pauliState, Complex.ext_iff] <;> norm_num

/-- Moving the sum over the six states inside four sums over a qubit. -/
theorem form_swap (f : Fin 6 → Q → Q → Q → Q → ℂ) :
    ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, f s a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ s, f s a b c d := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/-- The six-state sum of a bilinear expression in the state. -/
theorem form_six_sum (Y : Q → Q → Q → Q → ℂ) :
    ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, pauliState s a b * pauliState s c d * Y a b c d =
      ∑ a, ∑ c, (Y a a c c + Y a c c a) := by
  rw [form_swap]
  simp only [← Finset.sum_mul, form_design]
  simp [Fin.sum_univ_two]
  ring

/-- The one-operator six-state sums as quadratic forms (`6 W₁ = 1 + Ω₁`): with `k_{r a b} = K (a, b) r`,
`6 · sixAvg₁ ![K] = Σ |K x i|² + Σⱼ |K (0, j) 0 + K (1, j) 1|²`. -/
theorem form_six_one (K : Matrix QQ Q ℂ) :
    6 * sixAvg₁ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (0, j) 0 + K (1, j) 1) := by
  have h1 : 6 * sixAvg₁ ![K] =
      (∑ s, Matrix.trace (pauliState s * traceSecond (krausApply ![K] (pauliState s)))).re := by
    rw [Complex.re_sum]; unfold sixAvg₁ fidelity; ring
  rw [h1, ← Complex.ofReal_re
    (∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (0, j) 0 + K (1, j) 1))]
  congr 1
  simp only [form_trace_two]
  rw [form_six_sum]
  simp only [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, starRingEnd_apply,
    star_add, Fin.sum_univ_two, Fintype.sum_prod_type]
  ring

/-- `6 · sixAvg₂ ![K] = Σ |K x i|² + Σⱼ |K (j, 0) 0 + K (j, 1) 1|²` (`6 W₂ = 1 + Ω₂`). -/
theorem form_six_two (K : Matrix QQ Q ℂ) :
    6 * sixAvg₂ ![K] = ∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (j, 0) 0 + K (j, 1) 1) := by
  have h1 : 6 * sixAvg₂ ![K] =
      (∑ s, Matrix.trace (pauliState s * traceFirst (krausApply ![K] (pauliState s)))).re := by
    rw [Complex.re_sum]; unfold sixAvg₂ fidelity; ring
  rw [h1, ← Complex.ofReal_re
    (∑ x, ∑ i, Complex.normSq (K x i) + ∑ j, Complex.normSq (K (j, 0) 0 + K (j, 1) 1))]
  congr 1
  simp only [form_trace_one]
  rw [form_six_sum]
  simp only [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, starRingEnd_apply,
    star_add, Fin.sum_univ_two, Fintype.sum_prod_type]
  ring

/-- The symmetric certificate: the six-term sum of squares (the desk's `probe.py`, H2). -/
theorem form_sos (K : Matrix QQ Q ℂ) :
    6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) =
      5 * ∑ x, ∑ i, Complex.normSq (K x i)
        - (Complex.normSq (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1) + 2 * Complex.normSq (K (0, 1) 0 - K (1, 1) 1 / 2)
          + 2 * Complex.normSq (K (1, 0) 0 - K (1, 1) 1 / 2) + 3 * Complex.normSq (K (1, 1) 0)
          + 3 * Complex.normSq (K (0, 0) 1) + Complex.normSq (K (0, 1) 1 - K (1, 0) 1)) := by
  have h1 := form_six_one K
  have h2 := form_six_two K
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im] at h1 h2 ⊢
  linear_combination h1 + h2

/-- Gisin–Massar's bound in the six-state form: for every channel the mean single-clone fidelity, averaged
over the six Pauli eigenstates, is at most `5/6`. -/
theorem sixAvg_le_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    (sixAvg₁ K + sixAvg₂ K) / 2 ≤ 5 / 6 := by
  have key : ∀ i, 6 * (sixAvg₁ ![K i] + sixAvg₂ ![K i]) ≤ 5 * ∑ x, ∑ j, Complex.normSq (K i x j) := by
    intro i
    rw [form_sos]
    have e1 := Complex.normSq_nonneg (K i (0, 0) 0 - K i (0, 1) 1 - K i (1, 0) 1)
    have e2 := Complex.normSq_nonneg (K i (0, 1) 0 - K i (1, 1) 1 / 2)
    have e3 := Complex.normSq_nonneg (K i (1, 0) 0 - K i (1, 1) 1 / 2)
    have e4 := Complex.normSq_nonneg (K i (1, 1) 0)
    have e5 := Complex.normSq_nonneg (K i (0, 0) 1)
    have e6 := Complex.normSq_nonneg (K i (0, 1) 1 - K i (1, 0) 1)
    linarith
  have h : 6 * (sixAvg₁ K + sixAvg₂ K) ≤ 5 * ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) := by
    rw [st_sixAvg₁_eq_sum, st_sixAvg₂_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => key i
  rw [st_isChannel_normSq_sum K hK] at h
  linarith

/-- No channel clones every pure state with both fidelities above `5/6`: some unit vector has
`min (F₁, F₂) ≤ 5/6`. -/
theorem exists_unit_min_le_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∃ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ min (F₁ K ψ) (F₂ K ψ) ≤ 5 / 6 := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hs : ∀ s : Fin 6,
      5 / 6 < fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) ∧
        5 / 6 < fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) := by
    intro s
    have h := hcon (pauliVec s) (pauliVec_unit_internal s)
    rw [st_F₁_pauliVec, st_F₂_pauliVec] at h
    exact lt_min_iff.mp h
  have h1 : ∑ _s : Fin 6, (5 / 6 : ℝ) <
      ∑ s, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s))) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun s _ => (hs s).1
  have h2 : ∑ _s : Fin 6, (5 / 6 : ℝ) <
      ∑ s, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s))) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun s _ => (hs s).2
  have hle := sixAvg_le_internal K hK
  unfold sixAvg₁ sixAvg₂ at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h1 h2
  linarith

/-- The six-state average of either clone's fidelity is at least `1/3` for every channel (the universal-NOT
bound in average form: no channel anti-clones better than the universal NOT). -/
theorem sixAvg_ge_third_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    1 / 3 ≤ sixAvg₁ K ∧ 1 / 3 ≤ sixAvg₂ K := by
  have hsum := st_isChannel_normSq_sum K hK
  refine ⟨?_, ?_⟩
  · have h : ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) ≤ 6 * sixAvg₁ K := by
      rw [st_sixAvg₁_eq_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [form_six_one]
      have : 0 ≤ ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1) :=
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      linarith
    linarith
  · have h : ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j) ≤ 6 * sixAvg₂ K := by
      rw [st_sixAvg₂_eq_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [form_six_two]
      have : 0 ≤ ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1) :=
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      linarith
    linarith

end QubitCloning

