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

/-- The certificate's gap summed over a channel's Kraus family, in terms of the six-state averages:
`Σᵢ ((2a + b)(a + 2b) ‖Kᵢ‖² − a(a + 2b) Σⱼ |uⱼ(Kᵢ)|² − b(2a + b) Σⱼ |vⱼ(Kᵢ)|²)
  = 6(a² + 3ab + b²) − 6(a(a + 2b) F̄₁ + b(2a + b) F̄₂)`. -/
theorem af_sum_gap {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) :
    ∑ i, ((2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) =
      6 * (a ^ 2 + 3 * a * b + b ^ 2)
        - 6 * (a * (a + 2 * b) * sixAvg₁ K + b * (2 * a + b) * sixAvg₂ K) := by
  have hN := st_isChannel_normSq_sum K hK
  have hW := af_weighted_eq K hK a b
  have hS : ∑ i, ((2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) =
      (2 * a + b) * (a + 2 * b) * ∑ i, ∑ x, ∑ j, Complex.normSq (K i x j)
        - ∑ i, (a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
          + b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hS, hN]
  linear_combination hW

/-- The equality case of the asymmetric bound, operator by operator: for weights `a, b ≥ 0`, not both zero, a
channel attaining `a b = a (a + 2b)(1 − F̄₁) + b (2a + b)(1 − F̄₂)` has every square of the certificate zero for
every Kraus operator: `Kᵢ (1,1) 0 = Kᵢ (0,0) 1 = 0`, `Kᵢ (0,0) 0 = Kᵢ (1,0) 1 + Kᵢ (0,1) 1`,
`Kᵢ (1,1) 1 = Kᵢ (0,1) 0 + Kᵢ (1,0) 0`, and `(a + 2b) uⱼ = (2a + b) vⱼ` for `j = 0, 1`. -/
theorem af_equality_terms {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a + b)
    (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) (i : Fin r) :
    K i (1, 1) 0 = 0 ∧ K i (0, 0) 1 = 0 ∧ K i (0, 0) 0 = K i (1, 0) 1 + K i (0, 1) 1 ∧
      K i (1, 1) 1 = K i (0, 1) 0 + K i (1, 0) 0 ∧
      ∀ j, ((a + 2 * b : ℝ) : ℂ) * (K i (0, j) 0 + K i (1, j) 1) =
        ((2 * a + b : ℝ) : ℂ) * (K i (j, 0) 0 + K i (j, 1) 1) := by
  have hC : 0 < (2 * a + b) * (a + 2 * b) := mul_pos (by linarith) (by linarith)
  have hR : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      0 ≤ (2 * a + b) * (a + 2 * b) * ∑ x, ∑ j, Complex.normSq (K i x j)
        - a * (a + 2 * b) * ∑ j, Complex.normSq (K i (0, j) 0 + K i (1, j) 1)
        - b * (2 * a + b) * ∑ j, Complex.normSq (K i (j, 0) 0 + K i (j, 1) 1) := by
    intro i _
    rw [af_sos a b (K i)]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
    · refine mul_nonneg hC.le ?_
      have h3 : (0 : ℝ) < 3 := by norm_num
      exact add_nonneg (add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
        (div_nonneg (Complex.normSq_nonneg _) h3.le)) (div_nonneg (Complex.normSq_nonneg _) h3.le)
  have hsum := af_sum_gap K hK a b
  have hzero : 6 * (a ^ 2 + 3 * a * b + b ^ 2)
      - 6 * (a * (a + 2 * b) * sixAvg₁ K + b * (2 * a + b) * sixAvg₂ K) = 0 := by
    linear_combination (-6 : ℝ) * h
  rw [hzero, Finset.sum_eq_zero_iff_of_nonneg hR] at hsum
  have hi := hsum i (Finset.mem_univ i)
  rw [af_sos a b (K i), Fin.sum_univ_two] at hi
  have n₁ := Complex.normSq_nonneg (K i (1, 1) 0)
  have n₂ := Complex.normSq_nonneg (K i (0, 0) 1)
  have n₃ := Complex.normSq_nonneg (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1)
  have n₄ := Complex.normSq_nonneg (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0)
  have w₀ := Complex.normSq_nonneg (((a + 2 * b : ℝ) : ℂ) * (K i (0, 0) 0 + K i (1, 0) 1)
    - ((2 * a + b : ℝ) : ℂ) * (K i (0, 0) 0 + K i (0, 1) 1))
  have w₁ := Complex.normSq_nonneg (((a + 2 * b : ℝ) : ℂ) * (K i (0, 1) 0 + K i (1, 1) 1)
    - ((2 * a + b : ℝ) : ℂ) * (K i (1, 0) 0 + K i (1, 1) 1))
  have hQ : 0 ≤ (2 * a + b) * (a + 2 * b) * (Complex.normSq (K i (1, 1) 0) + Complex.normSq (K i (0, 0) 1)
      + Complex.normSq (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1) / 3
      + Complex.normSq (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0) / 3) :=
    mul_nonneg hC.le (by positivity)
  have hW0 : Complex.normSq (((a + 2 * b : ℝ) : ℂ) * (K i (0, 0) 0 + K i (1, 0) 1)
      - ((2 * a + b : ℝ) : ℂ) * (K i (0, 0) 0 + K i (0, 1) 1)) = 0 := by linarith
  have hW1 : Complex.normSq (((a + 2 * b : ℝ) : ℂ) * (K i (0, 1) 0 + K i (1, 1) 1)
      - ((2 * a + b : ℝ) : ℂ) * (K i (1, 0) 0 + K i (1, 1) 1)) = 0 := by linarith
  have hQ0 : (2 * a + b) * (a + 2 * b) * (Complex.normSq (K i (1, 1) 0) + Complex.normSq (K i (0, 0) 1)
      + Complex.normSq (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1) / 3
      + Complex.normSq (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0) / 3) = 0 := by linarith
  have hP := (mul_eq_zero.1 hQ0).resolve_left hC.ne'
  have z₁ : Complex.normSq (K i (1, 1) 0) = 0 := by linarith
  have z₂ : Complex.normSq (K i (0, 0) 1) = 0 := by linarith
  have z₃ : Complex.normSq (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1) = 0 := by linarith
  have z₄ : Complex.normSq (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0) = 0 := by linarith
  rw [Complex.normSq_eq_zero] at z₁ z₂ z₃ z₄ hW0 hW1
  refine ⟨z₁, z₂, by linear_combination z₃, by linear_combination z₄, ?_⟩
  rw [Fin.forall_fin_two]
  exact ⟨by linear_combination hW0, by linear_combination hW1⟩

/-- The span of the asymmetric cloner's operators: a Kraus operator satisfying the five equality conditions of
`af_equality_terms` (with `a ≠ 0`) is `x • asymA₀ a b + y • asymA₁ a b` with `x = K (1,0) 1 / a`,
`y = K (0,1) 0 / a`. -/
theorem af_eq_span (a b : ℝ) (ha : a ≠ 0) (K : Matrix QQ Q ℂ) (h₁ : K (1, 1) 0 = 0) (h₂ : K (0, 0) 1 = 0)
    (h₃ : K (0, 0) 0 = K (1, 0) 1 + K (0, 1) 1) (h₄ : K (1, 1) 1 = K (0, 1) 0 + K (1, 0) 0)
    (h₅ : ∀ j, ((a + 2 * b : ℝ) : ℂ) * (K (0, j) 0 + K (1, j) 1) =
      ((2 * a + b : ℝ) : ℂ) * (K (j, 0) 0 + K (j, 1) 1)) :
    K = (K (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K (0, 1) 0 / (a : ℂ)) • asymA₁ a b := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have e₀ := h₅ 0
  have e₁ := h₅ 1
  push_cast at e₀ e₁
  rw [h₃] at e₀
  rw [h₄] at e₁
  have hq : (a : ℂ) * K (0, 1) 1 = b * K (1, 0) 1 := by linear_combination (-1 / 3 : ℂ) * e₀
  have ht : (a : ℂ) * K (1, 0) 0 = b * K (0, 1) 0 := by linear_combination (-1 / 3 : ℂ) * e₁
  have hq' : K (0, 1) 1 = b * K (1, 0) 1 / a := by
    rw [eq_div_iff ha']
    linear_combination hq
  have ht' : K (1, 0) 0 = b * K (0, 1) 0 / a := by
    rw [eq_div_iff ha']
    linear_combination ht
  have key : ∀ x₁ x₂ i, K (x₁, x₂) i =
      ((K (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K (0, 1) 0 / (a : ℂ)) • asymA₁ a b) (x₁, x₂) i := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> simp [asymA₀, asymA₁]
    all_goals try simp only [h₁, h₂, h₃, h₄, hq', ht']
    all_goals try field_simp
  ext ⟨x₁, x₂⟩ i
  exact key x₁ x₂ i

/-- The equality case in span form: for `a > 0`, `b ≥ 0`, a channel attaining the asymmetric bound has every
Kraus operator in the span of the cloner's operators, `Kᵢ = xᵢ • asymA₀ a b + yᵢ • asymA₁ a b`. -/
theorem af_span_of_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 ≤ b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K))
    (i : Fin r) :
    K i = (K i (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K i (0, 1) 0 / (a : ℂ)) • asymA₁ a b := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := af_equality_terms K hK a b ha.le hb (by linarith) h i
  exact af_eq_span a b ha.ne' (K i) h₁ h₂ h₃ h₄ h₅

/-- The sandwich of a two-term operator: `(x A + y B) ρ (x A + y B)ᴴ` expanded. -/
theorem af_sandwich (x y : ℂ) (A B : Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) :
    (x • A + y • B) * ρ * (x • A + y • B)ᴴ =
      (x * star x) • (A * ρ * Aᴴ) + (x * star y) • (A * ρ * Bᴴ) + (y * star x) • (B * ρ * Aᴴ)
        + (y * star y) • (B * ρ * Bᴴ) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  rw [mul_comm (star x) x, mul_comm (star x) y, mul_comm (star y) x, mul_comm (star y) y]
  abel

/-- The Gram entries of `M = x • asymA₀ a b + y • asymA₁ a b`: `MᴴM = |x|² diag((a + b)², a² + b²)
+ |y|² diag(a² + b², (a + b)²) + 2ab (x ȳ E₀₁ + y x̄ E₁₀)`. -/
theorem af_gram (a b : ℝ) (x y : ℂ) :
    ((x • asymA₀ a b + y • asymA₁ a b)ᴴ * (x • asymA₀ a b + y • asymA₁ a b)) 0 0 =
        x * star x * ((a : ℂ) + b) ^ 2 + y * star y * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ∧
      ((x • asymA₀ a b + y • asymA₁ a b)ᴴ * (x • asymA₀ a b + y • asymA₁ a b)) 1 1 =
        x * star x * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) + y * star y * ((a : ℂ) + b) ^ 2 ∧
      ((x • asymA₀ a b + y • asymA₁ a b)ᴴ * (x • asymA₀ a b + y • asymA₁ a b)) 0 1 =
        x * star y * (2 * a * b) ∧
      ((x • asymA₀ a b + y • asymA₁ a b)ᴴ * (x • asymA₀ a b + y • asymA₁ a b)) 1 0 =
        y * star x * (2 * a * b) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, asymA₀, asymA₁,
      Matrix.conjTranspose_apply]
    ring

/-- Uniqueness of the asymmetric optimum (the statement of `eq_asym_of_equality_internal`, proved here from
`af_span_of_equality`, `af_gram` and `af_sandwich`): for `a, b > 0`, a channel with equality in the bound at
the weights `(a, b)` is the asymmetric cloner `Λ_{a,b}` as a map. -/
theorem af_eq_asym_of_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  intro ρ
  obtain ⟨x, y, hspan⟩ : ∃ x y : Fin r → ℂ, ∀ i, K i = x i • asymA₀ a b + y i • asymA₁ a b :=
    ⟨fun i => K i (1, 0) 1 / (a : ℂ), fun i => K i (0, 1) 0 / (a : ℂ),
      fun i => af_span_of_equality K hK a b ha hb.le h i⟩
  have hentry : ∀ j k : Q, ∑ i, ((x i • asymA₀ a b + y i • asymA₁ a b)ᴴ
      * (x i • asymA₀ a b + y i • asymA₁ a b)) j k = (1 : Matrix Q Q ℂ) j k := by
    intro j k
    have hK' : ∑ i, (K i)ᴴ * K i = 1 := hK
    rw [← hK', Matrix.sum_apply]
    simp only [hspan]
  have e₀₀ := hentry 0 0
  have e₁₁ := hentry 1 1
  have e₀₁ := hentry 0 1
  have e₁₀ := hentry 1 0
  rw [Finset.sum_congr rfl (fun i _ => (af_gram a b (x i) (y i)).1), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, Matrix.one_apply_eq] at e₀₀
  rw [Finset.sum_congr rfl (fun i _ => (af_gram a b (x i) (y i)).2.1), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, Matrix.one_apply_eq] at e₁₁
  rw [Finset.sum_congr rfl (fun i _ => (af_gram a b (x i) (y i)).2.2.1), ← Finset.sum_mul,
    Matrix.one_apply_ne (by decide)] at e₀₁
  rw [Finset.sum_congr rfl (fun i _ => (af_gram a b (x i) (y i)).2.2.2), ← Finset.sum_mul,
    Matrix.one_apply_ne (by decide)] at e₁₀
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hab : (2 * a * b : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ha') hb'
  have hZ : ∑ i, x i * star (y i) = 0 := (mul_eq_zero.1 e₀₁).resolve_right hab
  have hZ' : ∑ i, y i * star (x i) = 0 := (mul_eq_zero.1 e₁₀).resolve_right hab
  have hXY : ∑ i, x i * star (x i) = ∑ i, y i * star (y i) := by
    have h2 : (∑ i, x i * star (x i) - ∑ i, y i * star (y i)) * (2 * a * b) = 0 := by
      linear_combination e₀₀ - e₁₁
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hab)
  have hX : ∑ i, x i * star (x i) = (2 * ((a : ℂ) ^ 2 + a * b + b ^ 2))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hXY] at e₀₀
    linear_combination e₀₀
  have hY : ∑ i, y i * star (y i) = (2 * ((a : ℂ) ^ 2 + a * b + b ^ 2))⁻¹ := hXY ▸ hX
  have hk : krausApply K ρ = ∑ i, ((x i * star (x i)) • (asymA₀ a b * ρ * (asymA₀ a b)ᴴ)
      + (x i * star (y i)) • (asymA₀ a b * ρ * (asymA₁ a b)ᴴ)
      + (y i * star (x i)) • (asymA₁ a b * ρ * (asymA₀ a b)ᴴ)
      + (y i * star (y i)) • (asymA₁ a b * ρ * (asymA₁ a b)ᴴ)) := by
    unfold krausApply
    exact Finset.sum_congr rfl (fun i _ => by rw [hspan i, af_sandwich])
  rw [hk, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul,
    ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul, hX, hY, hZ, hZ', zero_smul, zero_smul,
    add_zero, add_zero, ← smul_add]
  unfold asymChannel
  push_cast
  rfl

/-- The one-variable step of `af_of_bounds`: if `0 < D < 1/2`, some `t > 0` has `(2 + t) D < 1`. -/
theorem af_exists_lt (D : ℝ) (hD : 0 < D) (hlt : D < 1 / 2) : ∃ t : ℝ, 0 < t ∧ (2 + t) * D < 1 := by
  refine ⟨(1 - 2 * D) / (2 * D), div_pos (by linarith) (by linarith), ?_⟩
  have h2 : (2 + (1 - 2 * D) / (2 * D)) * D = D + 1 / 2 := by
    field_simp
    ring
  linarith

/-- The real lemma behind the square-root form (the statement of `tr_of_bounds`): if
`a b ≤ a (a + 2b) D₁ + b (2a + b) D₂` for all `a, b ≥ 0`, then `D₁, D₂ ≥ 0` and
`1/2 ≤ D₁ + D₂ + √(D₁ D₂)`. -/
theorem af_of_bounds (D₁ D₂ : ℝ)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ a * (a + 2 * b) * D₁ + b * (2 * a + b) * D₂) :
    0 ≤ D₁ ∧ 0 ≤ D₂ ∧ 1 / 2 ≤ D₁ + D₂ + Real.sqrt (D₁ * D₂) := by
  have h₁ : 0 ≤ D₁ := by
    have := h 1 0 zero_le_one le_rfl
    linarith
  have h₂ : 0 ≤ D₂ := by
    have := h 0 1 le_rfl zero_le_one
    linarith
  refine ⟨h₁, h₂, not_lt.1 fun hlt => ?_⟩
  have hg := Real.sqrt_nonneg (D₁ * D₂)
  rcases h₁.eq_or_lt with e₁ | p₁
  · -- `D₁ = 0`: then `t ≤ t (2 + t) D₂` for every `t > 0`
    rcases h₂.eq_or_lt with e₂ | p₂
    · have := h 1 1 zero_le_one zero_le_one
      rw [← e₁, ← e₂] at this
      linarith
    · obtain ⟨t, ht, htD⟩ := af_exists_lt D₂ p₂ (by linarith)
      have := h 1 t zero_le_one ht.le
      rw [← e₁] at this
      nlinarith
  · rcases h₂.eq_or_lt with e₂ | p₂
    · -- `D₂ = 0`: then `t ≤ t (t + 2) D₁` for every `t > 0`
      obtain ⟨t, ht, htD⟩ := af_exists_lt D₁ p₁ (by linarith)
      have := h t 1 ht.le zero_le_one
      rw [← e₂] at this
      nlinarith
    · -- both positive: `a = √D₂`, `b = √D₁`
      have s₁ := Real.sqrt_nonneg D₁
      have s₂ := Real.sqrt_nonneg D₂
      have q₁ : Real.sqrt D₁ * Real.sqrt D₁ = D₁ := Real.mul_self_sqrt h₁
      have q₂ : Real.sqrt D₂ * Real.sqrt D₂ = D₂ := Real.mul_self_sqrt h₂
      have eg : Real.sqrt D₂ * Real.sqrt D₁ = Real.sqrt (D₁ * D₂) := by
        rw [Real.sqrt_mul h₁, mul_comm]
      have gsq : Real.sqrt (D₁ * D₂) * Real.sqrt (D₁ * D₂) = D₁ * D₂ :=
        Real.mul_self_sqrt (mul_nonneg h₁ h₂)
      have gpos : 0 < Real.sqrt (D₁ * D₂) := Real.sqrt_pos.2 (mul_pos p₁ p₂)
      have hab := h (Real.sqrt D₂) (Real.sqrt D₁) s₂ s₁
      have expand : Real.sqrt D₂ * (Real.sqrt D₂ + 2 * Real.sqrt D₁) * D₁
          + Real.sqrt D₁ * (2 * Real.sqrt D₂ + Real.sqrt D₁) * D₂ =
          2 * (D₁ * D₂) + 2 * (Real.sqrt D₂ * Real.sqrt D₁) * (D₁ + D₂) := by
        linear_combination D₁ * q₂ + D₂ * q₁
      rw [expand, eg] at hab
      have hm := mul_lt_mul_of_pos_left hlt gpos
      nlinarith

/-- The trade-off in the square-root form (the statement of `tradeoff_sqrt_internal`):
`F̄₁ + F̄₂ − 3/2 ≤ √((1 − F̄₁)(1 − F̄₂))` for every channel. -/
theorem af_tradeoff_sqrt {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 ≤ Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := by
  obtain ⟨-, -, h⟩ := af_of_bounds (1 - sixAvg₁ K) (1 - sixAvg₂ K)
    (fun a b ha hb => asym_bound_internal K hK a b ha hb)
  linarith

/-- The trade-off for worst-case fidelities (the statement of `tradeoff_forall_internal`). -/
theorem af_tradeoff_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (f₁ f₂ : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    f₁ + f₂ - 3 / 2 ≤ Real.sqrt ((1 - f₁) * (1 - f₂)) := by
  obtain ⟨-, -, h'⟩ := af_of_bounds (1 - f₁) (1 - f₂)
    (fun a b ha hb => asym_bound_forall_internal K hK a b ha hb f₁ f₂ h)
  linarith

end QubitCloning
