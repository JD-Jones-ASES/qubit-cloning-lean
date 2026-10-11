module

public import QubitCloning.Signed
public import QubitCloning.FullTradeoff

/-!
# The equality cases of the full-range trade-off

Along the asymmetric family with `(2a + b)(a + 2b) ≥ 0` the full-range trade-off
`3(F̄₁ + F̄₂) − 7/2 ≤ √((3F̄₁ − 1)(3F̄₂ − 1))` is an equality. Conversely, equality away from the
perfect-clone endpoints forces a member of the family: with `U = Σ|u|²`, `V = Σ|v|²`, `C = Σ Re(ū v)`
equality gives `C = √(UV)` and `U + V − C = 3`, so the summed Gram identity makes every square vanish,
and `Σ |√V u − √U v|² = 2UV − 2√(UV) C = 0` puts the Kraus operators in the kernel of the
asymmetric certificate at `a = (2√U − √V)/3`, `b = (2√V − √U)/3`. The floor companions
`(5/6, 1/3)` and `(1/3, 5/6)` are `Λ_{2,−1}` and `Λ_{−1,2}`, and a perfect clone on average forces the
other output's average fidelity to be `1/2`. Every public theorem is the `_internal` twin of a Challenge
statement (header verbatim) or a helper prefixed `fe_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The first six-state average in the contraction `u`: `6 F̄₁ = 2 + Σᵢⱼ |uⱼ(Kᵢ)|²`. -/
theorem fe_six₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    6 * sixAvg₁ K = 2 + ∑ i, ∑ j, Complex.normSq (fr_u (K i) j) := by
  simpa only [fr_u, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add,
    one_add_one_eq_two] using af_weighted_eq K hK 1 0

/-- The second six-state average in the contraction `v`: `6 F̄₂ = 2 + Σᵢⱼ |vⱼ(Kᵢ)|²`. -/
theorem fe_six₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    6 * sixAvg₂ K = 2 + ∑ i, ∑ j, Complex.normSq (fr_v (K i) j) := by
  simpa only [fr_v, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add,
    one_add_one_eq_two] using af_weighted_eq K hK 0 1

/-- Cauchy–Schwarz for the two contractions over the index `(i, j)`. -/
theorem fe_cauchy {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) :
    ∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re ≤
      Real.sqrt ((∑ i, ∑ j, Complex.normSq (fr_u (K i) j)) *
        (∑ i, ∑ j, Complex.normSq (fr_v (K i) j))) := by
  simpa only [Fintype.sum_prod_type] using
    fr_cauchy (fun p : Fin r × Q => fr_u (K p.1) p.2) (fun p : Fin r × Q => fr_v (K p.1) p.2)

/-- The Gram expression of one Kraus operator is nonnegative (it is four squares). -/
theorem fe_gram_nonneg (K : Matrix QQ Q ℂ) :
    0 ≤ 3 * (∑ x, ∑ i, Complex.normSq (K x i)) - 2 * (∑ j, Complex.normSq (fr_u K j))
      - 2 * (∑ j, Complex.normSq (fr_v K j)) + 2 * (∑ j, (star (fr_u K j) * fr_v K j).re) := by
  rw [fr_gram_identity]
  have h₁ := Complex.normSq_nonneg (K (1, 1) 0)
  have h₂ := Complex.normSq_nonneg (K (0, 0) 1)
  have h₃ := Complex.normSq_nonneg (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1)
  have h₄ := Complex.normSq_nonneg (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0)
  linarith

/-- The summed Gram identity: `Σᵢ (3‖Kᵢ‖² − 2Σ|u|² − 2Σ|v|² + 2Σ Re ūv) = 6 − 2U − 2V + 2C`. -/
theorem fe_gram_sum {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∑ i, (3 * (∑ x, ∑ j, Complex.normSq (K i x j)) - 2 * (∑ j, Complex.normSq (fr_u (K i) j))
        - 2 * (∑ j, Complex.normSq (fr_v (K i) j)) + 2 * (∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re)) =
      6 - 2 * (∑ i, ∑ j, Complex.normSq (fr_u (K i) j)) - 2 * (∑ i, ∑ j, Complex.normSq (fr_v (K i) j))
        + 2 * (∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re) := by
  have hs := st_isChannel_normSq_sum K hK
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- When `6 − 2U − 2V + 2C = 0`, every square of the Gram identity vanishes for every Kraus operator. -/
theorem fe_squares {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 6 - 2 * (∑ i, ∑ j, Complex.normSq (fr_u (K i) j)) - 2 * (∑ i, ∑ j, Complex.normSq (fr_v (K i) j))
        + 2 * (∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re) = 0) (i : Fin r) :
    K i (1, 1) 0 = 0 ∧ K i (0, 0) 1 = 0 ∧ K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1 = 0 ∧
      K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0 = 0 := by
  rw [← fe_gram_sum K hK] at h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => fe_gram_nonneg (K i))).mp h i
    (Finset.mem_univ i)
  rw [fr_gram_identity] at hi
  have n1 := Complex.normSq_nonneg (K i (1, 1) 0)
  have n2 := Complex.normSq_nonneg (K i (0, 0) 1)
  have n3 := Complex.normSq_nonneg (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1)
  have n4 := Complex.normSq_nonneg (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact Complex.normSq_eq_zero.mp (by linarith)

/-- A double sum of squared moduli vanishes only when every term vanishes. -/
theorem fe_eq_zero_of_sum {r : ℕ} (w : Fin r → Q → ℂ)
    (h : ∑ i, ∑ j, Complex.normSq (w i j) = 0) (i : Fin r) (j : Q) : w i j = 0 := by
  have h1 : ∑ j, Complex.normSq (w i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (f := fun i => ∑ j, Complex.normSq (w i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (w i j))).mp h i (Finset.mem_univ i)
  have h2 : Complex.normSq (w i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (f := fun j => Complex.normSq (w i j))
      (fun j _ => Complex.normSq_nonneg (w i j))).mp h1 j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp h2

/-- `|α u − β v|² = α²|u|² + β²|v|² − 2αβ Re(ū v)` for real `α, β`. -/
theorem fe_normSq_comb (α β : ℝ) (u v : ℂ) :
    Complex.normSq ((α : ℂ) * u - (β : ℂ) * v) =
      α ^ 2 * Complex.normSq u + β ^ 2 * Complex.normSq v - 2 * α * β * (star u * v).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The summed form: `Σ |α u − β v|² = α² U + β² V − 2αβ C`. -/
theorem fe_sum_comb {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (α β : ℝ) :
    ∑ i, ∑ j, Complex.normSq ((α : ℂ) * fr_u (K i) j - (β : ℂ) * fr_v (K i) j) =
      α ^ 2 * (∑ i, ∑ j, Complex.normSq (fr_u (K i) j)) + β ^ 2 * (∑ i, ∑ j, Complex.normSq (fr_v (K i) j))
        - 2 * α * β * (∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re) := by
  simp only [fe_normSq_comb, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The kernel of the asymmetric certificate at `(a, b)`, `a, b ≠ 0`: if every Gram square vanishes and
`(a + 2b) u = (2a + b) v` entrywise, the channel is `Λ_{a,b}` as a map. -/
theorem fe_channel_of_kernel {r : ℕ} (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K)
    (hg : 6 - 2 * (∑ i, ∑ j, Complex.normSq (fr_u (K i) j)) - 2 * (∑ i, ∑ j, Complex.normSq (fr_v (K i) j))
        + 2 * (∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re) = 0)
    (huv : ∀ i j, ((a + 2 * b : ℝ) : ℂ) * fr_u (K i) j - ((2 * a + b : ℝ) : ℂ) * fr_v (K i) j = 0) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  have hdec : ∀ i, K i = (K i (1, 0) 1 / (a : ℂ)) • asymA₀ a b + (K i (0, 1) 0 / (a : ℂ)) • asymA₁ a b := by
    intro i
    obtain ⟨c1, c2, c3, c4⟩ := fe_squares K hK hg i
    exact au_kraus_eq a b ha (K i) c1 c2 c3 c4 (huv i 0) (huv i 1)
  exact au_eq_asym_of_span a b ha hb K hK _ _ hdec

/-- Along the asymmetric family with `(2a + b)(a + 2b) ≥ 0` the full-range trade-off is an equality: both
sides equal `(2a + b)(a + 2b)/(2(a² + ab + b²))`. -/
theorem tradeoff_full_attained_internal {r : ℕ} (a b : ℝ) (hP : 0 ≤ (2 * a + b) * (a + 2 * b))
    (hs : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 =
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)) := by
  have hpos := as_pos a b hs
  have h2 : 0 < 2 * (a ^ 2 + a * b + b ^ 2) := by linarith
  rw [as_sixAvg₁ a b hs K hK, as_sixAvg₂ a b hs K hK]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, (2 * (a ^ 2 + a * b + b ^ 2))⁻¹ = T := ⟨_, rfl⟩
  have hST : 2 * (a ^ 2 + a * b + b ^ 2) * T = 1 := by rw [← hT]; exact mul_inv_cancel₀ h2.ne'
  have hL : 3 * (1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) + (1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2))))
      - 7 / 2 = (2 * a + b) * (a + 2 * b) / (2 * (a ^ 2 + a * b + b ^ 2)) := by
    simp only [div_eq_mul_inv, hT]
    linear_combination (-5 / 2 : ℝ) * hST
  have hR : (3 * (1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2))) - 1) *
      (3 * (1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2))) - 1) =
      ((2 * a + b) * (a + 2 * b) / (2 * (a ^ 2 + a * b + b ^ 2))) ^ 2 := by
    simp only [div_eq_mul_inv, hT]
    linear_combination (-(4 + 4 * (2 * (a ^ 2 + a * b + b ^ 2)) * T - 6 * (a ^ 2 + b ^ 2) * T)) * hST
  rw [hL, hR, Real.sqrt_sq (div_nonneg hP h2.le)]

/-- The companion of the universal-NOT floor on the second clone is unique: `F̄₁ = 5/6` and `F̄₂ = 1/3`
force `Λ_{2,−1}` as a map. -/
theorem eq_asym_of_floor₂_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h₁ : sixAvg₁ K = 5 / 6) (h₂ : sixAvg₂ K = 1 / 3) :
    ∀ ρ, krausApply K ρ = asymChannel 2 (-1) ρ := by
  have e1 := fe_six₁ K hK
  have e2 := fe_six₂ K hK
  have hV : ∑ i, ∑ j, Complex.normSq (fr_v (K i) j) = 0 := by linarith
  have hv : ∀ i j, fr_v (K i) j = 0 := fe_eq_zero_of_sum (fun i j => fr_v (K i) j) hV
  have hC : ∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re = 0 := by simp [hv]
  apply fe_channel_of_kernel 2 (-1) (by norm_num) (by norm_num) K hK
  · linarith
  · intro i j
    rw [hv i j]
    push_cast
    ring

/-- The companion of the universal-NOT floor on the first clone is unique: `F̄₁ = 1/3` and `F̄₂ = 5/6`
force `Λ_{−1,2}` as a map. -/
theorem eq_asym_of_floor₁_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h₁ : sixAvg₁ K = 1 / 3) (h₂ : sixAvg₂ K = 5 / 6) :
    ∀ ρ, krausApply K ρ = asymChannel (-1) 2 ρ := by
  have e1 := fe_six₁ K hK
  have e2 := fe_six₂ K hK
  have hU : ∑ i, ∑ j, Complex.normSq (fr_u (K i) j) = 0 := by linarith
  have hu : ∀ i j, fr_u (K i) j = 0 := fe_eq_zero_of_sum (fun i j => fr_u (K i) j) hU
  have hC : ∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re = 0 := by simp [hu]
  apply fe_channel_of_kernel (-1) 2 (by norm_num) (by norm_num) K hK
  · linarith
  · intro i j
    rw [hu i j]
    push_cast
    ring

/-- Equality in the full-range trade-off away from the perfect-clone endpoints forces a member of the
asymmetric family with both weights nonzero and `(2a + b)(a + 2b) ≥ 0`: the boundary arc of the region
is the family. -/
theorem eq_asym_of_tradeoff_full_equality_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 =
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)))
    (h₁ : sixAvg₁ K ≠ 1) (h₂ : sixAvg₂ K ≠ 1) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ 0 ≤ (2 * a + b) * (a + 2 * b) ∧
      ∀ ρ, krausApply K ρ = asymChannel a b ρ := by
  have e1 := fe_six₁ K hK
  have e2 := fe_six₂ K hK
  have hc := fe_cauchy K
  have hg := fe_gram_sum K hK
  have hgn : 0 ≤ ∑ i, (3 * (∑ x, ∑ j, Complex.normSq (K i x j)) - 2 * (∑ j, Complex.normSq (fr_u (K i) j))
        - 2 * (∑ j, Complex.normSq (fr_v (K i) j)) + 2 * (∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re)) :=
    Finset.sum_nonneg fun i _ => fe_gram_nonneg (K i)
  rw [hg] at hgn
  have hw := fe_sum_comb K
  have hU0 : 0 ≤ ∑ i, ∑ j, Complex.normSq (fr_u (K i) j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hV0 : 0 ≤ ∑ i, ∑ j, Complex.normSq (fr_v (K i) j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hkey := fe_channel_of_kernel (r := r) (K := K) (hK := hK)
  obtain ⟨U, hUd⟩ : ∃ U : ℝ, ∑ i, ∑ j, Complex.normSq (fr_u (K i) j) = U := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℝ, ∑ i, ∑ j, Complex.normSq (fr_v (K i) j) = V := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, ∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re = C := ⟨_, rfl⟩
  rw [hUd] at e1 hU0
  rw [hVd] at e2 hV0
  rw [hUd, hVd, hCd] at hc hgn hkey
  obtain ⟨su, hsud⟩ : ∃ s : ℝ, Real.sqrt U = s := ⟨_, rfl⟩
  obtain ⟨sv, hsvd⟩ : ∃ s : ℝ, Real.sqrt V = s := ⟨_, rfl⟩
  have hsu0 : 0 ≤ su := hsud ▸ Real.sqrt_nonneg U
  have hsv0 : 0 ≤ sv := hsvd ▸ Real.sqrt_nonneg V
  have hsu : su ^ 2 = U := hsud ▸ Real.sq_sqrt hU0
  have hsv : sv ^ 2 = V := hsvd ▸ Real.sq_sqrt hV0
  have hUV : Real.sqrt (U * V) = su * sv := by rw [Real.sqrt_mul hU0, hsud, hsvd]
  rw [hUV] at hc
  have hF1 : sixAvg₁ K = (2 + su ^ 2) / 6 := by rw [hsu]; linarith
  have hF2 : sixAvg₂ K = (2 + sv ^ 2) / 6 := by rw [hsv]; linarith
  rw [hF1, hF2] at h
  rw [show (3 * ((2 + su ^ 2) / 6) - 1) * (3 * ((2 + sv ^ 2) / 6) - 1) = (su * sv / 2) ^ 2 by ring,
    Real.sqrt_sq (div_nonneg (mul_nonneg hsu0 hsv0) (by norm_num))] at h
  -- equality: `C = √(UV)` and `U + V − C = 3`
  have hC : C = su * sv := by linarith
  have hg0 : 6 - 2 * U - 2 * V + 2 * C = 0 := by linarith
  -- `Σ |√V u − √U v|² = 2UV − 2√(UV) C = 0`
  have hw0 : ∑ i, ∑ j, Complex.normSq ((sv : ℂ) * fr_u (K i) j - (su : ℂ) * fr_v (K i) j) = 0 := by
    rw [hw sv su, hUd, hVd, hCd, hC, ← hsu, ← hsv]
    ring
  have hv0 : ∀ i j, (sv : ℂ) * fr_u (K i) j - (su : ℂ) * fr_v (K i) j = 0 :=
    fe_eq_zero_of_sum (fun i j => (sv : ℂ) * fr_u (K i) j - (su : ℂ) * fr_v (K i) j) hw0
  -- the weights `a = (2√U − √V)/3`, `b = (2√V − √U)/3`
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = (2 * su - sv) / 3 := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = (2 * sv - su) / 3 := ⟨_, rfl⟩
  have hab1 : a + 2 * b = sv := by rw [had, hbd]; ring
  have hab2 : 2 * a + b = su := by rw [had, hbd]; ring
  have ha : a ≠ 0 := by
    intro ha0
    have e : sv = 2 * su := by rw [had] at ha0; linarith
    apply h₂
    rw [hF2, e]
    rw [e] at h
    linarith
  have hb : b ≠ 0 := by
    intro hb0
    have e : su = 2 * sv := by rw [hbd] at hb0; linarith
    apply h₁
    rw [hF1, e]
    rw [e] at h
    linarith
  refine ⟨a, b, ha, hb, by rw [hab2, hab1]; exact mul_nonneg hsu0 hsv0, ?_⟩
  apply hkey a b ha hb hg0
  intro i j
  rw [hab1, hab2]
  exact hv0 i j

/-- A perfect first clone on average forces the second output's average fidelity to be `1/2`. -/
theorem sixAvg₂_eq_half_of_sixAvg₁_eq_one_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₁ K = 1) : sixAvg₂ K = 1 / 2 := by
  have ht := tradeoff_full_sqrt_internal K hK
  have hf := (sixAvg_ge_third_internal K hK).2
  rw [h] at ht
  have hy : 0 ≤ (3 * 1 - 1) * (3 * sixAvg₂ K - 1) := by nlinarith
  have hL : 0 ≤ 3 * (1 + sixAvg₂ K) - 7 / 2 := by linarith
  have hsq := mul_self_le_mul_self hL ht
  rw [Real.mul_self_sqrt hy] at hsq
  have h0 : (sixAvg₂ K - 1 / 2) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  have h1 := (pow_eq_zero_iff two_ne_zero).mp h0
  linarith

/-- A perfect second clone on average forces the first output's average fidelity to be `1/2`. -/
theorem sixAvg₁_eq_half_of_sixAvg₂_eq_one_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₂ K = 1) : sixAvg₁ K = 1 / 2 := by
  have ht := tradeoff_full_sqrt_internal K hK
  have hf := (sixAvg_ge_third_internal K hK).1
  rw [h] at ht
  have hy : 0 ≤ (3 * sixAvg₁ K - 1) * (3 * 1 - 1) := by nlinarith
  have hL : 0 ≤ 3 * (sixAvg₁ K + 1) - 7 / 2 := by linarith
  have hsq := mul_self_le_mul_self hL ht
  rw [Real.mul_self_sqrt hy] at hsq
  have h0 : (sixAvg₁ K - 1 / 2) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  have h1 := (pow_eq_zero_iff two_ne_zero).mp h0
  linarith

end QubitCloning
