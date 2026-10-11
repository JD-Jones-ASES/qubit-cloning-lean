module

public import QubitCloning.Form

/-!
# Stability

The symmetric certificate is twice the squared distance to `span{V₁, V₂}` plus four squares, so a channel with `(F̄₁ + F̄₂)/2 ≥ 5/6 − ε` has Kraus operators within total squared distance `6ε` of that span. Every public theorem is the `_internal` twin of a Challenge statement (header verbatim) or a helper prefixed `sb_`.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The coefficient of `bhV₁` in the Hilbert–Schmidt projection. -/
def sb_x (K : Matrix QQ Q ℂ) : ℂ :=
  (2 * K (0, 0) 0 + K (0, 1) 1 + K (1, 0) 1) / 6

/-- The coefficient of `bhV₂` in the Hilbert–Schmidt projection. -/
def sb_y (K : Matrix QQ Q ℂ) : ℂ :=
  (K (0, 1) 0 + K (1, 0) 0 + 2 * K (1, 1) 1) / 3

/-- Hilbert–Schmidt projection onto the optimal two-dimensional Kraus space. -/
def sb_project (K : Matrix QQ Q ℂ) : Matrix QQ Q ℂ :=
  sb_x K • bhV₁ + sb_y K • bhV₂

/-- Squared Hilbert–Schmidt distance to the projected Kraus operator. -/
def sb_distanceSq (K : Matrix QQ Q ℂ) : ℝ :=
  ∑ x, ∑ i, Complex.normSq (K x i - sb_project K x i)

/-- Orthogonal projection minimizes the squared distance. The factors `6` and
`3/2` are the squared Hilbert–Schmidt norms of `bhV₁` and `bhV₂`. -/
theorem sb_projection_distance (K : Matrix QQ Q ℂ) (x y : ℂ) :
    ∑ z, ∑ i, Complex.normSq (K z i - (x • bhV₁ + y • bhV₂) z i) =
      sb_distanceSq K + 6 * Complex.normSq (x - sb_x K) +
        (3 / 2) * Complex.normSq (y - sb_y K) := by
  simp only [bhV₁, Fin.isValue, smul_of, bhV₂, one_div, Matrix.add_apply, of_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
    Fin.sum_univ_two, and_true, zero_ne_one, and_false, ↓reduceIte, one_ne_zero, Fintype.sum_prod_type, Prod.mk.injEq,
    false_or, Complex.zero_re, add_zero, Complex.zero_im, or_false, zero_add, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, sub_zero, Complex.mul_im, Complex.inv_re, div_self_mul_self',
    Complex.inv_im, neg_zero, zero_div, sb_distanceSq, sb_project, sb_x, sb_y, Complex.div_ofNat_re, zero_mul,
    Complex.div_ofNat_im]
  ring

/-- The symmetric certificate is twice the squared distance to `span{V₁, V₂}` plus four squares. -/
theorem sb_coercivity_identity (K : Matrix QQ Q ℂ) :
    5 * ∑ x, ∑ i, Complex.normSq (K x i) -
        6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) =
      2 * sb_distanceSq K + Complex.normSq (K (1, 1) 0) +
        Complex.normSq (K (0, 0) 1) +
        Complex.normSq (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1) / 3 +
        Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) / 3 := by
  rw [form_sos]
  simp only [Complex.normSq_apply, Fin.sum_univ_two, Fin.isValue, Fintype.sum_prod_type, Complex.sub_re,
    Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, sub_sub_cancel, sb_distanceSq, sb_project, sb_x, bhV₁,
    smul_of, sb_y, bhV₂, one_div, Matrix.add_apply, of_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Complex.add_re, Complex.add_im, and_true, zero_ne_one, and_false, ↓reduceIte, one_ne_zero, Prod.mk.injEq, false_or,
    Complex.zero_re, add_zero, Complex.zero_im, or_false, zero_add, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, Complex.mul_im, Complex.inv_re, div_self_mul_self', Complex.inv_im,
    neg_zero, zero_div]
  ring

/-- The symmetric certificate dominates twice squared distance to its kernel. -/
theorem sb_coercivity (K : Matrix QQ Q ℂ) :
    2 * sb_distanceSq K ≤
      5 * ∑ x, ∑ i, Complex.normSq (K x i) -
        6 * (sixAvg₁ ![K] + sixAvg₂ ![K]) := by
  rw [sb_coercivity_identity]
  have h₁ := Complex.normSq_nonneg (K (1, 1) 0)
  have h₂ := Complex.normSq_nonneg (K (0, 0) 1)
  have h₃ := Complex.normSq_nonneg (K (0, 0) 0 - K (0, 1) 1 - K (1, 0) 1)
  have h₄ := Complex.normSq_nonneg (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0)
  linarith

/-- Summed squared distance is at most six times the mean-fidelity deficit. -/
theorem sb_channel_coercivity {r : ℕ} (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K) :
    ∑ i, sb_distanceSq (K i) ≤
      6 * (5 / 6 - (sixAvg₁ K + sixAvg₂ K) / 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sb_coercivity (K i))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← st_sixAvg₁_eq_sum, ← st_sixAvg₂_eq_sum] at h
  rw [st_isChannel_normSq_sum K hK] at h
  linarith

/-- If `(F̄₁ + F̄₂)/2 ≥ 5/6 − ε`, there are coefficients `xᵢ, yᵢ` with `Σᵢ ‖Kᵢ − xᵢV₁ − yᵢV₂‖² ≤ 6ε`:
every Kraus family of a near-optimal channel is near the Bužek–Hillery Kraus space. -/
theorem kraus_span_stability_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K) (ε : ℝ)
    (hε : 5 / 6 - ε ≤ (sixAvg₁ K + sixAvg₂ K) / 2) :
    ∃ x y : Fin r → ℂ,
      ∑ i, ∑ z, ∑ j,
        Complex.normSq (K i z j - (x i • bhV₁ + y i • bhV₂) z j) ≤ 6 * ε := by
  refine ⟨fun i => sb_x (K i), fun i => sb_y (K i), ?_⟩
  have h := sb_channel_coercivity K hK
  change ∑ i, sb_distanceSq (K i) ≤ 6 * ε
  linarith

end QubitCloning
