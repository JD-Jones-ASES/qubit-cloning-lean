module

public import QubitCloning.AsymForm

/-!
# A trade-off valid across the full fidelity range

The ordinary error-form trade-off loses information when a marginal fidelity
is below one half. A Gram identity and Cauchy–Schwarz give the necessary
inequality for the full region, including the clone/anticlone boundary.
This is the qubit specialization of the region described by Hashagen (2017)
and Nechita–Pellegrini–Rochette (2021), proved here directly on Kraus entries.
The converse realization of every point in that region is not asserted here.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- The contraction determining the first clone's six-state average. -/
def fr_u (K : Matrix QQ Q ℂ) (j : Q) : ℂ :=
  K (0, j) 0 + K (1, j) 1

/-- The contraction determining the second clone's six-state average. -/
def fr_v (K : Matrix QQ Q ℂ) (j : Q) : ℂ :=
  K (j, 0) 0 + K (j, 1) 1

/-- The Gram inverse of the two contraction vectors is
`(1/3) * !![2,-1;-1,2]`. Its orthogonal complement has four squares. -/
theorem fr_gram_identity (K : Matrix QQ Q ℂ) :
    3 * (∑ x, ∑ i, Complex.normSq (K x i)) -
      2 * (∑ j, Complex.normSq (fr_u K j)) -
      2 * (∑ j, Complex.normSq (fr_v K j)) +
      2 * (∑ j, (star (fr_u K j) * fr_v K j).re) =
    3 * Complex.normSq (K (1, 1) 0) +
      3 * Complex.normSq (K (0, 0) 1) +
      Complex.normSq (K (0, 0) 0 - K (1, 0) 1 - K (0, 1) 1) +
      Complex.normSq (K (1, 1) 1 - K (0, 1) 0 - K (1, 0) 0) := by
  simp only [fr_u, fr_v, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Cauchy–Schwarz for the real part of a finite complex pairing. -/
theorem fr_cauchy {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    (∑ j, (star (u j) * v j).re) ≤
      Real.sqrt ((∑ j, Complex.normSq (u j)) * (∑ j, Complex.normSq (v j))) := by
  calc
    (∑ j, (star (u j) * v j).re) ≤ ∑ j, ‖u j‖ * ‖v j‖ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul, norm_star] using Complex.re_le_norm (star (u j) * v j)
    _ ≤ Real.sqrt (∑ j, ‖u j‖ ^ 2) * Real.sqrt (∑ j, ‖v j‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => ‖u j‖) (fun j => ‖v j‖)
    _ = Real.sqrt ((∑ j, Complex.normSq (u j)) * (∑ j, Complex.normSq (v j))) := by
      simp only [Complex.normSq_eq_norm_sq]
      rw [Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]

/-- The trade-off for the full fidelity range. Together with `F̄ᵢ ≥ 1/3`,
this is the necessary inequality of the complete qubit cloning region:
`3(F̄₁+F̄₂)-7/2 ≤ sqrt((3F̄₁-1)(3F̄₂-1))`.
Only necessity is formalized; no converse realization theorem is asserted. -/
theorem tradeoff_full_sqrt_internal {r : ℕ} (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K) :
    3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 ≤
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)) := by
  let U := ∑ i, ∑ j, Complex.normSq (fr_u (K i) j)
  let V := ∑ i, ∑ j, Complex.normSq (fr_v (K i) j)
  let C := ∑ i, ∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hc : C ≤ Real.sqrt (U * V) := by
    simpa only [Fintype.sum_prod_type] using
      fr_cauchy (fun p : Fin r × Q => fr_u (K p.1) p.2)
        (fun p : Fin r × Q => fr_v (K p.1) p.2)
  have hg : 0 ≤ 3 * (∑ i, ∑ x, ∑ j, Complex.normSq (K i x j)) -
      2 * U - 2 * V + 2 * C := by
    have hp : ∀ i : Fin r,
        0 ≤ 3 * (∑ x, ∑ j, Complex.normSq (K i x j)) -
          2 * (∑ j, Complex.normSq (fr_u (K i) j)) -
          2 * (∑ j, Complex.normSq (fr_v (K i) j)) +
          2 * (∑ j, (star (fr_u (K i) j) * fr_v (K i) j).re) := by
      intro i
      rw [fr_gram_identity]
      have h₁ := Complex.normSq_nonneg (K i (1, 1) 0)
      have h₂ := Complex.normSq_nonneg (K i (0, 0) 1)
      have h₃ := Complex.normSq_nonneg (K i (0, 0) 0 - K i (1, 0) 1 - K i (0, 1) 1)
      have h₄ := Complex.normSq_nonneg (K i (1, 1) 1 - K i (0, 1) 0 - K i (1, 0) 0)
      linarith
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hp i)
    simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  rw [st_isChannel_normSq_sum K hK] at hg
  have h1 : 6 * sixAvg₁ K = 2 + U := by
    simpa only [U, fr_u, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add,
      one_add_one_eq_two] using af_weighted_eq K hK 1 0
  have h2 : 6 * sixAvg₂ K = 2 + V := by
    simpa only [V, fr_v, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add,
      one_add_one_eq_two] using af_weighted_eq K hK 0 1
  have hprod : U * V = 2 ^ 2 * ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)) := by
    rw [show U = 6 * sixAvg₁ K - 2 by linarith,
      show V = 6 * sixAvg₂ K - 2 by linarith]
    ring
  rw [hprod, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at hc
  linarith

end QubitCloning
