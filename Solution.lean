module

public import QubitCloning

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `QubitCloning/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`QubitCloning/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace QubitCloning

open Matrix

theorem proj_pauliVec (s : Fin 6) : proj (pauliVec s) = pauliState s :=
  proj_pauliVec_internal s

theorem pauliVec_unit (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 :=
  pauliVec_unit_internal s

theorem sixAvg_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    (sixAvg₁ K + sixAvg₂ K) / 2 ≤ 5 / 6 :=
  sixAvg_le_internal K hK

theorem exists_unit_min_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∃ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ min (F₁ K ψ) (F₂ K ψ) ≤ 5 / 6 :=
  exists_unit_min_le_internal K hK

theorem sixAvg_ge_third {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    1 / 3 ≤ sixAvg₁ K ∧ 1 / 3 ≤ sixAvg₂ K :=
  sixAvg_ge_third_internal K hK

theorem exists_sixAvg_eq_third :
    ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧ sixAvg₁ K = 1 / 3 :=
  exists_sixAvg_eq_third_internal

theorem bh_isChannel :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = bhChannel ρ :=
  bh_isChannel_internal

theorem bh_trace (ρ : Matrix Q Q ℂ) : Matrix.trace (bhChannel ρ) = Matrix.trace ρ :=
  bh_trace_internal ρ

theorem bh_traceSecond (ρ : Matrix Q Q ℂ) :
    traceSecond (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) :=
  bh_traceSecond_internal ρ

theorem bh_traceFirst (ρ : Matrix Q Q ℂ) :
    traceFirst (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) :=
  bh_traceFirst_internal ρ

theorem bh_fidelity {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ)
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 5 / 6 :=
  bh_fidelity_internal K hK ψ hψ

theorem bh_sixAvg {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ) :
    sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 5 / 6 :=
  bh_sixAvg_internal K hK

theorem eq_bh_of_sixAvg {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : (sixAvg₁ K + sixAvg₂ K) / 2 = 5 / 6) : ∀ ρ, krausApply K ρ = bhChannel ρ :=
  eq_bh_of_sixAvg_internal K hK h

theorem eq_bh_of_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → 5 / 6 ≤ F₁ K ψ ∧ 5 / 6 ≤ F₂ K ψ) :
    ∀ ρ, krausApply K ρ = bhChannel ρ :=
  eq_bh_of_forall_internal K hK h

theorem isGreatest_cloning_fidelity :
    IsGreatest {t : ℝ | ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → t ≤ F₁ K ψ ∧ t ≤ F₂ K ψ} (5 / 6) :=
  isGreatest_cloning_fidelity_internal

theorem asym_bound {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) :=
  asym_bound_internal K hK a b ha hb

theorem asym_bound_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (f₁ f₂ : ℝ) (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    a * b ≤ a * (a + 2 * b) * (1 - f₁) + b * (2 * a + b) * (1 - f₂) :=
  asym_bound_forall_internal K hK a b ha hb f₁ f₂ h

theorem asym_isChannel (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = asymChannel a b ρ :=
  asym_isChannel_internal a b h

theorem asym_traceSecond (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceSecond (asymChannel a b ρ) =
      ((1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) :=
  asym_traceSecond_internal a b h ρ

theorem asym_traceFirst (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceFirst (asymChannel a b ρ) =
      ((1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) :=
  asym_traceFirst_internal a b h ρ

theorem asym_fidelity {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    F₁ K ψ = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      F₂ K ψ = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) :=
  asym_fidelity_internal a b h K hK ψ hψ

theorem asym_equality {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) :=
  asym_equality_internal a b h K hK

theorem eq_asym_of_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ :=
  eq_asym_of_equality_internal K hK a b ha hb h

theorem bhChannel_eq_asymChannel (ρ : Matrix Q Q ℂ) : bhChannel ρ = asymChannel 1 1 ρ :=
  bhChannel_eq_asymChannel_internal ρ

theorem tradeoff_sqrt {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 ≤ Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) :=
  tradeoff_sqrt_internal K hK

theorem tradeoff_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (f₁ f₂ : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    f₁ + f₂ - 3 / 2 ≤ Real.sqrt ((1 - f₁) * (1 - f₂)) :=
  tradeoff_forall_internal K hK f₁ f₂ h

theorem tradeoff_attained {r : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 = Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) :=
  tradeoff_attained_internal a b ha hb h K hK

theorem tradeoff_full_sqrt {r : ℕ} (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K) :
    3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 ≤
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)) :=
  tradeoff_full_sqrt_internal K hK

theorem signed_asym_bound {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ)
    (hP : 0 ≤ (2 * a + b) * (a + 2 * b)) :
    a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) :=
  signed_asym_bound_internal K hK a b hP

theorem eq_asym_of_signed_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ)
    (hP : 0 < (2 * a + b) * (a + 2 * b)) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ :=
  eq_asym_of_signed_equality_internal K hK a b hP ha hb h

theorem clone_anticlone_bound {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    3 * sixAvg₁ K - 5 * sixAvg₂ K ≤ 1 :=
  clone_anticlone_bound_internal K hK

theorem clone_anticlone_attained :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ (∀ ρ, krausApply K ρ = asymChannel 3 (-1) ρ) ∧
      sixAvg₁ K = 13 / 14 ∧ sixAvg₂ K = 5 / 14 :=
  clone_anticlone_attained_internal

theorem eq_clone_anticlone_of_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 3 * sixAvg₁ K - 5 * sixAvg₂ K = 1) :
    ∀ ρ, krausApply K ρ = asymChannel 3 (-1) ρ :=
  eq_clone_anticlone_of_equality_internal K hK h

theorem sixAvg₁_le_of_sixAvg₂_eq_third {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₂ K = 1 / 3) : sixAvg₁ K ≤ 5 / 6 :=
  sixAvg₁_le_of_sixAvg₂_eq_third_internal K hK h

theorem sixAvg₂_le_of_sixAvg₁_eq_third {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₁ K = 1 / 3) : sixAvg₂ K ≤ 5 / 6 :=
  sixAvg₂_le_of_sixAvg₁_eq_third_internal K hK h

theorem floor_companion_attained :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ (∀ ρ, krausApply K ρ = asymChannel 2 (-1) ρ) ∧
      sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 1 / 3 ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 1 / 3 :=
  floor_companion_attained_internal

theorem kraus_span_stability {r : ℕ} (K : Fin r → Matrix QQ Q ℂ)
    (hK : IsChannel K) (ε : ℝ)
    (hε : 5 / 6 - ε ≤ (sixAvg₁ K + sixAvg₂ K) / 2) :
    ∃ x y : Fin r → ℂ,
      ∑ i, ∑ z, ∑ j,
        Complex.normSq (K i z j - (x i • bhV₁ + y i • bhV₂) z j) ≤ 6 * ε :=
  kraus_span_stability_internal K hK ε hε

theorem tradeoff_full_attained {r : ℕ} (a b : ℝ) (hP : 0 ≤ (2 * a + b) * (a + 2 * b))
    (hs : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 =
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)) :=
  tradeoff_full_attained_internal a b hP hs K hK

theorem eq_asym_of_tradeoff_full_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : 3 * (sixAvg₁ K + sixAvg₂ K) - 7 / 2 =
      Real.sqrt ((3 * sixAvg₁ K - 1) * (3 * sixAvg₂ K - 1)))
    (h₁ : sixAvg₁ K ≠ 1) (h₂ : sixAvg₂ K ≠ 1) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ 0 ≤ (2 * a + b) * (a + 2 * b) ∧
      ∀ ρ, krausApply K ρ = asymChannel a b ρ :=
  eq_asym_of_tradeoff_full_equality_internal K hK h h₁ h₂

theorem eq_asym_of_floor₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h₁ : sixAvg₁ K = 5 / 6) (h₂ : sixAvg₂ K = 1 / 3) :
    ∀ ρ, krausApply K ρ = asymChannel 2 (-1) ρ :=
  eq_asym_of_floor₂_internal K hK h₁ h₂

theorem eq_asym_of_floor₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h₁ : sixAvg₁ K = 1 / 3) (h₂ : sixAvg₂ K = 5 / 6) :
    ∀ ρ, krausApply K ρ = asymChannel (-1) 2 ρ :=
  eq_asym_of_floor₁_internal K hK h₁ h₂

theorem sixAvg₂_eq_half_of_sixAvg₁_eq_one {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₁ K = 1) : sixAvg₂ K = 1 / 2 :=
  sixAvg₂_eq_half_of_sixAvg₁_eq_one_internal K hK h

theorem sixAvg₁_eq_half_of_sixAvg₂_eq_one {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : sixAvg₂ K = 1) : sixAvg₁ K = 1 / 2 :=
  sixAvg₁_eq_half_of_sixAvg₂_eq_one_internal K hK h

theorem channel_stability {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (ε : ℝ)
    (hε : 5 / 6 - ε ≤ (sixAvg₁ K + sixAvg₂ K) / 2) (ρ : Matrix Q Q ℂ) :
    Real.sqrt (∑ x, ∑ y, Complex.normSq ((krausApply K ρ - bhChannel ρ) x y)) ≤
      200 * Real.sqrt ε * Real.sqrt (∑ i, ∑ j, Complex.normSq (ρ i j)) :=
  channel_stability_internal K hK ε hε ρ

end QubitCloning
