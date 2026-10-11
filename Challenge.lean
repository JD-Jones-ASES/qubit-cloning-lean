module

public import Mathlib

/-!
# Universal 1 → 2 qubit cloning: the single-clone fidelity bound 5/6 with the Bužek–Hillery channel as its unique optimum, the universal-NOT floor 1/3, and the asymmetric trade-off √((1 − F₁)(1 − F₂)) ≥ F₁ + F₂ − 3/2 with its equality family

A *channel from one qubit to two* is a finite Kraus family `K : Fin r → Matrix (Fin 2 × Fin 2) (Fin 2) ℂ` with
`Σᵢ Kᵢᴴ Kᵢ = 1`, acting by `ρ ↦ Σᵢ Kᵢ ρ Kᵢᴴ` (the Choi–Kraus theorem, not proved here, says every completely
positive trace-preserving map has such a family; the blank qubit is fixed, so this is a `1 → 2` map and not a
two-qubit machine). For a pure input `ψ` the two *clone fidelities* are `F₁(ψ) = Re ⟨ψ| Tr₂ Λ(ψψ†) |ψ⟩` and
`F₂(ψ) = Re ⟨ψ| Tr₁ Λ(ψψ†) |ψ⟩`, and `F̄₁, F̄₂` are their averages over the six Pauli eigenstates `(1 ± σ)/2`
(the octahedron is a 2-design, so these equal the Bloch-sphere averages of Gisin–Massar; that equality is not
used and not claimed). This file states, and `Solution.lean` proves kernel-only (no `native_decide`):

* **the bound** (Gisin–Massar 1997; Bruß–DiVincenzo–Ekert–Fuchs–Macchiavello–Smolin 1998 within the symmetric
  isotropic ansatz): for every channel `(F̄₁ + F̄₂)/2 ≤ 5/6`, so some unit `ψ` has `min(F₁(ψ), F₂(ψ)) ≤ 5/6`
  (`sixAvg_le`, `exists_unit_min_le`); the certificate is a six-term sum of squares in the Kraus entries;
* **the Bužek–Hillery channel** (Bužek–Hillery 1996): `Λ_BH(ρ) = (1/6) V₁ ρ V₁ᴴ + (2/3) V₂ ρ V₂ᴴ` with
  `V₁|0⟩ = 2|00⟩`, `V₁|1⟩ = |01⟩ + |10⟩`, `V₂|0⟩ = (|01⟩ + |10⟩)/2`, `V₂|1⟩ = |11⟩` is a channel whose two
  marginals are `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1`, so `F₁(ψ) = F₂(ψ) = 5/6` for every unit `ψ` (`bh_isChannel`,
  `bh_traceSecond`, `bh_traceFirst`, `bh_fidelity`, `bh_sixAvg`);
* **uniqueness**: a channel with `(F̄₁ + F̄₂)/2 = 5/6`, or with `F₁(ψ), F₂(ψ) ≥ 5/6` for every unit `ψ`, is the
  Bužek–Hillery channel as a map (`eq_bh_of_sixAvg`, `eq_bh_of_forall`; the Kraus family, the dilation and the
  ancilla are not unique — Roubert–Braun 2008 exhibit a continuum of two-qubit machines with the same marginals);
  so `5/6` is the greatest `t` for which some channel has `t ≤ F₁(ψ), F₂(ψ)` for every unit `ψ`
  (`isGreatest_cloning_fidelity`). Keyl–Werner 1999 prove uniqueness for the worst-case one-clone criterion
  `Δ_one`; under the average-fidelity criterion it is proved here from the certificate;
* **the floor**: `F̄₁, F̄₂ ≥ 1/3` for every channel, attained (`sixAvg_ge_third`, `exists_sixAvg_eq_third`:
  the universal-NOT bound of Bužek–Hillery–Werner 1999 and Gisin–Popescu 1999, in the six-state average form);
* **the asymmetric trade-off** (Niu–Griffiths 1998; Cerf 1998, 2000; Bužek–Hillery–Bednik 1998;
  Fiurášek–Filip–Cerf 2005 for the operator method in every dimension; the full region in Hashagen 2017 and
  Nechita–Pellegrini–Rochette 2021): for every channel and all `a, b ≥ 0`,
  `a b ≤ a (a + 2b)(1 − F̄₁) + b (2a + b)(1 − F̄₂)` (`asym_bound`), also with worst-case fidelities in place of the
  averages (`asym_bound_forall`); the family `Λ_{a,b}(ρ) = (A₀ ρ A₀ᴴ + A₁ ρ A₁ᴴ) / (2(a² + ab + b²))` with
  `A₀|0⟩ = (a + b)|00⟩`, `A₀|1⟩ = a|10⟩ + b|01⟩`, `A₁|0⟩ = a|01⟩ + b|10⟩`, `A₁|1⟩ = (a + b)|11⟩` consists of
  channels with marginals `ρ ↦ (1 − b²/s) ρ + (b²/2s) Tr(ρ)·1` and `ρ ↦ (1 − a²/s) ρ + (a²/2s) Tr(ρ)·1`,
  `s = a² + ab + b²`, so `F₁(ψ) = 1 − b²/2s`, `F₂(ψ) = 1 − a²/2s` for every unit `ψ`, with equality in the bound
  at the weights `(a, b)` (`asym_isChannel`, `asym_traceSecond`, `asym_traceFirst`, `asym_fidelity`,
  `asym_equality`); for `a, b > 0` equality holds only for `Λ_{a,b}` (`eq_asym_of_equality`); `Λ_{1,1} = Λ_BH`
  (`bhChannel_eq_asymChannel`); hence the square-root form `√((1 − F̄₁)(1 − F̄₂)) ≥ F̄₁ + F̄₂ − 3/2`
  (Scarani–Iblisdir–Gisin–Acín 2005, Eq. (23); the equality curve of Niu–Griffiths (6.29)), its worst-case form,
  and equality along the family (`tradeoff_sqrt`, `tradeoff_forall`, `tradeoff_attained`).

Twenty-seven statements over twenty definitions; `comparator.json` lists no definition holes. The certificates
are the identities `6 F̄ᵢ(K) = Σᵢ ‖Kᵢ‖² + Σᵢ ⟨kᵢ, Ωᵢ kᵢ⟩` with `Ωᵢ = |Ω⟩⟨Ω|_{R Aᵢ} ⊗ 1`, `|Ω⟩ = |00⟩ + |11⟩`
(the averaged operators of Gisin–Massar's and Fiurášek–Filip–Cerf's largest-eigenvalue method, written as
quadratic forms in the Kraus entries), and `(2a + b)(a + 2b) ‖k‖² − ⟨k, (a(a + 2b) Ω₁ + b(2a + b) Ω₂) k⟩
= (1/3) Σⱼ |⟨(a + 2b) ũⱼ − (2a + b) ṽⱼ, k⟩|² + (2a + b)(a + 2b) ‖Π⊥ k‖²`, polynomial in `a, b`; nothing uses
Choi's theorem, positive semidefinite matrix theory or Haar measure.
-/

@[expose] public section
noncomputable section

namespace QubitCloning

open Matrix

/-- One qubit: the index type `Fin 2`. -/
abbrev Q : Type := Fin 2

/-- Two qubits, the first clone then the second: the index type `Fin 2 × Fin 2`. -/
abbrev QQ : Type := Fin 2 × Fin 2

/-- The action of a Kraus family on a one-qubit matrix: `ρ ↦ Σᵢ Kᵢ ρ Kᵢᴴ`. -/
def krausApply {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- A channel from one qubit to two: a finite Kraus family with `Σᵢ Kᵢᴴ Kᵢ = 1` (trace preservation; complete
positivity is built into the Kraus form). -/
def IsChannel {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

/-- The partial trace over the second clone: `(a, b) ↦ Σ_k M (a, k) (b, k)`. -/
def traceSecond (M : Matrix QQ QQ ℂ) : Matrix Q Q ℂ :=
  Matrix.of fun a b => ∑ k, M (a, k) (b, k)

/-- The partial trace over the first clone: `(a, b) ↦ Σ_k M (k, a) (k, b)`. -/
def traceFirst (M : Matrix QQ QQ ℂ) : Matrix Q Q ℂ :=
  Matrix.of fun a b => ∑ k, M (k, a) (k, b)

/-- The projector `ψ ψ†` onto a vector. -/
def proj (ψ : Q → ℂ) : Matrix Q Q ℂ :=
  Matrix.vecMulVec ψ (star ψ)

/-- The fidelity of the pure state `ρ = ψψ†` with a state `σ`: `Re Tr(ρ σ) = ⟨ψ|σ|ψ⟩`. -/
def fidelity (ρ σ : Matrix Q Q ℂ) : ℝ :=
  (Matrix.trace (ρ * σ)).re

/-- The first clone's fidelity on the pure input `ψ`. -/
def F₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ψ : Q → ℂ) : ℝ :=
  fidelity (proj ψ) (traceSecond (krausApply K (proj ψ)))

/-- The second clone's fidelity on the pure input `ψ`. -/
def F₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (ψ : Q → ℂ) : ℝ :=
  fidelity (proj ψ) (traceFirst (krausApply K (proj ψ)))

/-- The six Pauli eigenstates as density matrices `(1 ± σ)/2`: `0, 1` the `σ_z` eigenstates `|0⟩, |1⟩`;
`2, 3` the `σ_x` eigenstates `|±⟩`; `4, 5` the `σ_y` eigenstates `|±i⟩`. -/
def pauliState : Fin 6 → Matrix Q Q ℂ :=
  ![!![1, 0; 0, 0], !![0, 0; 0, 1],
    !![1 / 2, 1 / 2; 1 / 2, 1 / 2], !![1 / 2, -1 / 2; -1 / 2, 1 / 2],
    !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2], !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]]

/-- The six Pauli eigenstates as unit vectors: `|0⟩, |1⟩, (|0⟩ ± |1⟩)/√2, (|0⟩ ± i|1⟩)/√2`. -/
def pauliVec : Fin 6 → (Q → ℂ) :=
  ![![1, 0], ![0, 1],
    ![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹], ![(Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹],
    ![(Real.sqrt 2 : ℂ)⁻¹, Complex.I * (Real.sqrt 2 : ℂ)⁻¹],
    ![(Real.sqrt 2 : ℂ)⁻¹, -(Complex.I * (Real.sqrt 2 : ℂ)⁻¹)]]

/-- The six-state average of the first clone's fidelity. -/
def sixAvg₁ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : ℝ :=
  (∑ s, fidelity (pauliState s) (traceSecond (krausApply K (pauliState s)))) / 6

/-- The six-state average of the second clone's fidelity. -/
def sixAvg₂ {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) : ℝ :=
  (∑ s, fidelity (pauliState s) (traceFirst (krausApply K (pauliState s)))) / 6

/-- Bužek–Hillery's first operator: `V₁|0⟩ = 2|00⟩`, `V₁|1⟩ = |01⟩ + |10⟩`. -/
def bhV₁ : Matrix QQ Q ℂ :=
  Matrix.of fun x i =>
    if x = (0, 0) ∧ i = 0 then 2 else if (x = (0, 1) ∨ x = (1, 0)) ∧ i = 1 then 1 else 0

/-- Bužek–Hillery's second operator: `V₂|0⟩ = (|01⟩ + |10⟩)/2`, `V₂|1⟩ = |11⟩`. -/
def bhV₂ : Matrix QQ Q ℂ :=
  Matrix.of fun x i =>
    if (x = (0, 1) ∨ x = (1, 0)) ∧ i = 0 then 1 / 2 else if x = (1, 1) ∧ i = 1 then 1 else 0

/-- The Bužek–Hillery channel as a map: `ρ ↦ (1/6) V₁ ρ V₁ᴴ + (2/3) V₂ ρ V₂ᴴ` (Bužek–Hillery 1996; the
Kraus operators are `V₁/√6` and `√(2/3) V₂`). -/
def bhChannel (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ :=
  (1 / 6 : ℂ) • (bhV₁ * ρ * bhV₁ᴴ) + (2 / 3 : ℂ) • (bhV₂ * ρ * bhV₂ᴴ)

/-- The asymmetric cloner's first operator: `A₀|0⟩ = (a + b)|00⟩`, `A₀|1⟩ = a|10⟩ + b|01⟩`. -/
def asymA₀ (a b : ℝ) : Matrix QQ Q ℂ :=
  Matrix.of fun x i =>
    if x = (0, 0) ∧ i = 0 then ((a + b : ℝ) : ℂ)
    else if x = (1, 0) ∧ i = 1 then (a : ℂ) else if x = (0, 1) ∧ i = 1 then (b : ℂ) else 0

/-- The asymmetric cloner's second operator: `A₁|0⟩ = a|01⟩ + b|10⟩`, `A₁|1⟩ = (a + b)|11⟩`. -/
def asymA₁ (a b : ℝ) : Matrix QQ Q ℂ :=
  Matrix.of fun x i =>
    if x = (0, 1) ∧ i = 0 then (a : ℂ) else if x = (1, 0) ∧ i = 0 then (b : ℂ)
    else if x = (1, 1) ∧ i = 1 then ((a + b : ℝ) : ℂ) else 0

/-- The asymmetric cloning channel with weights `a, b` (not both zero), as a map:
`ρ ↦ (A₀ ρ A₀ᴴ + A₁ ρ A₁ᴴ) / (2(a² + ab + b²))` (the optimal asymmetric cloner of Niu–Griffiths 1998 and
Cerf 1998 in these coordinates; `a = b` is the Bužek–Hillery channel; the Kraus operators are
`A₀, A₁` divided by `√(2(a² + ab + b²))`). -/
def asymChannel (a b : ℝ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ :=
  ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ)⁻¹ : ℂ) •
    (asymA₀ a b * ρ * (asymA₀ a b)ᴴ + asymA₁ a b * ρ * (asymA₁ a b)ᴴ)

/-! ## The six states -/

/-- Each Pauli eigenstate is the projector onto its unit vector. -/
theorem proj_pauliVec (s : Fin 6) : proj (pauliVec s) = pauliState s := sorry

/-- The six vectors are unit vectors. -/
theorem pauliVec_unit (s : Fin 6) : star (pauliVec s) ⬝ᵥ pauliVec s = 1 := sorry

/-! ## The bound 5/6 -/

/-- Gisin–Massar's bound in the six-state form: for every channel the mean single-clone fidelity, averaged
over the six Pauli eigenstates, is at most `5/6`. -/
theorem sixAvg_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    (sixAvg₁ K + sixAvg₂ K) / 2 ≤ 5 / 6 := sorry

/-- No channel clones every pure state with both fidelities above `5/6`: some unit vector has
`min (F₁, F₂) ≤ 5/6`. -/
theorem exists_unit_min_le {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    ∃ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ min (F₁ K ψ) (F₂ K ψ) ≤ 5 / 6 := sorry

/-- The six-state average of either clone's fidelity is at least `1/3` for every channel (the universal-NOT
bound in average form: no channel anti-clones better than the universal NOT). -/
theorem sixAvg_ge_third {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    1 / 3 ≤ sixAvg₁ K ∧ 1 / 3 ≤ sixAvg₂ K := sorry

/-- The floor `1/3` is attained: the universal NOT on the first clone with a maximally mixed second clone. -/
theorem exists_sixAvg_eq_third :
    ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧ sixAvg₁ K = 1 / 3 := sorry

/-! ## The Bužek–Hillery channel -/

/-- The Bužek–Hillery map is a channel: it has a Kraus family. -/
theorem bh_isChannel :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- The Bužek–Hillery map preserves the trace. -/
theorem bh_trace (ρ : Matrix Q Q ℂ) : Matrix.trace (bhChannel ρ) = Matrix.trace ρ := sorry

/-- The first marginal of the Bužek–Hillery channel is the depolarizing map `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1`. -/
theorem bh_traceSecond (ρ : Matrix Q Q ℂ) :
    traceSecond (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- The second marginal of the Bužek–Hillery channel is the same depolarizing map. -/
theorem bh_traceFirst (ρ : Matrix Q Q ℂ) :
    traceFirst (bhChannel ρ) = (2 / 3 : ℂ) • ρ + (1 / 6 : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Any Kraus family of the Bužek–Hillery channel clones every pure state with both fidelities `5/6`. -/
theorem bh_fidelity {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ)
    (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : F₁ K ψ = 5 / 6 ∧ F₂ K ψ = 5 / 6 := sorry

/-- Its six-state averages are `5/6` and `5/6`. -/
theorem bh_sixAvg {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = bhChannel ρ) :
    sixAvg₁ K = 5 / 6 ∧ sixAvg₂ K = 5 / 6 := sorry

/-! ## Uniqueness -/

/-- Equality in the bound forces the channel: a channel whose six-state mean fidelity is `5/6` is the
Bužek–Hillery channel as a map. -/
theorem eq_bh_of_sixAvg {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : (sixAvg₁ K + sixAvg₂ K) / 2 = 5 / 6) : ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- A channel cloning every pure state with both fidelities at least `5/6` is the Bužek–Hillery channel. -/
theorem eq_bh_of_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → 5 / 6 ≤ F₁ K ψ ∧ 5 / 6 ≤ F₂ K ψ) :
    ∀ ρ, krausApply K ρ = bhChannel ρ := sorry

/-- `5/6` is the greatest worst-case common fidelity of a universal `1 → 2` qubit cloner: the greatest `t`
for which some channel has `t ≤ F₁(ψ)` and `t ≤ F₂(ψ)` for every unit `ψ`. -/
theorem isGreatest_cloning_fidelity :
    IsGreatest {t : ℝ | ∃ (r : ℕ) (K : Fin r → Matrix QQ Q ℂ), IsChannel K ∧
      ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → t ≤ F₁ K ψ ∧ t ≤ F₂ K ψ} (5 / 6) := sorry

/-! ## The asymmetric trade-off -/

/-- The asymmetric cloning bound: for every channel and all weights `a, b ≥ 0`,
`a b ≤ a (a + 2b) (1 − F̄₁) + b (2a + b) (1 − F̄₂)`. -/
theorem asym_bound {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : a * b ≤ a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := sorry

/-- The same bound for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`a b ≤ a (a + 2b) (1 − f₁) + b (2a + b) (1 − f₂)`. -/
theorem asym_bound_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (f₁ f₂ : ℝ) (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    a * b ≤ a * (a + 2 * b) * (1 - f₁) + b * (2 * a + b) * (1 - f₂) := sorry

/-- The asymmetric cloner is a channel for every `(a, b) ≠ (0, 0)`. -/
theorem asym_isChannel (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    ∃ K : Fin 2 → Matrix QQ Q ℂ, IsChannel K ∧ ∀ ρ, krausApply K ρ = asymChannel a b ρ := sorry

/-- Its first marginal is the depolarizing map with shrinking factor `1 − b²/(a² + ab + b²)`. -/
theorem asym_traceSecond (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceSecond (asymChannel a b ρ) =
      ((1 - b ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Its second marginal is the depolarizing map with shrinking factor `1 − a²/(a² + ab + b²)`. -/
theorem asym_traceFirst (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (ρ : Matrix Q Q ℂ) :
    traceFirst (asymChannel a b ρ) =
      ((1 - a ^ 2 / (a ^ 2 + a * b + b ^ 2) : ℝ) : ℂ) • ρ +
        ((a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) : ℝ) : ℂ) • Matrix.trace ρ • (1 : Matrix Q Q ℂ) := sorry

/-- Any Kraus family of the asymmetric cloner clones every pure state with fidelities
`1 − b²/(2(a² + ab + b²))` and `1 − a²/(2(a² + ab + b²))`. -/
theorem asym_fidelity {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) (ψ : Q → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    F₁ K ψ = 1 - b ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) ∧
      F₂ K ψ = 1 - a ^ 2 / (2 * (a ^ 2 + a * b + b ^ 2)) := sorry

/-- The asymmetric cloner attains the bound with equality at its own weights. -/
theorem asym_equality {r : ℕ} (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 ≠ 0) (K : Fin r → Matrix QQ Q ℂ)
    (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K) := sorry

/-- Uniqueness of the asymmetric optimum: for `a, b > 0`, a channel with equality in the bound at the weights
`(a, b)` is the asymmetric cloner `Λ_{a,b}` as a map. -/
theorem eq_asym_of_equality {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (h : a * b = a * (a + 2 * b) * (1 - sixAvg₁ K) + b * (2 * a + b) * (1 - sixAvg₂ K)) :
    ∀ ρ, krausApply K ρ = asymChannel a b ρ := sorry

/-- The Bužek–Hillery channel is the symmetric member `a = b` of the family. -/
theorem bhChannel_eq_asymChannel (ρ : Matrix Q Q ℂ) : bhChannel ρ = asymChannel 1 1 ρ := sorry

/-- The trade-off in square-root form (Scarani–Iblisdir–Gisin–Acín 2005, Eq. (23)):
`F̄₁ + F̄₂ − 3/2 ≤ √((1 − F̄₁)(1 − F̄₂))` for every channel. -/
theorem tradeoff_sqrt {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 ≤ Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := sorry

/-- The trade-off for worst-case fidelities: if `f₁ ≤ F₁(ψ)` and `f₂ ≤ F₂(ψ)` for every unit `ψ`, then
`f₁ + f₂ − 3/2 ≤ √((1 − f₁)(1 − f₂))`. -/
theorem tradeoff_forall {r : ℕ} (K : Fin r → Matrix QQ Q ℂ) (hK : IsChannel K) (f₁ f₂ : ℝ)
    (h : ∀ ψ : Q → ℂ, star ψ ⬝ᵥ ψ = 1 → f₁ ≤ F₁ K ψ ∧ f₂ ≤ F₂ K ψ) :
    f₁ + f₂ - 3 / 2 ≤ Real.sqrt ((1 - f₁) * (1 - f₂)) := sorry

/-- The asymmetric cloners with `a, b ≥ 0` lie on the trade-off curve: equality in the square-root form
(the curve of Niu–Griffiths 1998, Eq. (6.29)). -/
theorem tradeoff_attained {r : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (K : Fin r → Matrix QQ Q ℂ) (hK : ∀ ρ, krausApply K ρ = asymChannel a b ρ) :
    sixAvg₁ K + sixAvg₂ K - 3 / 2 = Real.sqrt ((1 - sixAvg₁ K) * (1 - sixAvg₂ K)) := sorry

end QubitCloning
