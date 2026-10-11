module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character with the same import (`Mathlib`), so
that every definition elaborates to the same term in both files; the registry's comparator judges the
elaborated constants. `scripts/check_definitions.py` compares the two files and `scripts/verify.py` the
`pp.all` output. The development's modules import this file; `Solution.lean` restates the Challenge's
theorems over it and never imports `Challenge.lean`.
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

/-- The fidelity of the pure state `ρ = ψψ†` with a state `σ`: `Re Tr(ρ σ) = Re ⟨ψ|σ|ψ⟩`. -/
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
Cerf, J. Mod. Opt. 2000, in these coordinates; `a = b` is the Bužek–Hillery channel; the Kraus operators are
`A₀, A₁` divided by `√(2(a² + ab + b²))`). -/
def asymChannel (a b : ℝ) (ρ : Matrix Q Q ℂ) : Matrix QQ QQ ℂ :=
  ((2 * (a ^ 2 + a * b + b ^ 2) : ℝ)⁻¹ : ℂ) •
    (asymA₀ a b * ρ * (asymA₀ a b)ᴴ + asymA₁ a b * ρ * (asymA₁ a b)ᴴ)

end QubitCloning
