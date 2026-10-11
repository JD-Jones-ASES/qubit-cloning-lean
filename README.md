# Universal 1 → 2 qubit cloning: optimality, uniqueness, fidelity trade-offs, and quantitative stability

A channel from one qubit to two is a finite Kraus family `K : Fin r → Matrix (Fin 2 × Fin 2) (Fin 2) ℂ` with
`Σᵢ Kᵢᴴ Kᵢ = 1`, acting by `ρ ↦ Σᵢ Kᵢ ρ Kᵢᴴ` (the blank qubit is fixed: a `1 → 2` map). For a pure input `ψ` the clone
fidelities are `F₁(ψ) = Re ⟨ψ| Tr₂ Λ(ψψ†) |ψ⟩` and `F₂(ψ) = Re ⟨ψ| Tr₁ Λ(ψψ†) |ψ⟩`; `F̄₁, F̄₂` are their averages over
the six Pauli eigenstates `(1 ± σ)/2` (the six states form a 2-design, the octahedron being a spherical 3-design, so
these equal the Bloch-sphere averages of Gisin–Massar; that equality is neither used nor claimed). Every averaging
state is Gaussian-rational, so every statement is finite.

[Challenge.lean](Challenge.lean) states twenty definitions and thirty-seven theorems; [Solution.lean](Solution.lean)
proves them, kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each:

- **the bound:** for every channel `(F̄₁ + F̄₂)/2 ≤ 5/6`, so some unit `ψ` has `min(F₁(ψ), F₂(ψ)) ≤ 5/6`
  (Gisin–Massar 1997, (12)–(17), their largest-eigenvalue bound at `M = 2`; Bruß–DiVincenzo–Ekert–Fuchs–Macchiavello–
  Smolin 1998, (16), within their symmetric isotropic ansatz), proved by a six-term sum of squares in the Kraus entries;
- **the Bužek–Hillery channel:** `Λ_BH(ρ) = (1/6) V₁ ρ V₁ᴴ + (2/3) V₂ ρ V₂ᴴ` with `V₁|0⟩ = 2|00⟩`, `V₁|1⟩ = |01⟩ + |10⟩`,
  `V₂|0⟩ = (|01⟩ + |10⟩)/2`, `V₂|1⟩ = |11⟩` (Bužek–Hillery 1996, (3.29)) is a channel whose marginals are
  `ρ ↦ (2/3) ρ + (1/6) Tr(ρ)·1` (their (4.6); Werner 1998, (3.7)–(3.8)), so `F₁(ψ) = F₂(ψ) = 5/6` for every unit `ψ`
  (Bužek–Hillery's root fidelity `√(5/6)`, p. 7);
- **uniqueness:** a channel with `(F̄₁ + F̄₂)/2 = 5/6`, or with `F₁(ψ), F₂(ψ) ≥ 5/6` for every unit `ψ`, is `Λ_BH` as a map,
  so `5/6` is the greatest `t` for which some channel has `t ≤ F₁(ψ), F₂(ψ)` for every unit `ψ` (`IsGreatest`). The
  uniqueness under this average-fidelity criterion is proved here; Keyl–Werner 1999 prove it for the worst-case one-clone
  criterion `Δ_one`, Werner 1998 for the global criterion; the Kraus family, the dilation and the ancilla are not unique
  (Roubert–Braun 2008 exhibit a continuum of two-qubit machines with the same marginals);
- **the floor:** `F̄₁, F̄₂ ≥ 1/3` for every channel, attained for the first clone by the universal NOT `(1/3)(XρX + YρY + ZρZ)` on one clone
  with a maximally mixed other clone (the universal-NOT bound of Bužek–Hillery–Werner 1999 and Gisin–Popescu 1999, in
  six-state average form);
- **the asymmetric trade-off:** for every channel and all `a, b ≥ 0`, `ab ≤ a(a + 2b)(1 − F̄₁) + b(2a + b)(1 − F̄₂)`, also
  with worst-case fidelities in place of the averages (Fiurášek–Filip–Cerf 2005, §II, their largest-eigenvalue bound in
  every dimension, written homogeneously at `d = 2` for their weights `A = a(a + 2b)`, `B = b(2a + b)`, where
  `√(A² − AB + B²) = a² + ab + b²`; the conic of Cerf, J. Mod. Opt. 2000, (2.31), and the curve of Niu–Griffiths 1998,
  (6.29); the full region in Hashagen 2017 and Nechita–Pellegrini–Rochette 2021), proved
  by a sum of squares polynomial in `a, b`;
- **the family:** `Λ_{a,b}(ρ) = (A₀ ρ A₀ᴴ + A₁ ρ A₁ᴴ)/(2(a² + ab + b²))` with `A₀|0⟩ = (a + b)|00⟩`, `A₀|1⟩ = a|10⟩ + b|01⟩`,
  `A₁|0⟩ = a|01⟩ + b|10⟩`, `A₁|1⟩ = (a + b)|11⟩` (Niu–Griffiths (4.13), Cerf, J. Mod. Opt. 2000, (2.28), Fiurášek–Filip–Cerf (19),
  Scarani–Iblisdir–Gisin–Acín 2005, (27)) consists of channels with marginals `ρ ↦ (1 − b²/s) ρ + (b²/2s) Tr(ρ)·1` and
  `ρ ↦ (1 − a²/s) ρ + (a²/2s) Tr(ρ)·1`, `s = a² + ab + b²`, so `F₁(ψ) = 1 − b²/2s`, `F₂(ψ) = 1 − a²/2s` for every unit `ψ`
  (Fiurášek–Filip–Cerf (22)), with equality in the bound at the weights `(a, b)`; for `a, b > 0` equality holds only for
  `Λ_{a,b}` (proved here; Hashagen's uniqueness is within symmetrized channels); `Λ_{1,1} = Λ_BH`;
- **the square-root form:** `√((1 − F̄₁)(1 − F̄₂)) ≥ F̄₁ + F̄₂ − 3/2` for every channel (Scarani–Iblisdir–Gisin–Acín 2005,
  (23)), its worst-case form, and equality along the family for `a, b ≥ 0` (the curve of Niu–Griffiths (6.29));
- **the full-range necessary trade-off:** `3(F̄₁ + F̄₂) − 7/2 ≤ √((3F̄₁ − 1)(3F̄₂ − 1))`, including fidelities below `1/2`
  (Hashagen 2017, Theorem 6.4; Nechita–Pellegrini–Rochette 2021, Theorem 6; a direct Kraus Gram proof here);
- **signed bounds and extremizers:** the homogeneous bound holds for `(2a + b)(a + 2b) ≥ 0`; for a positive product
  and nonzero `a,b`, equality uniquely determines `Λ_{a,b}`. In particular, `3F̄₁ − 5F̄₂ ≤ 1`, with unique extremizer
  `Λ_{3,−1}` at `(13/14,5/14)`. If either average is `1/3`, the other is at most `5/6`; `Λ_{2,−1}` attains `(5/6,1/3)`
  on every pure input;
- **quantitative stability:** mean fidelity at least `5/6 − ε` implies coefficients `xᵢ,yᵢ` with
  `Σᵢ ‖Kᵢ − xᵢV₁ − yᵢV₂‖²_F ≤ 6ε`. [STABILITY.md](STABILITY.md) proves sharpness of `6` within the asymmetric family
  and derives separate handwritten Choi and diamond-norm bounds. Only the Kraus-span inequality is a Lean main result.

Not claimed: the equality of the six-state and Bloch-sphere averages; the Choi–Kraus theorem (a channel is a finite
Kraus family here); uniqueness of two-qubit machines, dilations or Kraus representations; realization of every point allowed by
the full-range inequality; formalized Choi or diamond-norm stability; higher dimensions or `N → M`; any priority.
The full-range and signed inequalities concern actual average fidelities; arbitrary pointwise lower bounds cannot
be substituted into them. See [PRE_SUBMISSION_REVIEW.md](PRE_SUBMISSION_REVIEW.md) for the distinction and an application
to compatible depolarizing marginals. The nearest formal work
holds the qualitative no-cloning theorem (physlib, atlas-lean, csd-lean4, the Isabelle AFP),
channel-level no-broadcasting with Kraus and partial-trace machinery (zblore/csd-lean4, which names a quantitative
cloning bound as a later tranche), the spectrum of the Bužek–Hillery ancilla state (the-omega-institute/trureturing), and
asymptotic global-fidelity mixed-state cloning (JWang226/Cloning, Fei–Wang 2026); physlib's `docs/WildeTODO.md` lists the
`5/6` bound as wanted. Hettel 2026 certifies optimal cloners numerically by semidefinite programming. No code is shared
with any of them.

## Verifying

Lean `v4.35.0-rc2` with Mathlib at the same tag (pinned by `lake-manifest.json`). `python scripts/verify.py` runs the pins,
the source guard and its controls, the definition and statement checks, the standard-library replay of every identity
(`scripts/check_cloning.py`: the quadratic forms, the sums of squares and their kernels, the channels, marginals and
fidelities, the trace-preservation solves, 582 exact checks; `scripts/check_extensions.py`: the full-range Gram identity,
signed certificates, extremizers and stability identities, 62 exact checks), the metadata check, the build with the axiom audit
(`Test/Axioms.lean` rejects any axiom beyond `propext`, `Classical.choice`, `Quot.sound`), the module-resolution check,
the `pp.all` elaboration check of the definitions and Palomar's core-notation audit, and ends with `VERIFY: PASS`
(`--skip-build` leaves out the Lean steps and ends with `VERIFY (source/replay only)`, which does not check the proofs).
The review validation record is [REVIEW_VALIDATION.md](REVIEW_VALIDATION.md); the new GitHub Actions workflow still
needs an upstream run. [PROOF.md](PROOF.md) gives the proofs with the Lean names; [DISCLOSURE.md](DISCLOSURE.md) says how the repository was made.

License: [MIT](LICENSE) for the Lean files and scripts; `scripts/core_notation_audit.lean` is Palomar's, under its MIT
licence ([LICENSES/PalomarSubmission-MIT.txt](LICENSES/PalomarSubmission-MIT.txt)). The papers are cited, not copied.
