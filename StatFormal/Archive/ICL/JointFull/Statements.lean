import StatFormal.Archive.ICL.Joint.Statements

/-!
# FROZEN STATEMENTS — context distributions for ICL: `thm:joint` with the coverage term

Source: `thm:joint` (`paper/v3/sections/06_estimation.tex:76`), objective `J_m`/`J_pool` (`03_framework.tex:69-73`),
coverage `ρ_μ(z) = ∫K(z,z') dΠ̄_μ(z')` and `Φ(μ) = −∫ log ρ_μ dP_0` (`04_selector.tex:5-14`, `Π̄` the one-slot
marginal), proof `supp/proofs_main.tex:90-118`. Extends the frozen `ICL/Joint` (risk part, `λ_cov = 0`).

Covered: with probability at least `1 − δ` (a measurable event), simultaneously for every law `Π` on `[n]^M`,
`|J_m(Π) − J_pool(Π)| ≤ 4B_L√(2M log n/m) + 4λ_cov (K_max/K_min)√(2 log(2n)/m)
                     + (B_L + λ_cov log(K_max/K_min))√(log(1/δ)/(2m))`.
Not covered (declared): the `M`-subset refinement with the coverage term; `cor:consistency`.

Encodings (see card): as in `ICL/Joint` (pool fixed; `L_j` any measurable `[0,B_L]` loss per index tuple; validation
sample `X : Fin m → Ω → Z` i.i.d. `μ = P_0`); the kernel enters through `k_j = K(·, z_j)`, measurable with values in
`[K_min, K_max]`, `0 < K_min`; the one-slot marginal of `Π` is `Π̄_j = M⁻¹ Σ_t Π(t)·#{s : t_s = j}`; the coverage
deviation is `Φ_m(Π) − Φ_pool(Π) = −m⁻¹Σ_i log ρ(Z_i) + ∫ log ρ dP_0`; pool-only penalties (`λ_KL KL(w|u_n)`) are
dropped because they cancel exactly; `K_min ≤ K_max` and `B_L ≥ 0` follow from the hypotheses; probability as a
measurable event (inner form).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open Finset MeasureTheory ProbabilityTheory

namespace StatFormal.ICL.JointFull

open StatFormal.ICL.Joint

/-- One-slot marginal `Π̄_j = M⁻¹ Σ_t Π(t) #{s : t_s = j}` of a law on `[n]^M`. -/
def oneSlot {n M : ℕ} (law : (Fin M → Fin n) → ℝ) (j : Fin n) : ℝ :=
  (1 / (M : ℝ)) * ∑ t, law t * ((univ.filter fun s => t s = j).card : ℝ)

/-- Coverage `ρ(z) = Σ_j Π̄_j K(z, z_j)`. -/
def cover {Z : Type*} {n M : ℕ} (k : Fin n → Z → ℝ) (law : (Fin M → Fin n) → ℝ) (z : Z) : ℝ :=
  ∑ j, oneSlot law j * k j z

/-- `J_m(Π) − J_pool(Π)` with the coverage term. -/
def devFull {Z : Type*} [MeasurableSpace Z] {n M m : ℕ} (μ : Measure Z) (L : (Fin M → Fin n) → Z → ℝ)
    (k : Fin n → Z → ℝ) (lcov : ℝ) (law : (Fin M → Fin n) → ℝ) (zs : Fin m → Z) : ℝ :=
  devJ μ m L law zs +
    lcov * (-(1 / (m : ℝ)) * ∑ i, Real.log (cover k law (zs i)) + ∫ z, Real.log (cover k law z) ∂μ)

namespace Claims

/-- `thm:joint`, full form (risk and coverage terms), laws on `[n]^M`. -/
def joint_full : Prop :=
  ∀ (Z Ω : Type) [MeasurableSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n M m : ℕ) (L : (Fin M → Fin n) → Z → ℝ)
    (k : Fin n → Z → ℝ) (BL Kmin Kmax lcov δ : ℝ) (X : Fin m → Ω → Z),
    2 ≤ n → 1 ≤ M → 0 < m → 0 < δ → δ < 1 → 0 ≤ lcov → 0 < Kmin →
    (∀ j, Measurable (L j)) → (∀ j z, 0 ≤ L j z ∧ L j z ≤ BL) →
    (∀ j, Measurable (k j)) → (∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = μ) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
        E ⊆ {ω | ∀ law : (Fin M → Fin n) → ℝ, ProbVec law →
          |devFull μ L k lcov law (fun i => X i ω)| ≤
            4 * BL * √(2 * M * Real.log n / m) +
            4 * lcov * (Kmax / Kmin) * √(2 * Real.log (2 * n) / m) +
            (BL + lcov * Real.log (Kmax / Kmin)) * √(Real.log (1 / δ) / (2 * m))}

end Claims
end StatFormal.ICL.JointFull
