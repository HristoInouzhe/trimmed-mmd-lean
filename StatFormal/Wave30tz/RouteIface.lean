import StatFormal.Wave30tz.Statements

/-!
# Wave 30tz route: interfaces for the assembly of Proposition 1 (untrusted proof material)

Two intermediate statements (definitions only; proved in `RouteLower.lean`, used in `RouteLimits.lean`):
* `Iface.CoreLowerBound`: the lower-side bound of §5 for every floor `σ²_min > 0` and with no condition on `N`: the betting
  term is `genEps … (λ_N)` with the general lower fraction `λ_N = lamLo` (it is `ε_N(ϱ_*)` when `σ²_min ≤ 4` and
  `N ≥ L(1+α)²/(2λ_max²)`);
* `Iface.DpopAntitone`: `α ↦ D_α(P,Q)` is nonincreasing on `[0,1)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Wave30tp StatFormal.TrimmedMMD.Unconditional

/-- The betting term with a general lower fraction `lo`: `exp(−(σ²/(4L)) (N·lo·ϱ − L − 4L(1+α)²/σ²)₊²)`. -/
def genEps (s2 α L : ℝ) (N : ℕ) (ρ lo : ℝ) : ℝ :=
  Real.exp (-(s2 / (4 * L)) * (max (N * lo * ρ - L - 4 * L * (1 + α) ^ 2 / s2) 0) ^ 2)

namespace Iface

/-- The lower-side bound of §5 for every floor `s2 > 0`: `P(α̂_lo < α_i) ≤ 2B e^{−2(τ_* − μ₁)₊²/(D_φ² r)} + J·genEps(ϱ_*, λ_N)`. -/
def CoreLowerBound : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ Dφ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (J n m : ℕ) (α : Fin J → ℝ) (δ lmax s2 : ℝ) (R : LoRun 𝒳 J n m) (Bmax : ℕ) (i : Fin J)
    (d r : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ Dφ) →
    IsGrid α → 0 < δ → δ < 1 → 0 < lmax → lmax ≤ 1 / 2 → 0 < s2 → R.IsWitnessRun φ α δ lmax s2 →
    (∀ k, R.bat k ≤ Bmax) → (∀ k, 1 ≤ fitCard R.lx (R.bat k) ∧ 1 ≤ fitCard R.ly (R.bat k)) →
    (∀ k, 1 / (fitCard R.lx (R.bat k) : ℝ) + 1 / (fitCard R.ly (R.bat k) : ℝ) ≤ r) →
    0 < d → d ≤ Dpop φ P Q (α i) →
    beta (α i) * Dφ * r ≤ d / 8 → beta (α i) ^ 2 * κ ^ 2 * r ≤ 7 * d ^ 2 / 64 →
      sampleLaw P Q n m {ω | R.alphaLo α δ ω.1 ω.2 < α i} ≤
        ENNReal.ofReal (2 * Bmax * Real.exp (-(2 * (max (d / (8 * beta (α i)) - 2 * (1 + √2) * κ * √r) 0) ^ 2 /
            (Dφ ^ 2 * r))) +
          J * genEps s2 (α i) (Real.log (1 / δ)) R.N (d / (2 * beta (α i) * Dφ))
            (lamLo lmax (α i) (Real.log (1 / δ)) s2 R.N))

/-- `α ↦ D_α(P,Q)` is nonincreasing on `[0,1)` (the regions grow with `α`). -/
def DpopAntitone : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (κ : ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (α α' : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α ≤ α' → α' < 1 → Dpop φ P Q α' ≤ Dpop φ P Q α

end Iface
end StatFormal.Wave30tz
