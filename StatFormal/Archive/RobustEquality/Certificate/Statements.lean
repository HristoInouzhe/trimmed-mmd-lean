import StatFormal.Archive.RobustEquality.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# FROZEN STATEMENTS — robust equality (JASA): the certificate `thm:certificate` and `prop:uniform`

Sources: `jasa/main.tex:180-215` (`eq:robust`, worst-case disparity), `:236-285` (`def:family`,
`lem:kernel`), `:340-375` (`eq:T`, `thm:certificate`), `:453` (`prop:uniform`); supplement
`supp_proofs.tex:15-23` (references with `0 < ν(K) ≤ 1`, paper's KL = `klRef`).

Conditional formalisation (see card):
* Ball membership `Q ∈ B^N(r)` is encoded by the witness of `lem:kernel`: a reference `ν ∈ N` and a kernel
  `Γ` (one probability law per labelled anchor) with `E_{P̂}Γ = Q` and
  `E_{x₀∼P̂}[E_{Γ_{x₀}} c(x₀,·) + ε KL(Γ_{x₀}‖ν)] ≤ r`. The equivalence with the entropic-OT definition
  (`lem:kernel`, `lem:tax`) is not formalised.
* The bound is stated with `T` evaluated at the witnessing reference `ν` (`T^{{ν}}_s ≤ T^N_s` whenever the
  supremum in `eq:T` is finite), in the equivalent non-squared form `W₂ ≤ Δ + √T₀ + √T₁`, in `ℝ≥0∞`.
* `W₂` is Tau Ceti's `wassersteinEDist 2` (infimum over couplings of the `L²` norm of the distance).
* The cost `c` is any bounded measurable nonnegative function (paper: `‖x−x'‖²` on a compact `K`).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti
open scoped ENNReal

namespace StatFormal.RobustEquality.Certificate

variable {K : Type} [MeasurableSpace K]

/-- The empirical centre `P̂ = n⁻¹ Σ_i δ_{x_i}` (labelled atoms, ties allowed). -/
def centre {n : ℕ} (x : Fin n → K) : Measure K := (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- `lem:kernel` witness that `Q` lies in the ball of radius `r` around `P̂` for the reference `ν`. -/
def KernelWitness {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (ν Q : Measure K) : Prop :=
  ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧
    Q = (n : ℝ≥0∞)⁻¹ • ∑ i, Γ i ∧
    ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) + (ε : EReal) * klRef (Γ i) ν)
      ≤ (r : EReal)

/-- `eq:T` at a single reference: `T(h,λ) = λr + λε n⁻¹ Σ_i log E_ν exp{(f_h(x_i,·) − λc(x_i,·))/(λε)}`,
with `f_h(x₀,x) = (h(x) − h(x₀))²`. -/
def Tref1 {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε r lam : ℝ) (ν : Measure K) : ℝ :=
  lam * r + lam * ε * ((n : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp
    (((h z - h (x i)) ^ 2 - lam * c (x i) z) / (lam * ε)) ∂ν))

namespace Claims

/-- `thm:certificate`: for nonempty balls (witnessed by `lem:kernel`), every bounded measurable rule
`h` and every `λ₀, λ₁ > 0`,
`W₂(h#Q₀, h#Q₁) ≤ W₂(h#P̂₀, h#P̂₁) + √T₀(h,λ₀) + √T₁(h,λ₁)`. -/
def certificate : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε r₀ r₁ lam₀ lam₁ : ℝ) (h : K → ℝ) (ν₀ ν₁ Q₀ Q₁ : Measure K)
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁],
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    ν₀ Set.univ ≠ 0 → ν₀ Set.univ ≤ 1 → ν₁ Set.univ ≠ 0 → ν₁ Set.univ ≤ 1 →
    KernelWitness x₀ c ε r₀ ν₀ Q₀ → KernelWitness x₁ c ε r₁ ν₁ Q₁ →
      wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ≤
        wassersteinEDist 2 ((centre x₀).map h) ((centre x₁).map h) +
          ENNReal.ofReal (√(Tref1 x₀ c h ε r₀ lam₀ ν₀)) + ENNReal.ofReal (√(Tref1 x₁ c h ε r₁ lam₁ ν₁))

/-- `prop:uniform`: if each population lies in its (data-dependent) ball with probability
`≥ 1 − α/2`, then with probability `≥ 1 − α`, simultaneously for every bounded measurable rule and
every pair of multipliers, the population disparity is bounded by the certificate. -/
def uniform : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n₀ n₁ : ℕ) (x₀ : Ω → Fin n₀ → K) (x₁ : Ω → Fin n₁ → K) (c : K → K → ℝ) (ε α : ℝ)
    (r₀ r₁ : Ω → ℝ) (ν₀ ν₁ : Ω → Measure K) (P₀ P₁ : Measure K)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (E₀ E₁ : Set Ω),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < α → α < 1 →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    (∀ ω, IsFiniteMeasure (ν₀ ω) ∧ ν₀ ω Set.univ ≠ 0 ∧ ν₀ ω Set.univ ≤ 1) →
    (∀ ω, IsFiniteMeasure (ν₁ ω) ∧ ν₁ ω Set.univ ≠ 0 ∧ ν₁ ω Set.univ ≤ 1) →
    MeasurableSet E₀ → MeasurableSet E₁ →
    ENNReal.ofReal (1 - α / 2) ≤ P E₀ → ENNReal.ofReal (1 - α / 2) ≤ P E₁ →
    (∀ ω ∈ E₀, KernelWitness (x₀ ω) c ε (r₀ ω) (ν₀ ω) P₀) →
    (∀ ω ∈ E₁, KernelWitness (x₁ ω) c ε (r₁ ω) (ν₁ ω) P₁) →
      ENNReal.ofReal (1 - α) ≤ P {ω | ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h →
        (∃ H, ∀ z, |h z| ≤ H) → 0 < lam₀ → 0 < lam₁ →
          wassersteinEDist 2 (P₀.map h) (P₁.map h) ≤
            wassersteinEDist 2 ((centre (x₀ ω)).map h) ((centre (x₁ ω)).map h) +
              ENNReal.ofReal (√(Tref1 (x₀ ω) c h ε (r₀ ω) lam₀ (ν₀ ω))) +
              ENNReal.ofReal (√(Tref1 (x₁ ω) c h ε (r₁ ω) lam₁ (ν₁ ω)))}

end Claims
end StatFormal.RobustEquality.Certificate
