import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Basic

/-!
# FROZEN STATEMENTS — robust equality of outcomes (JASA version)

Sources (verbatim in `inventory/extracted/robust-equality-jasa.md`):
* `prop:mc` (`jasa/main.tex:556`), Certification-preserving estimator;
* `lem:gibbs` (`jasa/supp_proofs.tex:52`), Gibbs variational principle, with the paper's convention
  for references (`supp_proofs.tex:15-23`): `ν` any finite Borel measure with `0 < ν(K) ≤ 1`;
  `KL(Γ‖ν) = ∫ log(dΓ/dν) dΓ` if `Γ ≪ ν`, `+∞` otherwise. Mathlib's `klDiv` differs from this for
  non-probability `ν`, so the paper's KL is defined here (`klRef`).

Scope notes (see card):
* `prop:mc` is stated for a probability reference `ν` ("m independent draws from ν") and, in
  `prop_mc_subprob`, for a reference with `0 < ν(K) ≤ 1` sampled from `ν/ν(K)` with the mean
  multiplied by `ν(K)` — the step the paper states only inside its proof (`supp_proofs.tex:745`).
* `U^{(i)} = exp(...)` enters as an arbitrary measurable positive function; `h` and `R` are fixed
  in advance (deterministic here), as the proposition requires.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Classical Real MeasureTheory ProbabilityTheory

namespace StatFormal.RobustEquality

/-- The paper's KL for a reference `ν` (`supp_proofs.tex:19-20`): `∫ log(dΓ/dν) dΓ` when `Γ ≪ ν`
and the log-likelihood ratio is `Γ`-integrable, `+∞` otherwise (for probability `Γ` and finite `ν`
a non-integrable `llr` has integral `+∞`). -/
def klRef {K : Type*} [MeasurableSpace K] (Γ ν : Measure K) : EReal :=
  if Γ ≪ ν ∧ Integrable (llr Γ ν) Γ then ((∫ x, llr Γ ν x ∂Γ : ℝ) : EReal) else ⊤

/-- `T^{{ν}}_s(h,λ) = λ r + λ ε n⁻¹ Σ_i log E_ν U^{(i)}`. -/
def Tref {K : Type*} [MeasurableSpace K] (ν : Measure K) (n : ℕ) (U : Fin n → K → ℝ)
    (lam ε r : ℝ) : ℝ :=
  lam * r + lam * ε / n * ∑ i, Real.log (∫ x, U i x ∂ν)

/-- `T̂⁺_s(h,λ) = λ r + λ ε n⁻¹ Σ_i log{ Ū^{(i)}_m + R_i √(log(L/α)/(2m)) }`, with `L = n` (single
multiplier) or `L = n|Λ|` (grid). -/
def That {K Ω : Type*} (n m : ℕ) (U : Fin n → K → ℝ) (R : Fin n → ℝ)
    (X : Fin n → Fin m → Ω → K) (lam ε r L α : ℝ) (ω : Ω) : ℝ :=
  lam * r + lam * ε / n *
    ∑ i, Real.log ((1 / (m : ℝ)) * ∑ j, U i (X i j ω) + R i * √(Real.log (L / α) / (2 * m)))

namespace Claims

/-- `prop:mc`, single multiplier: `Pr[T̂⁺ ≥ T] ≥ 1 - α_MC`. -/
def prop_mc : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (ν : Measure K) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (U : Fin n → K → ℝ) (R : Fin n → ℝ)
    (X : Fin n → Fin m → Ω → K) (lam ε r α : ℝ),
    0 < n → 0 < m → 0 < lam → 0 < ε → 0 < α → α < 1 →
    (∀ i, Measurable (U i)) → (∀ i x, 0 < U i x) → (∀ i, ∀ᵐ x ∂ν, U i x ≤ R i) →
    (∀ i j, Measurable (X i j)) → (∀ i, iIndepFun (fun j => X i j) P) →
    (∀ i j, P.map (X i j) = ν) →
      ENNReal.ofReal (1 - α) ≤
        P {ω | Tref ν n U lam ε r ≤ That n m U R X lam ε r n α ω}

/-- `prop:mc`, grid version: replacing `n` by `n|Λ|` inside the logarithm makes the bound hold
simultaneously over a finite grid `Λ` of multipliers (`U`, `R` may depend on the multiplier). -/
def prop_mc_grid : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (ν : Measure K) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (Λ : Finset ℝ)
    (U : ℝ → Fin n → K → ℝ) (R : ℝ → Fin n → ℝ) (X : Fin n → Fin m → Ω → K) (ε r α : ℝ),
    0 < n → 0 < m → Λ.Nonempty → (∀ lam ∈ Λ, 0 < lam) → 0 < ε → 0 < α → α < 1 →
    (∀ lam i, Measurable (U lam i)) → (∀ lam i x, 0 < U lam i x) →
    (∀ lam i, ∀ᵐ x ∂ν, U lam i x ≤ R lam i) →
    (∀ i j, Measurable (X i j)) → (∀ i, iIndepFun (fun j => X i j) P) →
    (∀ i j, P.map (X i j) = ν) →
      ENNReal.ofReal (1 - α) ≤
        P {ω | ∀ lam ∈ Λ,
          Tref ν n (U lam) lam ε r ≤ That n m (U lam) (R lam) X lam ε r (n * Λ.card) α ω}

/-- `prop:mc` for a sub-probability reference (`0 < ν(K) ≤ 1`, the paper's convention
`supp_proofs.tex:17-22`): draws from `ν/ν(K)`, mean multiplied by `ν(K)` (proof, l.745). -/
def prop_mc_subprob : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (ν : Measure K) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (U : Fin n → K → ℝ) (R : Fin n → ℝ)
    (X : Fin n → Fin m → Ω → K) (lam ε r α : ℝ),
    0 < n → 0 < m → 0 < lam → 0 < ε → 0 < α → α < 1 → ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
    (∀ i, Measurable (U i)) → (∀ i x, 0 < U i x) → (∀ i, ∀ᵐ x ∂ν, U i x ≤ R i) →
    (∀ i j, Measurable (X i j)) → (∀ i, iIndepFun (fun j => X i j) P) →
    (∀ i j, P.map (X i j) = (ν Set.univ)⁻¹ • ν) →
      ENNReal.ofReal (1 - α) ≤
        P {ω | Tref ν n U lam ε r ≤ lam * r + lam * ε / n *
          ∑ i, Real.log ((ν Set.univ).toReal * ((1 / (m : ℝ)) * ∑ j, U i (X i j ω)) +
            R i * √(Real.log (n / α) / (2 * m)))}

/-- `lem:gibbs`: for a reference `ν` (`0 < ν(K)`, finite; the paper also has `ν(K) ≤ 1`, not needed)
and bounded measurable `g`, `sup_{Γ ∈ P(K)} {E_Γ g − KL(Γ‖ν)} = log Z`, `Z = ∫ e^g dν`, and the
supremum is attained only at `Γ* = e^g ν / Z` (Mathlib's `ν.tilted g`). -/
def lem_gibbs : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν], ν Set.univ ≠ 0 →
    ∀ g : K → ℝ, Measurable g → (∃ B, ∀ x, |g x| ≤ B) →
      IsGreatest
          {v : EReal | ∃ Γ : Measure K, IsProbabilityMeasure Γ ∧
            v = ((∫ x, g x ∂Γ : ℝ) : EReal) - klRef Γ ν}
          ((Real.log (∫ x, Real.exp (g x) ∂ν) : ℝ) : EReal) ∧
        ∀ Γ : Measure K, IsProbabilityMeasure Γ →
          ((∫ x, g x ∂Γ : ℝ) : EReal) - klRef Γ ν = ((Real.log (∫ x, Real.exp (g x) ∂ν) : ℝ) : EReal) →
            Γ = ν.tilted g

end Claims
end StatFormal.RobustEquality
