import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Kernel.WithDensity

/-!
# FROZEN STATEMENTS — context distributions for ICL: the Gibbs selectors (`prop:gibbs` (i)–(ii))

**Draft for critic review; not frozen, not hashed.**

Source (verbatim in `lean-formalisation/inventory/extracted/context-distribution-icl.md`):
`context-distribution-ICL/paper/v3/sections/04_selector.tex:69-79` (`prop:gibbs`), with the objective
`J(μ) = 𝒜(μ) + λ_cov Φ(μ) + λ_KL KL(μ | P₀)` of `04_selector.tex:38-41` and the mean risk
`𝒜(μ) = ∫ G_μ dP₀`, `G_μ(z) = ∫ L(z; z_{1:M}) dΠ_μ` of `03_framework.tex:26,39`. "Let `M = 1`, `𝒜` the mean
risk, `λ_cov = 0` and `λ_KL = λ > 0`. (i) If `c(z') = ∫ L(z; z') dP₀(z)` is bounded and measurable,
`J` has the unique minimizer `μ⋆(dz') ∝ e^{−c(z')/λ} P₀(dz')`, and `J(μ⋆) = −λ log ∫ e^{−c/λ} dP₀`.
(ii) If the context may depend on the query and `c_x(z') = E[L((x,Y); z') | X = x]` is bounded and
jointly measurable, the policy objective `E_X[∫ c_X dμ_X + λ KL(μ_X | P₀)]` is minimized by
`μ⋆_x(dz') ∝ e^{−c_x(z')/λ} P₀(dz')`, uniquely for almost every `x`."

Covered:
* `gibbs_global` (i): `μ⋆ = P₀` tilted by `−c/λ` is a probability measure with finite KL,
  `J(μ⋆) = −λ log ∫ e^{−c/λ} dP₀`, `J(μ⋆) ≤ J(μ)` for every probability measure `μ` with
  `KL(μ‖P₀) < ∞`, and equality forces `μ = μ⋆` (unique minimizer);
* `gibbs_conditional` (ii): the kernel `x ↦ μ⋆_x = P₀` tilted by `−c_x/λ` is a Markov kernel (a
  measurable policy) with finite KL and integrable objective for every `x`, it minimizes the policy
  objective over Markov kernels, and any policy attaining the same value agrees with it `P_X`-a.e.
Not covered (declared): the derivation of `c` from the loss `L` (`c(z') = ∫ L(z; z') dP₀(z)`,
`c_x(z') = E[L((x,Y); z') | X = x]`): `c` is a primitive here (any bounded measurable `c`, resp.
bounded jointly measurable `c : 𝒳 → 𝒵 → ℝ`), and the `M = 1` mean risk is taken to be
`𝒜(μ) = ∫ c dμ` (the paper's `∫∫ L(z; z') dμ(z') dP₀(z)` after the Fubini swap, which needs an
integrability condition on `L` that the paper leaves implicit); the cases `M ≥ 2`, `λ_cov > 0`, `𝒜 = CVaR_α`; the minimum value of the policy
objective in (ii); the remarks after the proposition.

Encodings (to be checked by the critic):
* `KL(μ | P₀)` is Mathlib's `klDiv μ P₀ : ℝ≥0∞`. `J` is real-valued, `gibbsObj P₀ c λ μ =
  ∫ c dμ + λ · (klDiv μ P₀).toReal`, and is used only where `klDiv μ P₀ ≠ ⊤`: the paper's `J(μ) = +∞`
  when `KL = ∞`, so such `μ` cannot be (or tie with) a minimizer and excluding them loses nothing
  (it avoids the junk `ENNReal.toReal ⊤ = 0`). `∫ c dμ` is a genuine integral since `c` is bounded
  measurable and `μ` finite.
* `μ⋆(dz') ∝ e^{−c(z')/λ} P₀(dz')` is `P₀.tilted (fun z => −c z / λ)` (density `e^f / ∫ e^f dP₀`).
* (ii): a policy `x ↦ μ_x` is a Markov kernel `κ : Kernel 𝒳 𝒵` (measurable in `x`); `P_X` is a
  probability measure on `𝒳`; the policy objective is the Bochner integral
  `policyObj = ∫ gibbsObj P₀ (c x) λ (κ x) dP_X(x)`. Competing policies are required to have
  `KL(κ x | P₀) < ∞` for `P_X`-a.e. `x` and an integrable integrand. Since the integrand is `≥ −B`,
  any other policy has paper objective `+∞` (or undefined), so it neither beats nor ties `κ⋆`; the
  restriction loses nothing for either the minimality or the uniqueness clause, and it rules out the
  junk value `∫ = 0` of a non-integrable function.
* `gibbsKernel` is built with `Kernel.withDensity` (which is `0` for a non-measurable density); the
  claim asserts `gibbsKernel P₀ c λ x = P₀.tilted (−c x/λ)` for every `x` and `IsMarkovKernel`, so no
  junk kernel can satisfy it.
* Boundedness is `∃ B, ∀ z, |c z| ≤ B` (resp. `∀ x z, |c x z| ≤ B`); joint measurability is
  `Measurable (Function.uncurry c)` for the product σ-algebra.

Hash-lock: when frozen, this file is renamed `Statements.lean` and hashed in
`certify/statements.lock` (with its imports); AI agents must not edit it after that.
(The untrusted `Route.lean` defines the same names in `StatFormal.ICL.Gibbs`; it must be switched to
import the frozen file and drop its copies.)
Critic note: `c` is a primitive with `𝒜(μ) = ∫ c dμ`; for `L ≥ 0` the passage from the loss `L` is Tonelli plus joint
measurability (mild, not formalised).
-/

noncomputable section
open Real MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatFormal.ICL.Gibbs

/-- `J(μ) = ∫ c dμ + λ KL(μ‖P₀)` (meaningful when `klDiv μ P₀ ≠ ⊤`). -/
def gibbsObj {Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) (c : Z → ℝ) (lam : ℝ)
    (μ : Measure Z) : ℝ :=
  ∫ z, c z ∂μ + lam * (klDiv μ P0).toReal

/-- The Gibbs policy `κ⋆ x = P₀.tilted (−c x/λ)`, as a kernel. -/
def gibbsKernel {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] (P0 : Measure Z)
    [IsFiniteMeasure P0] (c : X → Z → ℝ) (lam : ℝ) : Kernel X Z :=
  Kernel.withDensity (Kernel.const X P0)
    fun x z => ENNReal.ofReal (exp (-c x z / lam) / ∫ z', exp (-c x z' / lam) ∂P0)

/-- The policy objective `∫ J_x(κ x) dP_X`. -/
def policyObj {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] (PX : Measure X)
    (P0 : Measure Z) (c : X → Z → ℝ) (lam : ℝ) (κ : Kernel X Z) : ℝ :=
  ∫ x, gibbsObj P0 (c x) lam (κ x) ∂PX

namespace Claims

/-- **`prop:gibbs` (i)**: the Gibbs measure is the unique minimizer of `J`, with value
`−λ log ∫ e^{−c/λ} dP₀`. -/
def gibbs_global : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (P0 : Measure Z) [IsProbabilityMeasure P0] (c : Z → ℝ)
    (lam : ℝ), 0 < lam → Measurable c → (∃ B, ∀ z, |c z| ≤ B) →
    IsProbabilityMeasure (P0.tilted fun z => -c z / lam) ∧
      klDiv (P0.tilted fun z => -c z / lam) P0 ≠ ⊤ ∧
      gibbsObj P0 c lam (P0.tilted fun z => -c z / lam) =
        -lam * log (∫ z, exp (-c z / lam) ∂P0) ∧
      ∀ μ : Measure Z, IsProbabilityMeasure μ → klDiv μ P0 ≠ ⊤ →
        gibbsObj P0 c lam (P0.tilted fun z => -c z / lam) ≤ gibbsObj P0 c lam μ ∧
        (gibbsObj P0 c lam μ = gibbsObj P0 c lam (P0.tilted fun z => -c z / lam) →
          μ = P0.tilted fun z => -c z / lam)

/-- **`prop:gibbs` (ii)**: the Gibbs policy minimizes the policy objective, uniquely `P_X`-a.e. -/
def gibbs_conditional : Prop :=
  ∀ (X Z : Type) [MeasurableSpace X] [MeasurableSpace Z] (PX : Measure X) [IsProbabilityMeasure PX]
    (P0 : Measure Z) [IsProbabilityMeasure P0] (c : X → Z → ℝ) (lam : ℝ),
    0 < lam → Measurable (Function.uncurry c) → (∃ B, ∀ x z, |c x z| ≤ B) →
    IsMarkovKernel (gibbsKernel P0 c lam) ∧
      (∀ x, gibbsKernel P0 c lam x = P0.tilted fun z => -c x z / lam) ∧
      (∀ x, klDiv (gibbsKernel P0 c lam x) P0 ≠ ⊤) ∧
      Integrable (fun x => gibbsObj P0 (c x) lam (gibbsKernel P0 c lam x)) PX ∧
      ∀ κ : Kernel X Z, IsMarkovKernel κ → (∀ᵐ x ∂PX, klDiv (κ x) P0 ≠ ⊤) →
        Integrable (fun x => gibbsObj P0 (c x) lam (κ x)) PX →
        policyObj PX P0 c lam (gibbsKernel P0 c lam) ≤ policyObj PX P0 c lam κ ∧
        (policyObj PX P0 c lam κ = policyObj PX P0 c lam (gibbsKernel P0 c lam) →
          ∀ᵐ x ∂PX, κ x = gibbsKernel P0 c lam x)

end Claims
end StatFormal.ICL.Gibbs
