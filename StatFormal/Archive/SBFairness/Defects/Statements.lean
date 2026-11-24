import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# FROZEN STATEMENTS — SB fairness repair: the sentence "the excess `𝒥 − 𝒥^⋆ ≥ 0`" (DEFECTS #12)

Source: `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:1193-1206`
(`eq:repaircost` and the sentence at `:1202`, verbatim: "The \emph{excess} of a repair is
$\Jcal(T_0,T_1)-\Jcal^\star\ge0$."), with the definition of a repair at `:345-346` ("A \emph{repair}
is a family of (possibly randomised) maps $T_{s,t}$" — no parity requirement), `ass:main` (`:353-356`,
`R_s ∈ 𝒫₂(ℝᵈ)`) and `lem:excess` (`:1208-1216`, which itself allows `𝒥 − 𝒥^⋆ < 0`, down to `−2γM`).

Covered:
* `excess_nonneg_false` (the printed sentence is false): it is not true that every pair of measurable
  maps `T₀, T₁` with `T_s − Id ∈ L²(R_s)` has `𝒥^⋆ ≤ 𝒥(T₀,T₁)`, even with `p₀, p₁ > 0`
  (witness `d = 1`, `R₀ = δ₀`, `R₁ = δ_{e₀}`, `p_s = ½`, `T_s = Id`: `𝒥 = 0`, `𝒥^⋆ = ¼ > 0`);
* `excess_nonneg_parity` (corrected sentence): under exact parity `(T₀)_#R₀ = (T₁)_#R₁`,
  `𝒥^⋆ ≤ 𝒥(T₀,T₁)` — the `γ = 0` case of `lem:excess`, with `𝒥^⋆` as an infimum.
Not covered (declared): attainment of `𝒥^⋆` at a barycenter (Agueh–Carlier); `lem:excess` for
`γ > 0`; randomised maps `T_{s,t}`; DEFECTS #10 (`prop:pareto`), which was checked and is **not** a
defect of the statement: `def:repair` (`:435-437`) requires `𝒞_ε(R_s,ν) < ∞`, which by `:400-402` fails
as soon as `R_s` has an atom, so `R_s = δ₀` has no repair kernel and atomlessness is implied.

Encodings (see card):
* `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`; `W₂` is Tau Ceti's `wassersteinEDist 2`, and `𝒫₂` is
  "probability measure with `HasFiniteMoment 2`";
* `‖T_s − Id‖²_{L²(R_s)}` is `eLpNorm (T_s − id) 2 R_s ^ 2` in `ℝ≥0∞` (`repairCost`);
  the weights enter as `ENNReal.ofReal p_s` with `p_s ≥ 0`, `p₀ + p₁ = 1`;
* `𝒥^⋆ = min_ν F(ν)` is encoded as the infimum over `ν ∈ 𝒫₂` (no existence claim);
* "`𝒥 − 𝒥^⋆ ≥ 0`" is encoded as `𝒥^⋆ ≤ 𝒥` (truncated subtraction in `ℝ≥0∞` would make it vacuous);
  both sides are finite for `R_s ∈ 𝒫₂` and `T_s − Id ∈ L²(R_s)`;
* specialisation: the refutation uses `d = 1`, a case the sentence covers.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes
`Defects/Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
Critic note: the defect is a scope slip — the sentence needs "of an exact-parity repair" (the surrounding text has
exact-parity repairs in mind; `lem:excess` itself allows negative excess for approximate parity). `excess_nonneg_parity`
is the intended reading (the `γ = 0` case of `lem:excess`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.SBFairness.Defects

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- `‖T − Id‖²_{L²(R)}`. -/
def repairCost {d : ℕ} (R : Measure (E d)) (T : (E d) → (E d)) : ℝ≥0∞ :=
  eLpNorm (fun x => T x - x) 2 R ^ 2

/-- `eq:repaircost`: `𝒥(T₀,T₁) = Σ_s p_s ‖T_s − Id‖²_{L²(R_s)}`. -/
def J {d : ℕ} (p₀ p₁ : ℝ) (R₀ R₁ : Measure (E d)) (T₀ T₁ : (E d) → (E d)) : ℝ≥0∞ :=
  ENNReal.ofReal p₀ * repairCost R₀ T₀ + ENNReal.ofReal p₁ * repairCost R₁ T₁

/-- `eq:repaircost`: the barycenter functional `F(ν) = Σ_s p_s W₂²(R_s, ν)`. -/
def baryF {d : ℕ} (p₀ p₁ : ℝ) (R₀ R₁ ν : Measure (E d)) : ℝ≥0∞ :=
  ENNReal.ofReal p₀ * wassersteinEDist 2 R₀ ν ^ 2 + ENNReal.ofReal p₁ * wassersteinEDist 2 R₁ ν ^ 2

/-- `eq:repaircost`: `𝒥^⋆ = inf_{ν ∈ 𝒫₂(ℝᵈ)} F(ν)`. -/
def Jstar {d : ℕ} (p₀ p₁ : ℝ) (R₀ R₁ : Measure (E d)) : ℝ≥0∞ :=
  ⨅ (ν : Measure (E d)) (_ : IsProbabilityMeasure ν ∧ HasFiniteMoment 2 ν), baryF p₀ p₁ R₀ R₁ ν

namespace Claims

/-- The sentence at `:1202` as printed is false: not every repair has non-negative excess. -/
def excess_nonneg_false : Prop :=
  ¬ ∀ (d : ℕ) (R₀ R₁ : Measure (E d)) [IsProbabilityMeasure R₀] [IsProbabilityMeasure R₁]
      (p₀ p₁ : ℝ) (T₀ T₁ : (E d) → (E d)),
      HasFiniteMoment 2 R₀ → HasFiniteMoment 2 R₁ → 0 < p₀ → 0 < p₁ → p₀ + p₁ = 1 →
      Measurable T₀ → Measurable T₁ → repairCost R₀ T₀ ≠ ⊤ → repairCost R₁ T₁ ≠ ⊤ →
        Jstar p₀ p₁ R₀ R₁ ≤ J p₀ p₁ R₀ R₁ T₀ T₁

/-- Corrected sentence: under exact parity `(T₀)_#R₀ = (T₁)_#R₁` the excess is non-negative,
`𝒥^⋆ ≤ 𝒥(T₀,T₁)`. -/
def excess_nonneg_parity : Prop :=
  ∀ (d : ℕ) (R₀ R₁ : Measure (E d)) [IsProbabilityMeasure R₀] [IsProbabilityMeasure R₁]
    (p₀ p₁ : ℝ) (T₀ T₁ : (E d) → (E d)),
    HasFiniteMoment 2 R₀ → HasFiniteMoment 2 R₁ → 0 ≤ p₀ → 0 ≤ p₁ → p₀ + p₁ = 1 →
    Measurable T₀ → Measurable T₁ → R₀.map T₀ = R₁.map T₁ →
      Jstar p₀ p₁ R₀ R₁ ≤ J p₀ p₁ R₀ R₁ T₀ T₁

end Claims
end StatFormal.SBFairness.Defects
