import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.EReal.Basic

/-!
# FROZEN STATEMENTS — otfd G: conformal depth p-values, central regions, permutation tests

Sources (verbatim in `inventory/extracted/otfd-G_geodesic.md`): `prop:conformal` (`papers/G_geodesic/main.tex:901`),
`prop:test` (`main.tex:925`).

Abstraction (see card): the fitted score `Ŝ` (any of `R̂, κ̂, ϱ̂`) is computed from the training split and the
reference draws; conditionally on them it is a fixed function, so the claims are stated for the score vector
`(Ŝ(X), Ŝ(X_1), …, Ŝ(X_n))` = `S ω : Fin (n+1) → ℝ` (index `0` the new curve, `i.succ` the calibration curves),
assumed **exchangeable** (law invariant under every permutation of `Fin (n+1)`), which is what "`X` is exchangeable
with the calibration curves under `H_0`, conditionally on the training split and the reference draws" gives. For
`prop:test`, the pooled data is `x : ι → Y` (curves, or clusters of curves: `Y` any measurable space), relabelling by
`σ` is `x ↦ x ∘ σ⁻¹`, and a statistic of the fit and the labels that is invariant under simultaneous re-indexing is a
measurable function `T` of the relabelled data; `𝒢` is any subgroup of permutations under which the law is invariant
(all permutations: part (a); strata- or size-preserving: part (b)). Monte-Carlo draws `g_1..g_B` are i.i.d. uniform on
`𝒢`, independent of the data. Upper bounds on probabilities are stated for the raw event (an outer-measure upper bound,
which is the stronger form); coverage as a measurable event of probability `≥ 1 − α`.
Caveats (critic): the unconditional use of the score claims needs `Ŝ` jointly measurable in (curve, fit) — otherwise
apply them to the conditional law; the passage from "a statistic of the pooled fit and the labels invariant under
re-indexing" to "a measurable function of the relabelled data" uses that the pooled fit is symmetric
(`τ_ℓ(σW) = τ_{ℓ∘σ}(W)`), a modelling step not formalised; the size-preserving group of (b) depends on the cluster
sizes and is covered by applying the claims to the conditional law given the sizes, as the supplement does. The
whole-group `p`-value is the supplement's `#{g ∈ 𝒢 : T(gW) ≥ T(W)}/|𝒢|` (`lem:randomisation`).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Finset

namespace StatFormal.OTFD.Conformal

/-- Conformal `p`-value `(1 + #{i ≥ 1 : S_i ≥ S_0})/(n+1)`. -/
def confPval {n : ℕ} (s : Fin (n + 1) → ℝ) : ℝ :=
  (1 + ((univ.filter fun i : Fin n => s 0 ≤ s i.succ).card : ℝ)) / (n + 1)

/-- The `k`-th smallest calibration score (`EReal`; `⊤` when `k > n`, i.e. the region is the whole space). -/
def kthCal {n : ℕ} (k : ℕ) (s : Fin (n + 1) → ℝ) : EReal :=
  sInf {t : EReal | k ≤ (univ.filter fun i : Fin n => ((s i.succ : ℝ) : EReal) ≤ t).card}

/-- The uniform law on a finite type. -/
def unif (G : Type*) [Fintype G] [MeasurableSpace G] : Measure G :=
  ((Fintype.card G : ENNReal))⁻¹ • Measure.count

/-- Exchangeability of a random score vector. -/
def Exch {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ} (S : Ω → Fin (n + 1) → ℝ) : Prop :=
  ∀ τ : Equiv.Perm (Fin (n + 1)), P.map (fun ω => S ω ∘ τ) = P.map S

namespace Claims

/-- `prop:conformal`: the conformal `p`-value is valid, `P(p ≤ α) ≤ α` for all `α ∈ (0,1)`. -/
def pval_valid : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (S : Ω → Fin (n + 1) → ℝ),
    Measurable S → Exch P S → ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | confPval (S ω) ≤ α} ≤ ENNReal.ofReal α

/-- `prop:conformal`: the central region `{S ≤ S_(⌈(1−α)(n+1)⌉)}` (whole space if the index exceeds `n`) has
coverage `≥ 1 − α`. -/
def region_coverage : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (S : Ω → Fin (n + 1) → ℝ),
    Measurable S → Exch P S → ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ P E ∧
        E ⊆ {ω | ((S ω 0 : ℝ) : EReal) ≤ kthCal ⌈(1 - α) * (n + 1)⌉₊ (S ω)}

/-- `prop:conformal`: the Bonferroni combination `min{1, 2 min(p_R, p_κ)}` of two conformal `p`-values is valid. -/
def bonferroni : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (S S' : Ω → Fin (n + 1) → ℝ),
    Measurable S → Measurable S' → Exch P S → Exch P S' → ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | min 1 (2 * min (confPval (S ω)) (confPval (S' ω))) ≤ α} ≤ ENNReal.ofReal α

/-- `prop:test`, whole group of relabellings: `p(x) = #{σ ∈ 𝒢 : T(x∘σ⁻¹) ≥ T(x)}/|𝒢|` satisfies
`P(p ≤ α) ≤ α` for every `α ∈ [0,1]`, whenever the law of `x` is `𝒢`-invariant. -/
def perm_test_full : Prop :=
  ∀ (ι Y : Type) [Fintype ι] [DecidableEq ι] [MeasurableSpace Y] (μ : Measure (ι → Y)) [IsProbabilityMeasure μ]
    (𝒢 : Subgroup (Equiv.Perm ι)) [Fintype 𝒢] (T : (ι → Y) → ℝ),
    Measurable T → (∀ σ ∈ 𝒢, μ.map (fun x => x ∘ σ.symm) = μ) → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      μ {x | ((univ.filter fun σ : 𝒢 => T x ≤ T (x ∘ (σ : Equiv.Perm ι).symm)).card : ℝ) / Fintype.card 𝒢 ≤ α}
        ≤ ENNReal.ofReal α

/-- `prop:test`, Monte Carlo: with `g_1..g_B` i.i.d. uniform on `𝒢` independent of the data,
`p = (1 + #{b : T(x∘g_b⁻¹) ≥ T(x)})/(B+1)` satisfies `P(p ≤ α) ≤ α` for every `α ∈ [0,1]`. -/
def perm_test_mc : Prop :=
  ∀ (ι Y : Type) [Fintype ι] [DecidableEq ι] [MeasurableSpace Y] (μ : Measure (ι → Y)) [IsProbabilityMeasure μ]
    (𝒢 : Subgroup (Equiv.Perm ι)) [Fintype 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (T : (ι → Y) → ℝ) (B : ℕ),
    Measurable T → (∀ σ ∈ 𝒢, μ.map (fun x => x ∘ σ.symm) = μ) → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      (μ.prod (Measure.pi fun _ : Fin B => unif 𝒢))
          {z | (1 + ((univ.filter fun b : Fin B => T z.1 ≤ T (z.1 ∘ ((z.2 b : 𝒢) : Equiv.Perm ι).symm)).card : ℝ))
              / (B + 1) ≤ α}
        ≤ ENNReal.ofReal α

end Claims
end StatFormal.OTFD.Conformal
