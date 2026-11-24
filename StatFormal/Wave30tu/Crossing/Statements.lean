import StatFormal.Wave30tu.Full.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tu, `lem:crossing` without continuity of the threshold, and at the full `τ_{n,m}`

Printed source: `trimmed-mmd/jmlr/` at master `9b754c8` (sha256 as in `StatFormal/Wave30tu/Full/Statements.lean`): `lem:crossing`
(`A_basic.tex:264-273`), the paragraph after `eq:alphaest` (`05_estimator.tex:26-31`).

The printed `lem:crossing` assumes `τ` continuous on `(0,1)`; the frozen generic `Wave30tu.Claims.crossing`, `crossing_meas` carry that
hypothesis for all clauses, and continuity of the sharper candidate `τ^{P'}` is not certified (Wave 30ts). Every clause except
"`S = [α̂,1)` if `α̂ > 0`" holds for any nondecreasing `τ` (generalisation), and `α̂` is measurable without assuming the crossing set
nonempty (strengthening: if `S = ∅` then `α̂ = sInf ∅ = 0`, and `{S = ∅}` is measurable). Frozen here, generically (`crossing_nc`) and at
the full `τ_{n,m} = min{τ^A, τ^P, τ^{P'}}` of `StatFormal/Wave30tu/Full/Statements.lean` (`crossing_full`; the coupled and grid versions are
the same composition with `tauFullCpl_threshold`, `tauFullGrid_threshold`). Encodings as in `StatFormal/Wave30tu/Statements.lean`.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (2 claims ACCEPT, header ACCEPT). Hashed in `certify/statements.lock` (with its imports); AI agents
must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu.Crossing

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu StatFormal.Wave30tu.Full

namespace Claims

/-- `lem:crossing (v2)` for any `τ : [0,1) → [0,∞)` nondecreasing (no continuity): for every realization with a nonempty crossing set
`S`, the path is continuous and nonincreasing on `[0,1)`, `(α̂,1) ⊆ S` and `D̂_{α̂} ≤ τ(α̂+)`; if `S` is nonempty for every realization,
`{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0,a)} {D̂_q ≤ τ(q)}` for every `a`; and `α̂` is a measurable function of the samples. -/
def crossing_nc : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) →
      (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty →
        (ContinuousOn (Demp φ x y) (Ico 0 1) ∧ AntitoneOn (Demp φ x y) (Ico 0 1)) ∧
        Ioo (alphaHat (Demp φ x y) τ) 1 ⊆ crossSet (Demp φ x y) τ ∧
        Demp φ x y (alphaHat (Demp φ x y) τ) ≤ tauRight τ (alphaHat (Demp φ x y) τ)) ∧
      ((∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty) →
        ∀ a : ℝ, {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ < a} =
          ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < a), {z | Demp φ z.1 z.2 q ≤ τ q}) ∧
      Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ

/-- `lem:crossing (v2)` and the paragraph after `eq:alphaest` at the full `τ_{n,m} = min{τ^A, τ^P, τ^{P'}}` (general kernel): for every
realization with a nonempty crossing set, `(α̂,1) ⊆ S` and `D̂_{α̂} ≤ τ_{n,m}(α̂+,δ)`; and `α̂` is a measurable function of the
samples. -/
def crossing_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) (fun α => tauFull κ D α δ n m)).Nonempty →
        Ioo (alphaHat (Demp φ x y) (fun α => tauFull κ D α δ n m)) 1 ⊆
            crossSet (Demp φ x y) (fun α => tauFull κ D α δ n m) ∧
          Demp φ x y (alphaHat (Demp φ x y) (fun α => tauFull κ D α δ n m)) ≤
            tauRight (fun α => tauFull κ D α δ n m) (alphaHat (Demp φ x y) (fun α => tauFull κ D α δ n m))) ∧
      Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)

end Claims
end StatFormal.Wave30tu.Crossing
