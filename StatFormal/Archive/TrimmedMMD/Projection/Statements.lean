import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# FROZEN STATEMENTS — trimmed MMD: projection stability (supplement §S, `lem:minkhaus`,
`lem:projstab`, `def:sharp`, `prop:sharprate`) and `rem:ratioregime`

Sources (`trimmed-mmd/supplement.tex:653-812`, `paper.tex:1557-1562, 1644`), verbatim in
`inventory/extracted/trimmed-mmd.md`. Setting: a real Hilbert space `E`.
* "`η ≥ d_H(C,C')` finite" is encoded with the extended Hausdorff distance
  `Metric.hausdorffEDist C C' ≤ ENNReal.ofReal η` (Mathlib's real `hausdorffDist` is junk `0` when the
  sets are at infinite distance).
* `p = Π_C(0)` is encoded as "`p ∈ C` and `‖p‖ ≤ ‖q‖` for all `q ∈ C`" (existence/uniqueness is the
  projection theorem, already in Mathlib).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Real Set Metric
open scoped Pointwise

namespace StatFormal.TrimmedMMD.Projection

/-- `p` is the minimum-norm element of `C`. -/
def IsMinNorm {E : Type*} [NormedAddCommGroup E] (C : Set E) (p : E) : Prop :=
  p ∈ C ∧ ∀ q ∈ C, ‖p‖ ≤ ‖q‖

/-- `def:sharp`: `p` is `(θ,ρ)`-sharp in `C`. -/
def IsSharp {E : Type*} [NormedAddCommGroup E] (C : Set E) (p : E) (θ ρ : ℝ) : Prop :=
  ∀ q ∈ C, ‖q - p‖ ≤ ρ → ‖p‖ + θ * ‖q - p‖ ≤ ‖q‖

namespace Claims

/-- `lem:minkhaus`: for nonempty bounded sets, Hausdorff distance is subadditive under Minkowski sums,
invariant under negation, and hence subadditive under Minkowski differences. -/
def lem_minkhaus : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A A' B B' : Set E),
    A.Nonempty → A'.Nonempty → B.Nonempty → B'.Nonempty →
    Bornology.IsBounded A → Bornology.IsBounded A' → Bornology.IsBounded B → Bornology.IsBounded B' →
      hausdorffDist (A + B) (A' + B') ≤ hausdorffDist A A' + hausdorffDist B B' ∧
      hausdorffDist (-B) (-B') = hausdorffDist B B' ∧
      hausdorffDist (A - B) (A' - B') ≤ hausdorffDist A A' + hausdorffDist B B'

/-- `lem:projstab` (i)–(iii). -/
def lem_projstab : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C C' : Set E) (p p' : E) (η : ℝ),
    C.Nonempty → C'.Nonempty → Convex ℝ C → Convex ℝ C' → IsClosed C → IsClosed C' →
    0 ≤ η → Metric.hausdorffEDist C C' ≤ ENNReal.ofReal η →
    IsMinNorm C p → IsMinNorm C' p' →
      |‖p‖ - ‖p'‖| ≤ η ∧
      ‖p - p'‖ ≤ η + min (√((‖p'‖ + η) ^ 2 - ‖p‖ ^ 2)) (√((‖p‖ + η) ^ 2 - ‖p'‖ ^ 2)) ∧
      ‖p - p'‖ ≤ η + √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) ∧
      η + √(2 * η * min ‖p‖ ‖p'‖ + η ^ 2) ≤ √(2 * η * min ‖p‖ ‖p'‖) + 2 * η

/-- `prop:sharprate`, as stated: if `p` is `(θ,ρ)`-sharp and `√(2ηD+η²) ≤ ρ` then
`‖p − p'‖ ≤ (1 + 2/θ) η`. -/
def prop_sharprate : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C C' : Set E) (p p' : E) (η θ ρ : ℝ),
    C.Nonempty → C'.Nonempty → Convex ℝ C → Convex ℝ C' → IsClosed C → IsClosed C' →
    0 ≤ η → Metric.hausdorffEDist C C' ≤ ENNReal.ofReal η →
    IsMinNorm C p → IsMinNorm C' p' →
    0 < θ → θ ≤ 1 → 0 < ρ → IsSharp C p θ ρ → √(2 * η * ‖p‖ + η ^ 2) ≤ ρ →
      ‖p - p'‖ ≤ (1 + 2 / θ) * η

/-- Strengthening (critic/inventory observation): on a convex set local sharpness is global, so the
side condition on `η` is unnecessary. -/
def prop_sharprate_global : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C C' : Set E) (p p' : E) (η θ ρ : ℝ),
    C.Nonempty → C'.Nonempty → Convex ℝ C → Convex ℝ C' → IsClosed C → IsClosed C' →
    0 ≤ η → Metric.hausdorffEDist C C' ≤ ENNReal.ofReal η →
    IsMinNorm C p → IsMinNorm C' p' →
    0 < θ → θ ≤ 1 → 0 < ρ → IsSharp C p θ ρ →
      ‖p - p'‖ ≤ (1 + 2 / θ) * η

/-- The proof of `prop:sharprate` (supplement l.810) uses `√((D'+η)²−D²) ≤ √(2ηD+η²)` given only
`|D−D'| ≤ η`; that step is false (REVIEW_REPORT T4-5). -/
def sharprate_proof_step_false : Prop :=
  ¬ ∀ D D' η : ℝ, 0 ≤ D → 0 ≤ D' → 0 ≤ η → |D - D'| ≤ η →
      √((D' + η) ^ 2 - D ^ 2) ≤ √(2 * η * D + η ^ 2)

/-- `rem:ratioregime` (paper l.1644) says the bound `√(2ηD) + 2η` of `eq:witnessstab` "tends to `3η`"
as `D ↓ 0`; it tends to `2η` (REVIEW_REPORT T4-7). -/
def ratioregime_limit : Prop :=
  ∀ η : ℝ, 0 ≤ η →
    Filter.Tendsto (fun D : ℝ => √(2 * η * D) + 2 * η) (nhdsWithin 0 (Ici 0)) (nhds (2 * η))

/-- `rem:ratioregime`, middle member of `eq:witnessstab`: `η + √(2ηD + η²) → 2η` as `D ↓ 0` (also not
`3η`). -/
def ratioregime_limit_mid : Prop :=
  ∀ η : ℝ, 0 ≤ η →
    Filter.Tendsto (fun D : ℝ => η + √(2 * η * D + η ^ 2)) (nhdsWithin 0 (Ici 0)) (nhds (2 * η))

end Claims
end StatFormal.TrimmedMMD.Projection
