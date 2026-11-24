import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Lib.Distances.TV

/-!
# FROZEN STATEMENTS — trimmed MMD: the zero set of `D_α` and `α* = TV(P,Q)`

Sources: `eq:trimset` (`trimmed-mmd/paper.tex:83`), `eq:tvintersect` (`:94`, after Álvarez-Esteban et al. 2012),
`eq:zeroeq` (`:598`, "the forward direction uses attainment of the infimum", `lem:attainment` `:673`),
`ass:regularity` (A3, characteristic kernel), `thm:consistency` (`:964`, `α* = TV(P,Q)`).
Closes the gap declared in `TrimmedMMD/Unconditional`: there the theorems hold for any `α*` with `D_{α*} = 0`.

Covered:
* `tvintersect`: `TV(P,Q) ≤ α ⇔ P` and `Q` share an `α`-trimming (`α ∈ [0,1)`);
* `zero_of_tv_le`: `TV(P,Q) ≤ α < 1 ⇒ D_α(P,Q) = 0` (no characteristic kernel needed);
* `zeroeq`: for a characteristic feature map (A3), `D_α(P,Q) = 0 ⇔ TV(P,Q) ≤ α` (`α ∈ [0,1)`);
* `consistency_tv`, `consistency_tv_zero`: `thm:consistency` (i), both halves, at the paper's `α* = TV(P,Q)` (when
  `TV < 1`), unconditionally and without A3 (the paper assumes A3 for the theorem; part (i) does not need it).

Encodings (see card): setting of `TrimmedMMD/Concentration` and `Unconditional` (`region`, `Dpop`, `Demp`, `tau`,
`alphaHat`); an `α`-trimming of `P` is `P.withDensity g` with `g` measurable, `0 ≤ g ≤ 1/(1−α)`, `∫ g dP = 1`
(`eq:trimset`); `TV` is `StatFormal.Distances.tvDist` (`sup_A |P(A) − Q(A)|`, the paper's `d_TV`); "characteristic"
(A3) is: for probability measures `μ, ν`, `∫ φ dμ = ∫ φ dν ⇒ μ = ν` (MMD = norm of the embedding difference).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.TrimmedMMD.ZeroSet

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-- `g` is the density of an `α`-trimming of `P` (`eq:trimset`). -/
def IsTrimDensity {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (α : ℝ) (g : 𝒳 → ℝ) : Prop :=
  Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) ∧ ∫ x, g x ∂P = 1

/-- The feature map is characteristic (A3): the mean embedding is injective on probability measures. -/
def Characteristic {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) : Prop :=
  ∀ μ ν : Measure 𝒳, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∫ x, φ x ∂μ = ∫ x, φ x ∂ν → μ = ν

namespace Claims

/-- `eq:tvintersect`: `TV(P,Q) ≤ α ⇔ R_α(P) ∩ R_α(Q) ≠ ∅`. -/
def tvintersect : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ), 0 ≤ α → α < 1 →
      (StatFormal.Distances.tvDist P Q ≤ α ↔
        ∃ gP gQ : 𝒳 → ℝ, IsTrimDensity P α gP ∧ IsTrimDensity Q α gQ ∧
          P.withDensity (fun x => ENNReal.ofReal (gP x)) = Q.withDensity (fun x => ENNReal.ofReal (gQ x)))

/-- `eq:zeroeq`, backward direction: `TV(P,Q) ≤ α < 1 ⇒ D_α(P,Q) = 0` (any bounded feature map). -/
def zero_of_tv_le : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      StatFormal.Distances.tvDist P Q ≤ α → Dpop φ P Q α = 0

/-- `eq:zeroeq`: for a characteristic feature map, `D_α(P,Q) = 0 ⇔ TV(P,Q) ≤ α`, `α ∈ [0,1)`. -/
def zeroeq : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → Characteristic φ → 0 ≤ α → α < 1 →
      (Dpop φ P Q α = 0 ↔ StatFormal.Distances.tvDist P Q ≤ α)

/-- `thm:consistency` (i) at the paper's `α* = TV(P,Q)`: if `TV(P,Q) < 1`, then `α̂ ≤ TV(P,Q)` on a measurable
event of probability `≥ 1 − δ`, for every `n, m ≥ 1` (no characteristic kernel needed for this half). -/
def consistency_tv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Distances.tvDist P Q < 1 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `thm:consistency` (i), second half, at `α* = TV(P,Q)`: if `TV(P,Q) = 0` then `α̂ = 0` on a measurable event of
probability `≥ 1 − δ`. -/
def consistency_tv_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Distances.tvDist P Q = 0 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) = 0}

end Claims
end StatFormal.TrimmedMMD.ZeroSet
