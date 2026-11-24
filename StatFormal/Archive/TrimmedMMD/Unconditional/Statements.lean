import StatFormal.Archive.TrimmedMMD.Concentration.Statements

/-!
# FROZEN STATEMENTS — trimmed MMD: the threshold estimator, unconditionally

Sources: `eq:setdist` (`prop:georep`, `paper.tex:653`), `eq:radius` (`:775`), `cor:uniform` (`:785`),
`eq:alphaest` (`:903`), `thm:consistency` (i) (`:964`), `ass:margin` + `thm:rate` (`:1004-1018`).
The frozen `TrimmedMMD/Statements.lean` certifies these **conditionally** on two concentration events `EP`, `EQ`;
here the events are constructed (from `cor:uniform` for each sample) and the conclusions are unconditional.

Encodings (see card):
* setting of `TrimmedMMD/Concentration/Statements.lean` (separable Hilbert space, strongly measurable feature map
  `‖φ‖ ≤ κ`); two independent samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)`;
* `D_{α,k}(P,Q)` is the distance between the trimmed regions, `inf{‖a − b‖ : a ∈ 𝒞_{α,k}(P), b ∈ 𝒞_{α,k}(Q)}`
  (`eq:setdist`; that this equals the infimum of MMD over trimmings is `prop:georep`, not formalised here — it
  is the definition of the regions as the embeddings of the trimmings), and `D̂_α` the same for `P_n, Q_m`;
* the properties of `D` used by the theorems (`D(α*) = 0`, `ass:margin`) remain hypotheses, as in the paper; the
  theorems hold for any `α* ∈ [0,1)` with `D(α*) = 0` — the paper's `α* = TV(P,Q)` needs `D(TV) = 0`
  (`eq:zeroeq` ⇐ via `eq:tvintersect`), not formalised here. "Unconditional" means: free of the concentration
  events (they are constructed), not of the link to TV;
* `EP`, `EQ` are cylinder sets, each determined by one sample;
* every probability is stated as a **measurable** event of probability `≥ 1 − δ` inside the claimed event
  (stronger than the conditional claims' outer-measure form, critic note N1).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.TrimmedMMD.Unconditional

open StatFormal.TrimmedMMD.Concentration

/-- Distance between two sets of a normed space, `inf{‖a − b‖ : a ∈ A, b ∈ B}`. -/
def setDist {H : Type*} [NormedAddCommGroup H] (A B : Set H) : ℝ :=
  sInf {r | ∃ a ∈ A, ∃ b ∈ B, r = ‖a - b‖}

/-- `D_{α,k}(P,Q)` (`eq:setdist`). -/
def Dpop {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : ℝ :=
  setDist (region φ α P) (region φ α Q)

/-- `D̂_α = D_{α,k}(P_n, Q_m)`. -/
def Demp {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α : ℝ) : ℝ :=
  setDist (region φ α (empirical x)) (region φ α (empirical y))

namespace Claims

/-- The concentration events: measurable `EP` (first sample) and `EQ` (second sample), each of probability
`≥ 1 − δ/2`, on whose intersection `|D̂_α − D_α| ≤ τ_{n,m}(α,δ)` for every `α ∈ [0,1)`. -/
def events : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ (AP : Set (Fin n → 𝒳)) (AQ : Set (Fin m → 𝒳)), MeasurableSet AP ∧ MeasurableSet AQ ∧
        let EP := Prod.fst ⁻¹' AP; let EQ := Prod.snd ⁻¹' AQ
        ENNReal.ofReal (1 - δ / 2) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) EP ∧
        ENNReal.ofReal (1 - δ / 2) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) EQ ∧
        ∀ z ∈ EP ∩ EQ, ∀ α ∈ Ico (0 : ℝ) 1,
          |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ StatFormal.TrimmedMMD.tau κ α δ n m

/-- `thm:consistency` (i), unconditional: if `D_{α*} = 0` then `α̂ ≤ α*` on a measurable event of probability
`≥ 1 − δ`, for every `n, m ≥ 1`. -/
def consistency_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ αs : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    αs ∈ Ico (0 : ℝ) 1 → Dpop φ P Q αs = 0 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) ≤ αs}

/-- `thm:consistency` (i), second half, unconditional: if `D_0 = 0` then `α̂ = 0` exactly on a measurable event of
probability `≥ 1 − δ`. -/
def consistency_i_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    Dpop φ P Q 0 = 0 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) = 0}

/-- `thm:rate` under `ass:margin`, unconditional: `α* − ε_{n,m} ≤ α̂ ≤ α*` on a measurable event of probability
`≥ 1 − δ`, with `ε_{n,m} = ω⁻¹(2τ_{n,m}(α*))`. -/
def rate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ αs : ℝ) (n m : ℕ) (om : ℝ → ℝ) (ε : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    αs ∈ Ico (0 : ℝ) 1 → Dpop φ P Q αs = 0 →
    StrictMonoOn om (Icc 0 αs) → (∀ e ∈ Icc (0 : ℝ) αs, om e ≤ Dpop φ P Q (αs - e)) →
    ε ∈ Icc (0 : ℝ) αs → om ε = 2 * StatFormal.TrimmedMMD.tau κ αs δ n m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2)
              (fun α => StatFormal.TrimmedMMD.tau κ α δ n m) ∈ Icc (αs - ε) αs}

end Claims
end StatFormal.TrimmedMMD.Unconditional
