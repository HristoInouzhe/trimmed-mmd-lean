import StatFormal.Wave30tu.Instance.Statements
import StatFormal.Wave30ts.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tu, full instance: the v2 estimator results at the paper's full `τ_{n,m}` (with the sharper candidate)

Printed source: `trimmed-mmd/jmlr/` at master `9b754c8` (read-only, read 2026-11-08; sha256 `sections/04_test.tex` `26902166…`,
`sections/05_estimator.tex` `d1d8f75a…`, `sections/06_splitting.tex` `58506daf…`, `appendix/A_basic.tex` `68f03031…` (last changed at
`9f11e18`), `appendix/B_split.tex` `4355a4d8…`): `04_test.tex:177-181` (`τ_{n,m}` = the smallest of the plug-in thresholds — the closed
form of `thm:plugin`, its sharper version, coupled or not — and of `τ^A_{n,m}`), `A_basic.tex:437-473` (the sharper threshold), the printed
`thm:consistency`, `cor:consistency`, the rate-condition sentence, `thm:rate`, `cor:confset` (`05_estimator.tex:79-171`), `cor:upperfs` and
the sentence after it (`06_splitting.tex:238-253`). Relative to `0c41fb5` (the source of the other two frozen files), `adb8e08` and
`9f11e18` aligned the sharper paragraph with the Wave 30ts encoding (roots `t₁, t₂ ≥ 0` as infima in `[0,∞)`, `K` as lists, `u ∈ [0,κ²)`,
the `‖μ_R‖ = κ` remark); the meaning of `tauPs`, `tauCpl`, `tauGrid` is unchanged, and the other target passages are verbatim unchanged
(lines moved in `06_splitting.tex`, `B_split.tex`).

Completes `StatFormal/Wave30tu/Instance/Statements.lean` (which has `τ_{n,m} = min(τ^P, τ^A)`) with the sharper candidate `τ^{P'}` of the
frozen Wave 30ts (`tauPs`; coupled `tauCpl`; the implemented grid form `tauGrid`), whose validity, monotonicity and one-event property
for the minimum are the certified Wave 30ts `corollary_C`, `corollary_C_coupled`, `corollary_C_grid` (with `τ^A` valid by the certified
Wave 30tr `thmA`):
* `tauFull = min{τ^A, τ^P, τ^{P'}}` (general kernel), `tauFullCpl = min{τ^A, τ^P, τ^{P'}, τ^{cpl}_{P'}}` (`k ≥ 0`, `k(x,x) ≡ κ²`),
  `tauFullGrid = min{τ^A, τ^P, τ^{P'}, τ_grid}` (as implemented), all with `v = √min(κ², D²/2)`, `ρ̄ = D`, in the order of Corollary C.
* The printed results that use `τ_{n,m}` only through its validity and `τ_{n,m} ≤ τ^A` are instantiated at `tauFull`
  (`thm:consistency` (i), (ii), `cor:consistency`, `thm:rate`, `cor:confset`, the `1 − 2δ` sentence after `cor:upperfs`); at the coupled and
  grid versions they are the same compositions of the generic Wave 30tu claims with `tauFullCpl_threshold`, `tauFullGrid_threshold`.
* Not stated (declared): continuity of `τ^{P'}` on `(0,1)` and `τ^{P'} → ∞` (not certified in Wave 30ts), hence the clause "`S = [α̂,1)` if
  `α̂ > 0`" of `lem:crossing` and the well-definedness sentence after `eq:alphaest` at the full `τ_{n,m}` (on the events of the claims
  below the crossing set always contains `α*`).
* The rate-condition example at the full `τ_{n,n}` at the Gaussian constants: general kernel (`ratecond_full`), and — the printed
  Gaussian case, since the Gaussian kernel has `k ≥ 0` and constant diagonal — with the coupled candidate (`ratecond_full_cpl`: the
  family defining `τ^{cpl}_{P'}(0)` is bounded above by the McDiarmid root and its `u = 0` member is `≥ D_φ`) and with the implemented grid
  form (`ratecond_full_grid`: the cell containing `u = 0` has `v_j ≥ κ`).

Encodings as in `StatFormal/Wave30tu/Statements.lean`; `D` any bound on `‖φ(x) − φ(x')‖`; `D ≤ 2κ` where `τ^A ≤ r_n + r_m` is used.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (10 claims ACCEPT, none false; header updated to `9b754c8`; `ratecond_full_cpl`, `ratecond_full_grid` added for the printed Gaussian case, ACCEPT). Hashed in `certify/statements.lock` (with its imports); AI agents
must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.Wave30tu.Full

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu

/-- The paper's `τ_{n,m}(α,δ)`, general kernel: `min{τ^A, τ^P, τ^{P'}}` with `v = √min(κ², D²/2)`, `ρ̄ = D`. -/
def tauFull (κ D α δ : ℝ) (n m : ℕ) : ℝ :=
  min (StatFormal.Wave30tr.tauA κ D α δ n m)
    (min (StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)
      (StatFormal.Wave30ts.tauPs D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m))

/-- The paper's `τ_{n,m}(α,δ)` with the coupled sharper candidate (`k ≥ 0`, constant diagonal):
`min{τ^A, τ^P, τ^{P'}, τ^{cpl}_{P'}}`. -/
def tauFullCpl (κ D α δ : ℝ) (n m : ℕ) : ℝ :=
  min (StatFormal.Wave30tr.tauA κ D α δ n m)
    (min (StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)
      (min (StatFormal.Wave30ts.tauPs D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)
        (StatFormal.Wave30ts.tauCpl D κ α δ n m)))

/-- The implemented `τ_{n,m}(α,δ)` with the grid form of the coupled candidate: `min{τ^A, τ^P, τ^{P'}, τ_grid}`. -/
def tauFullGrid (κ D : ℝ) (vg ρg : ℕ → ℝ) (J : ℕ) (α δ : ℝ) (n m : ℕ) : ℝ :=
  min (StatFormal.Wave30tr.tauA κ D α δ n m)
    (min (StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)
      (min (StatFormal.Wave30ts.tauPs D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m)
        (StatFormal.Wave30ts.tauGrid D vg ρg J α δ n m)))

namespace Claims

/-! ### The full threshold satisfies the hypotheses (`04_test.tex:177-181`) -/

/-- The full `τ_{n,m}` (general kernel) is a valid threshold (nonnegative, nondecreasing on `[0,1)`, `P(D̂_α > τ_{n,m}(α,δ)) ≤ δ` for
every `α` and every pair with `TV ≤ α`), `τ_{n,m} ≤ τ^A`, `τ_{n,m} ≤ r_n(·,δ/2) + r_m(·,δ/2)` when `D ≤ 2κ`, and for every pair one
event of probability `≥ 1 − δ` serves every level. -/
def tauFull_threshold : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (fun α => tauFull κ D α δ n m) ∧
        (∀ α ∈ Ico (0 : ℝ) 1, tauFull κ D α δ n m ≤ StatFormal.Wave30tr.tauA κ D α δ n m) ∧
        (D ≤ 2 * κ → ∀ α ∈ Ico (0 : ℝ) 1, tauFull κ D α δ n m ≤ tau κ α δ n m) ∧
        ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ tauFull κ D α δ n m

/-- The same for the coupled full `τ_{n,m}` (kernel with `k ≥ 0` and `k(x,x) ≡ κ²`). -/
def tauFullCpl_threshold : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (fun α => tauFullCpl κ D α δ n m) ∧
        (∀ α ∈ Ico (0 : ℝ) 1, tauFullCpl κ D α δ n m ≤ StatFormal.Wave30tr.tauA κ D α δ n m) ∧
        (D ≤ 2 * κ → ∀ α ∈ Ico (0 : ℝ) 1, tauFullCpl κ D α δ n m ≤ tau κ α δ n m) ∧
        ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ tauFullCpl κ D α δ n m

/-- The same for the implemented full `τ_{n,m}` with the grid form of the coupled candidate (the grid of cells `[lo j, hi j]`, `j < J`,
covering `[0,κ²]`, with corner constants `vg j`, `ρg j` as in the frozen Wave 30ts `corollary_C_grid`). -/
def tauFullGrid_threshold : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (J : ℕ) (lo hi vg ρg : ℕ → ℝ) (δ : ℝ) (n m : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j) →
    (∀ j < J, 0 ≤ vg j ∧ κ ^ 2 - lo j ≤ vg j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρg j) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (fun α => tauFullGrid κ D vg ρg J α δ n m) ∧
        (∀ α ∈ Ico (0 : ℝ) 1, tauFullGrid κ D vg ρg J α δ n m ≤ StatFormal.Wave30tr.tauA κ D α δ n m) ∧
        (D ≤ 2 * κ → ∀ α ∈ Ico (0 : ℝ) 1, tauFullGrid κ D vg ρg J α δ n m ≤ tau κ α δ n m) ∧
        ∀ P Q : Measure 𝒳, IsProbabilityMeasure P → IsProbabilityMeasure Q →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α →
              Demp φ z.1 z.2 α ≤ tauFullGrid κ D vg ρg J α δ n m

/-! ### The printed results at the full `τ_{n,m}` (general kernel) and `τ^A` -/

/-- `thm:consistency` (i) at the full `τ_{n,m}`: `P(α̂ ≤ α*) ≥ 1 − δ` for every `n, m ≥ 1`, and `α̂ = 0` if `α* = 0`. -/
def consistency_i_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              (StatFormal.Distances.tvDist P Q = 0 → alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) = 0)}

/-- `thm:consistency` (ii) at the full `τ_{n,m}` and `τ^A`: under (A1)–(A3), `0 < α* < 1`, for every `ε ∈ (0,α*]` and `η ∈ (0,1)` there
is `N` with `P(α* − ε ≤ α̂ ≤ α*) ≥ 1 − δ − η` for all `n, m ≥ N`. -/
def consistency_ii_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    StatFormal.TrimmedMMD.ZeroSet.Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 → 0 < δ → δ < 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (StatFormal.Distances.tvDist P Q), ∀ η : ℝ, 0 < η → η < 1 →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → 1 ≤ n → 1 ≤ m →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ - η) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ∧
                  alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `cor:consistency` at the full `τ_{n,m}`: along any schedule with `δ → 0` and `log(1/δ)/min(n,m) → 0`, `α̂_{n,m} → α*` in
probability. -/
def cor_consistency_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D : ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ) (δ : ι → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    StatFormal.TrimmedMMD.ZeroSet.Characteristic φ → StatFormal.Distances.tvDist P Q < 1 →
    (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) → (∀ i, 0 < δ i) → Tendsto δ l (𝓝 0) →
    Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0) →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α (δ i) (n i) (m i)) -
          StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-- `thm:rate` at the full `τ_{n,m}` and `τ^A`: with `ω(ε_{n,m}) = τ_{n,m}(α*,δ) + τ^A(α*,δ')`, `ε_{n,m} ∈ [0,α*]`,
`P(α* − ε_{n,m} ≤ α̂ ≤ α*) ≥ 1 − δ − δ'`. -/
def rate_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ) (ε : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    Margin φ P Q ω → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ε ∈ Icc 0 (StatFormal.Distances.tvDist P Q) →
    ω ε = tauFull κ D (StatFormal.Distances.tvDist P Q) δ n m +
      StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ∧
              alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `cor:confset` at the full `τ_{n,m}` and `τ^A`: `P(α̂ ≤ α* ≤ α̂ + ω^←(τ_{n,m}(α̂+,δ) + τ^A(α̂,δ'))) ≥ 1 − δ − δ'`. -/
def confset_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) +
                omegaGen ω (tauRight (fun α => tauFull κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)) +
                  StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)) δ' n m)}

/-- The sentence after `cor:upperfs` at the full `τ_{n,m}` and `τ^A`: one event of probability `≥ 1 − 2δ` on which
`α̂ ≤ α* ≤ α̂_hi ≤ α̂ + ω^←(τ_{n,m}(α̂+,δ) + τ^A(α̂,δ))`. -/
def upperfs_interval_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - 2 * δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤
                alphaHi ω (fun α => Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m) ∧
              alphaHi ω (fun α => Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m) ≤
                alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m) +
                  omegaGen ω (tauRight (fun α => tauFull κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)) +
                    StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauFull κ D α δ n m)) δ n m)}

/-- "The rate condition cannot be dropped" at the full `τ_{n,n}` (general kernel) for the Gaussian constants (`‖φ‖ ≤ κ`,
`D_φ = √2κ`, so `v = √min(κ², D_φ²/2) = κ`), `δ = e^{−n}`: `τ_{n,n}(α,δ) ≥ D_φ` at every `α ∈ [0,1)` and `α̂_{n,n} = 0` for every sample
(with `ratecond_noconv`: `α̂_{n,n}` does not converge to `α* > 0`). -/
def ratecond_full : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ √2 * κ) → 0 < κ → 1 ≤ n →
      (∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFull κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) ∧
        ∀ x y : Fin n → 𝒳, alphaHat (Demp φ x y) (fun α => tauFull κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) = 0

/-- "The rate condition cannot be dropped" for the Gaussian kernel as printed: a kernel with `k ≥ 0` and `k(x,x) ≡ κ²` (`κ > 0`) and
`D_φ = √2κ`, whose `τ_{n,n}` includes the coupled candidate, `δ = e^{−n}`: `τ_{n,n}(α,δ) ≥ D_φ` at every `α ∈ [0,1)` and `α̂_{n,n} = 0` for
every sample. -/
def ratecond_full_cpl : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (n : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ √2 * κ) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) → 0 < κ → 1 ≤ n →
      (∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFullCpl κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) ∧
        ∀ x y : Fin n → 𝒳, alphaHat (Demp φ x y) (fun α => tauFullCpl κ (√2 * κ) α (Real.exp (-(n : ℝ))) n n) = 0

/-- The same with the implemented grid form of the coupled candidate (a grid as in `tauFullGrid_threshold`). -/
def ratecond_full_grid : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (J : ℕ) (lo hi vg ρg : ℕ → ℝ) (n : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ √2 * κ) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j) →
    (∀ j < J, 0 ≤ vg j ∧ κ ^ 2 - lo j ≤ vg j ^ 2 ∧ min (√(κ ^ 2 + hi j)) (√2 * κ) ≤ ρg j) → 0 < κ → 1 ≤ n →
      (∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ tauFullGrid κ (√2 * κ) vg ρg J α (Real.exp (-(n : ℝ))) n n) ∧
        ∀ x y : Fin n → 𝒳,
          alphaHat (Demp φ x y) (fun α => tauFullGrid κ (√2 * κ) vg ρg J α (Real.exp (-(n : ℝ))) n n) = 0

end Claims
end StatFormal.Wave30tu.Full
