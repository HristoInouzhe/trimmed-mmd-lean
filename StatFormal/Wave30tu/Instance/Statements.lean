import StatFormal.Wave30tu.Statements
import StatFormal.Wave30tr.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tu, instance: the generalised estimator results at the paper's thresholds (Theorem P, Theorem A)

Printed source as in `StatFormal/Wave30tu/Statements.lean` (trimmed-mmd `0c41fb5`): `04_test.tex:177-181` ("We write `τ_{n,m}(α,δ)` for
the smallest of these valid thresholds [the closed form of `thm:plugin` and its sharper version, coupled or not] and of `τ^A_{n,m}(α,δ)`, which is valid by Theorem `thm:twosided` because
`D_{α,k}(P,Q) = 0` under the null, and which is at most `r_n(α,δ/2) + r_m(α,δ/2)` by `eq:tauA`. Each is a deterministic, nondecreasing
function of `α`, so their minimum is valid at every `α` and is nondecreasing too. One event then serves every level."), `thm:plugin`
(`04_test.tex:159-170`, constants `v² = min(κ², D_φ²/2)`, `ρ̄ = D_φ`, `:156-157`), `thm:twosided` (`04_test.tex:106-122`), and the
printed `thm:consistency`, `cor:consistency`, `thm:rate`, `cor:confset`, `cor:upperfs` (`05_estimator.tex:79-117, 137-171`,
`06_splitting.tex:232-247`).

Instantiates the frozen Wave 30tu claims with
* `τ_{n,m} := tauNM = min(τ^P, τ^A)`: `τ^P` is the frozen Wave 30tp `tauP` with `v = √min(κ², D²/2)`, `ρ̄ = D` (the closed form of
  `thm:plugin`), `τ^A` is the frozen Wave 30tr `tauA` (`eq:tauA`, `e_k` exact). **The sharper (numerically inverted, coupled or not)
  candidate of `τ_{n,m}` is not included** (its wave, 30ts, is in progress); adding it is one more application of the certified
  Wave 30tu `threshold_min` and lowers `τ_{n,m}`, so every claim below holds for the full `τ_{n,m}` once that candidate is certified
  valid, nondecreasing on `[0,1)`, continuous on `(0,1)` and `→ ∞` as `α → 1` (for `D > 0`) (the instance claims use `τ_{n,m}` only
  through `ValidThreshold`, continuity, `→ ∞` and `τ_{n,m} ≤ τ^A`). The instances of `rem:grid`, of the well-definedness sentence after
  `eq:alphaest` and of `lem:crossing` at `τ_{n,m}` are the direct compositions of the generic claims with `tauNM_threshold` (not restated).
* `τ^A := tauA` with the events `E⁺`, `E⁻` of the frozen Wave 30tr `thmA` (for every pair).

Encodings as in `StatFormal/Wave30tu/Statements.lean`; `D` is any bound on `‖φ(x) − φ(x')‖` (the printed `D_φ` is the least one); where
the decay `τ^A ≤ r_n + r_m` is used, `D ≤ 2κ` is assumed (true for `D = D_φ`, since `D_φ ≤ 2κ`). `𝒳` nonempty where no law is given.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (10 claims ACCEPT, none false; header overclaim fixed (`→ ∞` among the required properties of the sharper candidate); `rate_poly_inst` and `confset_width_inst` added as suggested). Hashed in `certify/statements.lock` (with its imports); AI agents
must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu.Instance

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu

/-- `τ_{n,m}(α,δ)` without the sharper candidate: `min(τ^P(α,δ), τ^A(α,δ))` with `v = √min(κ², D²/2)`, `ρ̄ = D`. -/
def tauNM (κ D α δ : ℝ) (n m : ℕ) : ℝ :=
  min (StatFormal.Wave30tp.tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m) (StatFormal.Wave30tr.tauA κ D α δ n m)

namespace Claims

/-! ### The thresholds satisfy the hypotheses -/

/-- `04_test.tex:177-181` and `A_basic.tex:288-291` for `τ_{n,m} = min(τ^P, τ^A)`: it is a valid threshold (`P(D̂_α > τ_{n,m}(α,δ)) ≤ δ`
for every `α ∈ [0,1)` and every pair with `TV ≤ α`), nonnegative and nondecreasing on `[0,1)`, continuous on `(0,1)`, `→ ∞` as `α → 1`
when `D > 0`, and `τ_{n,m} ≤ τ^A`. -/
def tauNM_threshold : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    Nonempty 𝒳 → StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (fun α => tauNM κ D α δ n m) ∧
        ContinuousOn (fun α => tauNM κ D α δ n m) (Ioo 0 1) ∧
        (0 < D → Tendsto (fun α => tauNM κ D α δ n m) (𝓝[<] 1) atTop) ∧
        ∀ α ∈ Ico (0 : ℝ) 1, tauNM κ D α δ n m ≤ StatFormal.Wave30tr.tauA κ D α δ n m

/-- "One event then serves every level" for `τ_{n,m}`: for every pair, one measurable event of probability `≥ 1 − δ` on which
`D̂_α ≤ τ_{n,m}(α,δ)` for every `α ∈ [0,1)` with `TV(P,Q) ≤ α` (no true `H_{0,α}` is rejected). -/
def tauNM_oneevent : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ tauNM κ D α δ n m

/-- `thm:twosided` (`τ^A` of Theorem A) as the two-sided tool: for every pair, the events `E⁺` and `E⁻` at level `δ` (with
`τ^A ≥ 0` nondecreasing on `[0,1)`), and `τ^A ≤ r_n(·,δ/2) + r_m(·,δ/2)` when `D ≤ 2κ` (`eq:tauA`). -/
def tauA_tool : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      UpperTool φ P Q n m δ (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) ∧
        LowerTool φ P Q n m δ (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) ∧
        (D ≤ 2 * κ → ∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Wave30tr.tauA κ D α δ n m ≤ tau κ α δ n m)

/-! ### The printed results at `τ_{n,m} = min(τ^P, τ^A)` and `τ^A` -/

/-- `thm:consistency` (i) at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate): `P(α̂ ≤ α*) ≥ 1 − δ` for every `n, m ≥ 1`, and `α̂ = 0` if `α* = 0`. -/
def consistency_i_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              (StatFormal.Distances.tvDist P Q = 0 → alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) = 0)}

/-- `thm:consistency` (ii) at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: under (A1)–(A3), `0 < α* < 1`, for every `ε ∈ (0,α*]` and `η ∈ (0,1)` there is `N`
with `P(α* − ε ≤ α̂ ≤ α*) ≥ 1 − δ − η` for all `n, m ≥ N`. -/
def consistency_ii_inst : Prop :=
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
            E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ∧
                  alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `cor:consistency` at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate): along any schedule with `δ → 0` and `log(1/δ)/min(n,m) → 0`, `α̂_{n,m} → α*` in probability. -/
def cor_consistency_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D : ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ) (δ : ι → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    StatFormal.TrimmedMMD.ZeroSet.Characteristic φ → StatFormal.Distances.tvDist P Q < 1 →
    (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) → (∀ i, 0 < δ i) → Tendsto δ l (𝓝 0) →
    Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0) →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α (δ i) (n i) (m i)) -
          StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-- `thm:rate` at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: with `t_{n,m} = τ_{n,m}(α*,δ) + τ^A(α*,δ')` and `ω(ε_{n,m}) = t_{n,m}`, `ε_{n,m} ∈ [0,α*]`,
`P(α* − ε_{n,m} ≤ α̂ ≤ α*) ≥ 1 − δ − δ'`. -/
def rate_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ) (ε : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    Margin φ P Q ω → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ε ∈ Icc 0 (StatFormal.Distances.tvDist P Q) →
    ω ε = tauNM κ D (StatFormal.Distances.tvDist P Q) δ n m +
      StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ∧
              alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `cor:confset` at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: `P(α̂ ≤ α* ≤ α̂ + ω^←(τ_{n,m}(α̂+,δ) + τ^A(α̂,δ'))) ≥ 1 − δ − δ'`, every `n, m ≥ 1`. -/
def confset_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) +
                omegaGen ω (tauRight (fun α => tauNM κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) +
                  StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) δ' n m)}

/-- `thm:rate`, polynomial case `ω(ε) = c₀ε^γ`, at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: if
`t = τ_{n,m}(α*,δ) + τ^A(α*,δ') ≤ c₀α*^γ`, then with probability `≥ 1 − δ − δ'`, `|α̂ − α*| ≤ (t/c₀)^{1/γ}`, and (for `D ≤ 2κ`)
`(t/c₀)^{1/γ} ≤ (24κ/(c₀(1−α*)) · √((1 + log(1/δ) + log(1/δ'))/min(n,m)))^{1/γ}`. -/
def rate_poly_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' c₀ γ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → D ≤ 2 * κ →
    StatFormal.Distances.tvDist P Q < 1 → 0 < c₀ → 0 < γ →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      c₀ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    tauNM κ D (StatFormal.Distances.tvDist P Q) δ n m + StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m ≤
      c₀ * StatFormal.Distances.tvDist P Q ^ γ →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) - StatFormal.Distances.tvDist P Q| ≤
              ((tauNM κ D (StatFormal.Distances.tvDist P Q) δ n m +
                StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m) / c₀) ^ (1 / γ)}) ∧
      ((tauNM κ D (StatFormal.Distances.tvDist P Q) δ n m +
          StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m) / c₀) ^ (1 / γ) ≤
        (24 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q)) *
          √((1 + Real.log (1 / δ) + Real.log (1 / δ')) / (min n m : ℕ))) ^ (1 / γ)

/-- The sentence after `cor:confset` at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: on one event of probability
`≥ 1 − δ − δ'` the interval covers `α*`, and whenever `α̂ < α*` its width is at most every `ε_{n,m} ∈ [0,α*]` with
`ω(ε_{n,m}) = τ_{n,m}(α*,δ) + τ^A(α*,δ')`. -/
def confset_width_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ δ' : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) +
                omegaGen ω (tauRight (fun α => tauNM κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) +
                  StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) δ' n m) ∧
              (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) < StatFormal.Distances.tvDist P Q →
                ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
                  ω ε = tauNM κ D (StatFormal.Distances.tvDist P Q) δ n m +
                    StatFormal.Wave30tr.tauA κ D (StatFormal.Distances.tvDist P Q) δ' n m →
                    omegaGen ω (tauRight (fun α => tauNM κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) +
                      StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) δ' n m) ≤ ε)}

/-- `cor:upperfs` at `τ^A`: with `Ď_α = D̂_α + τ^A(α,δ)`, with probability `≥ 1 − δ`, `D_α ≤ Ď_α` for every `α ∈ [0,1)` and
`TV(P,Q) ≤ α̂_hi`. -/
def upperfs_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | (∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m) ∧
              StatFormal.Distances.tvDist P Q ≤
                alphaHi ω (fun α => Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m)}

/-- The sentence after `cor:upperfs` at `τ_{n,m} = min(τ^P, τ^A)` (no sharper candidate) and `τ^A`: one event of probability `≥ 1 − 2δ` on which
`α̂ ≤ α* ≤ α̂_hi ≤ α̂ + ω^←(τ_{n,m}(α̂+,δ) + τ^A(α̂,δ))`. -/
def upperfs_interval_inst : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → StatFormal.Distances.tvDist P Q < 1 →
    KnownMargin φ P Q ω → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - 2 * δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤
                alphaHi ω (fun α => Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m) ∧
              alphaHi ω (fun α => Demp φ z.1 z.2 α + StatFormal.Wave30tr.tauA κ D α δ n m) ≤
                alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m) +
                  omegaGen ω (tauRight (fun α => tauNM κ D α δ n m) (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) +
                    StatFormal.Wave30tr.tauA κ D (alphaHat (Demp φ z.1 z.2) (fun α => tauNM κ D α δ n m)) δ n m)}

end Claims
end StatFormal.Wave30tu.Instance
