import StatFormal.Wave30tu.Crossing.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tw: trimmed-mmd (JMLR revision v2), continuity of the sharper threshold and the crossing set at the full `τ_{n,m}`

Printed source: `trimmed-mmd/jmlr/` at trimmed-mmd master `81716bd` ("JMLR v2: estimator results certified in Lean at the paper's
threshold (Wave30tu, gate 3611); minor print fixes from its audit"; read-only, read 2026-11-08; sha256 `appendix/A_basic.tex`
`6cda1e04ccad03f83b4b92175b96584eabb58911728c8e1970019bcab1ec4a1f`, `sections/05_estimator.tex`
`e5eaa21842071db38546afceeedd1865ce0ed7afcbf423b692d26286c3f419b9`, `sections/04_test.tex`
`bbd28b351d253f1ec3ad801ab38f9061d7e00a6fc2239f501e736ec433107a3e`):
* `A_basic.tex:288-291`, the paragraph after the proof of `lem:crossing`: "The thresholds of Section `sec:thetest` satisfy the
  hypotheses of Lemma `lem:crossing`. Each candidate is continuous and nondecreasing on `(0,1)`, the numerical ones because the tail
  bounds are continuous, and strictly decreasing in `t` where they are below `1`, so their roots are continuous in `β`. The set is
  nonempty because every candidate tends to infinity as `α → 1` when `D_φ > 0`; if `D_φ = 0`, then `D̂_{α,k} ≡ 0` and the set is
  `[0,1)`."
* `A_basic.tex:437-473`, "The sharper threshold": `Ψ_H(t;β,s',c') = min{McDiarmid, Pinelis}` (`a = βρ̄c'`, `b² = βv²s'`), `Ψ_R(t;β,K) =
  inf_{λ>0} e^{−λt} ∏_{k∈K} [β⁻¹e^{λ(1−β)/k} + (1−β⁻¹)e^{λ/k}]^k` for the lists `K = (n), (m), (n,m)`, `t₁, t₂` the infima of the
  admissible values in `[0,∞)`, `δ₁ = fδ`, `δ₂ = (1−f)δ` with the best `f ∈ {0.5,…,0.9}`, at `α = 0` the smallest `t ≥ 0` with
  `Ψ_H(t;1,s,c) ≤ δ`; the coupled version (`k ≥ 0`, constant diagonal) as the supremum over `u = ‖μ_R‖² ∈ [0,κ²)` of the threshold at
  `v² = κ² − u`, `ρ̄² = κ² + u`, and the maximum over a finite grid of cells (worst corner of each cell).
* `A_basic.tex:264-273`, `lem:crossing`: for `τ : [0,1) → [0,∞)` nondecreasing and continuous on `(0,1)` and `S ≠ ∅`: the path is continuous
  and nonincreasing, `(α̂,1) ⊆ S`, `D̂_{α̂} ≤ τ(α̂+)`; if `α̂ > 0` then `S = [α̂,1)`; `{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0, min(a,1))} {D̂_q ≤ τ(q)}`;
  `α̂` is measurable.
* `05_estimator.tex:17-32`, `eq:alphaest` and the paragraph after it: "It is always well defined, because `D̂_{α,k} ≤ 2κ` …, while
  `τ_{n,m}(α,δ) → ∞` as `α → 1`, so the set … is nonempty. (If `D_φ = 0`, then `D̂_{α,k} ≡ 0` and the set is `[0,1)`.) Since
  `α ↦ D̂_{α,k}` is continuous and nonincreasing and `τ_{n,m}` is nondecreasing and continuous on `(0,1)`, the set contains `(α̂,1)`, and
  `D̂_{α̂,k} ≤ τ_{n,m}(α̂+,δ)`, the right limit, which equals `τ_{n,m}(α̂,δ)` when `α̂ > 0`."
* `04_test.tex:177-181`: `τ_{n,m}` is the smallest of the plug-in thresholds (closed form `τ^P`, the sharper `τ^{P'}`, coupled or not) and
  of `τ^A_{n,m}`.

Closes the coverage gap declared by wave 30tu (card `certify/cards/wave30tu.md`, "Not covered"): continuity of `τ^{P'}` on `(0,1)`,
`τ^{P'} → ∞`, and therefore, at the full `τ_{n,m}`, "`S = [α̂,1)` if `α̂ > 0`", "`τ(α̂+) = τ(α̂)` when `α̂ > 0`", the union formula and the
well-definedness sentence after `eq:alphaest`.

Reuses (imported, not copied) the frozen wave 30ts (`psiH`, `psiR`, `rootH` = `t₁`, `rootR` = `t₂`, `tauPs` = `τ^{P'}`, `tauCpl` =
`τ^{cpl}_{P'}`, `tauGrid`), wave 30tp (`tauP` = `τ^P`), wave 30tr (`tauA` = `τ^A`), wave 30tu (`tauRight` = `τ(a+)`; `Full.tauFull`,
`Full.tauFullCpl`, `Full.tauFullGrid` = the full `τ_{n,m}` in its general, coupled and implemented-grid forms) and `TrimmedMMD`
(`crossSet` = `S`, `alphaHat` = `α̂`, `Demp` = `D̂`).

Encodings and declared deviations (see the card `certify/cards/wave30tw.md`):
* `β = 1/(1−α)`; "continuous on `(0,1)`" is `ContinuousOn … (Ioo 0 1)`; "`→ ∞` as `α → 1`" is `Tendsto … (𝓝[<] 1) atTop`. The roots are
  continuous in `β` on `(1,∞)` (the range of `β` for `α ∈ (0,1)`), at levels `δ₁, δ₂ ∈ (0,1)` (the printed `fδ`, `(1−f)δ`).
* "The tail bounds are continuous": `Ψ_H` jointly in `(β,t)` on `(0,∞) × [0,∞)`; `Ψ_R` in `β` on `(1,∞)` for every fixed `t` (it is not
  continuous in `t`, see below).
* "Strictly decreasing in `t` where they are below `1`": for `Ψ_H` as printed (`t ≥ 0`, `Ψ_H(t) < 1` and `t' > t` give `Ψ_H(t') < Ψ_H(t)`);
  for `Ψ_R` it is FALSE as printed, and the frozen form is the corrected one: from every `t` with `0 < Ψ_R(t) < 1`. Counterexample
  (`repair_tail_jump`): for `β > 1`, `n ≥ 1`, `Ψ_R(1;β,(n)) ≥ (1 − β⁻¹)^n > 0` while `Ψ_R(t;β,(n)) = 0` for every `t > 1`; so `Ψ_R` is
  neither continuous in `t` at `t = 1` nor strictly decreasing on `{t : Ψ_R(t) < 1}`. The conclusion ("their roots are continuous in
  `β`", hence `τ^{P'}`, its coupled supremum and its grid form are continuous on `(0,1)`) is TRUE and frozen.
* "Tends to infinity as `α → 1` when `D_φ > 0`": frozen as an equivalence for each threshold, with `D` any bound on `‖φ(x) − φ(x')‖`
  (generalisation; `D = D_φ` is the printed case): `τ^{P'} → ∞` iff `D > 0` or `v, ρ̄ > 0` (with `D = 0` and `v = 0` or `ρ̄ = 0` the Hilbert
  admissible set is empty for every `β` and `τ^{P'} ≤ 3ρ̄`); the coupled supremum iff `κ ≠ 0`; the grid form iff some cell `j < J` has
  `D > 0` or `v_j, ρ̄_j > 0`; the full `τ_{n,m}` (`v = √min(κ², D²/2)`, `ρ̄ = D`) iff `D > 0`, the coupled one iff `D > 0` and `κ > 0`,
  the grid one iff `D > 0` and `J ≥ 1`. In the kernel setting `D_φ > 0` (`φ` not constant) gives `D > 0` and `κ > 0`.
* The deterministic claims assume `D, v, ρ̄ ≥ 0` (as in the frozen wave 30ts `sharp_tau_monotone`); in the kernel setting they follow
  from a nonempty `𝒳`.
* `CrossingFacts φ κ n m τ` bundles, for a threshold `τ`, the printed conclusions of `lem:crossing` and of the paragraph after
  `eq:alphaest`, with the crossing set nonempty for EVERY realization (well-definedness, proved, not assumed) and the case `D_φ = 0`
  (`φ` constant) giving `D̂ ≡ 0` and `S = [0,1)`. `crossing_union_min` is the printed union formula `(0, min(a,1))` for any threshold
  satisfying the hypotheses of `lem:crossing` (the frozen wave 30tu `crossing_meas` has the earlier `(0,a)`, also true). The crossing claims for the coupled and grid versions need neither `k ≥ 0` nor the constant diagonal
  nor the covering of `[0,κ²]` (generalisation): only `J ≥ 1` and nonnegative cell constants for the grid.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (14 claims ACCEPT, none false; applied: `D̂ ≡ 0` for a constant `φ`
in `CrossingFacts`, the generic `crossing_union_min` added). Hashed in `certify/statements.lock` (with its imports); AI agents
must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.Wave30tw

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30ts StatFormal.Wave30tp
open StatFormal.Wave30tu.Full

/-- The conclusions of `lem:crossing (v2)` (`A_basic.tex:264-273`) and of the paragraph after `eq:alphaest (v2)`
(`05_estimator.tex:26-32`) for a threshold `τ` at sample sizes `n, m`. For every realization `(x, y)`:
* the crossing set `S = {α ∈ [0,1) : D̂_α ≤ τ(α)}` is nonempty (`α̂` is well defined), and `D̂_α ≤ 2κ` on `[0,1)`;
* if `φ` is constant (`D_φ = 0`), then `D̂_α = 0` on `[0,1)` and `S = [0,1)`;
* `α ↦ D̂_α` is continuous and nonincreasing on `[0,1)`;
* `(α̂,1) ⊆ S` and `D̂_{α̂} ≤ τ(α̂+)` (`tauRight`);
* if `α̂ > 0`, then `τ(α̂+) = τ(α̂)` and `S = [α̂,1)`.
Moreover `{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0, min(a,1))} {D̂_q ≤ τ(q)}` (as sets of samples) for every real `a`, and `α̂` is a measurable function
of the samples. -/
def CrossingFacts {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (κ : ℝ) (n m : ℕ) (τ : ℝ → ℝ) : Prop :=
  (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      (crossSet (Demp φ x y) τ).Nonempty ∧ (∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ 2 * κ) ∧
      ((∀ x₁ x₂ : 𝒳, φ x₁ = φ x₂) → (∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α = 0) ∧ crossSet (Demp φ x y) τ = Ico 0 1) ∧
      (ContinuousOn (Demp φ x y) (Ico 0 1) ∧ AntitoneOn (Demp φ x y) (Ico 0 1)) ∧
      Ioo (alphaHat (Demp φ x y) τ) 1 ⊆ crossSet (Demp φ x y) τ ∧
      Demp φ x y (alphaHat (Demp φ x y) τ) ≤ StatFormal.Wave30tu.tauRight τ (alphaHat (Demp φ x y) τ) ∧
      (0 < alphaHat (Demp φ x y) τ →
        StatFormal.Wave30tu.tauRight τ (alphaHat (Demp φ x y) τ) = τ (alphaHat (Demp φ x y) τ) ∧
          crossSet (Demp φ x y) τ = Ico (alphaHat (Demp φ x y) τ) 1)) ∧
    (∀ a : ℝ, {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ < a} =
      ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < min a 1), {z | Demp φ z.1 z.2 q ≤ τ q}) ∧
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ

namespace Claims

/-! ### The tail bounds (`A_basic.tex:288-290`, with `:440-449`) -/

/-- `A_basic.tex:289` (v2), "the tail bounds are continuous": `Ψ_H(t;β,s',c')` is jointly continuous in `(β,t)` on `(0,∞) × [0,∞)`
(for `ρ̄ ≥ 0`, `s', c' > 0`, any `D`, `v`), and `Ψ_R(t;β,K)` is continuous in `β` on `(1,∞)` for every fixed `t` and list `K`. -/
def tails_continuous : Prop :=
  (∀ D v ρbar s' c' : ℝ, 0 ≤ ρbar → 0 < s' → 0 < c' →
      ContinuousOn (fun p : ℝ × ℝ => psiH D v ρbar p.1 s' c' p.2) (Ioi 0 ×ˢ Ici 0)) ∧
    ∀ (t : ℝ) (K : List ℕ), ContinuousOn (fun β => psiR β t K) (Ioi 1)

/-- `A_basic.tex:290` (v2), "strictly decreasing in `t` where they are below `1`": for `Ψ_H` as printed (`ρ̄ ≥ 0`, `β > 0`,
`s', c' > 0`, `0 ≤ t < t'`, `Ψ_H(t) < 1` give `Ψ_H(t') < Ψ_H(t)`); for `Ψ_R` (`β ≥ 1`, any list `K`) in the corrected form: from every `t`
with `0 < Ψ_R(t) < 1` (see `repair_tail_jump` for the printed form). -/
def tails_strict : Prop :=
  (∀ D v ρbar β s' c' t t' : ℝ, 0 ≤ ρbar → 0 < β → 0 < s' → 0 < c' → 0 ≤ t → t < t' →
      psiH D v ρbar β s' c' t < 1 → psiH D v ρbar β s' c' t' < psiH D v ρbar β s' c' t) ∧
    ∀ (β t t' : ℝ) (K : List ℕ), 1 ≤ β → t < t' → 0 < psiR β t K → psiR β t K < 1 → psiR β t' K < psiR β t K

/-- Counterexample to the printed reason at `A_basic.tex:289-290` for the repair term: for `β > 1` and `n ≥ 1`,
`Ψ_R(1;β,(n)) ≥ (1 − β⁻¹)^n > 0` and `Ψ_R(1;β,(n)) < 1`, while `Ψ_R(t;β,(n)) = 0` for every `t > 1`; hence `t ↦ Ψ_R(t;β,(n))` is not
continuous at `1` and not strictly decreasing on `{t : Ψ_R(t;β,(n)) < 1}`. -/
def repair_tail_jump : Prop :=
  ∀ (β : ℝ) (n : ℕ), 1 < β → 1 ≤ n →
    0 < (1 - β⁻¹) ^ n ∧ (1 - β⁻¹) ^ n ≤ psiR β 1 [n] ∧ psiR β 1 [n] < 1 ∧ (∀ t, 1 < t → psiR β t [n] = 0) ∧
      ¬ ContinuousAt (fun t => psiR β t [n]) 1 ∧ ¬ StrictAntiOn (fun t => psiR β t [n]) {t | psiR β t [n] < 1}

/-! ### The roots and the sharper threshold (`A_basic.tex:288-291`) -/

/-- `A_basic.tex:290` (v2), "so their roots are continuous in `β`": `t₁(β,δ₁)` (`rootH`, for `D, v, ρ̄ ≥ 0`, `n, m ≥ 1`) and `t₂(β,δ₂)`
(`rootR`) are continuous in `β` on `(1,∞)` for levels `δ₁, δ₂ ∈ (0,1)`. -/
def sharp_roots_continuous : Prop :=
  (∀ (D v ρbar δ1 : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 0 < δ1 → δ1 < 1 → 1 ≤ n → 1 ≤ m →
      ContinuousOn (fun β => rootH D v ρbar β δ1 n m) (Ioi 1)) ∧
    ∀ (δ2 : ℝ) (n m : ℕ), 0 < δ2 → δ2 < 1 → ContinuousOn (fun β => rootR β δ2 n m) (Ioi 1)

/-- `A_basic.tex:288-289` (v2), "Each candidate is continuous … on `(0,1)`", for the sharper threshold: for `D, v, ρ̄ ≥ 0`, `δ ∈ (0,1)`,
`n, m ≥ 1`, `α ↦ τ^{P'}(α,δ)` is continuous on `(0,1)`. -/
def sharp_tau_continuous : Prop :=
  ∀ (D v ρbar δ : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ContinuousOn (fun α => tauPs D v ρbar α δ n m) (Ioo 0 1)

/-- `A_basic.tex:290-291` (v2), "every candidate tends to infinity as `α → 1` when `D_φ > 0`", for the sharper threshold, as an
equivalence: for `D, v, ρ̄ ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`, `τ^{P'}(α,δ) → ∞` as `α → 1⁻` iff `D > 0` or `v, ρ̄ > 0`. -/
def sharp_tau_tendsto : Prop :=
  ∀ (D v ρbar δ : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (Tendsto (fun α => tauPs D v ρbar α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∨ (0 < v ∧ 0 < ρbar)))

/-- `A_basic.tex:288-291` (v2) for the coupled supremum `τ^{cpl}_{P'}(α,δ) = sup_{u ∈ [0,κ²)} τ^{P'}(α,δ; √(κ²−u), √(κ²+u))` (`tauCpl`):
for `D ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`, it is continuous on `(0,1)`, and it tends to `∞` as `α → 1⁻` iff `κ ≠ 0`. -/
def coupled_tau_continuous : Prop :=
  ∀ (D κ δ : ℝ) (n m : ℕ), 0 ≤ D → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ContinuousOn (fun α => tauCpl D κ α δ n m) (Ioo 0 1) ∧
      (Tendsto (fun α => tauCpl D κ α δ n m) (𝓝[<] 1) atTop ↔ κ ≠ 0)

/-- `A_basic.tex:288-291` (v2) for the grid form `max(0, max_{j<J} τ^{P'}(α,δ; v_j, ρ̄_j))` (`tauGrid`): for `D ≥ 0`, `v_j, ρ̄_j ≥ 0`
(`j < J`), `δ ∈ (0,1)`, `n, m ≥ 1`, it is continuous on `(0,1)`, and it tends to `∞` as `α → 1⁻` iff some cell `j < J` has `D > 0` or
`v_j, ρ̄_j > 0`. -/
def grid_tau_continuous : Prop :=
  ∀ (D : ℝ) (J : ℕ) (v ρ : ℕ → ℝ) (δ : ℝ) (n m : ℕ), 0 ≤ D → (∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j) → 0 < δ → δ < 1 →
    1 ≤ n → 1 ≤ m →
      ContinuousOn (fun α => tauGrid D v ρ J α δ n m) (Ioo 0 1) ∧
        (Tendsto (fun α => tauGrid D v ρ J α δ n m) (𝓝[<] 1) atTop ↔ ∃ j < J, 0 < D ∨ (0 < v j ∧ 0 < ρ j))

/-- `A_basic.tex:288-291` (v2) for the closed-form candidates: `τ^A(·,δ)` and `τ^P(·,δ)` are continuous on `(0,1)`; `τ^A → ∞` as
`α → 1⁻` for `κ ≥ 0`, `D > 0`, and `τ^P → ∞` for `D > 0`, `ρ̄ ≥ 0` (`δ ∈ (0,1)`, `n, m ≥ 1`). -/
def closed_candidates : Prop :=
  ∀ (κ D v ρbar δ : ℝ) (n m : ℕ),
    ContinuousOn (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) (Ioo 0 1) ∧
      ContinuousOn (fun α => tauP D v ρbar α δ n m) (Ioo 0 1) ∧
      (0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → 0 ≤ κ → 0 < D →
        Tendsto (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) (𝓝[<] 1) atTop) ∧
      (0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → 0 < D → 0 ≤ ρbar →
        Tendsto (fun α => tauP D v ρbar α δ n m) (𝓝[<] 1) atTop)

/-- `lem:crossing (v2)`, last sentence as printed at `81716bd` (`A_basic.tex:270-272`): for any `τ : [0,1) → [0,∞)` nondecreasing and
continuous on `(0,1)` whose crossing set is nonempty for every realization, `{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0, min(a,1))} {D̂_q ≤ τ(q)}` for
every real `a`. -/
def crossing_union_min : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
    (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty) →
      ∀ a : ℝ, {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ < a} =
        ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < min a 1), {z | Demp φ z.1 z.2 q ≤ τ q}

/-! ### The full `τ_{n,m}` (`04_test.tex:177-181`, `05_estimator.tex:26-32`) -/

/-- `05_estimator.tex:29-30` (v2), "`τ_{n,m}` is nondecreasing and continuous on `(0,1)`", continuity part, for the full `τ_{n,m} =
min{τ^A, τ^P, τ^{P'}}`, its coupled version `min{τ^A, τ^P, τ^{P'}, τ^{cpl}_{P'}}` and its implemented grid version (cell constants
`≥ 0`), for `D ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`. -/
def tauFull_continuous : Prop :=
  ∀ (κ D δ : ℝ) (n m : ℕ), 0 ≤ D → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ContinuousOn (fun α => tauFull κ D α δ n m) (Ioo 0 1) ∧
      ContinuousOn (fun α => tauFullCpl κ D α δ n m) (Ioo 0 1) ∧
      ∀ (J : ℕ) (vg ρg : ℕ → ℝ), (∀ j < J, 0 ≤ vg j ∧ 0 ≤ ρg j) →
        ContinuousOn (fun α => tauFullGrid κ D vg ρg J α δ n m) (Ioo 0 1)

/-- `05_estimator.tex:27-28` (v2), "`τ_{n,m}(α,δ) → ∞` as `α → 1`", as an equivalence, for `κ, D ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`: the full
`τ_{n,m}` tends to `∞` iff `D > 0`; the coupled version iff `D > 0` and `κ > 0`; the grid version (cell constants `≥ 0`) iff `D > 0`
and `J ≥ 1`. -/
def tauFull_tendsto : Prop :=
  ∀ (κ D δ : ℝ) (n m : ℕ), 0 ≤ κ → 0 ≤ D → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (Tendsto (fun α => tauFull κ D α δ n m) (𝓝[<] 1) atTop ↔ 0 < D) ∧
      (Tendsto (fun α => tauFullCpl κ D α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∧ 0 < κ)) ∧
      ∀ (J : ℕ) (vg ρg : ℕ → ℝ), (∀ j < J, 0 ≤ vg j ∧ 0 ≤ ρg j) →
        (Tendsto (fun α => tauFullGrid κ D vg ρg J α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∧ 0 < J))

/-- `lem:crossing (v2)` and `eq:alphaest (v2)` with the paragraph after it, at the full `τ_{n,m} = min{τ^A, τ^P, τ^{P'}}` (general
kernel; `D` any bound on `‖φ(x) − φ(x')‖`): every clause of `CrossingFacts` (well-definedness for every realization, `S = [0,1)` for a
constant `φ`, the path, `(α̂,1) ⊆ S`, `D̂_{α̂} ≤ τ(α̂+)`, `τ(α̂+) = τ(α̂)` and `S = [α̂,1)` when `α̂ > 0`, the union formula, measurability). -/
def crossing_full_cont : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      CrossingFacts φ κ n m (fun α => tauFull κ D α δ n m)

/-- The same at the coupled full `τ_{n,m} = min{τ^A, τ^P, τ^{P'}, τ^{cpl}_{P'}}` (no kernel hypothesis beyond (A1)–(A2) is needed). -/
def crossing_full_cpl : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      CrossingFacts φ κ n m (fun α => tauFullCpl κ D α δ n m)

/-- The same at the implemented full `τ_{n,m} = min{τ^A, τ^P, τ^{P'}, τ_grid}` for a grid of `J ≥ 1` cells with constants
`vg j, ρg j ≥ 0`. -/
def crossing_full_grid : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (J : ℕ) (vg ρg : ℕ → ℝ) (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 1 ≤ J → (∀ j < J, 0 ≤ vg j ∧ 0 ≤ ρg j) →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      CrossingFacts φ κ n m (fun α => tauFullGrid κ D vg ρg J α δ n m)

end Claims
end StatFormal.Wave30tw
