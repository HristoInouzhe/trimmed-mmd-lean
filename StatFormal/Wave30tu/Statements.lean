import StatFormal.Wave30tl.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tu: trimmed-mmd (JMLR revision v2), the estimator side re-certified for the v2 threshold

Printed source: `trimmed-mmd/jmlr/` at trimmed-mmd commit `0c41fb5` ("JMLR revision v2, batch 1b: fixes from the independent
re-check"; read-only, read 2026-11-08; sha256 `sections/04_test.tex` `65b98e82…`, `sections/05_estimator.tex` `d1d8f75a…`,
`sections/06_splitting.tex` `2c720b0a…`, `appendix/A_basic.tex` `5f05deab…`, `appendix/B_split.tex` `4385b5d9…`; full hashes on the
card). Revision v2 replaced the test threshold by `τ_{n,m}(α,δ)`, "the smallest of these valid thresholds [the plug-in closed form
`τ^P` of `thm:plugin`, its sharper numerical version, coupled or not] and of `τ^A_{n,m}(α,δ)`, which is valid by Theorem `thm:twosided`
because `D_{α,k}(P,Q) = 0` under the null, and which is at most `r_n(α,δ/2) + r_m(α,δ/2)` by `eq:tauA`" (`04_test.tex:177-181`), and the
two-sided tool by `τ^A_{n,m}` with events `E⁺`, `E⁻` for every pair (`thm:twosided`, `04_test.tex:106-122`). Re-certified as printed:
* the definition of `τ_{n,m}` and "Each is a deterministic, nondecreasing function of `α`, so their minimum is valid at every `α` and is
  nondecreasing too" (`04_test.tex:177-181`), with "`τ^A` … is valid by Theorem `thm:twosided` because `D = 0` under the null";
  `lem:oneevent` (`04_test.tex:183-189`, proof `A_basic.tex:473-477`).
* `eq:alphaest` and the paragraph after it (`05_estimator.tex:17-31`: well defined since `D̂ ≤ 2κ` and `τ → ∞` as `α → 1`; the set
  contains `(α̂,1)`; `D̂_{α̂} ≤ τ(α̂+)`, the right limit, which equals `τ(α̂)` when `α̂ > 0`); `rem:grid` (`05_estimator.tex:33-43`).
* `lem:crossing` restated (`A_basic.tex:264-273`, proof `:275-286`), and the paragraph after it (`:288-291`).
* `thm:consistency` (i) and the new (ii) with `η` (`05_estimator.tex:79-92`, proof `A_basic.tex:226-247`).
* `cor:consistency` (`05_estimator.tex:107-117`, proof `A_basic.tex:293-301`).
* "The rate condition cannot be dropped" (`05_estimator.tex:119-122`, argued in `A_basic.tex:303-311`, with the sharper threshold's tails
  `A_basic.tex:437-471`).
* `thm:rate` (`05_estimator.tex:137-154`, proof `A_basic.tex:313-328`), `cor:confset` and the sentence after it
  (`05_estimator.tex:156-175`, proof `A_basic.tex:330-339`).
* `cor:upperfs` and the sentence after it (`06_splitting.tex:232-247`, proof `B_split.tex:199-206`).
* `eq:pathwise` (`A_basic.tex:249-260`) as an instance of the lower two-sided tool.

**Declared generalisation.** The results are frozen for ANY threshold `τ` and ANY two-sided tool `τ^A` with the properties the
printed proofs use, not only for the paper's `τ_{n,m}` and `τ^A_{n,m}`:
* `ValidThreshold φ n m δ τ`: `τ : [0,1) → [0,∞)` nondecreasing, with `P(D̂_α > τ(α)) ≤ δ` for every `α ∈ [0,1)` and every pair of
  laws with `TV ≤ α` (the hypothesis of `lem:oneevent`); continuity on `(0,1)` and `τ → ∞` as `α → 1` are separate hypotheses where
  used (`lem:crossing`, `eq:alphaest`).
* `LowerTool φ P Q n m δ τA`: `τ^A ≥ 0` nondecreasing on `[0,1)`, and the event `E⁻` of `thm:twosided` for the pair `(P,Q)` at level
  `δ`: a measurable event of probability `≥ 1 − δ`, not depending on `α`, on which `D̂_α ≥ D_α(P,Q) − τ^A(α)` for every `α ∈ [0,1)`.
  `UpperTool` is the event `E⁺` (`D̂_α ≤ D_α(P,Q) + τ^A(α)`); it is used only to show that `τ^A` is a valid threshold (`upper_valid`).
* Where a sample-size limit is taken (`thm:consistency` (ii), `cor:consistency`, the polynomial case of `thm:rate`), the decay is the
  printed one: `τ_{n,m}(α,δ) ≤ τ^A_{n,m}(α,δ) ≤ r_n(α,δ/2) + r_m(α,δ/2)` (`eq:tauA`), i.e. `τ, τ^A ≤ TrimmedMMD.tau κ α δ n m`.
The paper's instances are supplied by other certified (or in-progress) claims, listed on the card (`certify/cards/wave30tu.md`); the
old (v1) threshold `r_n + r_m`, still a valid threshold and an upper bound for `τ^A`, is instantiated here (`hausdorff_valid`,
`hausdorff_lower`), which also shows that the hypotheses are satisfiable.

Reuses (imported, not copied) the frozen `TrimmedMMD` (`rn`, `tau`, `crossSet`, `alphaHat`), `Unconditional` (`Dpop`, `Demp`),
`ZeroSet` (`Characteristic`, `tvDist`), and the Wave 30tl definitions `omegaGen` (`ω^←`), `alphaHi` (`α̂_hi`), `KnownMargin` (the
hypothesis on `ω` of `cor:confset`), `MeshGrid`, `GridReturn`, `LastRejected` (`rem:grid`: a grid with first level `≤ h` and gaps `≤ h`;
the smallest non-rejected grid level, or the last level if every level is rejected; the largest rejected level).

Encodings (see the card):
* (A1)–(A2): `H` a real separable Hilbert space, `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ`; (A3) is `Characteristic φ`
  (injective mean embedding), assumed only in `consistency_ii` and `cor_consistency` (it gives `D_{α*−ε} > 0`); dropped elsewhere
  (generalisation). `D_φ`: any `D` with `‖φ x − φ x'‖ ≤ D`.
* Samples on `(Fin n → 𝒳) × (Fin m → 𝒳)` with `P^{⊗n} ⊗ Q^{⊗m}`; "with probability at least `1 − p`" is a measurable event of probability
  `≥ 1 − p` inside the claimed set; "`P(D̂_α > τ) ≤ δ`" is the (outer) measure of `{τ < D̂_α}`.
* `α* = TV(P,Q)` (`tvDist`); `D_{α,k}(P,Q) = Dpop`, `D̂_{α,k} = Demp`; `α̂ = alphaHat D̂ τ` (`sInf` of the crossing set).
* `τ(a+)` is `tauRight τ a = inf_{a' ∈ (a,1)} τ(a')` (`tauRight_spec`: it is the right limit, `≥ τ(a)`, and `= τ(a)` at `a > 0` when
  `τ` is continuous on `(0,1)`).
* `ε_{n,m} = ω^{-1}(t_{n,m})` of `thm:rate`: any `ε ∈ [0,α*]` with `ω(ε) = t_{n,m}` (when `0 ≤ t_{n,m} ≤ ω(α*)` it exists and is unique:
  `rate_eps`). `O(·)` in the polynomial case: the explicit constant 24.
* Convergence in probability: the encoding of the frozen Wave 18b `cor_consistency` (any filter of schedules; measurable inner events
  of probability `→ 1`).
* The sharper threshold's tails (`A_basic.tex:440-447`): `psiMcD`, `psiPin` (with `a = βρ̄c'`, `b² = βv²s'`), `psiH = min`; its value at
  `α = 0` is `sharpZero` = the smallest `t ≥ 0` with `Ψ_H(t;1,s,c) ≤ δ` (an `sInf`; the set is certified nonempty where used).
  `τ^A_{n,n}(0,δ) = 2κ√s + 2κ(e_n + e_m) + D_φ√(s log(1/δ)/2)` with the Rademacher means `e_n, e_m ≥ 0` left as parameters.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (29 claims ACCEPT on the first draft, none false; then the 0c41fb5 deltas — `UpperTool`, `upper_valid`, `grid_mesh`, `grid_prob`, `ratecond_tauA`, the new `ratecond_gauss`, header — ACCEPT; line references fixed). Hashed in `certify/statements.lock` (with its imports); AI agents
must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A valid threshold at sample sizes `n, m` and level `δ` (the hypothesis of `lem:oneevent`): `τ ≥ 0` and nondecreasing on
`[0,1)`, and `P(D̂_α > τ(α)) ≤ δ` for every `α ∈ [0,1)` and every pair of probability laws with `TV(P',Q') ≤ α`. -/
def ValidThreshold (φ : 𝒳 → H) (n m : ℕ) (δ : ℝ) (τ : ℝ → ℝ) : Prop :=
  (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) ∧ MonotoneOn τ (Ico 0 1) ∧
    ∀ α ∈ Ico (0 : ℝ) 1, ∀ P' Q' : Measure 𝒳, IsProbabilityMeasure P' → IsProbabilityMeasure Q' →
      StatFormal.Distances.tvDist P' Q' ≤ α →
        ((Measure.pi fun _ : Fin n => P').prod (Measure.pi fun _ : Fin m => Q'))
          {z | τ α < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- The lower half of the two-sided tool of `thm:twosided` for the pair `(P,Q)` at level `δ`: `τ^A ≥ 0` and nondecreasing on `[0,1)`,
and an event `E⁻` (measurable, probability `≥ 1 − δ`, not depending on `α`) on which `D̂_α ≥ D_α(P,Q) − τ^A(α)` for every
`α ∈ [0,1)`. -/
def LowerTool (φ : 𝒳 → H) (P Q : Measure 𝒳) (n m : ℕ) (δ : ℝ) (τA : ℝ → ℝ) : Prop :=
  (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τA α) ∧ MonotoneOn τA (Ico 0 1) ∧
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
      ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - τA α ≤ Demp φ z.1 z.2 α

/-- The upper half of the two-sided tool of `thm:twosided` for the pair `(P,Q)` at level `δ`: an event `E⁺` (measurable, probability
`≥ 1 − δ`, not depending on `α`) on which `D̂_α ≤ D_α(P,Q) + τ^A(α)` for every `α ∈ [0,1)`. -/
def UpperTool (φ : 𝒳 → H) (P Q : Measure 𝒳) (n m : ℕ) (δ : ℝ) (τA : ℝ → ℝ) : Prop :=
  ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
    ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
    ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, Demp φ z.1 z.2 α ≤ Dpop φ P Q α + τA α

/-- `ass:margin`: `ω : [0,α*] → [0,∞)` strictly increasing and continuous with `ω(0) = 0`, and `D_{α*−ε,k}(P,Q) ≥ ω(ε)` for all
`ε ∈ [0,α*]`, `α* = TV(P,Q)`. -/
def Margin (φ : 𝒳 → H) (P Q : Measure 𝒳) (ω : ℝ → ℝ) : Prop :=
  StrictMonoOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧ ContinuousOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)) ∧
    ω 0 = 0 ∧ (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q), 0 ≤ ω e) ∧
    ∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)

end Defs

/-- The right limit `τ(a+) = lim_{a' ↓ a} τ(a')`, written as `inf_{a' ∈ (a,1)} τ(a')`. -/
def tauRight (τ : ℝ → ℝ) (a : ℝ) : ℝ := sInf (τ '' Ioo a 1)

/-- McDiarmid's tail of `Ψ_H` (`A_basic.tex:440-447`): `exp(−2(t − √(βv²s'))_+² / (β²D_φ²s'))`. -/
def psiMcD (v D β s t : ℝ) : ℝ := Real.exp (-(2 * (max (t - √(β * v ^ 2 * s)) 0) ^ 2) / (β ^ 2 * D ^ 2 * s))

/-- Pinelis' tail of `Ψ_H` (`A_basic.tex:440-447`): `2 exp(t/a − (t/a + b²/a²) log(1 + ta/b²))` with `a = βρ̄c'`, `b² = βv²s'`. -/
def psiPin (v ρbar β s c t : ℝ) : ℝ :=
  2 * Real.exp (t / (β * ρbar * c) - (t / (β * ρbar * c) + β * v ^ 2 * s / (β * ρbar * c) ^ 2) *
    Real.log (1 + t * (β * ρbar * c) / (β * v ^ 2 * s)))

/-- `Ψ_H(t; β, s', c') = min{McDiarmid, Pinelis}` (`A_basic.tex:440-447`). -/
def psiH (v D ρbar β s c t : ℝ) : ℝ := min (psiMcD v D β s t) (psiPin v ρbar β s c t)

/-- The sharp threshold at `α = 0`: the smallest `t ≥ 0` with `Ψ_H(t; 1, s, c) ≤ δ`, `s = 1/n + 1/m`, `c = max(1/n, 1/m)`
(`A_basic.tex:455`). -/
def sharpZero (v D ρbar : ℝ) (n m : ℕ) (δ : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧
    psiH v D ρbar 1 (1 / (n : ℝ) + 1 / (m : ℝ)) (max (1 / (n : ℝ)) (1 / (m : ℝ))) t ≤ δ}

namespace Claims

/-! ### `lem:oneevent` and the minimum of valid thresholds (`04_test.tex:177-189`) -/

/-- `lem:oneevent (v2)`: for a valid nondecreasing `τ : [0,1) → [0,∞)` and every pair with `α* = TV(P,Q) < 1`, the event
`{D̂_{α*} ≤ τ(α*)}` is measurable with probability `≥ 1 − δ`, and on it `D̂_α ≤ τ(α)` for every `α ∈ [α*, 1)`. -/
def oneevent : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → StatFormal.Distances.tvDist P Q < 1 →
      MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) |
          Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q)} ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
          {z | Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q)} ∧
        ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳),
          Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q) →
            ∀ α ∈ Ico (StatFormal.Distances.tvDist P Q) 1, Demp φ z.1 z.2 α ≤ τ α

/-- `04_test.tex:177-181` (definition of `τ_{n,m}`): the pointwise minimum of finitely many valid nondecreasing thresholds is valid at
every `α` and nondecreasing; it is moreover continuous on `(0,1)` and tends to `∞` as `α → 1` when every candidate does (the
hypotheses of `lem:crossing` and `eq:alphaest`). -/
def threshold_min : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (δ : ℝ) (n m : ℕ) (ι : Type) (s : Finset ι) (hs : s.Nonempty) (τ : ι → ℝ → ℝ),
    (∀ i ∈ s, ValidThreshold φ n m δ (τ i)) →
      ValidThreshold φ n m δ (fun α => s.inf' hs fun i => τ i α) ∧
      ((∀ i ∈ s, ContinuousOn (τ i) (Ioo 0 1)) →
        ContinuousOn (fun α => s.inf' hs fun i => τ i α) (Ioo 0 1)) ∧
      ((∀ i ∈ s, Tendsto (τ i) (𝓝[<] 1) atTop) →
        Tendsto (fun α => s.inf' hs fun i => τ i α) (𝓝[<] 1) atTop)

/-- `04_test.tex:178-179`: "`τ^A_{n,m}(α,δ)`, which is valid by Theorem `thm:twosided` because `D_{α,k}(P,Q) = 0` under the null":
if `τ^A ≥ 0` is nondecreasing on `[0,1)` and every pair of laws has an event `E⁺` at level `δ`, then `τ^A` is a valid threshold. -/
def upper_valid : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (τA : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τA α) → MonotoneOn τA (Ico 0 1) →
    (∀ P' Q' : Measure 𝒳, IsProbabilityMeasure P' → IsProbabilityMeasure Q' → UpperTool φ P' Q' n m δ τA) →
      ValidThreshold φ n m δ τA

/-! ### `eq:alphaest`, `lem:crossing`, `rem:grid` -/

/-- `eq:alphaest (v2)`, "It is always well defined, because `D̂_{α,k} ≤ 2κ` …, while `τ(α) → ∞` as `α → 1`, so the set … is
nonempty": for every realization. -/
def alphaest_wellDefined : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m → Tendsto τ (𝓝[<] 1) atTop →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ 2 * κ) ∧ (crossSet (Demp φ x y) τ).Nonempty

/-- Encoding check for `τ(a+)` (`05_estimator.tex:30-31`, `A_basic.tex:269-270`): for `τ ≥ 0` nondecreasing on `[0,1)` and `a ∈ [0,1)`,
`tauRight τ a` is the limit of `τ` from the right at `a`, it is `≥ τ(a)`, and it equals `τ(a)` when `a > 0` and `τ` is continuous on
`(0,1)`. -/
def tauRight_spec : Prop :=
  ∀ (τ : ℝ → ℝ) (a : ℝ), (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → 0 ≤ a → a < 1 →
    Tendsto τ (𝓝[>] a) (𝓝 (tauRight τ a)) ∧ τ a ≤ tauRight τ a ∧
      (0 < a → ContinuousOn τ (Ioo 0 1) → tauRight τ a = τ a)

/-- `lem:crossing (v2)`: for `τ : [0,1) → [0,∞)` nondecreasing and continuous on `(0,1)` and a realization whose crossing set
`S = {α ∈ [0,1) : D̂_α ≤ τ(α)}` is nonempty: `α ↦ D̂_α` is continuous and nonincreasing on `[0,1)`, `(α̂,1) ⊆ S`,
`D̂_{α̂} ≤ τ(α̂+)`, and `S = [α̂,1)` if `α̂ > 0`. -/
def crossing : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty →
        (ContinuousOn (Demp φ x y) (Ico 0 1) ∧ AntitoneOn (Demp φ x y) (Ico 0 1)) ∧
        Ioo (alphaHat (Demp φ x y) τ) 1 ⊆ crossSet (Demp φ x y) τ ∧
        Demp φ x y (alphaHat (Demp φ x y) τ) ≤ tauRight τ (alphaHat (Demp φ x y) τ) ∧
        (0 < alphaHat (Demp φ x y) τ → crossSet (Demp φ x y) τ = Ico (alphaHat (Demp φ x y) τ) 1)

/-- `lem:crossing (v2)`, last sentence: if the crossing set is nonempty for every realization, then for every `a`,
`{α̂ < a} = ⋃_{q ∈ ℚ ∩ (0,a)} {D̂_q ≤ τ(q)}` (as sets of samples), and `α̂` is a measurable function of the samples. -/
def crossing_meas : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → ContinuousOn τ (Ioo 0 1) →
    (∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty) →
      (∀ a : ℝ, {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ < a} =
          ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < a), {z | Demp φ z.1 z.2 q ≤ τ q}) ∧
        Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ

/-- `rem:grid (v2)`, deterministic part (`05_estimator.tex:35-40`): for a grid with first level `≤ h` and gaps `≤ h` and a realization
with a nonempty crossing set, the returned level `α̂_grid` (smallest non-rejected grid level, or the last one if every level is
rejected) is `≤ α̂ + h`, and every rejected grid level, in particular `α_last`, is `≤ α̂` ("the non-rejected levels contain `(α̂,1)`
and are contained in `[α̂,1)`"; `τ` may jump at 0, so level `α̂` itself may be rejected). -/
def grid_mesh : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ h : ℝ) (τ : ℝ → ℝ) (n m : ℕ) (G : Finset ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) → MeshGrid G h →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty →
        (∀ a, GridReturn G (Demp φ x y) τ a → a ≤ alphaHat (Demp φ x y) τ + h) ∧
          ∀ b, LastRejected G (Demp φ x y) τ b → b ≤ alphaHat (Demp φ x y) τ

/-- `rem:grid (v2)` (`05_estimator.tex:40-42`): for a valid threshold and `α* = TV(P,Q) < 1`, on one event of probability `≥ 1 − δ`
(the same for every grid and mesh), `α̂_grid ≤ α* + h` and `α* > α_last`. -/
def grid_prob : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → ValidThreshold φ n m δ τ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (G : Finset ℝ) (h : ℝ), MeshGrid G h →
              (∀ a, GridReturn G (Demp φ z.1 z.2) τ a → a ≤ StatFormal.Distances.tvDist P Q + h) ∧
              ∀ b, LastRejected G (Demp φ z.1 z.2) τ b → b < StatFormal.Distances.tvDist P Q}

/-! ### `thm:consistency` and `cor:consistency` -/

/-- `thm:consistency (v2)` (i): for every `n, m ≥ 1`, with probability `≥ 1 − δ`, `α̂ ≤ α*`, and `α̂ = 0` if `α* = 0`. -/
def consistency_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → ValidThreshold φ n m δ τ →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
              (StatFormal.Distances.tvDist P Q = 0 → alphaHat (Demp φ z.1 z.2) τ = 0)}

/-- `thm:consistency (v2)` (ii): under (A1)–(A3), if `0 < α* < 1`, then for every `ε ∈ (0, α*]` and `η ∈ (0,1)` there is `N` such that
for all `n, m ≥ N`, `P(α* − ε ≤ α̂_{n,m} ≤ α*) ≥ 1 − δ − η`. Here `τ n m` is a valid threshold at level `δ` with
`τ ≤ r_n(·,δ/2) + r_m(·,δ/2)`, and `τA n m η` a lower two-sided tool at level `η` with `τ^A ≤ r_n(·,η/2) + r_m(·,η/2)` (`eq:tauA`). -/
def consistency_ii : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ : ℕ → ℕ → ℝ → ℝ) (τA : ℕ → ℕ → ℝ → ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.TrimmedMMD.ZeroSet.Characteristic φ →
    0 < StatFormal.Distances.tvDist P Q → StatFormal.Distances.tvDist P Q < 1 → 0 < δ → δ < 1 →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (τ n m) ∧ ∀ α ∈ Ico (0 : ℝ) 1, τ n m α ≤ tau κ α δ n m) →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ η : ℝ, 0 < η → η < 1 →
      LowerTool φ P Q n m η (τA n m η) ∧ ∀ α ∈ Ico (0 : ℝ) 1, τA n m η α ≤ tau κ α η n m) →
      ∀ ε ∈ Ioc (0 : ℝ) (StatFormal.Distances.tvDist P Q), ∀ η : ℝ, 0 < η → η < 1 →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → 1 ≤ n → 1 ≤ m →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ - η) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) (τ n m) ∧
                  alphaHat (Demp φ z.1 z.2) (τ n m) ≤ StatFormal.Distances.tvDist P Q}

/-- `cor:consistency (v2)`: under (A1)–(A3) and `α* < 1`, along any schedule with `δ → 0` and `log(1/δ)/min(n,m) → 0`, the estimator
built on `τ n m δ` converges in probability to `α* = TV(P,Q)` (the frozen Wave 18b encoding), for any valid thresholds and lower
two-sided tools at every level `d ∈ (0,1)` that are `≤ r_n(·,d/2) + r_m(·,d/2)`. -/
def cor_consistency : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (τ τA : ℕ → ℕ → ℝ → ℝ → ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ) (δ : ι → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.TrimmedMMD.ZeroSet.Characteristic φ →
    StatFormal.Distances.tvDist P Q < 1 →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ d : ℝ, 0 < d → d < 1 →
      ValidThreshold φ n m d (τ n m d) ∧ (∀ α ∈ Ico (0 : ℝ) 1, τ n m d α ≤ tau κ α d n m) ∧
      LowerTool φ P Q n m d (τA n m d) ∧ ∀ α ∈ Ico (0 : ℝ) 1, τA n m d α ≤ tau κ α d n m) →
    (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) → (∀ i, 0 < δ i) → Tendsto δ l (𝓝 0) →
    Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0) →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i)) -
          StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

/-! ### "The rate condition cannot be dropped" (`05_estimator.tex:119-122`, `A_basic.tex:303-311`) -/

/-- `A_basic.tex:304-305`: "every point of either empirical region is a convex combination of feature vectors, so
`D̂_{α,k} ≤ D_φ` always" (any `D ≥ ‖φ(x) − φ(x')‖`, every realization, every `α ∈ [0,1)`). -/
def Demp_le_Dphi : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), ∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ D

/-- `A_basic.tex:305-306`: with `n = m` and `δ = e^{−n}`, the closed form of `thm:plugin` at `α = 0`,
`v√s + D_φ√(s log(1/δ)/2)` with `s = 1/n + 1/n`, equals `v√(2/n) + D_φ`, which is `> D_φ` (for `v > 0`; Gaussian: `v = κ > 0`). -/
def ratecond_closed : Prop :=
  ∀ (v D : ℝ) (n : ℕ), 0 < v → 0 ≤ D → 1 ≤ n →
    v * √(1 / (n : ℝ) + 1 / (n : ℝ)) +
        D * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) = v * √(2 / (n : ℝ)) + D ∧
      D < v * √(2 / (n : ℝ)) + D

/-- `A_basic.tex:307`: `τ^A_{n,n}(0,δ) > D_φ√(s log(1/δ)/2) = D_φ` at `δ = e^{−n}`, `s = 1/n + 1/n`, where
`τ^A_{n,n}(0,δ) = 2κ√s + 2κ(e_n + e_n) + D_φ√(s log(1/δ)/2)` (`eq:tauA` at `β = 1`; any Rademacher means `e_n ≥ 0`), for `κ > 0`. -/
def ratecond_tauA : Prop :=
  ∀ (κ D e₁ e₂ : ℝ) (n : ℕ), 0 < κ → 0 ≤ D → 0 ≤ e₁ → 0 ≤ e₂ → 1 ≤ n →
    D * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) = D ∧
      D * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) <
        2 * κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) + 2 * κ * (e₁ + e₂) +
          D * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2)

/-- `A_basic.tex:309`: `(x + y) log(1 + x/y) − x ≤ x²/y` for `x ≥ 0`, `y > 0`. -/
def pinelis_ineq : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 < y → (x + y) * Real.log (1 + x / y) - x ≤ x ^ 2 / y

/-- `A_basic.tex:307-309`, McDiarmid's tail: with `n = m`, `s' = s = 1/n + 1/n`, at level `e^{−n}`, every `t` whose McDiarmid tail is
`≤ e^{−n}` has `t ≥ √(βv²s) + βD_φ` (at `α = 0`, `β = 1`: `t ≥ v√(2/n) + D_φ`), for every `β ≥ 1`. -/
def ratecond_mcd : Prop :=
  ∀ (v D β t : ℝ) (n : ℕ), 0 ≤ v → 0 ≤ D → 1 ≤ β → 1 ≤ n →
    psiMcD v D β (1 / (n : ℝ) + 1 / (n : ℝ)) t ≤ Real.exp (-(n : ℝ)) →
      √(β * v ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ))) + β * D ≤ t

/-- `A_basic.tex:309-310`, Pinelis' tail: with `n = m`, `s' = s`, `c' = c = max(1/n, 1/n)`, every `t ≥ 0` whose Pinelis tail is
`≤ e^{−n}` has `t > √2 v` (for `v, ρ̄ > 0` and every `β ≥ 1`). -/
def ratecond_pin : Prop :=
  ∀ (v ρbar β t : ℝ) (n : ℕ), 0 < v → 0 < ρbar → 1 ≤ β → 0 ≤ t → 1 ≤ n →
    psiPin v ρbar β (1 / (n : ℝ) + 1 / (n : ℝ)) (max (1 / (n : ℝ)) (1 / (n : ℝ))) t ≤ Real.exp (-(n : ℝ)) →
      √2 * v < t

/-- `A_basic.tex:307-311` and `:455`, the sharper threshold at `α = 0` for the Gaussian constants `v = κ`, `D_φ = √2κ` (any `ρ̄ > 0`: `ρ̄ = D_φ`, or
`ρ̄ = κ` at `u = 0` in the coupled version), `n = m`, `δ = e^{−n}`: the set `{t ≥ 0 : Ψ_H(t;1,s,c) ≤ δ}` is nonempty, every element
exceeds `D_φ = √2κ`, so the smallest one is `≥ D_φ`. -/
def ratecond_sharp : Prop :=
  ∀ (κ ρbar : ℝ) (n : ℕ), 0 < κ → 0 < ρbar → 1 ≤ n →
    {t : ℝ | 0 ≤ t ∧ psiH κ (√2 * κ) ρbar 1 (1 / (n : ℝ) + 1 / (n : ℝ)) (max (1 / (n : ℝ)) (1 / (n : ℝ))) t ≤
        Real.exp (-(n : ℝ))}.Nonempty ∧
      (∀ t : ℝ, 0 ≤ t →
        psiH κ (√2 * κ) ρbar 1 (1 / (n : ℝ) + 1 / (n : ℝ)) (max (1 / (n : ℝ)) (1 / (n : ℝ))) t ≤ Real.exp (-(n : ℝ)) →
          √2 * κ < t) ∧
      √2 * κ ≤ sharpZero κ (√2 * κ) ρbar n n (Real.exp (-(n : ℝ)))

/-- `05_estimator.tex:119-121`, deterministic step: if every threshold `τ_i` entering the minimum is nondecreasing on `[0,1)` and
`≥ D_φ` at `α = 0`, then the minimum is `≥ D_φ` at every `α ∈ [0,1)`, and since `D̂ ≤ D_φ`, `α̂_{n,n} = 0` for every sample. -/
def ratecond_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (n : ℕ) (ι : Type) (s : Finset ι) (hs : s.Nonempty)
    (τ : ι → ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 1 ≤ n →
    (∀ i ∈ s, MonotoneOn (τ i) (Ico 0 1) ∧ D ≤ τ i 0) →
      (∀ α ∈ Ico (0 : ℝ) 1, D ≤ s.inf' hs fun i => τ i α) ∧
        ∀ x y : Fin n → 𝒳, alphaHat (Demp φ x y) (fun α => s.inf' hs fun i => τ i α) = 0

/-- `05_estimator.tex:121-122`: "`α̂_{n,n}` does not converge to `α* > 0`": for thresholds `τ n ≥ D_φ` on `[0,1)` (every `n ≥ 1`), if
`α* = TV(P,Q) > 0`, then for every `e ∈ (0, α*)` there are no measurable `E_n ⊆ {|α̂_{n,n} − α*| ≤ e}` with `P(E_n) → 1`. -/
def ratecond_noconv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ D : ℝ) (τ : ℕ → ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ n : ℕ, 1 ≤ n → ∀ α ∈ Ico (0 : ℝ) 1, D ≤ τ n α) → 0 < StatFormal.Distances.tvDist P Q →
      ∀ e : ℝ, 0 < e → e < StatFormal.Distances.tvDist P Q →
        ¬ ∃ E : ∀ n : ℕ, Set ((Fin n → 𝒳) × (Fin n → 𝒳)), (∀ n, MeasurableSet (E n)) ∧
          (∀ n, E n ⊆ {z | |alphaHat (Demp φ z.1 z.2) (τ n) - StatFormal.Distances.tvDist P Q| ≤ e}) ∧
          Tendsto (fun n => ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n)) atTop (𝓝 1)

/-- `05_estimator.tex:119-121` for the Gaussian constants (`‖φ‖ ≤ κ`, `D_φ = √2κ`, `v = κ`), `n = m`, `δ = e^{−n}`: for the minimum
of the candidates entering `τ_{n,n}` — any nondecreasing `τP` equal at `α = 0` to the closed form `v√s + D_φ√(s log(1/δ)/2)`, any
nondecreasing `τS` at least the sharper value `sharpZero` at `α = 0` (any `ρ̄ > 0`: uncoupled `ρ̄ = D_φ`, or coupled, whose supremum over
`u` is at least its value at `u = 0`, `ρ̄ = κ`), and any nondecreasing `τA` equal at `α = 0` to `τ^A_{n,n}(0,δ)` (any Rademacher means
`e₁, e₂ ≥ 0`) — the minimum is `≥ D_φ` at every `α ∈ [0,1)` and `α̂_{n,n} = 0` for every sample. -/
def ratecond_gauss : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ ρbar e₁ e₂ : ℝ) (n : ℕ) (τP τS τA : ℝ → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ √2 * κ) → 0 < κ → 0 < ρbar →
    0 ≤ e₁ → 0 ≤ e₂ → 1 ≤ n →
    MonotoneOn τP (Ico 0 1) →
    τP 0 = κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) +
      √2 * κ * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) →
    MonotoneOn τS (Ico 0 1) → sharpZero κ (√2 * κ) ρbar n n (Real.exp (-(n : ℝ))) ≤ τS 0 →
    MonotoneOn τA (Ico 0 1) →
    τA 0 = 2 * κ * √(1 / (n : ℝ) + 1 / (n : ℝ)) + 2 * κ * (e₁ + e₂) +
      √2 * κ * √((1 / (n : ℝ) + 1 / (n : ℝ)) * Real.log (1 / Real.exp (-(n : ℝ))) / 2) →
      (∀ α ∈ Ico (0 : ℝ) 1, √2 * κ ≤ min (min (τP α) (τS α)) (τA α)) ∧
        ∀ x y : Fin n → 𝒳, alphaHat (Demp φ x y) (fun α => min (min (τP α) (τS α)) (τA α)) = 0

/-! ### `thm:rate` -/

/-- Encoding check for `ε_{n,m} = ω^{-1}(t_{n,m})` (`thm:rate`, `05_estimator.tex:139-141`): under `ass:margin`, for every `t ∈ [0, ω(α*)]` there is exactly one
`ε ∈ [0, α*]` with `ω(ε) = t`. -/
def rate_eps : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (ω : ℝ → ℝ) (t : ℝ),
    Margin φ P Q ω → 0 ≤ t → t ≤ ω (StatFormal.Distances.tvDist P Q) →
      ∃! ε : ℝ, ε ∈ Icc 0 (StatFormal.Distances.tvDist P Q) ∧ ω ε = t

/-- `thm:rate (v2)`: under `ass:margin`, with `t_{n,m} = τ(α*) + τ^A(α*)` (`τ` valid at level `δ`, `τ^A` a lower tool at level `δ'`)
and `ε_{n,m} ∈ [0,α*]` with `ω(ε_{n,m}) = t_{n,m}`: `P(α* − ε_{n,m} ≤ α̂ ≤ α*) ≥ 1 − δ − δ'`, every `n, m ≥ 1`. -/
def rate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ) (ε : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → Margin φ P Q ω →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
    ε ∈ Icc 0 (StatFormal.Distances.tvDist P Q) →
    ω ε = τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q) →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) τ ∧
              alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q}

/-- `thm:rate (v2)`, polynomial case `ω(ε) = c₀ε^γ`: if `t = τ(α*) + τ^A(α*) ≤ ω(α*)`, then with probability `≥ 1 − δ − δ'`,
`|α̂ − α*| ≤ (t/c₀)^{1/γ}`; and when `τ`, `τ^A` are `≤ r_n(·,·/2) + r_m(·,·/2)` at `α*`,
`(t/c₀)^{1/γ} ≤ (24κ/(c₀(1−α*)) · √((1 + log(1/δ) + log(1/δ'))/min(n,m)))^{1/γ}` (the `O(·)`, explicit constant 24). -/
def rate_poly : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' c₀ γ : ℝ) (τ τA : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → 0 < c₀ → 0 < γ →
    (∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      c₀ * e ^ γ ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)) →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
    τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q) ≤
      c₀ * StatFormal.Distances.tvDist P Q ^ γ →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | |alphaHat (Demp φ z.1 z.2) τ - StatFormal.Distances.tvDist P Q| ≤
              ((τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) / c₀) ^ (1 / γ)}) ∧
      (τ (StatFormal.Distances.tvDist P Q) ≤ tau κ (StatFormal.Distances.tvDist P Q) δ n m →
        τA (StatFormal.Distances.tvDist P Q) ≤ tau κ (StatFormal.Distances.tvDist P Q) δ' n m →
        ((τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) / c₀) ^ (1 / γ) ≤
          (24 * κ / (c₀ * (1 - StatFormal.Distances.tvDist P Q)) *
            √((1 + Real.log (1 / δ) + Real.log (1 / δ')) / (min n m : ℕ))) ^ (1 / γ))

/-! ### `cor:confset` -/

/-- `cor:confset (v2)`: for every `n, m ≥ 1`, `P(α̂ ≤ α* ≤ α̂ + ω^←(τ(α̂+) + τ^A(α̂))) ≥ 1 − δ − δ'` (`τ` valid at level `δ`, `τ^A` a
lower tool at level `δ'`, `ω` as in `cor:confset`). -/
def confset : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) τ +
                omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ))}

/-- The sentence after `cor:confset (v2)`: on one event of probability `≥ 1 − δ − δ'` the interval covers `α*`, and whenever
`α̂ < α*` the width `ω^←(τ(α̂+) + τ^A(α̂))` is at most every `ε_{n,m} ∈ [0, α*]` with `ω(ε_{n,m}) = τ(α*) + τ^A(α*)` (the `ε_{n,m}`
of `thm:rate`). -/
def confset_width : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ δ' : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 0 < δ' → δ' < 1 → 1 ≤ n → 1 ≤ m →
    ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ' τA →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) τ +
                omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ)) ∧
              (alphaHat (Demp φ z.1 z.2) τ < StatFormal.Distances.tvDist P Q →
                ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
                  ω ε = τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q) →
                    omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ)) ≤ ε)}

/-! ### `cor:upperfs` -/

/-- `cor:upperfs (v2)`: with `Ď_α = D̂_α + τ^A(α)` (`τ^A` a lower tool at level `δ`), for every `n, m ≥ 1`, with probability `≥ 1 − δ`,
`D_α(P,Q) ≤ Ď_α` for every `α ∈ [0,1)` simultaneously, and `TV(P,Q) ≤ α̂_hi = inf_{α ∈ [0,1)} {α + ω^←(Ď_α)}`. -/
def upperfs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → LowerTool φ P Q n m δ τA →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | (∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + τA α) ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHi ω (fun α => Demp φ z.1 z.2 α + τA α)}

/-- The sentence after `cor:upperfs (v2)`: "Taking `α = α̂` in the infimum and using `D̂_{α̂} ≤ τ(α̂+)` gives
`α̂_hi ≤ α̂ + ω^←(τ(α̂+) + τ^A(α̂))`", for every realization with a nonempty crossing set and any `ω` (`τ ≥ 0` nondecreasing). -/
def alphaHi_le : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty →
        alphaHi ω (fun α => Demp φ x y α + τA α) ≤
          alphaHat (Demp φ x y) τ + omegaGen ω (tauRight τ (alphaHat (Demp φ x y) τ) + τA (alphaHat (Demp φ x y) τ))

/-- The sentence after `cor:upperfs (v2)`: "… the upper end of `cor:confset` with `δ' = δ`, so `[α̂, α̂_hi]` is a `1 − 2δ` interval for
every sample size": one event of probability `≥ 1 − 2δ` on which `α̂ ≤ α* ≤ α̂_hi ≤ α̂ + ω^←(τ(α̂+) + τ^A(α̂))`. -/
def upperfs_interval : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (τ τA ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → ValidThreshold φ n m δ τ → LowerTool φ P Q n m δ τA →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - 2 * δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHi ω (fun α => Demp φ z.1 z.2 α + τA α) ∧
              alphaHi ω (fun α => Demp φ z.1 z.2 α + τA α) ≤ alphaHat (Demp φ z.1 z.2) τ +
                omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ))}

/-! ### Instances: the v1 (Hausdorff) threshold `r_n(α,δ/2) + r_m(α,δ/2)` -/

/-- The v1 threshold `τ = r_n(·,δ/2) + r_m(·,δ/2)` (no longer a candidate in `τ_{n,m}`, but an upper bound for `τ^A` by `eq:tauA`)
satisfies the hypotheses of the threshold: valid and nondecreasing (the frozen Wave 30tl `test_level`), continuous on `(0,1)`, and
`→ ∞` as `α → 1` when `κ > 0` (the properties `A_basic.tex:288-291` asks of every candidate). -/
def hausdorff_valid : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ValidThreshold φ n m δ (fun α => tau κ α δ n m) ∧
        ContinuousOn (fun α => tau κ α δ n m) (Ioo 0 1) ∧
        (0 < κ → Tendsto (fun α => tau κ α δ n m) (𝓝[<] 1) atTop)

/-- `eq:pathwise (v2)` (`A_basic.tex:249-260`): `τ^A = r_n(·,δ/2) + r_m(·,δ/2)` with the event of `cor:uniform` for each sample is a
lower two-sided tool at level `δ`, for every pair. -/
def hausdorff_lower : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      LowerTool φ P Q n m δ (fun α => tau κ α δ n m)

end Claims
end StatFormal.Wave30tu
