import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tl: trimmed-mmd (JMLR version), the estimator side

Source: `trimmed-mmd/jmlr/` at trimmed-mmd commit `e1869dd` (read-only, read 2026-11-07; sha256 at that commit
`sections/04_test.tex` `5065d7da…`, `sections/05_estimator.tex` `1bf051f4…`, `sections/06_splitting.tex` `a7f435b9…`,
`appendix/A_basic.tex` `c29f4d67…`, `appendix/B_split.tex` `6320abff…`; line numbers refer to that commit; the quoted passages are
unchanged in the working tree of the same evening, which is still being edited elsewhere):
* `lem:crossing` (`appendix/A_basic.tex:257-266`, proof `:268-279`): "Under Assumption `ass:regularity`, for every `n,m ≥ 1`,
  `δ ∈ (0,1)` and every realization of the samples, the map `α ↦ D̂_{α,k}` is continuous and nonincreasing on `[0,1)`, and
  `{α ∈ [0,1) : D̂_{α,k} ≤ τ_{n,m}(α,δ)} = [α̂,1)`. In particular the infimum in `eq:alphaest` is attained,
  `{α̂ ≤ a} = {D̂_{a,k} ≤ τ_{n,m}(a,δ)}` for every `a ∈ [0,1)`, and `α̂` is a measurable function of the samples."
* `cor:confset` (`sections/05_estimator.tex:151-155` (`ω^←`), `:157-167`, the remark `:169`; proof `appendix/A_basic.tex:317-334`):
  "`ω^←(u) = sup{ε ∈ [0,1] : ω(ε) ≤ u}` …, which equals 1 when `u ≥ ω(1)`. Let `ass:regularity` hold with `α* = TV(P,Q) < 1`, and
  let `ω : [0,1] → [0,∞)` be strictly increasing and continuous with `ω(0) = 0` and `D_{α*−ε,k}(P,Q) ≥ ω(ε)` for every
  `ε ∈ [0,α*]`. Fix `δ ∈ (0,1)` and `ᾱ ∈ [0,1)`, and put `â = sup{a ∈ [0,ᾱ] : a ≤ α̂ + ω^←(2τ_{n,m}(a,δ))}`. If `α* ≤ ᾱ`, then
  `P(α̂ ≤ α* ≤ â) ≥ 1 − δ` for every `n,m ≥ 1`. Moreover `â ≤ α̂ + ω^←(2τ_{n,m}(ᾱ,δ))`." Remark: "The set defining `â` always
  contains 0, so `â` is well defined."
* `cor:upperfs` (`sections/06_splitting.tex:191-200`, proof `appendix/B_split.tex:177-184`): "Let `ass:regularity` hold with
  `α* = TV(P,Q) < 1`, let `ω` be as in `cor:confset`, fix `δ ∈ (0,1)`, and put `Ď_α = D̂_{α,k} + τ_{n,m}(α,δ)`. Then, for every
  `n,m ≥ 1`, with probability at least `1 − δ`, `D_{α,k}(P,Q) ≤ Ď_α` for every `α ∈ [0,1)` simultaneously, and
  `TV(P,Q) ≤ α̂_hi := inf_{α ∈ [0,1)} {α + ω^←(Ď_α)}`."
* the sentence after `cor:consistency` (`sections/05_estimator.tex:114-117`): "The rate condition cannot be dropped. With `n = m`
  and `δ_{n,n} = e^{−n}`, `τ_{n,n}(α,δ_{n,n}) ≥ 2κ√(2 log(4/δ_{n,n})/n) > 2√2 κ > 2κ ≥ D̂_{α,k}` for every `α`, so `α̂_{n,n} = 0`
  for every sample and `α̂_{n,n}` does not converge to `α* > 0`." (`cor:consistency` `:102-112`: `δ_{n,m} → 0` and
  `log(1/δ_{n,m})/min(n,m) → 0`.)
* `rem:grid` (`sections/05_estimator.tex:34-42`): "An implementation evaluates the test on a grid of mesh `h` and returns the
  smallest grid level `α̂_grid` at which it does not reject. Because the non-rejected levels form the interval `[α̂,1)`, `α̂_grid`
  is at most one mesh above `α̂`, so `P(α̂_grid ≤ α* + h) ≥ 1 − δ`. What the data certify is `α* > α_last`, the largest grid level
  actually rejected, which holds with probability at least `1 − δ` on the same event."
* the level of `eq:test` for every bounded kernel (`sections/04_test.tex:92-108`; proof of `lem:nullbound`
  `appendix/A_basic.tex:94-106`): "the rule reject `H_{0,α}` if `D̂_{α,k} > r_n(α,δ/2) + r_m(α,δ/2)` is a level-`δ` test. If an
  implementation returns the squared value `eq:qp`, the comparison is with the square of the right-hand side. … Its level does not
  use (A3). … So the test is valid for every bounded measurable kernel with a separable RKHS, characteristic or not."

Reuses (imported, not copied) the frozen `TrimmedMMD` (`rn`, `tau`, `crossSet`, `alphaHat`), `TrimmedMMD/Concentration`
(`region`, `empirical`), `TrimmedMMD/Unconditional` (`setDist`, `Dpop`, `Demp`) and, through `TrimmedMMD/ZeroSet`,
`StatFormal.Distances.tvDist`.

Encodings (see card `certify/cards/wave30tl.md`):
* (A1)–(A2) as in every frozen trimmed-MMD claim: `H` a real separable Hilbert space, `φ : 𝒳 → H` strongly measurable with
  `‖φ x‖ ≤ κ` (Pettis). (A3) (characteristic kernel) is NOT assumed in any claim: a generalisation (none of the proofs needs it).
  `κ` is any real bound (no `κ > 0`), except in the strict chain `ratecond_chain`, where `κ > 0` is needed for "`>`".
* Samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)` with the product law; "with probability at least `1 − δ`"
  is a measurable event of probability `≥ 1 − δ` inside the claimed set (the convention of `TrimmedMMD/Unconditional`); the
  level of the test is the (outer) measure of the rejection region, which is moreover shown measurable.
* `ω^←` is `omegaGen` (an `sSup` over `[0,1]`: bounded above by 1, and `≥ 0` even at `sSup ∅ = 0`). In `confset` and `upperfs`
  (`ω(0) = 0`) its set contains 0 at every argument used, `2τ ≥ 0` and `Ď ≥ 0` (`κ ≥ 0` is automatic as soon as a sample or a law
  exists, since `‖φ x‖ ≤ κ`), so `sSup ∅` is never live there; in `aHat_wellDefined`, `confset_crude` and `alphaHi_isGLB` `ω` is
  arbitrary, so the junk value can be live, and those claims hold for every `ω`. `omegaGen_spec` certifies that `omegaGen` is the
  generalized inverse.
  `â` is `aHat` (an `sSup` over `[0,ᾱ]`, whose set contains 0: certified by `aHat_wellDefined`); `α̂_hi` is `alphaHi` (an `sInf`
  of a nonempty set bounded below by 0: certified by `alphaHi_isGLB`).
* `α* = TV(P,Q)` throughout (`tvDist`); `D_{α,k}(P,Q) = Dpop`, `D̂_{α,k} = Demp`.
* `rem:grid`: a "grid of mesh `h`" is a finite set of levels in `[0,1)` such that every `t ≥ 0` lying below some grid level has a
  grid level in `[t, t+h]` (`MeshGrid`; e.g. `{0, h, 2h, …}`; equivalently: the first level is `≤ h` and consecutive gaps are `≤ h`;
  the first-level clause is needed, since for `G = {1/2}`, `h = 1/100` and `α̂ = 0` the printed bound fails); `α̂_grid` is any `a`
  with `GridReturn`: the smallest grid level at
  which the test does not reject, or — when it rejects at every grid level, where the remark is silent — the last grid level (the
  convention of the package, `src/trimmedmmd/estimate.py:24-25`); `α_last` is any `b` with `LastRejected` (the largest rejected grid
  level; when none is rejected the clause is vacuous).
* The event of `grid_prob` does not depend on the grid: one event serves every grid and mesh at once ("on the same event").
* "does not converge to `α*`" is the negation of the convergence-in-probability encoding of the frozen Wave 18b `cor_consistency`
  (no measurable events `E_n ⊆ {|α̂_{n,n} − α*| ≤ e}` with `P(E_n) → 1`), for every `e ∈ (0, α*)`, along `n → ∞`.
FROZEN 2026-11-07 after an independent critic's pre-freeze review (19 claims: none false, no statement change; docstring fixes and
two strengthenings applied: `grid_prob` uniform in the grid, `ratecond_schedule` with the non-convergence of the rate). Hashed in
`certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-- `ω^←(u) = sup{ε ∈ [0,1] : ω(ε) ≤ u}`, the generalized inverse of `cor:confset`. -/
def omegaGen (ω : ℝ → ℝ) (u : ℝ) : ℝ := sSup {e | e ∈ Icc (0 : ℝ) 1 ∧ ω e ≤ u}

/-- `â = sup{a ∈ [0, ᾱ] : a ≤ α̂ + ω^←(2τ(a))}` (`cor:confset`); `ah` is `α̂`, `τ a = τ_{n,m}(a,δ)`, `ab` is `ᾱ`. -/
def aHat (ω : ℝ → ℝ) (ah : ℝ) (τ : ℝ → ℝ) (ab : ℝ) : ℝ :=
  sSup {a | a ∈ Icc (0 : ℝ) ab ∧ a ≤ ah + omegaGen ω (2 * τ a)}

/-- `α̂_hi = inf_{α ∈ [0,1)} {α + ω^←(Ď_α)}` (`cor:upperfs`). -/
def alphaHi (ω : ℝ → ℝ) (Dc : ℝ → ℝ) : ℝ := sInf ((fun α => α + omegaGen ω (Dc α)) '' Ico (0 : ℝ) 1)

/-- The margin hypothesis of `cor:confset` (also "`ω` as in `cor:confset`" of `cor:upperfs`): `ω : [0,1] → [0,∞)` strictly
increasing and continuous with `ω(0) = 0`, and `D_{α*−ε,k}(P,Q) ≥ ω(ε)` for every `ε ∈ [0, α*]`, `α* = TV(P,Q)`. -/
def KnownMargin {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (P Q : Measure 𝒳) (ω : ℝ → ℝ) : Prop :=
  StrictMonoOn ω (Icc 0 1) ∧ ContinuousOn ω (Icc 0 1) ∧ ω 0 = 0 ∧ (∀ e ∈ Icc (0 : ℝ) 1, 0 ≤ ω e) ∧
    ∀ e ∈ Icc 0 (StatFormal.Distances.tvDist P Q),
      ω e ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e)

/-- `rem:grid`: `G` is a grid of levels in `[0,1)` of mesh at most `h`: every `t ≥ 0` below some grid level has a grid level
in `[t, t + h]`. -/
def MeshGrid (G : Finset ℝ) (h : ℝ) : Prop :=
  (∀ g ∈ G, 0 ≤ g ∧ g < 1) ∧ ∀ t : ℝ, 0 ≤ t → (∃ g ∈ G, t ≤ g) → ∃ g ∈ G, t ≤ g ∧ g ≤ t + h

/-- `rem:grid`: `a` is the level returned on the grid — the smallest grid level at which the test does not reject
(`D̂_g ≤ τ(g)`), or, if the test rejects at every grid level, the last grid level (the package's convention). -/
def GridReturn (G : Finset ℝ) (Dh τ : ℝ → ℝ) (a : ℝ) : Prop :=
  IsLeast {g | g ∈ G ∧ Dh g ≤ τ g} a ∨ ((∀ g ∈ G, τ g < Dh g) ∧ IsGreatest {g | g ∈ G} a)

/-- `rem:grid`: `b = α_last`, the largest grid level actually rejected (`D̂_g > τ(g)`). -/
def LastRejected (G : Finset ℝ) (Dh τ : ℝ → ℝ) (b : ℝ) : Prop :=
  IsGreatest {g | g ∈ G ∧ τ g < Dh g} b

namespace Claims

/-! ### `lem:crossing` -/

/-- `lem:crossing`, first clause: for every `n, m ≥ 1` and every realization of the samples, `α ↦ D̂_{α,k}` is continuous and
nonincreasing on `[0,1)`. -/
def crossing_path : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        ContinuousOn (Demp φ x y) (Ico 0 1) ∧ AntitoneOn (Demp φ x y) (Ico 0 1)

/-- `lem:crossing`, the display: `{α ∈ [0,1) : D̂_{α,k} ≤ τ_{n,m}(α,δ)} = [α̂, 1)` for every realization. -/
def crossing_set : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        crossSet (Demp φ x y) (fun α => tau κ α δ n m) = Ico (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) 1

/-- `lem:crossing`: "the infimum in `eq:alphaest` is attained" (`α̂` is the least element of the crossing set). -/
def crossing_attained : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        IsLeast (crossSet (Demp φ x y) (fun α => tau κ α δ n m)) (alphaHat (Demp φ x y) (fun α => tau κ α δ n m))

/-- `lem:crossing`: `{α̂ ≤ a} = {D̂_{a,k} ≤ τ_{n,m}(a,δ)}` (as sets of samples) for every `a ∈ [0,1)`. -/
def crossing_le_iff : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ a} =
          {z : (Fin n → 𝒳) × (Fin m → 𝒳) | Demp φ z.1 z.2 a ≤ tau κ a δ n m}

/-- `lem:crossing`, last clause: `α̂` is a measurable function of the samples (and so is `D̂_{a,k}` for each `a ∈ [0,1)`, the
step of the proof). -/
def crossing_measurable : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      (∀ a : ℝ, 0 ≤ a → a < 1 → Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Demp φ z.1 z.2 a) ∧
        Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)

/-! ### `cor:confset` -/

/-- The sentence before `cor:confset`: `ω^←` is the generalized inverse of a strictly increasing continuous `ω` on `[0,1]` with
`ω(0) = 0` (it inverts `ω` on `[0, ω(1)]`), and it equals `1` when `u ≥ ω(1)`. -/
def omegaGen_spec : Prop :=
  ∀ ω : ℝ → ℝ, StrictMonoOn ω (Icc 0 1) → ContinuousOn ω (Icc 0 1) → ω 0 = 0 →
    (∀ u ∈ Icc 0 (ω 1), omegaGen ω u ∈ Icc (0 : ℝ) 1 ∧ ω (omegaGen ω u) = u) ∧
      ∀ u, ω 1 ≤ u → omegaGen ω u = 1

/-- The remark after `cor:confset`: "the set defining `â` always contains 0, so `â` is well defined" (it is the genuine least
upper bound of that set), for every realization of the samples and any `ω`. -/
def aHat_wellDefined : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ ab : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 0 ≤ ab → ab < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (0 : ℝ) ∈ {a | a ∈ Icc (0 : ℝ) ab ∧
            a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + omegaGen ω (2 * tau κ a δ n m)} ∧
          IsLUB {a | a ∈ Icc (0 : ℝ) ab ∧
              a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + omegaGen ω (2 * tau κ a δ n m)}
            (aHat ω (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) (fun a => tau κ a δ n m) ab)

/-- `cor:confset`: if `α* = TV(P,Q) ≤ ᾱ`, then `P(α̂ ≤ α* ≤ â) ≥ 1 − δ` for every `n, m ≥ 1`. -/
def confset : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ ab : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 0 ≤ ab → ab < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ ab →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤
                aHat ω (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) (fun a => tau κ a δ n m) ab}

/-- `cor:confset`, last sentence: `â ≤ α̂ + ω^←(2τ_{n,m}(ᾱ,δ))`, for every realization of the samples (and any `ω`). -/
def confset_crude : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ ab : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 0 ≤ ab → ab < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        aHat ω (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) (fun a => tau κ a δ n m) ab ≤
          alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + omegaGen ω (2 * tau κ ab δ n m)

/-! ### `cor:upperfs` -/

/-- Encoding check for `cor:upperfs`: `α̂_hi` is the genuine infimum of `{α + ω^←(Ď_α) : α ∈ [0,1)}` (a nonempty set bounded
below by 0), for every realization of the samples. -/
def alphaHi_isGLB : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        IsGLB ((fun α => α + omegaGen ω (Demp φ x y α + tau κ α δ n m)) '' Ico (0 : ℝ) 1)
          (alphaHi ω (fun α => Demp φ x y α + tau κ α δ n m))

/-- `cor:upperfs`: for every `n, m ≥ 1`, with probability at least `1 − δ`, `D_{α,k}(P,Q) ≤ Ď_α = D̂_{α,k} + τ_{n,m}(α,δ)` for
every `α ∈ [0,1)` simultaneously, and `TV(P,Q) ≤ α̂_hi`. -/
def upperfs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | (∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + tau κ α δ n m) ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHi ω (fun α => Demp φ z.1 z.2 α + tau κ α δ n m)}

/-! ### "The rate condition cannot be dropped" (after `cor:consistency`) -/

/-- The schedule `n = m`, `δ_{n,n} = e^{−n}`: `δ_{n,n} ∈ (0,1)` for `n ≥ 1` and `δ_{n,n} → 0`, but
`log(1/δ_{n,n})/min(n,n) = 1` for every `n ≥ 1`, so the rate condition of `cor:consistency` fails (does not tend to 0). -/
def ratecond_schedule : Prop :=
  Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < Real.exp (-(n : ℝ)) ∧ Real.exp (-(n : ℝ)) < 1 ∧
      Real.log (1 / Real.exp (-(n : ℝ))) / (min n n : ℕ) = 1) ∧
    ¬ Tendsto (fun n : ℕ => Real.log (1 / Real.exp (-(n : ℝ))) / (min n n : ℕ)) atTop (𝓝 0)

/-- The chain `τ_{n,n}(α,δ_{n,n}) ≥ 2κ√(2 log(4/δ_{n,n})/n) > 2√2 κ > 2κ` for every `α ∈ [0,1)`, `n ≥ 1`, `κ > 0`. -/
def ratecond_chain : Prop :=
  ∀ (κ α : ℝ) (n : ℕ), 0 < κ → 1 ≤ n → 0 ≤ α → α < 1 →
    2 * κ * √(2 * Real.log (4 / Real.exp (-(n : ℝ))) / n) ≤ tau κ α (Real.exp (-(n : ℝ))) n n ∧
      2 * √2 * κ < 2 * κ * √(2 * Real.log (4 / Real.exp (-(n : ℝ))) / n) ∧
      2 * κ < 2 * √2 * κ

/-- `2κ ≥ D̂_{α,k}` for every `α ∈ [0,1)`, so `α̂_{n,n} = 0` for every sample, at `δ_{n,n} = e^{−n}`. -/
def ratecond_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n →
      ∀ x y : Fin n → 𝒳, (∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ 2 * κ) ∧
        alphaHat (Demp φ x y) (fun α => tau κ α (Real.exp (-(n : ℝ))) n n) = 0

/-- "`α̂_{n,n}` does not converge to `α* > 0`": if `α* = TV(P,Q) > 0`, then for every `e ∈ (0, α*)` there are no measurable
events `E_n ⊆ {|α̂_{n,n} − α*| ≤ e}` with `P(E_n) → 1` (the negation of the frozen Wave 18b `cor_consistency` conclusion along
`n = m → ∞`, `δ_{n,n} = e^{−n}`). -/
def ratecond_noconv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < StatFormal.Distances.tvDist P Q →
      ∀ e : ℝ, 0 < e → e < StatFormal.Distances.tvDist P Q →
        ¬ ∃ E : ∀ n : ℕ, Set ((Fin n → 𝒳) × (Fin n → 𝒳)), (∀ n, MeasurableSet (E n)) ∧
          (∀ n, E n ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tau κ α (Real.exp (-(n : ℝ))) n n) -
            StatFormal.Distances.tvDist P Q| ≤ e}) ∧
          Tendsto (fun n => ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n)) atTop (𝓝 1)

/-! ### `rem:grid` -/

/-- `rem:grid`, deterministic part: for every realization, the returned grid level is at most one mesh above `α̂`
(`α̂_grid ≤ α̂ + h`), and every rejected grid level, in particular `α_last`, lies below `α̂`. -/
def grid_mesh : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ h : ℝ) (n m : ℕ) (G : Finset ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → MeshGrid G h →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (∀ a, GridReturn G (Demp φ x y) (fun α => tau κ α δ n m) a →
            a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + h) ∧
          ∀ b, LastRejected G (Demp φ x y) (fun α => tau κ α δ n m) b →
            b < alphaHat (Demp φ x y) (fun α => tau κ α δ n m)

/-- `rem:grid`: with `α* = TV(P,Q) < 1`, on one event of probability at least `1 − δ` (the same for every grid and mesh),
`α̂_grid ≤ α* + h` and `α* > α_last`. -/
def grid_prob : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (G : Finset ℝ) (h : ℝ), MeshGrid G h →
              (∀ a, GridReturn G (Demp φ z.1 z.2) (fun α => tau κ α δ n m) a →
                  a ≤ StatFormal.Distances.tvDist P Q + h) ∧
              ∀ b, LastRejected G (Demp φ z.1 z.2) (fun α => tau κ α δ n m) b →
                b < StatFormal.Distances.tvDist P Q}

/-! ### The level of `eq:test` for every bounded kernel -/

/-- `eq:test` is a level-`δ` test for every kernel satisfying (A1)–(A2), characteristic or not: under `H_{0,α}`
(`TV(P,Q) ≤ α`), the rejection region `{D̂_{α,k} > r_n(α,δ/2) + r_m(α,δ/2)}` is measurable and has probability at most `δ`, for
every `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1`. -/
def test_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    StatFormal.Distances.tvDist P Q ≤ α →
      MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | rn κ α (δ / 2) n + rn κ α (δ / 2) m < Demp φ z.1 z.2 α} ∧
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
            {z | rn κ α (δ / 2) n + rn κ α (δ / 2) m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- After `eq:test`: "if an implementation returns the squared value `eq:qp`, the comparison is with the square of the
right-hand side" — for every realization, `D̂_{α,k} > r_n + r_m ⇔ D̂_{α,k}² > (r_n + r_m)²` (that `eq:qp` returns `D̂²` is the
frozen, certified Wave 8a `georep_qp`; not restated here). -/
def test_squared : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (rn κ α (δ / 2) n + rn κ α (δ / 2) m < Demp φ x y α ↔
          (rn κ α (δ / 2) n + rn κ α (δ / 2) m) ^ 2 < Demp φ x y α ^ 2)

end Claims
end StatFormal.Wave30tl
