import StatFormal.Wave30tl.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tl, revision: trimmed-mmd (JMLR version) at commit `62afb2a` — the revised `cor:confset`, the
# interval sentence after `cor:upperfs`, and the revised `rem:grid`

The frozen `StatFormal/Wave30tl/Statements.lean` was locked from the JMLR text at trimmed-mmd commit `e1869dd`. Eight minutes later
the author's commit `62afb2a` ("re-check fixes, closed-form confidence interval") replaced `cor:confset` (no `ᾱ`, no `â`), added a
sentence after `cor:upperfs` and gave `rem:grid` an explicit fallback. The earlier file is not edited (trust model); its claims
remain true and are certified as the superseded printed version. This file freezes the revised printed text.

Source: `trimmed-mmd/jmlr/` at commit `62afb2a` (read-only, read 2026-11-07; sha256 at that commit `sections/05_estimator.tex`
`309824c6…`, `sections/06_splitting.tex` `1114c20c…`, `appendix/A_basic.tex` `579019de…`, `appendix/B_split.tex` `59e3ba30…`):
* `cor:confset` (`sections/05_estimator.tex:152-156` (`ω^←`), `:158-166`; proof `appendix/A_basic.tex:318-330`): "Let
  `ass:regularity` hold with `α* = TV(P,Q) < 1`, and let `ω : [0,1] → [0,∞)` be strictly increasing and continuous with
  `ω(0) = 0` and `D_{α*−ε,k}(P,Q) ≥ ω(ε)` for every `ε ∈ [0,α*]`. Fix `δ ∈ (0,1)`. Then for every `n,m ≥ 1`,
  `P(α̂ ≤ α* ≤ α̂ + ω^←(2τ_{n,m}(α̂,δ))) ≥ 1 − δ`."
* the sentence after it (`:168-169`): "Since `τ_{n,m}(α̂,δ) ≤ τ_{n,m}(α*,δ)` on the same event, the width is at most the `ε_{n,m}` of
  Theorem `thm:rate` whenever that theorem applies, and it is computable from the data."
* the sentence after `cor:upperfs` (`sections/06_splitting.tex:202-204`): "Taking `α = α̂` in the infimum gives
  `α̂_hi ≤ α̂ + ω^←(2τ_{n,m}(α̂,δ))`, the upper end of Corollary `cor:confset`, and both hold on the same event, so `[α̂, α̂_hi]` is
  a `1 − δ` interval for every sample size."
* `rem:grid` (`sections/05_estimator.tex:34-43`): "An implementation evaluates the test on a grid of mesh `h` and returns the
  smallest grid level `α̂_grid` at which it does not reject, or 1 if it rejects at every grid level. Because the non-rejected levels
  form the interval `[α̂,1)`, `α̂_grid` is at most one mesh above `α̂`, so `P(α̂_grid ≤ α* + h) ≥ 1 − δ`. What the data certify is
  `α* > α_last`, the largest grid level actually rejected, which holds with probability at least `1 − δ` on the same event."

Reuses (imported, not copied) the frozen Wave 30tl definitions `omegaGen` (`ω^←`), `alphaHi` (`α̂_hi`), `KnownMargin` (the margin
hypothesis of `cor:confset`), `LastRejected` (`α_last`), and through them `TrimmedMMD` (`tau`, `alphaHat`), `Unconditional`
(`Dpop`, `Demp`), `tvDist`.

Encodings (see card `certify/cards/wave30tl.md`): as in the frozen Wave 30tl file ((A1)–(A2) as a separable Hilbert space and a
strongly measurable feature map `‖φ‖ ≤ κ`; (A3) not assumed — a generalisation; any real `κ`; probabilities as a measurable event of
probability `≥ 1 − δ` inside the claimed set; `α* = TV(P,Q)`). In addition:
* `ω^←(2τ(α̂))`: `2τ ≥ 0 = ω(0)`, so the set of `omegaGen` contains 0 and `sSup ∅` is not live (`κ ≥ 0` is automatic once a law
  exists); in `alphaHi_le` `ω` is arbitrary, and the claim holds for every `ω`.
* "the `ε_{n,m}` of Theorem `thm:rate` whenever that theorem applies": any `ε ∈ [0, α*]` with `ω(ε) = 2τ_{n,m}(α*,δ)` (the encoding
  of the frozen `TrimmedMMD.rate`; such `ε` exists exactly when `2τ_{n,m}(α*,δ) ≤ ω(α*)`, the hypothesis of `thm:rate`).
* `rem:grid`: a grid of mesh `h` of `[0,1)` (`MeshGridUnit`): levels in `[0,1)`, and every `t ∈ [0,1)` has a grid level in
  `[t, t+h]` unless `t + h ≥ 1` (first level `≤ h`, gaps `≤ h`, last level `≥ 1 − h`; e.g. `{0, h, 2h, …} ∩ [0,1)`). With the
  fallback value 1 the last-level clause is needed: for `G = {0}`, `h = 1/100` and `α̂ = 1/2` every level is rejected and
  `α̂_grid = 1 > α̂ + h`. `α̂_grid` is any `a` with `GridReturnOne` (the smallest non-rejected grid level, or 1 if every grid level
  is rejected); the event of `grid_prob_one` serves every grid and mesh at once. The package (`src/trimmedmmd/estimate.py:24-25`
  at `62afb2a`) still returns the last grid level in that case; that convention is the one certified by the frozen Wave 30tl
  `GridReturn` claims.
FROZEN 2026-11-07 after an independent critic's pre-freeze review (6 claims ACCEPT, no change). Hashed in `certify/statements.lock`
(with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl.Revision

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

/-- `rem:grid` (revised text): `G` is a grid of mesh `h` of `[0,1)` — levels in `[0,1)`, and every `t ∈ [0,1)` has a grid level in
`[t, t + h]` unless `t + h ≥ 1`. -/
def MeshGridUnit (G : Finset ℝ) (h : ℝ) : Prop :=
  (∀ g ∈ G, 0 ≤ g ∧ g < 1) ∧ ∀ t : ℝ, 0 ≤ t → t < 1 → 1 ≤ t + h ∨ ∃ g ∈ G, t ≤ g ∧ g ≤ t + h

/-- `rem:grid` (revised text): `a = α̂_grid`, the smallest grid level at which the test does not reject (`D̂_g ≤ τ(g)`), or `1`
if it rejects at every grid level. -/
def GridReturnOne (G : Finset ℝ) (Dh τ : ℝ → ℝ) (a : ℝ) : Prop :=
  IsLeast {g | g ∈ G ∧ Dh g ≤ τ g} a ∨ ((∀ g ∈ G, τ g < Dh g) ∧ a = 1)

namespace Claims

/-! ### `cor:confset` (revised) -/

/-- `cor:confset`: for every `n, m ≥ 1`, `P(α̂ ≤ α* ≤ α̂ + ω^←(2τ_{n,m}(α̂,δ))) ≥ 1 − δ`, `α* = TV(P,Q)`. -/
def confset_ci : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) +
                omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m)}

/-- The sentence after `cor:confset`: on one event of probability at least `1 − δ`, the interval of `cor:confset` covers `α*`,
`τ_{n,m}(α̂,δ) ≤ τ_{n,m}(α*,δ)`, and the width `ω^←(2τ_{n,m}(α̂,δ))` is at most the `ε_{n,m}` of `thm:rate` (any `ε ∈ [0,α*]`
with `ω(ε) = 2τ_{n,m}(α*,δ)`) whenever that theorem applies. -/
def confset_width : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) +
                omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m) ∧
              tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m ≤
                tau κ (StatFormal.Distances.tvDist P Q) δ n m ∧
              ∀ ε ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
                ω ε = 2 * tau κ (StatFormal.Distances.tvDist P Q) δ n m →
                  omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m) ≤ ε}

/-! ### The sentence after `cor:upperfs` -/

/-- "Taking `α = α̂` in the infimum gives `α̂_hi ≤ α̂ + ω^←(2τ_{n,m}(α̂,δ))`": for every realization of the samples and any `ω`. -/
def alphaHi_le : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        alphaHi ω (fun α => Demp φ x y α + tau κ α δ n m) ≤
          alphaHat (Demp φ x y) (fun α => tau κ α δ n m) +
            omegaGen ω (2 * tau κ (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) δ n m)

/-- "… and both hold on the same event, so `[α̂, α̂_hi]` is a `1 − δ` interval for every sample size": one event of probability
at least `1 − δ`, for every `n, m ≥ 1`, on which `D_{α,k} ≤ Ď_α` for all `α ∈ [0,1)`, `α̂ ≤ α* ≤ α̂_hi`, and
`α̂_hi ≤ α̂ + ω^←(2τ_{n,m}(α̂,δ))`. -/
def upperfs_interval : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (ω : ℝ → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 → KnownMargin φ P Q ω →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | (∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + tau κ α δ n m) ∧
              alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
              StatFormal.Distances.tvDist P Q ≤ alphaHi ω (fun α => Demp φ z.1 z.2 α + tau κ α δ n m) ∧
              alphaHi ω (fun α => Demp φ z.1 z.2 α + tau κ α δ n m) ≤
                alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) +
                  omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m)}

/-! ### `rem:grid` (revised) -/

/-- `rem:grid`, deterministic part, with the fallback value 1: for every realization, `α̂_grid ≤ α̂ + h`, and every rejected grid
level, in particular `α_last`, lies below `α̂`. -/
def grid_mesh_one : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ δ h : ℝ) (n m : ℕ) (G : Finset ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → MeshGridUnit G h →
      ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
        (∀ a, GridReturnOne G (Demp φ x y) (fun α => tau κ α δ n m) a →
            a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + h) ∧
          ∀ b, LastRejected G (Demp φ x y) (fun α => tau κ α δ n m) b →
            b < alphaHat (Demp φ x y) (fun α => tau κ α δ n m)

/-- `rem:grid`, with the fallback value 1: with `α* = TV(P,Q) < 1`, on one event of probability at least `1 − δ` (the same for
every grid and mesh), `α̂_grid ≤ α* + h` and `α* > α_last`. -/
def grid_prob_one : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → StatFormal.Distances.tvDist P Q < 1 →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (G : Finset ℝ) (h : ℝ), MeshGridUnit G h →
              (∀ a, GridReturnOne G (Demp φ z.1 z.2) (fun α => tau κ α δ n m) a →
                  a ≤ StatFormal.Distances.tvDist P Q + h) ∧
              ∀ b, LastRejected G (Demp φ z.1 z.2) (fun α => tau κ α δ n m) b →
                b < StatFormal.Distances.tvDist P Q}

end Claims
end StatFormal.Wave30tl.Revision
