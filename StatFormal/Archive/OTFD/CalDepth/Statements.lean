import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.EReal.Basic
import Mathlib.Order.Monotone.Basic

/-!
# FROZEN STATEMENTS — otfd B / C: the conformal (calibrated) depth

Sources (verbatim in `inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`): B `prop:cal-depth`
(`papers/B_bands/supplement.tex:6532`), C `prop:cond-cal-depth` (`papers/C_conditional/supplement.tex:1826`; "the
argument is identical"), with the score `V* = max{H, T}` (`H` the probability-scale depth score, `T` the
reconstruction-accuracy score), the calibration scores `c_i = V*(X_i)`, `i ∈ 𝓘₂` (`n₂ = m`), and
`D̃(x) = ψ(V*(x))`, `ψ(s) = (1 + #{i : c_i ≥ s})/(m+1)`.

Abstraction (see card): `H`, `T` (hence `V*`) are fitted on `𝓘₁`; conditionally on `𝓘₁` they are fixed functions, so
(i)–(ii) are stated for an exchangeable score vector `(V*(X_{n+1}), V*(X_i))_{i ∈ 𝓘₂}` = `S ω : Fin (m+1) → ℝ`
(index `0` the new curve), and (ii)–(iv) as deterministic facts about `ψ` and any `H, T` on any space `X`. C is the
same with pairs `(x, y)` and `H = A(y|x)`, `T = B(y)`, `X = 𝒳 × 𝒴` — instances of these claims. `s_α`, "the
`⌊α(m+1)⌋`-th largest calibration score, `+∞` if this index is `0`", is `kthLargest` (`EReal`). Not formalised: the
computation of `H, T` from the fits; the clause "`lem:cal-blind` remains in force" of (iii) (immediate once `ψ ∘ V*`
factors through the score); joint measurability needed to uncondition (as in otfd G). In (iv) the premise
`Π_K x = Π_K x'` enters only through its consequence `H(x) = H(x')` (`H` depends on `Π_K x` only, as in `lem:cal-blind`),
a weaker hypothesis; `T = Ĝ ∘ r_K`. (i) and (ii) hold for every `α` (outside `(0,1)` they are trivial).
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Finset

namespace StatFormal.OTFD.CalDepth

/-- `ψ(s) = (1 + #{i : c_i ≥ s})/(m+1)`. -/
def calDepth {m : ℕ} (c : Fin m → ℝ) (s : ℝ) : ℝ :=
  (1 + ((univ.filter fun i => s ≤ c i).card : ℝ)) / (m + 1)

/-- The `k`-th largest calibration score (`⊤` for `k = 0`, `⊥` for `k > m`). -/
def kthLargest {m : ℕ} (k : ℕ) (c : Fin m → ℝ) : EReal :=
  sSup {t : EReal | k ≤ (univ.filter fun i => t ≤ ((c i : ℝ) : EReal)).card}

namespace Claims

/-- (i) exact scale: `P(D̃(X_{n+1}) ≤ α) ≤ α` for every `α ∈ (0,1)`. -/
def exact_scale : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (S : Ω → Fin (m + 1) → ℝ),
    Measurable S → (∀ τ : Equiv.Perm (Fin (m + 1)), P.map (fun ω => S ω ∘ τ) = P.map S) →
    ∀ α : ℝ,
      P {ω | calDepth (fun i : Fin m => S ω i.succ) (S ω 0) ≤ α} ≤ ENNReal.ofReal α

/-- (ii) level sets: `{D̃ > α} = {H ≤ s_α} ∩ {T ≤ s_α}`. -/
def level_sets : Prop :=
  ∀ (X : Type) (m : ℕ) (c : Fin m → ℝ) (H T : X → ℝ) (α : ℝ),
    {x | α < calDepth c (max (H x) (T x))} =
      {x | ((H x : ℝ) : EReal) ≤ kthLargest ⌊α * (m + 1)⌋₊ c} ∩
        {x | ((T x : ℝ) : EReal) ≤ kthLargest ⌊α * (m + 1)⌋₊ c}

/-- (ii) coverage: `P(X_{n+1} ∈ {D̃ > α}) ≥ 1 − α` (a measurable event of that probability). -/
def level_coverage : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (S : Ω → Fin (m + 1) → ℝ),
    Measurable S → (∀ τ : Equiv.Perm (Fin (m + 1)), P.map (fun ω => S ω ∘ τ) = P.map S) →
    ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ P E ∧
        E ⊆ {ω | α < calDepth (fun i : Fin m => S ω i.succ) (S ω 0)}

/-- (iii) `ψ` is nonincreasing and constant between consecutive calibration scores, so `D̃ = ψ ∘ V*` coarsens the
order of `V*`. -/
def step_function : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℝ),
    Antitone (calDepth c) ∧
      ∀ s s' : ℝ, s ≤ s' → (∀ i, ¬ (s ≤ c i ∧ c i < s')) → calDepth c s = calDepth c s'

/-- (iv) separation: if `H(x) = H(x')`, `T(x) ≠ T(x')` and one of them exceeds `H(x)`, then `V*(x) ≠ V*(x')`, and
`D̃(x) ≠ D̃(x')` iff some calibration score lies in `[min V*, max V*)`. -/
def separates : Prop :=
  ∀ (X : Type) (m : ℕ) (c : Fin m → ℝ) (H T : X → ℝ) (x x' : X),
    H x = H x' → T x ≠ T x' → H x < max (T x) (T x') →
      max (H x) (T x) ≠ max (H x') (T x') ∧
      (calDepth c (max (H x) (T x)) ≠ calDepth c (max (H x') (T x')) ↔
        ∃ i, min (max (H x) (T x)) (max (H x') (T x')) ≤ c i ∧
          c i < max (max (H x) (T x)) (max (H x') (T x')))

end Claims
end StatFormal.OTFD.CalDepth
