import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# FROZEN STATEMENTS — trimmed MMD: the threshold-crossing estimator `α̂`

Source: `trimmed-mmd/paper.tex` (verbatim in `inventory/extracted/trimmed-mmd.md`):
`eq:radius` (l.775), `cor:uniform` (l.785), `eq:alphaest` (l.903) and its well-definedness sentence,
`thm:consistency` (l.964), `ass:margin` (l.1004), `thm:rate` (l.1018).

Scope (conditional formalisation, see the card):
* the population discrepancy `D α = D_{α,k}(P,Q)` is an abstract function with the properties the
  paper establishes elsewhere (`D α* = 0`, `D > 0` below `α*`, nonincreasing; `ass:margin`);
* the concentration of `thm:concentration` + `cor:uniform` + `lem:projstab`(i) enters as two events
  `EP`, `EQ` (one per sample) of probability `≥ 1 - δ/2` on whose intersection
  `|D̂_α - D_α| ≤ τ_{n,m}(α,δ)` for every `α ∈ [0,1)`;
* `D̂ ≤ 2κ` (`lem:attainment`) enters as a hypothesis of the well-definedness claim.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open Real Set MeasureTheory

namespace StatFormal.TrimmedMMD

/-- `eq:radius`: `r_n(α,δ) = κ/(1-α) · [4/√n + √(2 log(2/δ)/n)]`. -/
def rn (κ α δ : ℝ) (n : ℕ) : ℝ := κ / (1 - α) * (4 / √(n : ℝ) + √(2 * Real.log (2 / δ) / n))

/-- `eq:alphaest`: `τ_{n,m}(α,δ) = r_n(α,δ/2) + r_m(α,δ/2)`. -/
def tau (κ α δ : ℝ) (n m : ℕ) : ℝ := rn κ α (δ / 2) n + rn κ α (δ / 2) m

/-- The crossing set `{α ∈ [0,1) : D̂_α ≤ τ(α)}`. -/
def crossSet (Dh τ : ℝ → ℝ) : Set ℝ := {α | α ∈ Ico (0 : ℝ) 1 ∧ Dh α ≤ τ α}

/-- `eq:alphaest`: `α̂ = inf {α ∈ [0,1) : D̂_α ≤ τ(α)}` (Lean's `sInf`, so well-definedness is a
separate claim). -/
def alphaHat (Dh τ : ℝ → ℝ) : ℝ := sInf (crossSet Dh τ)

namespace Claims

/-- Sentence after `eq:alphaest`: "It is always well defined: `D̂ ≤ 2κ` ... while `τ → ∞` as `α → 1`,
so the crossing set is nonempty." -/
def alphaest_wellDefined : Prop :=
  ∀ (κ δ : ℝ) (n m : ℕ) (Dh : ℝ → ℝ), 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α ∈ Ico (0 : ℝ) 1, Dh α ≤ 2 * κ) →
      (crossSet Dh (fun α => tau κ α δ n m)).Nonempty

/-- `thm:consistency` (i): `P(α̂ ≤ α*) ≥ 1 - δ` for every `n, m ≥ 1`. -/
def consistency_i : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℝ → ℝ) (Dh : Ω → ℝ → ℝ) (κ δ αs : ℝ) (n m : ℕ) (EP EQ : Set Ω),
    0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → αs ∈ Ico (0 : ℝ) 1 → D αs = 0 →
    MeasurableSet EP → MeasurableSet EQ →
    ENNReal.ofReal (1 - δ / 2) ≤ P EP → ENNReal.ofReal (1 - δ / 2) ≤ P EQ →
    (∀ ω ∈ EP ∩ EQ, ∀ α ∈ Ico (0 : ℝ) 1, |Dh ω α - D α| ≤ tau κ α δ n m) →
      ENNReal.ofReal (1 - δ) ≤ P {ω | alphaHat (Dh ω) (fun α => tau κ α δ n m) ≤ αs}

/-- `thm:consistency` (i), second half: if `α* = 0` then `α̂ = 0` exactly, w.p. `≥ 1 - δ`. -/
def consistency_i_zero : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℝ → ℝ) (Dh : Ω → ℝ → ℝ) (κ δ : ℝ) (n m : ℕ) (EP EQ : Set Ω),
    0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → D 0 = 0 →
    MeasurableSet EP → MeasurableSet EQ →
    ENNReal.ofReal (1 - δ / 2) ≤ P EP → ENNReal.ofReal (1 - δ / 2) ≤ P EQ →
    (∀ ω ∈ EP ∩ EQ, ∀ α ∈ Ico (0 : ℝ) 1, |Dh ω α - D α| ≤ tau κ α δ n m) →
      ENNReal.ofReal (1 - δ) ≤ P {ω | alphaHat (Dh ω) (fun α => tau κ α δ n m) = 0}

/-- `thm:consistency` (ii): if `α* > 0`, then for every `ε ∈ (0, α*]` there is `N(ε,δ)` such that for
all `n, m ≥ N`, `P(α* - ε ≤ α̂ ≤ α*) ≥ 1 - δ`. `N` depends on `κ, δ, ε` and on `D` (i.e. on `P, Q`),
not on the samples. -/
def consistency_ii : Prop :=
  ∀ (D : ℝ → ℝ) (κ δ αs : ℝ), 0 < κ → 0 < δ → δ < 1 → αs ∈ Ioo (0 : ℝ) 1 → D αs = 0 →
    AntitoneOn D (Ico 0 1) → (∀ α ∈ Ico (0 : ℝ) αs, 0 < D α) →
    ∀ ε ∈ Ioc (0 : ℝ) αs, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → 1 ≤ n → 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Dh : Ω → ℝ → ℝ) (EP EQ : Set Ω),
        MeasurableSet EP → MeasurableSet EQ →
        ENNReal.ofReal (1 - δ / 2) ≤ P EP → ENNReal.ofReal (1 - δ / 2) ≤ P EQ →
        (∀ ω ∈ EP ∩ EQ, ∀ α ∈ Ico (0 : ℝ) 1, |Dh ω α - D α| ≤ tau κ α δ n m) →
          ENNReal.ofReal (1 - δ) ≤
            P {ω | alphaHat (Dh ω) (fun α => tau κ α δ n m) ∈ Icc (αs - ε) αs}

/-- `thm:rate` under `ass:margin`: with `ω` strictly increasing on `[0, α*]`,
`D(α* - e) ≥ ω(e)` for `e ∈ [0, α*]`, and `ε_{n,m} = ω⁻¹(2τ(α*))` (encoded as: `ε ∈ [0, α*]` with
`ω ε = 2 τ(α*)`), `P(α* - ε ≤ α̂ ≤ α*) ≥ 1 - δ`. -/
def rate : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℝ → ℝ) (Dh : Ω → ℝ → ℝ) (κ δ αs : ℝ) (n m : ℕ) (EP EQ : Set Ω) (om : ℝ → ℝ) (ε : ℝ),
    0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → αs ∈ Ico (0 : ℝ) 1 → D αs = 0 →
    StrictMonoOn om (Icc 0 αs) → (∀ e ∈ Icc (0 : ℝ) αs, om e ≤ D (αs - e)) →
    ε ∈ Icc (0 : ℝ) αs → om ε = 2 * tau κ αs δ n m →
    MeasurableSet EP → MeasurableSet EQ →
    ENNReal.ofReal (1 - δ / 2) ≤ P EP → ENNReal.ofReal (1 - δ / 2) ≤ P EQ →
    (∀ ω ∈ EP ∩ EQ, ∀ α ∈ Ico (0 : ℝ) 1, |Dh ω α - D α| ≤ tau κ α δ n m) →
      ENNReal.ofReal (1 - δ) ≤
        P {ω | alphaHat (Dh ω) (fun α => tau κ α δ n m) ∈ Icc (αs - ε) αs}

/-- Pathwise form of (i) and of `thm:rate` (critic note N1: the probabilistic claims above are
outer-measure statements, since the event `{α̂ ≤ α*}` is not shown measurable). On the event itself,
deterministically: `α̂ ≤ α*`. -/
def consistency_i_onEvent : Prop :=
  ∀ (D Dh : ℝ → ℝ) (κ δ αs : ℝ) (n m : ℕ), αs ∈ Ico (0 : ℝ) 1 → D αs = 0 →
    (∀ α ∈ Ico (0 : ℝ) 1, |Dh α - D α| ≤ tau κ α δ n m) →
      alphaHat Dh (fun α => tau κ α δ n m) ≤ αs

/-- Pathwise form of `thm:rate`: on the event, `α̂ ∈ [α* - ε_{n,m}, α*]`. -/
def rate_onEvent : Prop :=
  ∀ (D Dh : ℝ → ℝ) (κ δ αs : ℝ) (n m : ℕ) (om : ℝ → ℝ) (ε : ℝ),
    0 < κ → αs ∈ Ico (0 : ℝ) 1 → D αs = 0 →
    StrictMonoOn om (Icc 0 αs) → (∀ e ∈ Icc (0 : ℝ) αs, om e ≤ D (αs - e)) →
    ε ∈ Icc (0 : ℝ) αs → om ε = 2 * tau κ αs δ n m →
    (∀ α ∈ Ico (0 : ℝ) 1, |Dh α - D α| ≤ tau κ α δ n m) →
      alphaHat Dh (fun α => tau κ α δ n m) ∈ Icc (αs - ε) αs

/-- The joint concentration event has probability `≥ 1 - δ` (union bound of `cor:uniform`'s two
events). -/
def event_prob : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ : ℝ) (EP EQ : Set Ω),
    0 < δ → δ < 1 → MeasurableSet EP → MeasurableSet EQ →
    ENNReal.ofReal (1 - δ / 2) ≤ P EP → ENNReal.ofReal (1 - δ / 2) ≤ P EQ →
      ENNReal.ofReal (1 - δ) ≤ P (EP ∩ EQ)

end Claims
end StatFormal.TrimmedMMD
