import StatFormal.Wave30tp.Statements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tr: trimmed-mmd (JMLR revision), one joint one-sided two-sample supremum (NOTE Theorem A)

Printed source: `trimmed-mmd/explore/sharper_threshold/NOTE.md` §2 (read-only research note for the JMLR revision; frozen
from the version with sha256 `b6f1aab476e51d1aba9b146074cbe93bbaae7311638a485d0f9cd8511565d284`, §2 = lines 112–207;
labels are to be remapped to the paper's when the JMLR text is revised). Notation of §1 (`:68-84`): (A1)–(A2) of
`ass:regularity`, `β = (1−α)⁻¹`, `𝒞_α(P)` the trimmed region, `D̂_α = dist(𝒞_α(P_n), 𝒞_α(Q_m))`, `s = 1/n + 1/m`,
`κ = sup_x k(x,x)^{1/2}`, `D_φ = sup_{x,x'} ‖φ(x) − φ(x')‖_H ≤ 2κ`.
Paper context (read-only): `trimmed-mmd/jmlr/sections/03_regions.tex:20-31` (`ass:regularity`: (A1) boundedness and
measurability, (A2) `H` separable), `04_test.tex` (`H_{0,α}`, `τ_{n,m}`), `05_estimator.tex` (`eq:alphaest`).
* §2, `:114-119`: "Let `e_k = E|σ_1+⋯+σ_k|/k = binom(k−1, ⌊(k−1)/2⌋) 2^{1−k}` (exact; `e_k ≤ k^{−1/2}`, `e_k√k → √(2/π)`) and
  `τ_A(α,δ) = β[2κ√s + 2κ(e_n+e_m) + D_φ√(s log(1/δ)/2)]`."
* §2, **Theorem A**, `:121-131`: "Under (A1)–(A2), for all `n,m ≥ 1` and `δ ∈ (0,1)` there are events `E⁺`, `E⁻`, not depending
  on `α`, each of probability `≥ 1−δ`, such that for **every** `α ∈ [0,1)` and every pair `(P,Q)`: (a) on `E⁺`,
  `D̂_α ≤ D_α(P,Q) + τ_A(α,δ)`; in particular `D̂_α ≤ τ_A(α,δ)` whenever `H_{0,α}` holds; (b) on `E⁻`,
  `D̂_α ≥ D_α(P,Q) − τ_A(α,δ)`. Hence `|D̂_α − D_α| ≤ τ_A(α,δ/2)` for all `α` on `E⁺∩E⁻` (probability `≥ 1−δ`), which can
  replace `τ_{n,m}(α,δ)` in the proofs of `thm:consistency`, `thm:rate`, `cor:confset`, `cor:upperfs`. Moreover
  `τ_A(α,δ) ≤ τ_{n,m}(α,δ)` for all `n,m,δ,α` and every kernel."
* §2, proof, Step 3 (`:192-193`): "… (note `τ_A(α,δ) = βτ_A(0,δ)`, so `E⁺` is free of `α`)."

Reuses (imported, not copied) the frozen `TrimmedMMD` (`tau` = `τ_{n,m}`), `TrimmedMMD/Concentration` (`region`,
`empirical`), `TrimmedMMD/Unconditional` (`Dpop` = `D_α(P,Q)`, `Demp` = `D̂_α`), `Wave30tp` (`sNM` = `s`, `sampleLaw`) and,
through `TrimmedMMD/ZeroSet`, `StatFormal.Distances.tvDist`.

Encodings (see card `certify/cards/wave30tr.md`):
* (A1)–(A2) as in the frozen `TrimmedMMD/Concentration` claims: `H` a **separable** real Hilbert space, `φ : 𝒳 → H` strongly
  measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ x‖² ≤ κ²`); `𝒳` any measurable space. (A3) is not assumed.
* `κ` is any bound on `‖φ‖` and `D` any bound on `‖φ(x) − φ(x')‖` (generalisation: the printed `κ`, `D_φ` are the least
  bounds and are themselves admissible, so the printed statement is the instance `κ = sup‖φ‖`, `D = D_φ`).
* `e_k` (`ek`) is the exact average of `|σ_1+⋯+σ_k|/k` over the `2^k` sign vectors (`σ : Fin k → Bool`, sign `+1` for
  `true`), i.e. `E|σ_1+⋯+σ_k|/k` for i.i.d. Rademacher signs. `k^{−1/2}` is written `1/√k`; `2^{1−k}` is an integer power.
* Samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)` with the product law `sampleLaw P Q n m`; `D̂_α = Demp`,
  `D_α(P,Q) = Dpop` (`inf ‖a − b‖` over the two regions).
* "An event of probability `≥ 1 − δ`" is a **measurable** event of probability `≥ 1 − δ` (convention of
  `TrimmedMMD/Unconditional`); "not depending on `α`" is the quantifier order `∃ E⁺ E⁻, ∀ α`.
* `H_{0,α}` is `TV(P,Q) ≤ α` with `TV = tvDist`.
* "for all `n,m,δ,α` and every kernel" (the comparison): for every `κ` and every `D ∈ [0, 2κ]` (every kernel has
  `D_φ ≤ 2κ`; `D = 2κ` is always admissible in `thmA`).
* Additions (not printed, declared): `tauA_scale` adds to the printed proof remark `τ_A(α,δ) = βτ_A(0,δ)` two unprinted
  conjuncts, `τ_A(·,δ)` nonnegative and nondecreasing on `[0,1)` (immediate from the scale identity), as ingredients of the
  "can replace" sentence; `thmA_compare_half` is the strengthening `τ_A(α,δ/2) ≤ τ_{n,m}(α,δ)` (the comparison that the
  two-sided radius `τ_A(α,δ/2)` of "Hence" needs; it implies the printed one since `τ_A` grows as `δ` shrinks).

Not covered (declared): "which can replace `τ_{n,m}(α,δ)` in the proofs of `thm:consistency`, `thm:rate`, `cor:confset`,
`cor:upperfs`" (a statement about proofs of the revised paper, to be frozen when that text exists; its ingredients
`thmA_twosided`, `thmA_compare_half` and `tauA_scale` are covered; the further properties those proofs use, `τ_A → 0` as
`n, m → ∞` and `τ_A → ∞` as `α → 1` for `κ > 0`, belong to that sentence); the proof-internal steps (the reduction to the
supremum `Z`, the bound on `E Z`, the McDiarmid step) are not frozen as claims; the "Gain" paragraph (`:200-207`) and every
numerical claim.
FROZEN 2026-11-08 after an independent critic's pre-freeze review (7 claims ACCEPT/ACCEPT-WITH-NOTE, none false, no
counterexample; applied: the generalisation reason for `κ`, `D`, the declaration of the `tauA_scale` conjuncts, the
"not covered" additions, and the optional `thmA_compare_half`).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave30tr

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tp

/-- `e_k = E|σ_1 + ⋯ + σ_k| / k` for i.i.d. uniform signs `σ_i ∈ {±1}` (exact average over the `2^k` sign vectors). -/
def ek (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹ * (∑ σ : Fin k → Bool, |∑ i, (if σ i then (1 : ℝ) else -1)|) / k

/-- `τ_A(α,δ) = β[2κ√s + 2κ(e_n + e_m) + D_φ √(s log(1/δ)/2)]`, `β = (1−α)⁻¹`, `s = 1/n + 1/m`. -/
def tauA (κ D α δ : ℝ) (n m : ℕ) : ℝ :=
  1 / (1 - α) *
    (2 * κ * √(sNM n m) + 2 * κ * (ek n + ek m) + D * √(sNM n m * Real.log (1 / δ) / 2))

namespace Claims

/-! ### §2: the constants `e_k` -/

/-- §2: `e_k = binom(k−1, ⌊(k−1)/2⌋) 2^{1−k}` (exact), for `k ≥ 1`. -/
def ek_closed : Prop :=
  ∀ k : ℕ, 1 ≤ k → ek k = ((k - 1).choose ((k - 1) / 2) : ℝ) * (2 : ℝ) ^ ((1 : ℤ) - k)

/-- §2: `e_k ≤ k^{−1/2}`, for `k ≥ 1`. -/
def ek_le : Prop :=
  ∀ k : ℕ, 1 ≤ k → ek k ≤ 1 / √(k : ℝ)

/-- §2: `e_k √k → √(2/π)`. -/
def ek_tendsto : Prop :=
  Filter.Tendsto (fun k : ℕ => ek k * √(k : ℝ)) Filter.atTop (nhds (√(2 / Real.pi)))

/-! ### §2: Theorem A -/

/-- **NOTE Theorem A**, (a) and (b). Under (A1)–(A2), for every pair `(P,Q)`, `n, m ≥ 1`, `δ ∈ (0,1)` and bounds `κ` on `‖φ‖`
and `D` on `‖φ(x) − φ(x')‖`, there are measurable events `E⁺`, `E⁻`, not depending on `α`, each of probability `≥ 1 − δ`
under `P^{⊗n} ⊗ Q^{⊗m}`, such that for every `α ∈ [0,1)`: (a) on `E⁺`, `D̂_α ≤ D_α(P,Q) + τ_A(α,δ)`, and `D̂_α ≤ τ_A(α,δ)`
whenever `TV(P,Q) ≤ α` (`H_{0,α}`); (b) on `E⁻`, `D̂_α ≥ D_α(P,Q) − τ_A(α,δ)`. -/
def thmA : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ Eplus Eminus : Set ((Fin n → 𝒳) × (Fin m → 𝒳)),
        MeasurableSet Eplus ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m Eplus ∧
        MeasurableSet Eminus ∧ ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m Eminus ∧
        (∀ z ∈ Eplus, ∀ α ∈ Ico (0 : ℝ) 1,
          Demp φ z.1 z.2 α ≤ Dpop φ P Q α + tauA κ D α δ n m ∧
          (StatFormal.Distances.tvDist P Q ≤ α → Demp φ z.1 z.2 α ≤ tauA κ D α δ n m)) ∧
        (∀ z ∈ Eminus, ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - tauA κ D α δ n m ≤ Demp φ z.1 z.2 α)

/-- **NOTE Theorem A**, "Hence": the events of Theorem A at level `δ/2` are measurable, each of probability `≥ 1 − δ/2`,
their intersection has probability `≥ 1 − δ`, and on it `|D̂_α − D_α(P,Q)| ≤ τ_A(α,δ/2)` for every `α ∈ [0,1)`. -/
def thmA_twosided : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ D : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ Eplus Eminus : Set ((Fin n → 𝒳) × (Fin m → 𝒳)),
        MeasurableSet Eplus ∧ MeasurableSet Eminus ∧
        ENNReal.ofReal (1 - δ / 2) ≤ sampleLaw P Q n m Eplus ∧
        ENNReal.ofReal (1 - δ / 2) ≤ sampleLaw P Q n m Eminus ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m (Eplus ∩ Eminus) ∧
        ∀ z ∈ Eplus ∩ Eminus, ∀ α ∈ Ico (0 : ℝ) 1,
          |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ tauA κ D α (δ / 2) n m

/-- **NOTE Theorem A**, "Moreover": `τ_A(α,δ) ≤ τ_{n,m}(α,δ)` for all `n, m ≥ 1`, `δ ∈ (0,1)`, `α ∈ [0,1)` and every kernel,
i.e. for every `κ` and every `D ∈ [0, 2κ]` (`D_φ ≤ 2κ` for every kernel with `k(x,x) ≤ κ²`). -/
def thmA_compare : Prop :=
  ∀ (κ D α δ : ℝ) (n m : ℕ), 0 ≤ D → D ≤ 2 * κ → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    tauA κ D α δ n m ≤ StatFormal.TrimmedMMD.tau κ α δ n m

/-- Addition (declared, not printed): the comparison at the two-sided radius, `τ_A(α,δ/2) ≤ τ_{n,m}(α,δ)`, under the same
hypotheses as `thmA_compare`. -/
def thmA_compare_half : Prop :=
  ∀ (κ D α δ : ℝ) (n m : ℕ), 0 ≤ D → D ≤ 2 * κ → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    tauA κ D α (δ / 2) n m ≤ StatFormal.TrimmedMMD.tau κ α δ n m

/-- §2, proof, Step 3: "`τ_A(α,δ) = βτ_A(0,δ)`, so `E⁺` is free of `α`"; with the properties of `τ_{n,m}` that the
two-sided bound is used with (nonnegative and nondecreasing on `[0,1)`), for `κ, D ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`. -/
def tauA_scale : Prop :=
  ∀ (κ D δ : ℝ) (n m : ℕ), 0 ≤ κ → 0 ≤ D → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    (∀ α : ℝ, α < 1 → tauA κ D α δ n m = 1 / (1 - α) * tauA κ D 0 δ n m) ∧
    MonotoneOn (fun α => tauA κ D α δ n m) (Ico 0 1) ∧
    ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauA κ D α δ n m

end Claims
end StatFormal.Wave30tr
