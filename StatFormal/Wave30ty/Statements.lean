import StatFormal.Wave30tr.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30ty: trimmed-mmd (JMLR v2), the two-sample hinge lemma `lem:hinge`

Printed source: `trimmed-mmd/jmlr/` at trimmed-mmd master `3a6d388` ("JMLR v2 long version: consistency fixes (FINAL_READ_v2, 44
findings) and approved cuts (100 -> 91 pp)"; read-only, read 2026-11-08; sha256 `appendix/A_basic.tex`
`fab7d2677cec05a2b3ad0f7fb6eec95867404875c9ffcd3a9351c6c5b0fa94bf`; context `sections/04_test.tex` `ab5da423…`,
`sections/03_regions.tex` `b9673cf0…`, `appendix/C_recover.tex` `07364ba6…`; full hashes on the card).
* `A_basic.tex:126-148`, **`lem:hinge`** ("A two-sample hinge class"): "Let (A1) and (A2) of Assumption~ass:regularity hold, let
  `X_1,…,X_n` be i.i.d. `P` and `Y_1,…,Y_m` i.i.d. `Q`, the two samples independent, and let `r, ρ_1, ρ_2 ≥ 0`. For each `x ∈ 𝒳` let
  `ψ^1_x, ψ^2_x : ℝ → ℝ` be 1-Lipschitz, with `(x,z) ↦ ψ^i_x(z)` measurable and `sup_x |ψ^i_x(0)| < ∞`. For `(v,a,b)` in
  `𝒮 = {(v,a,b) ∈ 𝓗 × ℝ² : ‖v‖_𝓗 ≤ r, |a| ≤ ρ_1, |b| ≤ ρ_2}` put `h^1_{v,a}(x) = ψ^1_x(a − v(x))` and `h^2_{v,b}(y) = ψ^2_y(v(y) − b)`,
  and let `Z = sup_𝒮[(P − P_n)h^1_{v,a} + (Q − Q_m)h^2_{v,b}]`, `Z^- = sup_𝒮[(P_n − P)h^1_{v,a} + (Q_m − Q)h^2_{v,b}]`. Then `Z` and
  `Z^-` are measurable and, with `s`, `e_n` and `e_m` as in Theorem~thm:twosided, `E Z ≤ 2[rκ√s + ρ_1e_n + ρ_2e_m]`,
  `E Z^- ≤ 2[rκ√s + ρ_1e_n + ρ_2e_m]`. If moreover `|h^1_{v,a}(x) − h^1_{v,a}(x')| ≤ Δ_1` and `|h^2_{v,b}(y) − h^2_{v,b}(y')| ≤ Δ_2`
  for all points and all `(v,a,b) ∈ 𝒮`, then for every `χ > 0` each of `Z` and `Z^-` exceeds its mean by at least
  `√(χ(Δ_1²/n + Δ_2²/m)/2)` with probability at most `e^{−χ}`. For one sample the same holds with the terms of the second sample
  removed: `s = 1/n`, and no `ρ_2e_m` and no `Δ_2²/m`."
* context: `04_test.tex:101-104` (`s = 1/n + 1/m`, `e_k = E|σ_1+⋯+σ_k|/k` for independent Rademacher signs), `03_regions.tex:20-31`
  (`ass:regularity`: (A1) `x ↦ k(x,x')` measurable and `k(x,x) ≤ κ²`, (A2) `𝓗` separable). Uses (read, not frozen): proofs of
  `thm:concentration` (`A_basic.tex:211-230`, one sample), `thm:twosided` (`A_basic.tex:390-397`), `lem:localmod` (`C_recover.tex:458-475`).

Reuses (imported, not copied): `Wave30tr` (`ek` = `e_k`), `Wave30tp` (`sNM` = `s`, `sampleLaw` = `P^{⊗n} ⊗ Q^{⊗m}`).

Encodings (see card `certify/cards/wave30ty.md`):
* (A1)–(A2) as in the frozen `TrimmedMMD/Concentration`, `Wave30tr`, `Wave30tx` claims: `𝓗` a **separable** real inner-product space
  and `φ : 𝒳 → 𝓗` strongly measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ x‖² ≤ κ²`), `v(x) = ⟨v, φ(x)⟩` (reproducing property);
  `𝒳` any measurable space; `κ` any bound on `‖φ‖`. Completeness of `𝓗` is not assumed (generalisation).
* `ψ^i` is a map `𝒳 → ℝ → ℝ` (`ψ x = ψ_x`); `IsHingeMap ψ`: every `ψ x` is 1-Lipschitz, `Function.uncurry ψ : 𝒳 × ℝ → ℝ` is measurable
  (product σ-algebra, Borel on `ℝ`) and `|ψ x 0| ≤ C` for some `C` and all `x`.
* Samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)` under `sampleLaw P Q n m` (one sample: `Fin n → 𝒳` under
  `Measure.pi`); `n, m ≥ 1` (the empirical measures need a point). `(P − P_n)h = ∫h dP − n⁻¹Σ_i h(x_i)` (`devPop`) and
  `(P_n − P)h = n⁻¹Σ_i h(x_i) − ∫h dP` (`devEmp`). `Z`, `Z^-` are real suprema over the subtype `𝒮` (nonempty and bounded: no junk value).
* "`F` exceeds its mean by at least `ε` with probability at most `e^{−χ}`" is `μ{F ≥ ∫F dμ + ε} ≤ e^{−χ}` (`TailAtLeast`); the strict
  form `μ{F > ∫F dμ + ε} ≤ e^{−χ}` is `TailMoreThan`.
* Additions (declared): `hinge`, `hinge1` also state that `Z`, `Z^-` are integrable (so the means are not the junk value of `∫`).

**Defect in the printed text** (declared, with a counterexample): the tail sentence is false when `Δ_1 = Δ_2 = 0` (one sample:
`Δ_1 = 0`), since then `√(…) = 0` and `Z` is constant, so `P(Z ≥ E Z + 0) = 1 > e^{−χ}` (`hinge_tail_printed_false`; e.g.
`ψ^1 = ψ^2 ≡ 0`). Frozen instead: the printed (non-strict) sentence under the added hypothesis `Δ_1²/n + Δ_2²/m > 0` (one sample:
`Δ_1²/n > 0`) (`hinge_tail`, `hinge1_tail`), and the strict form "exceeds its mean by **more than**", which needs no extra hypothesis
(`hinge_tail_strict`, `hinge1_tail_strict`) and is the form the three proofs need (the proof of `thm:twosided` writes the
non-strict event, `A_basic.tex:395`, and treats `D_φ = 0` separately). The added hypothesis is exactly where the non-strict sentence
holds: if `Δ_1²/n + Δ_2²/m = 0`, the oscillation bounds make every `h^1_{v,a}`, `h^2_{v,b}` constant in `x`, so `Z = Z^- ≡ 0` and the
non-strict tail fails. Read with "exceeds" as "is strictly greater", the printed sentence is true and follows from `hinge_tail` and
`hinge_tail_strict`.

Not covered (declared): the proof's prose (continuity of the bracket, symmetrization, contraction, the McDiarmid step) is not frozen
as separate claims; the three uses (the reductions of `thm:concentration`, `thm:twosided`, `lem:localmod` to this lemma) are not
re-frozen (those results are certified as `TrimmedMMD/Concentration`, `Wave30tr.thmA`, `Wave30tx.localmod`).
FROZEN 2026-11-08 after an independent critic's pre-freeze review (7 claims: 4 ACCEPT, 3 ACCEPT-WITH-NOTE, verdict READY TO
FREEZE; it re-derived the expectation bound and the McDiarmid constants and compiled a proof of `hinge_tail_printed_false`; applied:
the two docstring sentences above and a line reference). Hashed in `certify/statements.lock` (with its imports); AI
agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace StatFormal.Wave30ty

open StatFormal.Wave30tp StatFormal.Wave30tr

section Defs

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The maps `ψ_x` of `lem:hinge`: each `ψ_x : ℝ → ℝ` is 1-Lipschitz, `(x, z) ↦ ψ_x(z)` is measurable, and `sup_x |ψ_x(0)| < ∞`. -/
def IsHingeMap (ψ : 𝒳 → ℝ → ℝ) : Prop :=
  (∀ x, LipschitzWith 1 (ψ x)) ∧ Measurable (Function.uncurry ψ) ∧ ∃ C : ℝ, ∀ x, |ψ x 0| ≤ C

/-- `𝒮 = {(v, a, b) ∈ 𝓗 × ℝ² : ‖v‖ ≤ r, |a| ≤ ρ₁, |b| ≤ ρ₂}`. -/
def hingePar (r ρ₁ ρ₂ : ℝ) : Set (H × ℝ × ℝ) := {p | ‖p.1‖ ≤ r ∧ |p.2.1| ≤ ρ₁ ∧ |p.2.2| ≤ ρ₂}

/-- One sample: `{(v, a) ∈ 𝓗 × ℝ : ‖v‖ ≤ r, |a| ≤ ρ₁}`. -/
def hingePar1 (r ρ₁ : ℝ) : Set (H × ℝ) := {p | ‖p.1‖ ≤ r ∧ |p.2| ≤ ρ₁}

/-- `h¹_{v,a}(x) = ψ¹_x(a − v(x))`, with `v(x) = ⟨v, φ(x)⟩`. -/
def hOne (ψ : 𝒳 → ℝ → ℝ) (φ : 𝒳 → H) (v : H) (a : ℝ) (x : 𝒳) : ℝ := ψ x (a - ⟪v, φ x⟫_ℝ)

/-- `h²_{v,b}(y) = ψ²_y(v(y) − b)`, with `v(y) = ⟨v, φ(y)⟩`. -/
def hTwo (ψ : 𝒳 → ℝ → ℝ) (φ : 𝒳 → H) (v : H) (b : ℝ) (y : 𝒳) : ℝ := ψ y (⟪v, φ y⟫_ℝ - b)

/-- `(P − P_n)h = ∫ h dP − n⁻¹ Σ_i h(x_i)`. -/
def devPop (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) (h : 𝒳 → ℝ) : ℝ :=
  ∫ y, h y ∂P - (n : ℝ)⁻¹ * ∑ i, h (x i)

/-- `(P_n − P)h = n⁻¹ Σ_i h(x_i) − ∫ h dP`. -/
def devEmp (P : Measure 𝒳) {n : ℕ} (x : Fin n → 𝒳) (h : 𝒳 → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, h (x i) - ∫ y, h y ∂P

/-- `Z = sup_{(v,a,b) ∈ 𝒮} [(P − P_n)h¹_{v,a} + (Q − Q_m)h²_{v,b}]` at the samples `z = (x, y)`. -/
def hingeZ (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  ⨆ p : hingePar (H := H) r ρ₁ ρ₂,
    (devPop P z.1 (hOne ψ₁ φ p.1.1 p.1.2.1) + devPop Q z.2 (hTwo ψ₂ φ p.1.1 p.1.2.2))

/-- `Z⁻ = sup_{(v,a,b) ∈ 𝒮} [(P_n − P)h¹_{v,a} + (Q_m − Q)h²_{v,b}]` at the samples `z = (x, y)`. -/
def hingeZm (P Q : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ : ℝ) {n m : ℕ}
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  ⨆ p : hingePar (H := H) r ρ₁ ρ₂,
    (devEmp P z.1 (hOne ψ₁ φ p.1.1 p.1.2.1) + devEmp Q z.2 (hTwo ψ₂ φ p.1.1 p.1.2.2))

/-- One sample: `Z = sup_{(v,a)} (P − P_n)h¹_{v,a}`. -/
def hingeZ1 (P : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ : ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ :=
  ⨆ p : hingePar1 (H := H) r ρ₁, devPop P x (hOne ψ₁ φ p.1.1 p.1.2)

/-- One sample: `Z⁻ = sup_{(v,a)} (P_n − P)h¹_{v,a}`. -/
def hingeZ1m (P : Measure 𝒳) (φ : 𝒳 → H) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ : ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ :=
  ⨆ p : hingePar1 (H := H) r ρ₁, devEmp P x (hOne ψ₁ φ p.1.1 p.1.2)

/-- "`F` exceeds its mean by at least `ε` with probability at most `e^{−χ}`": `μ{ω : F ω ≥ ∫F dμ + ε} ≤ e^{−χ}`. -/
def TailAtLeast {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) (ε χ : ℝ) : Prop :=
  μ {ω | (∫ w, F w ∂μ) + ε ≤ F ω} ≤ ENNReal.ofReal (Real.exp (-χ))

/-- "`F` exceeds its mean by more than `ε` with probability at most `e^{−χ}`": `μ{ω : F ω > ∫F dμ + ε} ≤ e^{−χ}`. -/
def TailMoreThan {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) (ε χ : ℝ) : Prop :=
  μ {ω | (∫ w, F w ∂μ) + ε < F ω} ≤ ENNReal.ofReal (Real.exp (-χ))

end Defs

namespace Claims

/-! ### `lem:hinge (v2)`, two samples -/

/-- `lem:hinge (v2)`, measurability and means (`A_basic.tex:128-143`): under (A1)–(A2), for `r, ρ₁, ρ₂ ≥ 0`, `n, m ≥ 1` and maps
`ψ¹, ψ²` as printed, `Z` and `Z⁻` are measurable (and integrable: declared addition) and `E Z, E Z⁻ ≤ 2[rκ√s + ρ₁e_n + ρ₂e_m]`. -/
def hinge : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → IsHingeMap ψ₂ →
    0 ≤ r → 0 ≤ ρ₁ → 0 ≤ ρ₂ → 1 ≤ n → 1 ≤ m →
      Measurable (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z) ∧
      Measurable (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z) ∧
      Integrable (fun z => hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z) (sampleLaw P Q n m) ∧
      Integrable (fun z => hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z) (sampleLaw P Q n m) ∧
      ∫ z, hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z ∂(sampleLaw P Q n m) ≤
        2 * (r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m) ∧
      ∫ z, hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z ∂(sampleLaw P Q n m) ≤
        2 * (r * κ * √(sNM n m) + ρ₁ * ek n + ρ₂ * ek m)

/-- `lem:hinge (v2)`, the tail sentence as printed (`A_basic.tex:144-147`), under the added hypothesis `Δ₁²/n + Δ₂²/m > 0` (without it
the sentence is false: `hinge_tail_printed_false`): if `|h¹_{v,a}(x) − h¹_{v,a}(x')| ≤ Δ₁` and `|h²_{v,b}(y) − h²_{v,b}(y')| ≤ Δ₂` for
all points and all `(v,a,b) ∈ 𝒮`, then for every `χ > 0` each of `Z`, `Z⁻` exceeds its mean by at least `√(χ(Δ₁²/n + Δ₂²/m)/2)` with
probability at most `e^{−χ}`. -/
def hinge_tail : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ Δ₁ Δ₂ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → IsHingeMap ψ₂ →
    0 ≤ r → 0 ≤ ρ₁ → 0 ≤ ρ₂ → 1 ≤ n → 1 ≤ m →
    (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁) →
    (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂) →
    0 < Δ₁ ^ 2 / n + Δ₂ ^ 2 / m →
    ∀ χ : ℝ, 0 < χ →
      TailAtLeast (sampleLaw P Q n m) (fun z => hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
        (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ ∧
      TailAtLeast (sampleLaw P Q n m) (fun z => hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
        (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ

/-- `lem:hinge (v2)`, the tail sentence in the corrected strict form, with no condition on `Δ₁, Δ₂` beyond the printed oscillation
bounds: for every `χ > 0` each of `Z`, `Z⁻` exceeds its mean by **more than** `√(χ(Δ₁²/n + Δ₂²/m)/2)` with probability at most
`e^{−χ}`. -/
def hinge_tail_strict : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ Δ₁ Δ₂ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → IsHingeMap ψ₂ →
    0 ≤ r → 0 ≤ ρ₁ → 0 ≤ ρ₂ → 1 ≤ n → 1 ≤ m →
    (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁) →
    (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂) →
    ∀ χ : ℝ, 0 < χ →
      TailMoreThan (sampleLaw P Q n m) (fun z => hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
        (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ ∧
      TailMoreThan (sampleLaw P Q n m) (fun z => hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
        (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ

/-! ### `lem:hinge (v2)`, one sample ("the same holds with the terms of the second sample removed") -/

/-- `lem:hinge (v2)`, one sample, measurability and means: `Z = sup (P − P_n)h¹`, `Z⁻ = sup (P_n − P)h¹` over `‖v‖ ≤ r`, `|a| ≤ ρ₁`
are measurable (and integrable: declared addition) and `E Z, E Z⁻ ≤ 2[rκ√s + ρ₁e_n]` with `s = 1/n`. -/
def hinge1 : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → 0 ≤ r → 0 ≤ ρ₁ → 1 ≤ n →
      Measurable (fun x : Fin n → 𝒳 => hingeZ1 P φ ψ₁ r ρ₁ x) ∧
      Measurable (fun x : Fin n → 𝒳 => hingeZ1m P φ ψ₁ r ρ₁ x) ∧
      Integrable (fun x => hingeZ1 P φ ψ₁ r ρ₁ x) (Measure.pi fun _ : Fin n => P) ∧
      Integrable (fun x => hingeZ1m P φ ψ₁ r ρ₁ x) (Measure.pi fun _ : Fin n => P) ∧
      ∫ x, hingeZ1 P φ ψ₁ r ρ₁ x ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * (r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n) ∧
      ∫ x, hingeZ1m P φ ψ₁ r ρ₁ x ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * (r * κ * √(1 / (n : ℝ)) + ρ₁ * ek n)

/-- `lem:hinge (v2)`, one sample, the tail sentence as printed under the added hypothesis `Δ₁²/n > 0`: if
`|h¹_{v,a}(x) − h¹_{v,a}(x')| ≤ Δ₁` for all points and all `(v,a)`, then for every `χ > 0` each of `Z`, `Z⁻` exceeds its mean by at
least `√(χ(Δ₁²/n)/2)` with probability at most `e^{−χ}`. -/
def hinge1_tail : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ Δ₁ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → 0 ≤ r → 0 ≤ ρ₁ → 1 ≤ n →
    (∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2 x - hOne ψ₁ φ p.1 p.2 x'| ≤ Δ₁) →
    0 < Δ₁ ^ 2 / n →
    ∀ χ : ℝ, 0 < χ →
      TailAtLeast (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1 P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ ∧
      TailAtLeast (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1m P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ

/-- `lem:hinge (v2)`, one sample, the corrected strict form with no condition on `Δ₁` beyond the oscillation bound. -/
def hinge1_tail_strict : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (φ : 𝒳 → H) (κ : ℝ) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ Δ₁ : ℝ) (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → 0 ≤ r → 0 ≤ ρ₁ → 1 ≤ n →
    (∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2 x - hOne ψ₁ φ p.1 p.2 x'| ≤ Δ₁) →
    ∀ χ : ℝ, 0 < χ →
      TailMoreThan (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1 P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ ∧
      TailMoreThan (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1m P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ

/-! ### The printed tail sentence without a condition on `Δ` is false -/

/-- `lem:hinge (v2)`: the tail sentence **as printed** — two samples, and one sample — read with no condition on `Δ₁, Δ₂` beyond the
oscillation bounds, is false. (Witness, e.g.: `ψ¹ = ψ² ≡ 0`, so `h ≡ 0`, `Z = Z⁻ ≡ 0`, `Δ₁ = Δ₂ = 0`, the radius is `0`, and
`P(Z ≥ E Z + 0) = 1 > e^{−χ}`.) -/
def hinge_tail_printed_false : Prop :=
  (¬ ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (φ : 𝒳 → H) (κ : ℝ) (ψ₁ ψ₂ : 𝒳 → ℝ → ℝ) (r ρ₁ ρ₂ Δ₁ Δ₂ : ℝ) (n m : ℕ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → IsHingeMap ψ₂ →
      0 ≤ r → 0 ≤ ρ₁ → 0 ≤ ρ₂ → 1 ≤ n → 1 ≤ m →
      (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2.1 x - hOne ψ₁ φ p.1 p.2.1 x'| ≤ Δ₁) →
      (∀ p ∈ hingePar (H := H) r ρ₁ ρ₂, ∀ y y' : 𝒳, |hTwo ψ₂ φ p.1 p.2.2 y - hTwo ψ₂ φ p.1 p.2.2 y'| ≤ Δ₂) →
      ∀ χ : ℝ, 0 < χ →
        TailAtLeast (sampleLaw P Q n m) (fun z => hingeZ P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
          (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ ∧
        TailAtLeast (sampleLaw P Q n m) (fun z => hingeZm P Q φ ψ₁ ψ₂ r ρ₁ ρ₂ z)
          (√(χ * (Δ₁ ^ 2 / n + Δ₂ ^ 2 / m) / 2)) χ) ∧
  (¬ ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P]
      (φ : 𝒳 → H) (κ : ℝ) (ψ₁ : 𝒳 → ℝ → ℝ) (r ρ₁ Δ₁ : ℝ) (n : ℕ),
      StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → IsHingeMap ψ₁ → 0 ≤ r → 0 ≤ ρ₁ → 1 ≤ n →
      (∀ p ∈ hingePar1 (H := H) r ρ₁, ∀ x x' : 𝒳, |hOne ψ₁ φ p.1 p.2 x - hOne ψ₁ φ p.1 p.2 x'| ≤ Δ₁) →
      ∀ χ : ℝ, 0 < χ →
        TailAtLeast (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1 P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ ∧
        TailAtLeast (Measure.pi fun _ : Fin n => P) (fun x => hingeZ1m P φ ψ₁ r ρ₁ x) (√(χ * (Δ₁ ^ 2 / n) / 2)) χ)

end Claims
end StatFormal.Wave30ty
