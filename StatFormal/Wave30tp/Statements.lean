import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.Probability.Moments.Variance

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30tp: trimmed-mmd (JMLR revision), the plug-in common trimming (NOTE Theorem P)

Printed source: `trimmed-mmd/explore/sharper_threshold/NOTE.md` (read-only research note for the JMLR revision, still being
edited elsewhere; frozen from the snapshot read 2026-11-07 22:5x, sha256
`b1141e28273d09af58af5ae5e31eb41278364110c2649fea2be331203607b5ed`; the file later hashed
`5e80a476ff8218c397b9a73b63c053cb621d8b18b12255ed0bd491ab7a3322dc`, differing only at §5 lines 489–496 (Theorem A centring
remark), outside the frozen §1 and §3.1–3.3; labels are to be remapped to the paper's when the JMLR text is revised).
Paper context (read-only):
`trimmed-mmd/jmlr/sections/03_regions.tex` (`ass:regularity` (A1)–(A2), `𝒞_α(P)`, `prop:georep`), `04_test.tex`
(`H_{0,α}`, `eq:test`), `01_introduction.tex` (`eq:tvintersect`).
* §1, kernel constants: "`κ = sup_x k(x,x)^{1/2}`; `D_φ = sup_{x,x'} ‖φ(x) − φ(x')‖_H ≤ 2κ`; for a kernel with `k ≥ 0` and
  `k(x,x) ≡ κ²` … `D_φ ≤ √2 κ`; `v²`: any number with `tr Cov_R(φ) ≤ v²` for **every** probability `R`;
  `v² = min(κ², D_φ²/2)` works (Lemma P1); `ρ̄`: any number with `sup_x ‖φ(x) − μ_R‖ ≤ ρ̄` for every `R`; `ρ̄ = D_φ` works."
* §1, **Lemma 1** (monotone thresholds give one event): "Let `τ : [0,1) → [0,∞)` be deterministic and nondecreasing, and
  suppose that for every `α ∈ [0,1)` and every pair with `TV(P,Q) ≤ α`, `Pr(D̂_α > τ(α)) ≤ δ`. Then for every pair with
  `α* = TV(P,Q) < 1` the event `E = {D̂_{α*} ≤ τ(α*)}` has probability `≥ 1 − δ`, and on `E`: `D̂_α ≤ τ(α)` for every
  `α ≥ α*` …, `α̂ = inf{α : D̂_α ≤ τ(α)} ≤ α*`, and every grid rule 'largest rejected level' is `< α*`."
* §3.1, **Lemma P0**: "Let `α ∈ [0,1)` and let `R` be a probability measure with `R ≪ P`, `R ≪ Q`, `a = dR/dP ≤ β` and
  `b = dR/dQ ≤ β` (versions with values in `[0,β]`). Put `μ_R = E_R φ`, `ξ_i = a(X_i)(φ(X_i) − μ_R)`,
  `ζ_j = b(Y_j)(φ(Y_j) − μ_R)`, `A = n⁻¹Σ_i ξ_i`, `B = m⁻¹Σ_j ζ_j`, `S_X = n⁻¹Σ_i a(X_i)`, `S_Y = m⁻¹Σ_j b(Y_j)`,
  `ρ_R = sup_x ‖φ(x) − μ_R‖`. Then for every realization of the samples
  `D̂_α ≤ M + ρ_R[(1−S_X)_+ + (1−S_Y)_+]`, `M = max{‖A−B‖, ‖A‖, ‖B‖}`."
* §3.1, **Lemma P1** (moments and ranges), in the setting of Lemma P0: "(i) `E ξ_i = 0` and
  `E‖ξ_i‖² ≤ β tr Cov_R(φ) ≤ β v²`; (ii) `‖ξ(x)‖ ≤ β ρ_R` and `‖ξ(x) − ξ(x')‖ ≤ β D_φ`; (iii) `W = 1 − a(X)` has `E W = 0`,
  `1 − β ≤ W ≤ 1`, `Var W ≤ β − 1` and `E e^{λW} ≤ β⁻¹e^{λ(1−β)} + (1 − β⁻¹)e^{λ}` for `λ ≥ 0`; (iv) `ρ_R ≤ D_φ`;
  `tr Cov_R(φ) ≤ min(κ², D_φ²/2)`; if `k ≥ 0` and `k(x,x) ≡ κ²`, then `tr Cov_R(φ) = κ² − ‖μ_R‖²` and
  `ρ_R² ≤ κ² + ‖μ_R‖²`. The same holds for `ζ`, `b`, `Q`."
* §3.2, **Theorem P**: "Assume (A1)–(A2). For `n, m ≥ 1`, `δ ∈ (0,1)`, put `L = log(6/δ)` and
  `τ_P(0,δ) = v√s + D_φ√(s log(1/δ)/2)`, `τ_P(α,δ) = T₁ + ρ̄ T₂` (`0 < α < 1`), `T₁ = √(βv²s) + βD_φ√(sL/2)`,
  `T₂ = √(2(β−1)sL) + cL/3`. Then for every `α ∈ [0,1)` and **every** pair with `TV(P,Q) ≤ α`,
  `Pr(D̂_α > τ_P(α,δ)) ≤ δ`. `τ_P(·,δ)` is nondecreasing on `[0,1)`, so Lemma 1 applies: for every pair, one event of
  probability `≥ 1 − δ` on which no true `H_{0,α}` is rejected, for any `α`." (§1: `β = (1−α)⁻¹`, `s = 1/n + 1/m`,
  `c = max(1/n, 1/m)`.)
* §3.3, "Coupled constants": "For kernels with `k ≥ 0` and `k(x,x) ≡ κ²`, Lemma P1(iv) gives, with `u = ‖μ_R‖² ∈ [0,κ²]`
  unknown, `v² = κ² − u` and `ρ̄² = κ² + u` … `sup_u τ(·; v² = κ² − u, ρ̄ = √(κ²+u))` is valid" — frozen here for the
  closed form `τ_P` (the printed sentence is about the numerically inverted `τ_{P'}`, which needs Pinelis' inequality and is
  not formalised).

Reuses (imported, not copied) the frozen `TrimmedMMD` (`alphaHat`), `TrimmedMMD/Concentration` (`region`, `empirical`),
`TrimmedMMD/Unconditional` (`setDist`, `Demp`) and, through `TrimmedMMD/ZeroSet`, `StatFormal.Distances.tvDist`.

Encodings (see card `certify/cards/wave30tp.md`):
* (A1)–(A2) as in every frozen trimmed-MMD claim, weakened: `H` a real Hilbert space (complete inner-product space; separability
  is not assumed), `φ : 𝒳 → H` strongly measurable (what (A1)+(A2) give by Pettis) with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ x‖² ≤ κ²`);
  `k(x,y) = ⟪φ x, φ y⟫`. (A3) is not assumed. `𝒳` any measurable space.
* `D_φ`: any `D` with `‖φ x − φ x'‖ ≤ D` for all `x, x'` (the printed `D_φ` is the least such `D`, and every claim is monotone
  in `D` or quantifies over all such `D`); likewise `κ` is any bound on `‖φ‖`. `v ≥ 0` is the square root of the printed
  number `v²` (the printed formulas use both `v` and `v²`). `KernelConsts φ D v ρ̄` bundles the §1 definitions of `D_φ`, `v`,
  `ρ̄`, with "for every probability `R`" literal.
* `μ_R = ∫ φ dR` (Bochner; `φ` is bounded and strongly measurable, so integrable); `tr Cov_R(φ) = E_R‖φ − μ_R‖²` (`trCov`);
  `ρ_R = ⨆_x ‖φ x − μ_R‖` (`rhoR`; the family is bounded by `2κ` and `𝒳` is nonempty whenever a probability measure exists,
  so the real `iSup` is the genuine supremum).
* "`a = dR/dP ≤ β`, a version with values in `[0,β]`": `IsDensityLe R P α a` — `a` measurable, `0 ≤ a ≤ (1−α)⁻¹`
  everywhere, `R = P.withDensity a` (this gives `R ≪ P` and makes `a` a version of `dR/dP`).
* Samples `X ∼ P^{⊗n}`, `Y ∼ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)` with the product law `sampleLaw P Q n m`;
  `D̂_α = Demp φ x y α`, the distance between the empirical regions (`prop:georep`: the capped-simplex polytopes of `eq:qp`).
  "`Pr(D̂_α > τ) ≤ δ`" is the (outer) measure of the set `{D̂_α > τ}` (equivalently: it lies in a measurable event of
  probability `≤ δ`). "An event of probability `≥ 1 − δ`" (Lemma 1, the one-event sentence) is a **measurable** event of
  probability `≥ 1 − δ` contained in the claimed set (the convention of `TrimmedMMD/Unconditional`).
* `ξ(x) = a(x)(φ(x) − μ_R)`; "`E ξ_i`", "`E‖ξ_i‖²`", "`E e^{λW}`" are integrals against `P` (the law of each `X_i`);
  `Var W` is Mathlib's `variance` (`W` is bounded, so it is the genuine variance).
* `TV(P,Q)` is `tvDist` (`sup_A |P(A) − Q(A)|`); `H_{0,α}` is `TV(P,Q) ≤ α`; `α̂` is the frozen `alphaHat` (an `sInf` over
  `{α ∈ [0,1) : D̂_α ≤ τ(α)}`, which contains `α*` on the event, so it is not the junk `sInf ∅`); a "rejected level" is an
  `α ∈ [0,1)` with `τ(α) < D̂_α`; a grid is any set of levels in `[0,1)`.
* `sup_u` in the coupled form is encoded as "every `t` above all `τ_P(α,δ; v = √(κ²−u), ρ̄ = √(κ²+u))`, `u ∈ [0,κ²]`, is a
  valid threshold" (validity is monotone in the threshold, so this is the validity of the least such `t`, the supremum; no
  `sSup` junk).

Not covered (declared): Theorem A (§2); the numerically inverted `τ_{P'}` (§3.3: Pinelis' Hilbert-space Bennett bound,
`Ψ_H`, `Ψ_R`, the split set `F`) — Pinelis is not in Mathlib, a software refinement of the certified closed form; the
coupled `τ^{cpl}_{P'}`, its 20-cell grid bound and the "11–14%" gain (the closed-form analogue is `plugin_coupled`; its
monotonicity and one-event form are not stated, the printed text says only "valid"); Corollary C; the Gaussian line of §1
(`κ = 1, D_φ = √2, v² = 1, ρ̄ = √2`) and "with equality on an unbounded domain"; §3.4 and every numerical or table claim.
FROZEN 2026-11-07 after an independent critic's pre-freeze review (13 claims ACCEPT/ACCEPT-WITH-NOTE, none false; applied:
`plugin_one_event` for every pair (no `TV < 1` hypothesis), new `plugin_det_zero` for the remark after Lemma P0, both source
hashes, this list). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

namespace StatFormal.Wave30tp

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `s = 1/n + 1/m`. -/
def sNM (n m : ℕ) : ℝ := 1 / (n : ℝ) + 1 / (m : ℝ)

/-- `c = max(1/n, 1/m)`. -/
def cNM (n m : ℕ) : ℝ := max (1 / (n : ℝ)) (1 / (m : ℝ))

/-- `T₁ = √(β v² s) + β D_φ √(s L / 2)`, with `β = (1−α)⁻¹` and `L = log(6/δ)`. -/
def T1 (D v α δ : ℝ) (n m : ℕ) : ℝ :=
  √(1 / (1 - α) * v ^ 2 * sNM n m) + 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2)

/-- `T₂ = √(2(β−1) s L) + c L / 3`, with `β = (1−α)⁻¹` and `L = log(6/δ)`. -/
def T2 (α δ : ℝ) (n m : ℕ) : ℝ :=
  √(2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ)) + cNM n m * Real.log (6 / δ) / 3

/-- The closed-form threshold `τ_P(α,δ)` of Theorem P: `v√s + D_φ√(s log(1/δ)/2)` at `α = 0`, and `T₁ + ρ̄ T₂` for
`0 < α < 1`. -/
def tauP (D v ρbar α δ : ℝ) (n m : ℕ) : ℝ :=
  if α = 0 then v * √(sNM n m) + D * √(sNM n m * Real.log (1 / δ) / 2)
  else T1 D v α δ n m + ρbar * T2 α δ n m

/-- `tr Cov_R(φ) = E_R ‖φ − μ_R‖²`, `μ_R = E_R φ`. -/
def trCov (φ : 𝒳 → H) (R : Measure 𝒳) : ℝ := ∫ x, ‖φ x - ∫ y, φ y ∂R‖ ^ 2 ∂R

/-- `ρ_R = sup_x ‖φ(x) − μ_R‖`, `μ_R = E_R φ`. -/
def rhoR (φ : 𝒳 → H) (R : Measure 𝒳) : ℝ := ⨆ x, ‖φ x - ∫ y, φ y ∂R‖

/-- The kernel constants of §1: `D` bounds `‖φ(x) − φ(x')‖` (so `D ≥ D_φ`); `v ≥ 0` with `tr Cov_R(φ) ≤ v²` for every
probability `R`; `ρ̄` with `‖φ(x) − μ_R‖ ≤ ρ̄` for every `x` and every probability `R`. -/
def KernelConsts (φ : 𝒳 → H) (D v ρbar : ℝ) : Prop :=
  (∀ x x', ‖φ x - φ x'‖ ≤ D) ∧ 0 ≤ v ∧
    (∀ R : Measure 𝒳, IsProbabilityMeasure R → trCov φ R ≤ v ^ 2) ∧
    (∀ R : Measure 𝒳, IsProbabilityMeasure R → ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar)

/-- `a` is a version of `dR/dP` with values in `[0, β]`, `β = (1−α)⁻¹`: measurable, `0 ≤ a ≤ β` everywhere, and
`R = a · P` (so `R ≪ P`). -/
def IsDensityLe (R P : Measure 𝒳) (α : ℝ) (a : 𝒳 → ℝ) : Prop :=
  Measurable a ∧ (∀ x, 0 ≤ a x ∧ a x ≤ 1 / (1 - α)) ∧
    R = P.withDensity (fun x => ENNReal.ofReal (a x))

/-- `A = n⁻¹ Σ_i a(X_i)(φ(X_i) − μ)` (with `μ = μ_R`). -/
def wMeanDev (a : 𝒳 → ℝ) (φ : 𝒳 → H) (μ : H) {n : ℕ} (x : Fin n → 𝒳) : H :=
  (n : ℝ)⁻¹ • ∑ i, a (x i) • (φ (x i) - μ)

/-- `S_X = n⁻¹ Σ_i a(X_i)`. -/
def wMass (a : 𝒳 → ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ := (n : ℝ)⁻¹ * ∑ i, a (x i)

/-- The law of the two independent samples, `P^{⊗n} ⊗ Q^{⊗m}` on `(Fin n → 𝒳) × (Fin m → 𝒳)`. -/
def sampleLaw (P Q : Measure 𝒳) (n m : ℕ) : Measure ((Fin n → 𝒳) × (Fin m → 𝒳)) :=
  (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)

namespace Claims

/-! ### §1: the kernel constants -/

/-- §1: the printed choices are admissible kernel constants. For every bound `κ` on `‖φ‖` and every bound `D` on
`‖φ(x) − φ(x')‖`: `v = √min(κ², D²/2)` and `ρ̄ = D` satisfy the defining properties of `v` and `ρ̄` (so do any larger
numbers); `D_φ ≤ 2κ`; and if `k ≥ 0` with `k(x,x) ≡ κ²`, then `D_φ ≤ √2 κ`. -/
def kernel_consts : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
      KernelConsts φ D (√(min (κ ^ 2) (D ^ 2 / 2))) D ∧
      (∀ x x', ‖φ x - φ x'‖ ≤ 2 * κ) ∧
      ((∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) → ∀ x x', ‖φ x - φ x'‖ ≤ √2 * κ)

/-! ### §1: Lemma 1 (monotone thresholds give one event) -/

/-- **NOTE Lemma 1.** Let `τ` be nonnegative and nondecreasing on `[0,1)` and suppose that for every `α ∈ [0,1)` and every
pair of probability measures with `TV ≤ α`, `Pr(D̂_α > τ(α)) ≤ δ`. Then for every pair with `α* = TV(P,Q) < 1`: the event
`{D̂_{α*} ≤ τ(α*)}` contains a measurable event of probability `≥ 1 − δ`; and at every sample in it, `D̂_α ≤ τ(α)` for every
`α ∈ [α*, 1)`, `α̂ ≤ α*`, every rejected level `α ∈ [0,1)` is `< α*`, and for every grid `G ⊆ [0,1)` the largest rejected
grid level (when it exists) is `< α*`. -/
def monotone_event : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) (τ : ℝ → ℝ) (δ : ℝ) (n m : ℕ) (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    0 ≤ δ → 1 ≤ n → 1 ≤ m → (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) → MonotoneOn τ (Ico 0 1) →
    (∀ α ∈ Ico (0 : ℝ) 1, ∀ P' Q' : Measure 𝒳, IsProbabilityMeasure P' → IsProbabilityMeasure Q' →
      StatFormal.Distances.tvDist P' Q' ≤ α →
        sampleLaw P' Q' n m {z | τ α < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ) →
    StatFormal.Distances.tvDist P Q < 1 →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        E ⊆ {z | Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q)}) ∧
      ∀ z : (Fin n → 𝒳) × (Fin m → 𝒳),
        Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q) →
          (∀ α ∈ Ico (StatFormal.Distances.tvDist P Q) 1, Demp φ z.1 z.2 α ≤ τ α) ∧
          alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
          (∀ α ∈ Ico (0 : ℝ) 1, τ α < Demp φ z.1 z.2 α → α < StatFormal.Distances.tvDist P Q) ∧
          (∀ G : Set ℝ, G ⊆ Ico 0 1 → ∀ b : ℝ, IsGreatest {α | α ∈ G ∧ τ α < Demp φ z.1 z.2 α} b →
            b < StatFormal.Distances.tvDist P Q)

/-! ### §3.1: Lemma P0 (deterministic) -/

/-- **NOTE Lemma P0.** For `α ∈ [0,1)`, a probability `R` with versions `a = dR/dP`, `b = dR/dQ` with values in `[0,β]`,
`μ_R = E_R φ`, `A = n⁻¹Σ a(X_i)(φ(X_i) − μ_R)`, `B = m⁻¹Σ b(Y_j)(φ(Y_j) − μ_R)`, `S_X = n⁻¹Σ a(X_i)`, `S_Y = m⁻¹Σ b(Y_j)`
and `ρ_R = sup_x ‖φ(x) − μ_R‖`: for every realization of the samples,
`D̂_α ≤ max{‖A−B‖, ‖A‖, ‖B‖} + ρ_R[(1−S_X)_+ + (1−S_Y)_+]`. -/
def plugin_det : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ α : ℝ) (P Q R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] (a b : 𝒳 → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 1 ≤ m →
    IsDensityLe R P α a → IsDensityLe R Q α b →
    ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      Demp φ x y α ≤
        max (max ‖wMeanDev a φ (∫ z, φ z ∂R) x - wMeanDev b φ (∫ z, φ z ∂R) y‖
            ‖wMeanDev a φ (∫ z, φ z ∂R) x‖) ‖wMeanDev b φ (∫ z, φ z ∂R) y‖ +
          rhoR φ R * (max (1 - wMass a x) 0 + max (1 - wMass b y) 0)

/-- **NOTE, remark after Lemma P0** (`α = 0`, `β = 1`): "`0 ≤ a ≤ 1` and `E_P a = 1` force `a = 1` `P`-a.s., so
`S_X = S_Y = 1` a.s., `λ_X = λ_Y = 1` and `D̂_0 ≤ ‖A − B‖` a.s. (… `H_{0,0}` is `P = Q = R`)." -/
def plugin_det_zero : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (P Q R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] (a b : 𝒳 → ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 1 ≤ m →
    IsDensityLe R P 0 a → IsDensityLe R Q 0 b →
      (∀ᵐ x ∂P, a x = 1) ∧ (∀ᵐ y ∂Q, b y = 1) ∧ P = R ∧ Q = R ∧
      ∀ᵐ z ∂(sampleLaw P Q n m), wMass a z.1 = 1 ∧ wMass b z.2 = 1 ∧
        Demp φ z.1 z.2 0 ≤ ‖wMeanDev a φ (∫ w, φ w ∂R) z.1 - wMeanDev b φ (∫ w, φ w ∂R) z.2‖

/-! ### §3.1: Lemma P1 (moments and ranges) -/

/-- **NOTE Lemma P1 (i).** For `R = a · P` with `0 ≤ a ≤ β` and `ξ(x) = a(x)(φ(x) − μ_R)`: `E_P ξ = 0` and
`E_P‖ξ‖² ≤ β tr Cov_R(φ)`, and `β tr Cov_R(φ) ≤ β v²` for every `v` with `tr Cov_{R'}(φ) ≤ v²` for every probability `R'`.
(For `ζ, b, Q`: the same claim at `Q, b`.) -/
def plugin_moments_i : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ α : ℝ) (P R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure R] (a : 𝒳 → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → IsDensityLe R P α a →
      ∫ x, a x • (φ x - ∫ z, φ z ∂R) ∂P = 0 ∧
      ∫ x, ‖a x • (φ x - ∫ z, φ z ∂R)‖ ^ 2 ∂P ≤ 1 / (1 - α) * trCov φ R ∧
      ∀ v : ℝ, (∀ R' : Measure 𝒳, IsProbabilityMeasure R' → trCov φ R' ≤ v ^ 2) →
        1 / (1 - α) * trCov φ R ≤ 1 / (1 - α) * v ^ 2

/-- **NOTE Lemma P1 (ii).** `‖ξ(x)‖ ≤ β ρ_R` for every `x`, and `‖ξ(x) − ξ(x')‖ ≤ β D` for every `x, x'` and every bound `D`
on `‖φ(x) − φ(x')‖` (in particular for `D = D_φ`). -/
def plugin_moments_ii : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ α : ℝ) (P R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure R] (a : 𝒳 → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → IsDensityLe R P α a →
      (∀ x, ‖a x • (φ x - ∫ z, φ z ∂R)‖ ≤ 1 / (1 - α) * rhoR φ R) ∧
      ∀ D : ℝ, (∀ x x', ‖φ x - φ x'‖ ≤ D) → ∀ x x',
        ‖a x • (φ x - ∫ z, φ z ∂R) - a x' • (φ x' - ∫ z, φ z ∂R)‖ ≤ 1 / (1 - α) * D

/-- **NOTE Lemma P1 (iii).** `W = 1 − a(X)`, `X ∼ P`: `E W = 0`, `1 − β ≤ W ≤ 1`, `Var W ≤ β − 1`, and
`E e^{λW} ≤ β⁻¹ e^{λ(1−β)} + (1 − β⁻¹) e^{λ}` for every `λ ≥ 0`. -/
def plugin_moments_iii : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (α : ℝ) (P R : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (a : 𝒳 → ℝ),
    0 ≤ α → α < 1 → IsDensityLe R P α a →
      ∫ x, (1 - a x) ∂P = 0 ∧
      (∀ x, 1 - 1 / (1 - α) ≤ 1 - a x ∧ 1 - a x ≤ 1) ∧
      variance (fun x => 1 - a x) P ≤ 1 / (1 - α) - 1 ∧
      ∀ l : ℝ, 0 ≤ l →
        ∫ x, Real.exp (l * (1 - a x)) ∂P ≤
          (1 / (1 - α))⁻¹ * Real.exp (l * (1 - 1 / (1 - α))) + (1 - (1 / (1 - α))⁻¹) * Real.exp l

/-- **NOTE Lemma P1 (iv)** (for every probability `R`). `ρ_R ≤ D` and `tr Cov_R(φ) ≤ min(κ², D²/2)` for every bound `D` on
`‖φ(x) − φ(x')‖` (so with `D = D_φ`); and if `k ≥ 0` and `k(x,x) ≡ κ²`, then `tr Cov_R(φ) = κ² − ‖μ_R‖²` and
`ρ_R² ≤ κ² + ‖μ_R‖²`. -/
def plugin_moments_iv : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (R : Measure 𝒳) [IsProbabilityMeasure R],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
      (∀ D : ℝ, (∀ x x', ‖φ x - φ x'‖ ≤ D) → rhoR φ R ≤ D ∧ trCov φ R ≤ min (κ ^ 2) (D ^ 2 / 2)) ∧
      ((∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
        trCov φ R = κ ^ 2 - ‖∫ y, φ y ∂R‖ ^ 2 ∧ rhoR φ R ^ 2 ≤ κ ^ 2 + ‖∫ y, φ y ∂R‖ ^ 2)

/-! ### §3.2: Theorem P (closed form) -/

/-- **NOTE Theorem P**, level. Under (A1)–(A2), for kernel constants `D, v, ρ̄` as in §1, every `α ∈ [0,1)`, `δ ∈ (0,1)`,
`n, m ≥ 1` and **every** pair with `TV(P,Q) ≤ α`: `Pr(D̂_α > τ_P(α,δ)) ≤ δ`. -/
def plugin_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
      sampleLaw P Q n m {z | tauP D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

/-- **NOTE Theorem P**, monotonicity: for `D, v, ρ̄ ≥ 0` (automatic for kernel constants), `δ ∈ (0,1)`, `n, m ≥ 1`,
`τ_P(·,δ)` is nonnegative and nondecreasing on `[0,1)`. -/
def plugin_monotone : Prop :=
  ∀ (D v ρbar δ : ℝ) (n m : ℕ), 0 ≤ D → 0 ≤ v → 0 ≤ ρbar → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    MonotoneOn (fun α => tauP D v ρbar α δ n m) (Ico 0 1) ∧
      ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauP D v ρbar α δ n m

/-- **NOTE Theorem P**, "so Lemma 1 applies: for every pair, one event of probability `≥ 1 − δ` on which no true
`H_{0,α}` is rejected, for any `α`": for every pair, a measurable event of probability `≥ 1 − δ` on which
`D̂_α ≤ τ_P(α,δ)` for every `α ∈ [0,1)` with `TV(P,Q) ≤ α`, every rejected level is `< TV(P,Q)`, and (when
`TV(P,Q) < 1`) the estimator built on `τ_P` has `α̂ ≤ TV(P,Q)`. -/
def plugin_one_event : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D v ρbar : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → KernelConsts φ D v ρbar →
    0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ sampleLaw P Q n m E ∧
        ∀ z ∈ E,
          (∀ α ∈ Ico (0 : ℝ) 1, StatFormal.Distances.tvDist P Q ≤ α →
            Demp φ z.1 z.2 α ≤ tauP D v ρbar α δ n m) ∧
          (StatFormal.Distances.tvDist P Q < 1 →
            alphaHat (Demp φ z.1 z.2) (fun α => tauP D v ρbar α δ n m) ≤ StatFormal.Distances.tvDist P Q) ∧
          (∀ α ∈ Ico (0 : ℝ) 1, tauP D v ρbar α δ n m < Demp φ z.1 z.2 α → α < StatFormal.Distances.tvDist P Q)

/-- **NOTE Theorem P** with the §1 choices `v = √min(κ², D²/2)` and `ρ̄ = D` (any bounds `κ`, `D`). -/
def plugin_level_explicit : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
      sampleLaw P Q n m {z | tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m < Demp φ z.1 z.2 α} ≤
        ENNReal.ofReal δ

/-! ### §3.3: coupled constants, closed form -/

/-- **NOTE §3.3, coupled constants** (closed-form version). For a kernel with `k ≥ 0` and `k(x,x) ≡ κ²`, any bound `D` on
`‖φ(x) − φ(x')‖`, `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1` and every pair with `TV(P,Q) ≤ α`: every `t` with
`t ≥ τ_P(α,δ; v = √(κ² − u), ρ̄ = √(κ² + u))` for all `u ∈ [0,κ²]` (so `t = sup_u` of these) has `Pr(D̂_α > t) ≤ δ`. -/
def plugin_coupled : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ D t : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → (∀ x x', ‖φ x - φ x'‖ ≤ D) →
    (∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) → (∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m → StatFormal.Distances.tvDist P Q ≤ α →
    (∀ u ∈ Icc (0 : ℝ) (κ ^ 2), tauP D (√(κ ^ 2 - u)) (√(κ ^ 2 + u)) α δ n m ≤ t) →
      sampleLaw P Q n m {z | t < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ

end Claims
end StatFormal.Wave30tp
