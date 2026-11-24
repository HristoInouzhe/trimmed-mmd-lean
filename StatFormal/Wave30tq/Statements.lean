import StatFormal.Archive.TrimmedMMD.Lower.Statements
import StatFormal.Archive.Wave17a.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FROZEN STATEMENTS — wave 30tq: trimmed-mmd (jmlr), the finite-sample variance-adaptive split certificate
# (betting on the ramp of the kernel witness)

Source (printed, READ-ONLY): `trimmed-mmd/explore/split_adaptive/theory.md`, Section 2 (sha256 at freeze time
`5518c814f1ef6bda0ea1795b9990fc01e00c9424a1d9b7bd5adf63decc780852`; to be remapped to the paper's labels when the
JMLR revision absorbs it). Code: `explore/split_adaptive/sacert.py` (`ramp`, `pair_up`, `betting_test`, `sd_ucb`,
`lcb_bern2s`). Referenced paper objects: `eq:trimset` (`R_α(P)`), `eq:tvintersect`, `lem:cvar`, `eq:lowertrim`,
`eq:downclosed` (`jmlr/sections/06_splitting.tex`), all through their frozen encodings.

Setting (§2.1): `β = (1 − α)⁻¹` (`beta`), `ψ_s(u) = s − β(s − u)₊` (`psiS`),
`θ(f; s, s') = E_P[s − β(s − f(X))₊] − E_Q[s' + β(f(Y) − s')₊]` (`theta`), `R_α(P) = {P' ≪ P : dP'/dP ≤ β}`.

Covered (17 claims):
* Lemma 1 ("one cut point is enough"): `lem1_trim` (the inequality against every pair of trimmings),
  `lem1` (the printed `θ ≤ inf_{R_α(P)} E_{P'} f − sup_{R_α(Q)} E_{Q'} f`), `lem1_null` ("hence `θ ≤ 0` whenever
  `TV ≤ α`", with the right side `≤ 0`), `lem1_rkhs` (for `f ∈ H` the right side is `T(f) = sep(f; 𝒞_α(P), 𝒞_α(Q))`),
  `lem1_attain` (`sup_{s,s'} θ = ` the right side, attained, at every `(1−α)`-quantile of `f(X)` and every
  `α`-quantile of `f(Y)`, and such quantiles exist).
* Lemma 2 (clipping): `lem2_1` (`g ∈ [0,1]` and `θ(f̃) = β(s − s')(E_P g − E_Q g − α)`), `lem2_2` (the gain formula and
  its sign), `lem2_3` (both variance comparisons), `lem2_4` (`s ≤ s' ⇒ θ ≤ s − s' ≤ 0`).
* §2.3 pairing: `pair_facts` (`Z_k ∈ [−1,1]`, `E Z_k = Δ`, `Z_1, …, Z_N` independent given fold one, and the elementary
  `Δ = E_P g − E_Q g ≤ TV(P,Q)`).
* Theorem 1: `thm1_cond` (per fold: `P(max_{t≤N} K_t ≥ 1/δ) ≤ δ` for every fixed fold-one outcome), `thm1_condexp`
  (the printed conditional form `P(· | D_1) ≤ δ` a.s., with a random fold one), `thm1` (unconditional:
  `sup_{H_{0,α}} P(reject) ≤ δ`).
* Corollary 1: `cor1` (per fold: `P(LB > Δ) ≤ δ₁ + 2δ₂`), `cor1_test` (`TV ≤ α ⇒ P(LB > α) ≤ δ`, random fold one),
  `cor1_lcb` (`P(LB > TV) ≤ δ` for every `(P,Q)`, random fold one).
* Corollary 2: `cor2` (down-closed rule over a grid, each level tested by Theorem 1 or by Corollary 1, any fold-one
  rules per level, all on the same fold two: `P(α̂_lo > TV) ≤ δ` for every sample size and every `(P,Q)`).
Not covered (declared on the card): Lemma 3; Proposition 4 (asymptotic sketch, by instruction); §2.4; the variance
identity for equal blocks in §2.3; the per-sample Maurer–Pontil remark after Corollary 1; the fold-one construction
of `ŝ, ŝ'`, `σ₀²` and the default betting rule (they are instances of "any fold-one rule" / "predictable `λ`").

Encodings (see card `certify/cards/wave30tq.md`):
* an `α`-trimming of `P` is `trimMeasure P γ = P.withDensity (ofReal ∘ γ)` with `IsTrimDensity P α γ` (frozen
  `TrimmedMMD/ZeroSet`: `γ` measurable, `0 ≤ γ ≤ 1/(1−α)` everywhere, `∫ γ dP = 1`); `inf_{R_α(P)}`/`sup_{R_α(Q)}` are
  `⨅`/`⨆` over that subtype (`trimInf`, `trimSup`; nonempty and bounded for bounded `f`, `α ∈ [0,1)`);
  `TV` is the frozen `StatFormal.Distances.tvDist`; `T(f)` is the frozen `Wave17a.sepVal` of the frozen
  `TrimmedMMD.Concentration.region`;
* a `p`-quantile of `f` under `μ` is `q` with `μ{f < q} ≤ p ≤ μ{f ≤ q}` (`IsQuantileAt`);
* `f̃ = (f ∨ s') ∧ s` is `clip`, the ramp `g = (f̃ − s')/(s − s')` is `ramp`;
* fold one fixed (`*_cond`, `cor1`, `pair_facts`): the `[0,1]`-valued `g` and the betting fractions are parameters;
  fold two is `ω = (x, y) ∈ 𝒳^{n} × 𝒳^{m}` under `P^{⊗n} ⊗ Q^{⊗m}` (`n = n₂`, `m = m₂`);
  random fold one (`thm1`, `thm1_condexp`, `cor1_test`, `cor1_lcb`, `cor2`): fold one is an arbitrary probability
  space `(Ω₁, μ₁)` (the paper's `D_1 ∼ P^{⊗n₁} ⊗ Q^{⊗m₁}`, possibly with independent extra randomness, is an instance),
  independent of fold two (product measure), and the rules are jointly measurable functions of `D_1`;
* the block pairing: blocks `A_k ⊆ [n]`, `B_k ⊆ [m]`, `k < N`, nonempty and pairwise disjoint on each side
  (`IsBlockPairing`), `Z_k = mean_{A_k} G − mean_{B_k} H` (`pairZ`); the printed pairing (`n ≤ m`: `A_k = {k}`, `B_k` the
  `k`-th of `n` consecutive blocks of sizes `⌊m/n⌋` or `⌈m/n⌉`, `N = n`; mirror otherwise) is an instance;
* predictable fractions: `λ_k = lam k (Z_0, …, Z_{k−1})` (0-indexed; `past`), `lam k` measurable with values in
  `[0, c/(1+α)]` for `k < N` (`IsBetRule`); `K_t = ∏_{k<t}(1 + λ_k(Z_k − α))` (`wealth`); reject iff
  `∃ t ≤ N, K_t ≥ 1/δ` (`betReject`, `= max_{t≤N} K_t ≥ 1/δ`; `K_0 = 1 < 1/δ`);
* Corollary 1: `sMean`, `uVar` (unbiased, `(n−1)⁻¹`), `sigBar` (`σ̄ = min{1/2, √V + √(2 log(1/δ₂)/(n−1))}`), `ebLB`
  (`L̂B`), natural logarithm; Corollary 2: `levelReject` (the test at one level), `α̂_lo` the frozen
  `TrimmedMMD.Lower.alphaLo` (`eq:downclosed`).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30tq

open StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.Concentration

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Population objects (§2.1, §2.2) -/

/-- `β = (1 − α)⁻¹`. -/
def beta (α : ℝ) : ℝ := 1 / (1 - α)

/-- `ψ_s(u) = s − β (s − u)₊`. -/
def psiS (α s u : ℝ) : ℝ := s - beta α * max (s - u) 0

/-- `θ(f; s, s') = E_P[s − β(s − f(X))₊] − E_Q[s' + β(f(Y) − s')₊]`. -/
def theta (P Q : Measure 𝒳) (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ) : ℝ :=
  (∫ x, psiS α s (f x) ∂P) - ∫ y, (s' + beta α * max (f y - s') 0) ∂Q

/-- The trimming `P' = γ · P` of `P` with density `γ`. -/
def trimMeasure (P : Measure 𝒳) (γ : 𝒳 → ℝ) : Measure 𝒳 :=
  P.withDensity fun x => ENNReal.ofReal (γ x)

/-- `inf_{P' ∈ R_α(P)} E_{P'} f`. -/
def trimInf (P : Measure 𝒳) (α : ℝ) (f : 𝒳 → ℝ) : ℝ :=
  ⨅ γ : {γ : 𝒳 → ℝ // IsTrimDensity P α γ}, ∫ x, f x ∂(trimMeasure P γ.1)

/-- `sup_{Q' ∈ R_α(Q)} E_{Q'} f`. -/
def trimSup (Q : Measure 𝒳) (α : ℝ) (f : 𝒳 → ℝ) : ℝ :=
  ⨆ γ : {γ : 𝒳 → ℝ // IsTrimDensity Q α γ}, ∫ y, f y ∂(trimMeasure Q γ.1)

/-- `q` is a `p`-quantile of `f` under `μ`: `μ{f < q} ≤ p ≤ μ{f ≤ q}` (`F(q−) ≤ p ≤ F(q)`). -/
def IsQuantileAt (μ : Measure 𝒳) (f : 𝒳 → ℝ) (p q : ℝ) : Prop :=
  μ.real {x | f x < q} ≤ p ∧ p ≤ μ.real {x | f x ≤ q}

/-- The clipped witness `f̃ = (f ∨ s') ∧ s`. -/
def clip (f : 𝒳 → ℝ) (s s' : ℝ) (x : 𝒳) : ℝ := min (max (f x) s') s

/-- The ramp `g = (f̃ − s')/(s − s')` of `f` between `s'` and `s`. -/
def ramp (f : 𝒳 → ℝ) (s s' : ℝ) (x : 𝒳) : ℝ := (clip f s s' x - s') / (s - s')

/-! ### Fold two: block pairing and betting (§2.3) -/

/-- `|A|⁻¹ Σ_{i ∈ A} u_i`. -/
def blockMean {n : ℕ} (A : Finset (Fin n)) (u : Fin n → ℝ) : ℝ := (∑ i ∈ A, u i) / (A.card : ℝ)

/-- The pair statistics `Z_k = mean_{i ∈ A_k} g(x_i) − mean_{j ∈ B_k} g(y_j)`. -/
def pairZ {n m N : ℕ} (g : 𝒳 → ℝ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m))
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (k : Fin N) : ℝ :=
  blockMean (A k) (fun i => g (x i)) - blockMean (B k) (fun j => g (y j))

/-- A block pairing: nonempty blocks, pairwise disjoint on each side. -/
def IsBlockPairing {n m N : ℕ} (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) : Prop :=
  (∀ k, (A k).Nonempty) ∧ (∀ k, (B k).Nonempty) ∧
    (∀ k l, k ≠ l → Disjoint (A k) (A l)) ∧ (∀ k l, k ≠ l → Disjoint (B k) (B l))

/-- The past `(z_0, …, z_{k−1})` of `z` before step `k`. -/
def past {N : ℕ} (z : Fin N → ℝ) (k : Fin N) : Fin k → ℝ := fun i => z (Fin.castLE k.isLt.le i)

/-- The wealth `K_t = ∏_{k < t} (1 + λ_k (z_k − α))`, `λ_k = lam k (z_0, …, z_{k−1})`. -/
def wealth {N : ℕ} (lam : (k : ℕ) → (Fin k → ℝ) → ℝ) (α : ℝ) (z : Fin N → ℝ) (t : ℕ) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + lam k (past z k) * (z k - α))

/-- The betting test rejects `H_{0,α}`: `max_{t ≤ N} K_t ≥ 1/δ`. -/
def betReject {N : ℕ} (lam : (k : ℕ) → (Fin k → ℝ) → ℝ) (α δ : ℝ) (z : Fin N → ℝ) : Prop :=
  ∃ t : ℕ, t ≤ N ∧ 1 / δ ≤ wealth lam α z t

/-- Predictable betting fractions at level `α` with cap `c`: `λ_k` a measurable function of the past with values in
`[0, c/(1+α)]`, for every step `k < N`. -/
def IsBetRule (N : ℕ) (α c : ℝ) (lam : (k : ℕ) → (Fin k → ℝ) → ℝ) : Prop :=
  ∀ k < N, Measurable (lam k) ∧ ∀ z, 0 ≤ lam k z ∧ lam k z ≤ c / (1 + α)

/-! ### Corollary 1: the empirical-Bernstein bound -/

/-- Sample mean `n⁻¹ Σ u_i`. -/
def sMean {n : ℕ} (u : Fin n → ℝ) : ℝ := (∑ i, u i) / (n : ℝ)

/-- Unbiased sample variance `(n − 1)⁻¹ Σ (u_i − ū)²`. -/
def uVar {n : ℕ} (u : Fin n → ℝ) : ℝ := (∑ i, (u i - sMean u) ^ 2) / ((n : ℝ) - 1)

/-- `σ̄ = min{1/2, √V + √(2 log(1/δ₂)/(n − 1))}`. -/
def sigBar (n : ℕ) (δ₂ V : ℝ) : ℝ := min (1 / 2) (√V + √(2 * Real.log (1 / δ₂) / ((n : ℝ) - 1)))

/-- `L̂B = Ḡ − H̄ − √(2 L₁ (σ̄_G²/n + σ̄_H²/m)) − (L₁/3) max(1/n, 1/m)`, `L₁ = log(1/δ₁)`. -/
def ebLB {n m : ℕ} (δ₁ δ₂ : ℝ) (G : Fin n → ℝ) (H : Fin m → ℝ) : ℝ :=
  sMean G - sMean H
    - √(2 * Real.log (1 / δ₁) * (sigBar n δ₂ (uVar G) ^ 2 / n + sigBar m δ₂ (uVar H) ^ 2 / m))
    - Real.log (1 / δ₁) / 3 * max (1 / (n : ℝ)) (1 / (m : ℝ))

/-- The test of `H_{0,α}` at one grid level: Theorem 1's betting test (`useBet = true`) or Corollary 1's
"reject if `L̂B > α`" (`useBet = false`), with the level's ramp `g` and fractions `lam`, on fold two `(x, y)`. -/
def levelReject {n m N : ℕ} (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (useBet : Bool)
    (α δ δ₁ δ₂ : ℝ) (g : 𝒳 → ℝ) (lam : (k : ℕ) → (Fin k → ℝ) → ℝ) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : Prop :=
  if useBet then betReject lam α δ (pairZ g A B x y)
  else α < ebLB δ₁ δ₂ (fun i => g (x i)) (fun j => g (y j))

namespace Claims

/-! ### Lemma 1 -/

/-- Lemma 1, against every pair of trimmings: `θ(f; s, s') ≤ E_{P'} f − E_{Q'} f` for `P' ∈ R_α(P)`, `Q' ∈ R_α(Q)`. -/
def lem1_trim : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ) (γ γ' : 𝒳 → ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 →
    IsTrimDensity P α γ → IsTrimDensity Q α γ' →
      theta P Q α f s s' ≤ (∫ x, f x ∂(trimMeasure P γ)) - ∫ y, f y ∂(trimMeasure Q γ')

/-- Lemma 1 as printed: `θ(f; s, s') ≤ inf_{P' ∈ R_α(P)} E_{P'} f − sup_{Q' ∈ R_α(Q)} E_{Q'} f`. -/
def lem1 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 →
      theta P Q α f s s' ≤ trimInf P α f - trimSup Q α f

/-- Lemma 1, "hence": if `TV(P,Q) ≤ α` then the right side is `≤ 0` and `θ(f; s, s') ≤ 0` for all `s, s'`. -/
def lem1_null : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → StatFormal.Distances.tvDist P Q ≤ α →
      trimInf P α f - trimSup Q α f ≤ 0 ∧ ∀ s s' : ℝ, theta P Q α f s s' ≤ 0

/-- Lemma 1, RKHS sentence: for `f ∈ H` (the witness `x ↦ ⟨f, φ(x)⟩`), the right side is the paper's estimand
`T(f) = inf_{a ∈ 𝒞_{α,k}(P)} ⟨f, a⟩ − sup_{b ∈ 𝒞_{α,k}(Q)} ⟨f, b⟩`. -/
def lem1_rkhs : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α : ℝ) (f : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      (((trimInf P α (fun x => ⟪f, φ x⟫_ℝ) - trimSup Q α (fun x => ⟪f, φ x⟫_ℝ) : ℝ)) : EReal) =
        StatFormal.Wave17a.sepVal f (region φ α P) (region φ α Q)

/-- Lemma 1, attainment: `sup_{s,s'} θ(f; s, s')` equals the right side and is attained; it is attained at every
`(1−α)`-quantile `q` of `f(X)` and every `α`-quantile `q'` of `f(Y)`, and such quantiles exist. -/
def lem1_attain : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 →
      IsGreatest (Set.range fun p : ℝ × ℝ => theta P Q α f p.1 p.2) (trimInf P α f - trimSup Q α f) ∧
      (∃ q q' : ℝ, IsQuantileAt P f (1 - α) q ∧ IsQuantileAt Q f α q') ∧
      ∀ q q' : ℝ, IsQuantileAt P f (1 - α) q → IsQuantileAt Q f α q' →
        theta P Q α f q q' = trimInf P α f - trimSup Q α f

/-! ### Lemma 2 -/

/-- Lemma 2 (1), with the ramp's range: for `s > s'`, `g ∈ [0,1]` and `θ(f̃; s, s') = β(s − s')(E_P g − E_Q g − α)`. -/
def lem2_1 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ),
    Measurable f → 0 ≤ α → α < 1 → s' < s →
      (∀ x, ramp f s s' x ∈ Icc (0 : ℝ) 1) ∧
      theta P Q α (clip f s s') s s' =
        beta α * (s - s') * ((∫ x, ramp f s s' x ∂P) - (∫ y, ramp f s s' y ∂Q) - α)

/-- Lemma 2 (2): `θ(f̃) − θ(f) = β E_P(s' − f(X))₊ + β E_Q(f(Y) − s)₊ ≥ 0`. -/
def lem2_2 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → s' < s →
      theta P Q α (clip f s s') s s' - theta P Q α f s s' =
          beta α * (∫ x, max (s' - f x) 0 ∂P) + beta α * (∫ y, max (f y - s) 0 ∂Q) ∧
        0 ≤ beta α * (∫ x, max (s' - f x) 0 ∂P) + beta α * (∫ y, max (f y - s) 0 ∂Q)

/-- Lemma 2 (3): `Var ψ_s(f̃(X)) ≤ Var ψ_s(f(X))` and `Var (f̃(Y) − s')₊ ≤ Var (f(Y) − s')₊`. -/
def lem2_3 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → s' < s →
      variance (fun x => psiS α s (clip f s s' x)) P ≤ variance (fun x => psiS α s (f x)) P ∧
      variance (fun y => max (clip f s s' y - s') 0) Q ≤ variance (fun y => max (f y - s') 0) Q

/-- Lemma 2 (4): if `s ≤ s'` then `θ(f; s, s') ≤ s − s' ≤ 0` for all laws. -/
def lem2_4 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (α : ℝ) (f : 𝒳 → ℝ) (s s' : ℝ),
    Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ α → α < 1 → s ≤ s' →
      theta P Q α f s s' ≤ s - s' ∧ s - s' ≤ 0

/-! ### §2.3: the pair statistics -/

/-- §2.3, fold one fixed: `Z_k ∈ [−1,1]`, `E Z_k = Δ = E_P g − E_Q g` for every `k`, `Z_1, …, Z_N` independent, and
`Δ ≤ TV(P,Q)` (the elementary inequality for the `[0,1]`-valued `g`). -/
def pair_facts : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (g : 𝒳 → ℝ),
    IsBlockPairing A B → Measurable g → (∀ x, g x ∈ Icc (0 : ℝ) 1) →
      (∀ k x y, pairZ g A B x y k ∈ Icc (-1 : ℝ) 1) ∧
      (∀ k, ∫ ω, pairZ g A B ω.1 ω.2 k ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) =
        (∫ x, g x ∂P) - ∫ y, g y ∂Q) ∧
      iIndepFun (fun k (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => pairZ g A B ω.1 ω.2 k)
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ∧
      (∫ x, g x ∂P) - (∫ y, g y ∂Q) ≤ StatFormal.Distances.tvDist P Q

/-! ### Theorem 1 -/

/-- Theorem 1, fold one fixed: for every `[0,1]`-valued `g`, every block pairing, every predictable rule, and every
`(P,Q)` with `TV(P,Q) ≤ α`: `P(max_{t ≤ N} K_t ≥ 1/δ) ≤ δ` under `P^{⊗n} ⊗ Q^{⊗m}`. -/
def thm1_cond : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m N : ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α δ c : ℝ) (g : 𝒳 → ℝ)
    (lam : (k : ℕ) → (Fin k → ℝ) → ℝ),
    IsBlockPairing A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    Measurable g → (∀ x, g x ∈ Icc (0 : ℝ) 1) → IsBetRule N α c lam →
    StatFormal.Distances.tvDist P Q ≤ α →
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
        {ω | betReject lam α δ (pairZ g A B ω.1 ω.2)} ≤ ENNReal.ofReal δ

/-- Theorem 1, the printed conditional form: with fold one `D_1` random on `(Ω₁, μ₁)`, independent of fold two, and
`g`, `λ` jointly measurable functions of `D_1` (and of the past), the rejection event is measurable and
`P(max_{t ≤ N} K_t ≥ 1/δ | D_1) ≤ δ` almost surely (conditional expectation of the indicator given `σ(D_1)`). -/
def thm1_condexp : Prop :=
  ∀ (𝒳 Ω₁ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
    (n m N : ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α δ c : ℝ) (g : Ω₁ → 𝒳 → ℝ)
    (lam : Ω₁ → (k : ℕ) → (Fin k → ℝ) → ℝ),
    IsBlockPairing A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    Measurable (fun p : Ω₁ × 𝒳 => g p.1 p.2) → (∀ d x, g d x ∈ Icc (0 : ℝ) 1) →
    (∀ k < N, Measurable (fun p : Ω₁ × (Fin k → ℝ) => lam p.1 k p.2) ∧
      ∀ d z, 0 ≤ lam d k z ∧ lam d k z ≤ c / (1 + α)) →
    StatFormal.Distances.tvDist P Q ≤ α →
      MeasurableSet {ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
          betReject (lam ω.1) α δ (pairZ (g ω.1) A B ω.2.1 ω.2.2)} ∧
      condExp (MeasurableSpace.comap Prod.fst ‹MeasurableSpace Ω₁›)
          (μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
          (Set.indicator {ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
            betReject (lam ω.1) α δ (pairZ (g ω.1) A B ω.2.1 ω.2.2)} fun _ => (1 : ℝ))
        ≤ᵐ[μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))] fun _ => δ

/-- Theorem 1, "so": `sup_{(P,Q) ∈ H_{0,α}} P_{P,Q}(reject) ≤ δ`, fold one random. -/
def thm1 : Prop :=
  ∀ (𝒳 Ω₁ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
    (n m N : ℕ) (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α δ c : ℝ) (g : Ω₁ → 𝒳 → ℝ)
    (lam : Ω₁ → (k : ℕ) → (Fin k → ℝ) → ℝ),
    IsBlockPairing A B → 0 ≤ α → 0 < δ → δ < 1 → 0 < c → c ≤ 1 →
    Measurable (fun p : Ω₁ × 𝒳 => g p.1 p.2) → (∀ d x, g d x ∈ Icc (0 : ℝ) 1) →
    (∀ k < N, Measurable (fun p : Ω₁ × (Fin k → ℝ) => lam p.1 k p.2) ∧
      ∀ d z, 0 ≤ lam d k z ∧ lam d k z ≤ c / (1 + α)) →
    StatFormal.Distances.tvDist P Q ≤ α →
      (μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | betReject (lam ω.1) α δ (pairZ (g ω.1) A B ω.2.1 ω.2.2)} ≤ ENNReal.ofReal δ

/-! ### Corollary 1 -/

/-- Corollary 1, fold one fixed: for `n, m ≥ 2`, `δ = δ₁ + 2δ₂`, `P(L̂B > Δ) ≤ δ`, `Δ = E_P g − E_Q g`. -/
def cor1 : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m : ℕ) (g : 𝒳 → ℝ) (δ₁ δ₂ : ℝ),
    2 ≤ n → 2 ≤ m → 0 < δ₁ → 0 < δ₂ → Measurable g → (∀ x, g x ∈ Icc (0 : ℝ) 1) →
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
        {ω | (∫ x, g x ∂P) - (∫ y, g y ∂Q) < ebLB δ₁ δ₂ (fun i => g (ω.1 i)) (fun j => g (ω.2 j))}
          ≤ ENNReal.ofReal (δ₁ + 2 * δ₂)

/-- Corollary 1, "reject if `L̂B > α`" is a valid certificate: under `TV(P,Q) ≤ α`, `P(L̂B > α) ≤ δ`, fold one random. -/
def cor1_test : Prop :=
  ∀ (𝒳 Ω₁ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (n m : ℕ) (g : Ω₁ → 𝒳 → ℝ)
    (α δ₁ δ₂ : ℝ),
    2 ≤ n → 2 ≤ m → 0 < δ₁ → 0 < δ₂ →
    Measurable (fun p : Ω₁ × 𝒳 => g p.1 p.2) → (∀ d x, g d x ∈ Icc (0 : ℝ) 1) →
    StatFormal.Distances.tvDist P Q ≤ α →
      (μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | α < ebLB δ₁ δ₂ (fun i => g ω.1 (ω.2.1 i)) (fun j => g ω.1 (ω.2.2 j))}
          ≤ ENNReal.ofReal (δ₁ + 2 * δ₂)

/-- Corollary 1, `L̂B` is a `(1 − δ)` lower confidence bound for `TV(P,Q)`, for every `(P,Q)`, fold one random. -/
def cor1_lcb : Prop :=
  ∀ (𝒳 Ω₁ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (n m : ℕ) (g : Ω₁ → 𝒳 → ℝ)
    (δ₁ δ₂ : ℝ),
    2 ≤ n → 2 ≤ m → 0 < δ₁ → 0 < δ₂ →
    Measurable (fun p : Ω₁ × 𝒳 => g p.1 p.2) → (∀ d x, g d x ∈ Icc (0 : ℝ) 1) →
      (μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | StatFormal.Distances.tvDist P Q < ebLB δ₁ δ₂ (fun i => g ω.1 (ω.2.1 i)) (fun j => g ω.1 (ω.2.2 j))}
          ≤ ENNReal.ofReal (δ₁ + 2 * δ₂)

/-! ### Corollary 2 -/

/-- Corollary 2: a fixed grid `α_1, …, α_J ≥ 0`; at level `j` a fold-one ramp `g_j` and, for betting levels,
fractions `λ^{(j)}` (any jointly measurable functions of `D_1`, refitted per level or not), each level tested by
Theorem 1 (`useBet j`) or by Corollary 1 at level `δ`, all on the same fold two; `α̂_lo` by `eq:downclosed`. Then
`P(α̂_lo > TV(P,Q)) ≤ δ` for every sample size and every `(P,Q)`. -/
def cor2 : Prop :=
  ∀ (𝒳 Ω₁ : Type) [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (n m N J : ℕ)
    (A : Fin N → Finset (Fin n)) (B : Fin N → Finset (Fin m)) (α : Fin J → ℝ) (useBet : Fin J → Bool)
    (δ c δ₁ δ₂ : ℝ) (g : Fin J → Ω₁ → 𝒳 → ℝ) (lam : Fin J → Ω₁ → (k : ℕ) → (Fin k → ℝ) → ℝ),
    IsBlockPairing A B → 0 < δ → δ < 1 → 0 < c → c ≤ 1 → (∀ j, 0 ≤ α j) →
    (∀ j, Measurable fun p : Ω₁ × 𝒳 => g j p.1 p.2) → (∀ j d x, g j d x ∈ Icc (0 : ℝ) 1) →
    (∀ j, useBet j = true → ∀ k < N, Measurable (fun p : Ω₁ × (Fin k → ℝ) => lam j p.1 k p.2) ∧
      ∀ d z, 0 ≤ lam j d k z ∧ lam j d k z ≤ c / (1 + α j)) →
    (∀ j, useBet j = false → 2 ≤ n ∧ 2 ≤ m ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ = δ₁ + 2 * δ₂) →
      (μ₁.prod ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)))
        {ω | StatFormal.Distances.tvDist P Q < StatFormal.TrimmedMMD.Lower.alphaLo α
            (fun j => levelReject A B (useBet j) (α j) δ δ₁ δ₂ (g j ω.1) (lam j ω.1) ω.2.1 ω.2.2)}
          ≤ ENNReal.ofReal δ

end Claims
end StatFormal.Wave30tq
