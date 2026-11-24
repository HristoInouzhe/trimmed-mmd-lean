import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.Probability.Quantile
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — second batch of DEFECTS leads (#17, #19, #20, #33 `thm:finite-rank`)

Sources (verbatim quotes and verdicts in `lean-formalisation/inventory/defects_resolution.md`):
* #17 `robust-equality-outcomes-under-distribution-shift/jasa/supp_common_shift.tex:276-293`
  (`prop:cs-monotone`): "consider the pairs $(Q_0,Q_1)$ with
  $W_2^2(T_\#h_\#\widehat P_s,h_\#Q_s)\le\beta_s$ for a common $T\in\Theta_L$ … the supremum is
  at least $L\,\Delta(h)$ … Without a slope bound the supremum is $+\infty$ whenever
  $\Delta(h)>0$", with the standing notation `:7-12` (`K` compact, `Δ(h) = W₂(h#P̂₀, h#P̂₁)`)
  and populations in `𝒫(K)` (`jasa/main.tex:197,240`).
* #19 `…/paper2/main.tex:631-650` (`prop:repair`(ii)): prediction laws `μ_s = h#P̂_s` (empirical);
  "Partial barycentric repair $T_s=g_s\circ F_s$ with $g_s=\ell q_s+(1-\ell)q_B$,
  $q_B=\pi_0q_0+\pi_1q_1$ … has $\Delta_T=\ell\Delta$"; proof `app_proofs.tex:257-258`.
* #20 `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2234-2252` (`prop:debiased`) and
  `eq:ceps` (`:2156-2159`): the stationarity equation `τ²/c_ε(τ,τ) = Σ_s p_s σ_s²/c_ε(σ_s,τ)`, whose
  unique positive root the text calls "supported numerically … not proved".
* #33 `otfd/papers/A_sieves/supplement.tex:271-281` (`thm:finite-rank`, "every $K\ge r$ gives
  the same ranks"), assignment `main.tex:455-461` (`σ̂ ∈ argmin`).

Severities (DEFECTS.md scale):
* #17 S3, scope slip: true for prediction-line laws. `cs_monotone_line_lower` covers only the lower
  bound.
* #19 S1 for the section's own empirical laws. The root cause is a missing atomlessness hypothesis.
* #20 not a defect: the gap is closed.
* #33 `thm:finite-rank` S4: tie-break wording.
* #33 `prop:lift-dual`(iii), S4, not formalised: `Σ_X ≻ 0` is implied by the setting of `sec:lift`
  (`F = ∇ψ` pushes `P_T` to an a.c. `μ_T`), but is unstated.

Covered:
* `cs_monotone_lower_false`, `cs_monotone_infinite_false`: the printed lower bound `≥ LΔ` and the
  printed `+∞` claim are false for populations on a compact `K` (witness `K = [0,1]`, `h = id`,
  `P̂₀ = δ₀`, `P̂₁ = δ₁`, `β_s = 1`, `L = 2`; the feasible set is non-empty (`T = id`,
  `Q_s = P̂_s`) and every feasible pair has `W₂ ≤ 1`);
  `cs_monotone_line_lower` (corrected): over prediction-line laws `Q'_s ∈ 𝒫(ℝ)` the bound
  `≥ LΔ` holds.
* `repair_partial_false`: `Δ_T = ℓΔ` fails for empirical prediction laws (witness `μ₀ = δ₀`,
  `μ₁ = ½δ₀ + ½δ₁`, `π = (⅓, ⅔)` = sample proportions, `ℓ = 0`).
* `debiased_root_unique`, `debiased_root_between` (closing the "open" gap; not a defect of the
  statement): for any number `S` of groups the stationarity equation has exactly one positive
  root, and it lies between the arithmetic and quadratic means `Σ p_s σ_s ≤ τ ≤ (Σ p_s σ_s²)^{1/2}`.
* `finite_rank_false`: without a tie-break, two optimal assignments give different ranks
  (witness `n = 2`, `r = 1`, data `0, 0`, grid `−1, 1`); `finite_rank_optimal_iff` and
  `finite_rank_unique` (corrected): the optimal sets coincide, and a unique optimum is shared.

Not covered (declared):
* #17: `d ≥ 2`, the upper bound `≤ LΔ + √β₀ + √β₁`, equality at `β = 0`;
* #19: the corrected statement for atomless `μ_s` (needs the probability integral transform for
  `g_s ∘ F_s`), and parts (i), (iii);
* #20: that the root is the Gaussian *minimiser* (needs the derivative computation of the proof) and
  the two limits;
* #33: general `M_K` (encoded `M_K = I`); `prop:lift-dual`(iii) (its `Σ_X ≻ 0` is implied by the
  setting);
* leads #9, #11, #18, #21–#28, #32 (S2/S4 or not a defect; written verdicts only).

Encodings:
* populations "in `𝒫(K)`" are probability measures on `ℝ` with `Q Kᶜ = 0`; `h_#Q` is `Q.map h`;
  `W₂` is Tau Ceti's `wassersteinEDist 2` (`ℝ≥0∞`-valued) and the supremum is an `ℝ≥0∞` `iSup`;
  `Θ_L` = monotone and `L`-Lipschitz maps of the line; "without a slope bound" = monotone maps;
* empirical laws `n⁻¹ Σ δ_{x_i}` (`empirical`), with `0 < n`;
* `F_s` is Mathlib's `cdf`, `q_s` is Tau Ceti's `Measure.quantile` (`sInf {x | t ≤ F(x)}`, which at
  `t = 1` is the largest atom of an empirical law); the weights `π_s` are arbitrary with
  `π₀ + π₁ = 1` (the witness uses the sample proportions, so either reading is refuted);
* `c_ε(a,b) = (−ε + √(ε² + 4a²b²))/2` (`eq:ceps`); `S` groups with weights `p : Fin S → ℝ`,
  `p_s > 0`, `Σ p_s = 1`, and scales `σ_s > 0`;
* ranks: `R_{i,K} = u_{σ̂(i)}`; `Z^{(K)}` is zero padding (`Fin.append v 0`); `M_K = I`;
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes
`Defects2/Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal NNReal

namespace StatFormal.Defects2

/-- The empirical law `n⁻¹ Σᵢ δ_{xᵢ}`. -/
def empirical {n : ℕ} (x : Fin n → ℝ) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-! ### #17 `prop:cs-monotone` -/

/-- `Θ_L`: nondecreasing `L`-Lipschitz maps of the line. -/
def ThetaL (L : ℝ≥0) (T : ℝ → ℝ) : Prop := Monotone T ∧ LipschitzWith L T

/-- "Without a slope bound": nondecreasing maps of the line. -/
def ThetaMono (T : ℝ → ℝ) : Prop := Monotone T

/-- The supremum of `prop:cs-monotone` with populations in `𝒫(K)`:
`sup { W₂(h#Q₀, h#Q₁) : Q_s ∈ 𝒫(K), T ∈ Θ, W₂²(T#h#P̂_s, h#Q_s) ≤ β_s }`. -/
def csMonoSup (K : Set ℝ) (h : ℝ → ℝ) (P₀ P₁ : Measure ℝ) (β₀ β₁ : ℝ≥0∞)
    (Θ : (ℝ → ℝ) → Prop) : ℝ≥0∞ :=
  ⨆ (Q₀ : Measure ℝ) (Q₁ : Measure ℝ) (T : ℝ → ℝ)
    (_ : IsProbabilityMeasure Q₀ ∧ IsProbabilityMeasure Q₁ ∧ Q₀ Kᶜ = 0 ∧ Q₁ Kᶜ = 0 ∧ Θ T ∧
      wassersteinEDist 2 ((P₀.map h).map T) (Q₀.map h) ^ 2 ≤ β₀ ∧
      wassersteinEDist 2 ((P₁.map h).map T) (Q₁.map h) ^ 2 ≤ β₁),
    wassersteinEDist 2 (Q₀.map h) (Q₁.map h)

/-- The same supremum over prediction-line laws `Q'_s ∈ 𝒫(ℝ)` around `T#μ_s` (corrected reading). -/
def lineMonoSup (μ₀ μ₁ : Measure ℝ) (β₀ β₁ : ℝ≥0∞) (Θ : (ℝ → ℝ) → Prop) : ℝ≥0∞ :=
  ⨆ (Q₀ : Measure ℝ) (Q₁ : Measure ℝ) (T : ℝ → ℝ)
    (_ : IsProbabilityMeasure Q₀ ∧ IsProbabilityMeasure Q₁ ∧ Θ T ∧
      wassersteinEDist 2 (μ₀.map T) Q₀ ^ 2 ≤ β₀ ∧ wassersteinEDist 2 (μ₁.map T) Q₁ ^ 2 ≤ β₁),
    wassersteinEDist 2 Q₀ Q₁

/-! ### #19 `prop:repair`(ii) -/

/-- `q_B = π₀ q₀ + π₁ q₁`. -/
def baryQ (π₀ π₁ : ℝ) (μ₀ μ₁ : Measure ℝ) (u : ℝ) : ℝ :=
  π₀ * μ₀.quantile u + π₁ * μ₁.quantile u

/-- Partial barycentric repair `T_s = g_s ∘ F_s`, `g_s = ℓ q_s + (1 − ℓ) q_B`. -/
def repairMap (ℓ π₀ π₁ : ℝ) (μ₀ μ₁ μs : Measure ℝ) (y : ℝ) : ℝ :=
  ℓ * μs.quantile (cdf μs y) + (1 - ℓ) * baryQ π₀ π₁ μ₀ μ₁ (cdf μs y)

/-! ### #20 `prop:debiased` -/

/-- `eq:ceps`: `c_ε(a,b) = (−ε + √(ε² + 4a²b²))/2`. -/
def cEps (ε a b : ℝ) : ℝ := (-ε + Real.sqrt (ε ^ 2 + 4 * a ^ 2 * b ^ 2)) / 2

/-- The stationarity equation of `prop:debiased`, `S` groups. -/
def DebiasedEq {S : ℕ} (ε : ℝ) (p σ : Fin S → ℝ) (τ : ℝ) : Prop :=
  τ ^ 2 / cEps ε τ τ = ∑ s, p s * σ s ^ 2 / cEps ε (σ s) τ

/-! ### #33 `thm:finite-rank` -/

/-- Assignment cost `Σᵢ ‖zᵢ − u_{σ(i)}‖²` (`M_K = I`). -/
def assignCost {n k : ℕ} (z u : Fin n → Fin k → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, ∑ j, (z i j - u (σ i) j) ^ 2

/-- `σ` is an optimal assignment. -/
def IsOptAssign {n k : ℕ} (z u : Fin n → Fin k → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ, assignCost z u σ ≤ assignCost z u τ

/-- Zero padding `ℝ^r → ℝ^{r+k}`, `v ↦ (v, 0)`. -/
def pad {r k : ℕ} (v : Fin r → ℝ) : Fin (r + k) → ℝ := Fin.append v 0

namespace Claims

/-- #17, printed lower bound: false for populations on a compact `K`. -/
def cs_monotone_lower_false : Prop :=
  ¬ ∀ (K : Set ℝ) (h : ℝ → ℝ) (n₀ n₁ : ℕ) (x₀ : Fin n₀ → ℝ) (x₁ : Fin n₁ → ℝ) (L : ℝ≥0)
      (β₀ β₁ : ℝ≥0∞), IsCompact K → Continuous h → 0 < n₀ → 0 < n₁ →
      (∀ i, x₀ i ∈ K) → (∀ i, x₁ i ∈ K) →
      (L : ℝ≥0∞) * wassersteinEDist 2 ((empirical x₀).map h) ((empirical x₁).map h) ≤
        csMonoSup K h (empirical x₀) (empirical x₁) β₀ β₁ (ThetaL L)

/-- #17, printed "`+∞` without a slope bound whenever `Δ(h) > 0`": false on a compact `K`. -/
def cs_monotone_infinite_false : Prop :=
  ¬ ∀ (K : Set ℝ) (h : ℝ → ℝ) (n₀ n₁ : ℕ) (x₀ : Fin n₀ → ℝ) (x₁ : Fin n₁ → ℝ)
      (β₀ β₁ : ℝ≥0∞), IsCompact K → Continuous h → 0 < n₀ → 0 < n₁ →
      (∀ i, x₀ i ∈ K) → (∀ i, x₁ i ∈ K) →
      0 < wassersteinEDist 2 ((empirical x₀).map h) ((empirical x₁).map h) →
        csMonoSup K h (empirical x₀) (empirical x₁) β₀ β₁ ThetaMono = ⊤

/-- #17, corrected: over prediction-line laws the supremum is at least `L·Δ`. -/
def cs_monotone_line_lower : Prop :=
  ∀ (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (L : ℝ≥0)
    (β₀ β₁ : ℝ≥0∞),
    (L : ℝ≥0∞) * wassersteinEDist 2 μ₀ μ₁ ≤ lineMonoSup μ₀ μ₁ β₀ β₁ (ThetaL L)

/-- #19, printed `Δ_T = ℓΔ` for partial barycentric repair: false for empirical laws. -/
def repair_partial_false : Prop :=
  ¬ ∀ (n₀ n₁ : ℕ) (x₀ : Fin n₀ → ℝ) (x₁ : Fin n₁ → ℝ) (π₀ π₁ ℓ : ℝ),
      0 < n₀ → 0 < n₁ → 0 ≤ π₀ → 0 ≤ π₁ → π₀ + π₁ = 1 → 0 ≤ ℓ → ℓ ≤ 1 →
      wassersteinEDist 2
          ((empirical x₀).map (repairMap ℓ π₀ π₁ (empirical x₀) (empirical x₁) (empirical x₀)))
          ((empirical x₁).map (repairMap ℓ π₀ π₁ (empirical x₀) (empirical x₁) (empirical x₁))) =
        ENNReal.ofReal ℓ * wassersteinEDist 2 (empirical x₀) (empirical x₁)

/-- #20: the stationarity equation of `prop:debiased` has exactly one positive root. -/
def debiased_root_unique : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p σ : Fin S → ℝ), 0 < ε → (∀ s, 0 < p s) → ∑ s, p s = 1 →
    (∀ s, 0 < σ s) → ∃! τ : ℝ, 0 < τ ∧ DebiasedEq ε p σ τ

/-- #20: the positive root lies between the arithmetic and the quadratic mean. -/
def debiased_root_between : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p σ : Fin S → ℝ) (τ : ℝ), 0 < ε → (∀ s, 0 < p s) → ∑ s, p s = 1 →
    (∀ s, 0 < σ s) → 0 < τ → DebiasedEq ε p σ τ →
      ∑ s, p s * σ s ≤ τ ∧ τ ≤ Real.sqrt (∑ s, p s * σ s ^ 2)

/-- #33, printed "every `K ≥ r` gives the same ranks": false without a tie-break. -/
def finite_rank_false : Prop :=
  ¬ ∀ (n r k : ℕ) (z u : Fin n → Fin r → ℝ) (σr σK : Equiv.Perm (Fin n)),
      IsOptAssign z u σr →
      IsOptAssign (fun i => pad (k := k) (z i)) (fun i => pad (k := k) (u i)) σK →
        ∀ i, u (σK i) = u (σr i)

/-- #33, corrected (i): the optimal assignments of the padded and of the `r`-dimensional problem
coincide. -/
def finite_rank_optimal_iff : Prop :=
  ∀ (n r k : ℕ) (z u : Fin n → Fin r → ℝ) (σ : Equiv.Perm (Fin n)),
    IsOptAssign (fun i => pad (k := k) (z i)) (fun i => pad (k := k) (u i)) σ ↔ IsOptAssign z u σ

/-- #33, corrected (ii): with a unique optimal assignment the ranks agree for every `K ≥ r`. -/
def finite_rank_unique : Prop :=
  ∀ (n r k : ℕ) (z u : Fin n → Fin r → ℝ) (σr σK : Equiv.Perm (Fin n)),
    IsOptAssign z u σr → (∀ τ, IsOptAssign z u τ → τ = σr) →
    IsOptAssign (fun i => pad (k := k) (z i)) (fun i => pad (k := k) (u i)) σK →
      ∀ i, u (σK i) = u (σr i)

end Claims

end StatFormal.Defects2
