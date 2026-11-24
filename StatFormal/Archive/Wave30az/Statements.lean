import StatFormal.Archive.ICL.Cond.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.SBFairness.Decay.Statements
import StatFormal.Archive.Wave30ao.Statements
import StatFormal.Archive.Wave30h.Statements
import StatFormal.Archive.Wave29d.Statements
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.Wave9b.Statements
import Mathlib.Probability.CondVar
import Mathlib.Topology.Instances.EReal.Lemmas

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 30az: miscellaneous coverage-note gaps (ICL `lem:cond-osc`, `lem:cond-metric`; SB
# `thm:decay` caveat, `prop:randpenalty` at `t = 1`, journal `lem:quantiles` at `u ∈ {0, 1}`; paper 2 `thm:npmle` for a
# general Feller kernel; trimmed MMD `lem:trimmedmean`, `prop:witnessstab` rate)

Sources (current text, read 2026-10-21):
* ICL (`context-distribution-ICL/paper/v4/supp/proofs_conditional.tex`, HEAD 98c633b; the only change since 7a571bc is the status table at `:46`, no line shift): `lem:cond-osc` (`:421-432`, the
  sentence "Hence, for every `z`, `|G(z;w)−G(z;w')|` and `|G^iid(z;w)−G^iid(z;w')|` are at most
  `B_L tanh(MΔ/2) ≤ B_L MΔ/2`", `:430-431`); `lem:cond-metric` (`:489-503`: the display, "For a fixed floor
  `ε ∈ [0,1)`, the second term is absent" (`:501`), "Moreover, `Θ` lies in a Euclidean ball of radius `½(d_X τ_max² + 1)^{1/2}`";
  proof `:520-524`, radius `½(d_X τ_max² + (1 − 2ε_min)²)^{1/2}`).
* SB long (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex`, HEAD 4e08c81): `def:glued` (`:2285-2294`), the
  sentence after it "always `G_ε ≥ W₂(R₀,R₁)`" (`:2296-2298`), `thm:decay` (`:2300-2320`, the caveat "Since
  `G_ε ≥ W₂(R₀,R₁)` with equality only at `ε = 0`, the certificate is weaker …", `:2311-2313`); `prop:randpenalty`
  (`:607-624`, "strictly positive for `t ∈ (0,1]` when `ε > 0`", `:617-618`) with `def:repair` (`C_ε(R_s,ν) < ∞`).
* SB journal (`data-fairness-repair-journal/journal/`, read-only copy, HEAD d93e78a): `thm:decay` (`supp/s_univariate.tex:
  248-266`, caveat `:259-262`: the caveat already reads "Since `G_ε ≥ W₂(R₀,R₁)` (`G_ε` is the `L²` distance of one particular coupling of
  `R₀` and `R₁`), the certificate is in general weaker …"); `prop:randpenalty` (`supp/s_setting.tex:321-338`, identical
  to the long version); `lem:quantiles` (`supp/s_proofs_field.tex:56-71`, the display (`:67`)
  `sup_{u∈[0,1]} |Q̃_n(u) − F^{-1}(u)| ≤ L(ε_n + 2/n)`), with the convention `F^{-1}(p) = inf{x : F(x) ≥ p}`
  (`supp/s_setting.tex:30`) and `ass:marg`.
* Paper 2 (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex`, HEAD f81aa97): `thm:npmle`
  (`:506-524`), with the Conventions ("A rule is a measurable `h : K → ℝ`, bounded on `K` when `K` is compact", `:214`),
  `eq:T` (`:247-251`).
* Trimmed MMD (`trimmed-mmd/paper.tex`, HEAD 58caecc): `lem:trimmedmean` (`:1002-1022`, "the minimum is the same
  expression applied to the smallest such fraction", the maximiser clause "the values equal to `v_(n−k)` sharing the
  remaining mass … in any way", and the uniqueness sentence); `prop:witnessstab` (`:1483-1517`, "Let
  Assumption ass:regularity hold" — no structure on `𝒳` — and `eq:witnessrate`).

Frozen objects reused (imported, not copied): ICL `iidLaw`, `tv1`, `wRetr`, Wave 12c `Giid`; SB `Decay` (`Gsq`,
`IsGluing`, `bridge`), Wave 30ao (`entCost`, `IsPrintedPlan`, `HasFiniteEnt`); Wave 30h (`AssMarg`, `empCdf`,
`interpQuant`, `ordStat`); Wave 29d (`psiK`, `npmleK`, `lambdaK`, `MixSettingK`, `phiRule`), paper 2 Seminorm (`gexp`);
BangBang (`ord`, `cap`, `kfloor`, `capped`, `qp`); Concentration (`region`), Projection (`IsMinNorm`), Wave 4b
(`witness`, `etaNM`); Tau Ceti (`wassersteinEDist`, `Measure.quantile`); Mathlib `condVar`.
New definitions: `quantE` (the printed `F^{-1}` in `EReal`), `phiLin`, `PhiK`, `TK` (paper 2 objects for a general kernel).

Covered:
* ICL `lem:cond-osc` (ii), the i.i.d. risk: `cond_osc_iid` (`|G^iid(w) − G^iid(w')| ≤ B_L tanh(MΔ/2) ≤ B_L MΔ/2`). With the
  certified `cond_osc_i`, `cond_osc_ii` the lemma is fully covered.
* ICL `lem:cond-metric`: `cond_metric_fixed` (fixed floor `ε ∈ [0,1)`, no `ε_min`: `|log w_j(τ,ε) − log w_j(τ',ε)| ≤
  diam²‖τ−τ'‖_∞`, and `½ diam²|s − s'|` isotropic), `cond_metric_norm` (the second inequality
  `≤ (diam² + 1/ε_min)‖θ − θ'‖`, Euclidean norm on `ℝ^{d_X+1}`), `cond_metric_ball` (`Θ` in the ball centred at
  `(τ_max/2, ½)` of radius `½(d_Xτ_max² + (1−2ε_min)²)^{1/2} ≤ ½(d_Xτ_max² + 1)^{1/2}`). With the certified
  `cond_metric`, `cond_metric_iso` the lemma is fully covered.
* SB `thm:decay` caveat: `decay_ge_W2` (`W₂(R₀,R₁)² ≤ G_ε²` for the printed plans, every `ε`); `decay_equal_groups`
  (`R₀ = R₁`: for every `ε > 0` under `def:repair`, `G_ε = 0 = W₂(R₀,R₁)`); `decay_eq_refuted` (REFUTATION of "with
  equality only at `ε = 0`": the negated universal fails at `R₀ = R₁ = ν = N(0, I_d)`, every `d`, every `ε > 0`).
* SB `prop:randpenalty`, `t = 1`, both versions: `randpenalty_printed_one` (for the printed plan `π*_ε(R_s, ν)`, `d = 1`,
  under `def:repair`: `E[Var(X₁ | X₀)] > 0`, which is the `t = 1` penalty by the certified `randpenalty_bridge_var`);
  `randpenalty_printed_trace` (every `d ≥ 1`: `E[tr Cov(X₁ | X₀)] > 0`).
* SB journal `lem:quantiles` at the endpoints: `quantiles_zero_printed` (with the printed convention `F^{-1}(0) = −∞`, so
  `Q̃_n(0) − F^{-1}(0) = +∞`), `quantiles_printed_refuted` (REFUTATION of the printed `sup_{u∈[0,1]}` bound, at
  `F = U[0,1]`, `n = 1`), `quantiles_closed` (the corrected form: the bound for every `u ∈ (0,1]` against the printed
  `F^{-1}` — equal there to Tau Ceti's quantile — and at `u = 0` against `a`, the left end of the support,
  `= lim_{u↓0} F^{-1}(u)` (`|F^{-1}(u) − a| ≤ Lu`); `F^{-1}(1) = b`).
* Paper 2 `thm:npmle`, general Feller kernel on a compact `L`: `npmle_gen_duality` (continuous exponents: a maximiser
  `m*` over `𝒫(L)` exists; at every maximiser the sup over `𝒩` (the printed `ν`-form) equals `L(m*)`,
  `v_i = 1/∫ψ_i dm*` is dual feasible with dual value `L(m*)`, and `L(m*)` is the minimum of the dual: `sup = min`, both
  attained); `npmle_gen_strong` (every bounded measurable rule: the printed sup over `𝒩` is the minimum of the dual,
  attained); `npmle_weak` (weak duality for bounded measurable exponents, no topology); `npmle_attain_refuted`
  (REFUTATION of the maximiser clause for the Conventions' bounded measurable rules: `K = L = [−1,1]`, free end);
  `npmle_gen_convex` (every `Φ_y` jointly convex, general kernel, `K` compact); `npmle_gen_correction` (the shift `z'`
  is feasible and certifies `T^𝒩_s(w,λ)`, general kernel, no Feller condition needed); `npmle_gen_programme`
  (linear rules, general Feller kernel: per `λ > 0`, `T^𝒩_s(w,λ) = min{λr − n⁻¹Σz_i : Φ_y ≤ 0 ∀y}`, attained, and the
  `N_s²` identity as an `IsGLB` equivalence).
* Trimmed MMD `lem:trimmedmean`: `trimmedmean_min` (the minimum, `IsLeast`), `trimmedmean_suff` (every `w` in the capped
  simplex with `w_i = c` above `v_(n−k)` and `0` below — ties sharing the rest in any way — is a maximiser),
  `trimmedmean_unique` (distinct values: unique maximiser; in general two maximisers agree off the tie set; `k = n`: the
  capped simplex is a point). With the certified `trimmedmean_value`, `trimmedmean_argmax` the lemma is fully covered.
* Trimmed MMD `prop:witnessstab`: `witnessstab_gen` (the certified bounds with NO measurable-singleton hypothesis:
  `ass:regularity` puts no structure on `𝒳`), `witnessstab_rate` (`D ≤ 2κ` for every minimum-norm `d*` (indeed `≤ 2κ`
  for every element of `𝒞_α(P) − 𝒞_β(Q)`); `η_{n,m} ≤ C(n∧m)^{-1/2}`; and `eq:witnessrate` in the strong form: for each
  `δ` one constant `M` with `‖d̂ − d*‖ ≤ M(n∧m)^{-1/4}` on an event of probability `≥ 1 − δ`, for all `n, m ≥ 1`).

Not covered (declared):
* `thm:decay`: the `ε = 0` side of the caveat and the translated-groups equality instance (not needed for the refutation).
* `thm:npmle`: `L` is a compact METRIC space (paper: compact set), `ε > 0`; the maximiser clause is refuted for
  discontinuous rules (`npmle_attain_refuted`) and proved for continuous ones (`npmle_gen_duality`).
* `prop:randpenalty`: the identification of Mathlib's `condVar` with the variance of a chosen disintegration kernel
  (Bochner `varK` of `Wave18b`) — the penalty is stated as `E[Var(X₁ | X₀)]` directly.

Encodings (to be checked by the critic):
* `cond_metric_fixed`: `v ≥ ‖τ − τ'‖_∞` with `0 ≤ v` stated (it only matters for `d_X = 0`), as in the frozen
  `cond_metric`; `n ≥ 1` is implicit in `j : Fin n`.
* `cond_metric_norm`: `θ = (τ, ε) ∈ ℝ^{d_X} × ℝ`, `‖θ − θ'‖ = (Σ_l (τ_l − τ'_l)² + (ε − ε')²)^{1/2}` (Euclidean norm of
  `ℝ^{d_X+1}`); `cond_metric_ball`: the centre is explicit (stronger than "lies in a ball").
* `thm:decay`: `G_ε²` is the frozen `Gsq` of the printed plans `π_s` (`IsPrintedPlan ε R_s ν π_s`), `W₂` Tau Ceti's;
  `def:repair` is `entCost ε R_s ν < ⊤` with `R_s, ν ∈ 𝒫₂` (as in the certified Wave 30ao `repair_premise`); the
  refutation negates the universal "for all such data, `G_ε² ≠ W₂(R₀,R₁)²`" (squared, both in `ℝ≥0∞`).
* `prop:randpenalty`: `R`, `ν`, `π` on `ℝ^d = EuclideanSpace ℝ (Fin d)` (the paper's scalar case is `d = 1`, coordinate
  `0`); `E[Var(X₁ | X₀)] = ∫ Var[X₁; π | σ(X₀)] dπ` with Mathlib's `condVar` and `σ(X₀) = comap Prod.fst`.
* `lem:quantiles`: `quantE F p = inf{(x : EReal) : p ≤ F(x)}` is the printed `F^{-1}` (`s_setting.tex:30`), with
  `inf ∅ = +∞`, `inf ℝ = −∞`; `|Q̃_n(0) − F^{-1}(0)|` is `+∞` because `(Q̃_n(0) : EReal) − ⊥ = ⊤`. The setting is the frozen
  Wave 30h one (`AssMarg L a b F`, sample in `[a, b]`, `ε` bounding `|F_n − F|`).
* `thm:npmle`: the frozen Wave 29d objects (`MixSettingK`: `n ≥ 1`, `0 < κ(y,K) ≤ 1`, bounded measurable exponents;
  `ψ_i = psiK`, `L(m) = npmleK`, the printed `ν`-form sup `lambdaK` over `𝒫(L)`); the Feller condition "`y ↦ ∫ g dκ_y`
  continuous for continuous `g`"; the dual feasible set `{v > 0 : n⁻¹Σ v_iψ_i(y) ≤ 1 ∀y}`. Linear rules:
  `K ⊆ V` compact (a subtype), anchors `x_i ∈ V`, `φ_i(ξ) = (⟨w, ξ − x_i⟩² − λ‖ξ − x_i‖²)/(λε)` (`phiLin`, the frozen
  `gexp`), `T^𝒩_s(w,λ) = λr + λε Λ` (`TK`, `eq:T` with uniform weights `1/n` and `𝒩 = {m.bind κ : m ∈ 𝒫(L)}`).
* `lem:trimmedmean`: the frozen BangBang encoding; "the smallest such fraction" is `c Σ_{j<k} v_(j+1) + (1 − kc) v_(k+1)`
  (`ord v j = v_(j+1)`), the last term `0` when `k = n`.
* `prop:witnessstab`: the frozen Wave 4b encoding without `[MeasurableSingletonClass 𝒳]`; `(n∧m)^{-1/4}` is the real
  power of `min n m ≥ 1`; `O_P` in the uniform form above (which implies the sequential `O_P` along any `n, m → ∞`).

Junk audit: `condVar` integrals are of the integrable `Var[X₁ⁱ; π | σ(X₀)]` (Mathlib `integrable_condVar`), and a junk
`0` could not satisfy the strict `0 <`; every `Real.log` is of a positive quantity (`∫ψ_i dm > 0`, `v_i > 0`); `lambdaK` is
an `sSup` of a nonempty set bounded above (proved in the routes), so it is the genuine supremum; `F.quantile u` is used
for `u ∈ (0,1]`, where it equals the printed `EReal` infimum (`quantiles_closed`, first conjunct); `quantE` itself is
junk-free (`EReal`); `(min n m)^{−1/4}` with `min n m ≥ 1`; `ord v j` only at indices `< n` (`k < n` guards); `1/n`
with `n ≥ 1` throughout; `√` of nonnegative reals.

Manuscript defects found (OLD/NEW in the wave report): SB long `thm:decay` caveat "with equality only at `ε = 0`"
(`decay_eq_refuted`; the journal wording is already correct); SB journal `lem:quantiles` `sup_{u∈[0,1]}` with the
printed `F^{-1}(0) = −∞` (`quantiles_printed_refuted`); paper 2 `thm:npmle` "attained … for a maximiser `m*`" for
bounded measurable rules (`npmle_attain_refuted`).

DRAFT — not yet in `certify/statements.lock`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal Pointwise

namespace StatFormal.Wave30az

/-! ### Definitions -/

/-- The printed quantile `F^{-1}(p) = inf{x : F(x) ≥ p}` (`s_setting.tex:30`) in `EReal`: `+∞` for the empty set, `−∞`
for a set unbounded below. -/
def quantE (F : Measure ℝ) (p : ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x | p ≤ cdf F x})

section NPMLE

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] {n : ℕ}

open StatFormal.RobustEquality.Paper2.Seminorm (gexp)

/-- The exponents of the linear rule `h_w = ⟪w, ·⟫` at the anchors `x_i`, on `K ⊆ V`:
`φ_i(ξ) = (⟪w, ξ − x_i⟫² − λ‖ξ − x_i‖²)/(λε)`. -/
def phiLin (K : Set V) (ε : ℝ) (x : Fin n → V) (w : V) (l : ℝ) (i : Fin n) (ξ : K) : ℝ :=
  gexp w l ((ξ : V) - x i) / (l * ε)

/-- `Φ_y(z, w, λ) = (λ/n) Σ_i ∫ e^{(z_i + ⟪w, x − x_i⟫² − λ|x − x_i|²)/(λε)} κ(y, dx) − λ` for a general kernel. -/
def PhiK {L : Type*} [MeasurableSpace L] (K : Set V) (ε : ℝ) (κ : ProbabilityTheory.Kernel L K) (x : Fin n → V)
    (z : Fin n → ℝ) (w : V) (l : ℝ) (y : L) : ℝ :=
  l / n * ∑ i, ∫ ξ, Real.exp ((z i + gexp w l ((ξ : V) - x i)) / (l * ε)) ∂(κ y) - l

/-- `T^𝒩_s(w, λ) = λ r + λε sup_{m ∈ 𝒫(L)} n⁻¹ Σ_i log ∫ e^{φ_i} d(m.bind κ)` (`eq:T`, `𝒩 = {∫ κ(y,·) m(dy)}`). -/
def TK {L : Type*} [MeasurableSpace L] (K : Set V) (ε r : ℝ) (κ : ProbabilityTheory.Kernel L K) (x : Fin n → V)
    (w : V) (l : ℝ) : ℝ :=
  l * r + l * ε * StatFormal.Wave29d.lambdaK κ (phiLin K ε x w l) {m | IsProbabilityMeasure m}

end NPMLE

local notation "Eu" d => EuclideanSpace ℝ (Fin d)

namespace Claims

open StatFormal.ICL.Cond (iidLaw wRetr)
open StatFormal.SBFairness.Decay (Gsq)
open StatFormal.Wave30ao (entCost IsPrintedPlan)
open StatFormal.Wave30h (AssMarg empCdf interpQuant ordStat)
open StatFormal.Wave29d (psiK npmleK lambdaK MixSettingK phiRule)
open StatFormal.TrimmedMMD.BangBang (ord cap kfloor capped qp)

/-! ### ICL `lem:cond-osc` (ii), the i.i.d. risk -/

/-- `lem:cond-osc` (ii), last sentence for the i.i.d. contexts: for positive `w, w' ∈ Δ^{n−1}`, `n ≥ M ≥ 1`,
`Δ ≥ max_j |log w_j − log w'_j|` and any loss table `L` on `M`-tuples with values in `[0, B_L]` (the loss at a fixed
query `z`), `|G^iid(z;w) − G^iid(z;w')| ≤ B_L tanh(MΔ/2) ≤ B_L MΔ/2`. -/
def cond_osc_iid : Prop :=
  ∀ (n M : ℕ) (w w' : Fin n → ℝ) (Δ BL : ℝ) (L : (Fin M → Fin n) → ℝ), 1 ≤ M → M ≤ n →
    (∀ j, 0 < w j) → (∀ j, 0 < w' j) → ∑ j, w j = 1 → ∑ j, w' j = 1 →
    (∀ j, |Real.log (w j) - Real.log (w' j)| ≤ Δ) → (∀ J, 0 ≤ L J ∧ L J ≤ BL) →
      |StatFormal.Wave12c.Giid w M L - StatFormal.Wave12c.Giid w' M L| ≤ BL * Real.tanh (M * Δ / 2) ∧
      BL * Real.tanh (M * Δ / 2) ≤ BL * M * Δ / 2

/-! ### ICL `lem:cond-metric`: fixed floor, the norm form, the ball -/

/-- `lem:cond-metric`, "For a fixed floor `ε ∈ [0,1)`, the second term is absent": with no `ε_min`,
`|log w_j(x;τ,ε) − log w_j(x;τ',ε)| ≤ diam² v` for `v ≥ ‖τ − τ'‖_∞`, and for an isotropic metric
`≤ ½ diam² |s − s'|`. -/
def cond_metric_fixed : Prop :=
  ∀ (n d : ℕ) (xs : Fin n → Fin d → ℝ) (x : Fin d → ℝ) (diam v ε : ℝ) (τ τ' : Fin d → ℝ) (s s' : ℝ) (j : Fin n),
    (∀ k, ∑ l, (x l - xs k l) ^ 2 ≤ diam ^ 2) → (∀ l, |τ l - τ' l| ≤ v) → 0 ≤ v → 0 ≤ ε → ε < 1 →
      |Real.log (wRetr xs x τ ε j) - Real.log (wRetr xs x τ' ε j)| ≤ diam ^ 2 * v ∧
      |Real.log (wRetr xs x (fun _ => s) ε j) - Real.log (wRetr xs x (fun _ => s') ε j)| ≤
        (1 / 2) * diam ^ 2 * |s - s'|

/-- `lem:cond-metric`, the second inequality: `|log w_j(x;θ) − log w_j(x;θ')| ≤ (diam² + 1/ε_min)‖θ − θ'‖` with
`‖θ − θ'‖` the Euclidean norm of `θ − θ' = (τ − τ', ε − ε') ∈ ℝ^{d_X+1}`, for `θ, θ' ∈ Θ`. -/
def cond_metric_norm : Prop :=
  ∀ (n d : ℕ) (xs : Fin n → Fin d → ℝ) (x : Fin d → ℝ) (diam εmin : ℝ) (τ τ' : Fin d → ℝ) (ε ε' : ℝ) (j : Fin n),
    0 < εmin → εmin < 1 / 2 → (∀ k, ∑ l, (x l - xs k l) ^ 2 ≤ diam ^ 2) → (∀ l, 0 ≤ τ l) → (∀ l, 0 ≤ τ' l) →
    εmin ≤ ε → ε ≤ 1 - εmin → εmin ≤ ε' → ε' ≤ 1 - εmin →
      |Real.log (wRetr xs x τ ε j) - Real.log (wRetr xs x τ' ε' j)| ≤
        (diam ^ 2 + 1 / εmin) * Real.sqrt (∑ l, (τ l - τ' l) ^ 2 + (ε - ε') ^ 2)

/-- `lem:cond-metric`, "`Θ` lies in a Euclidean ball of radius `½(d_Xτ_max² + 1)^{1/2}`": every
`θ = (τ, ε) ∈ [0, τ_max]^{d_X} × [ε_min, 1 − ε_min]` is within `½(d_Xτ_max² + (1 − 2ε_min)²)^{1/2}` of the midpoint
`(τ_max/2, …, τ_max/2, ½)`, and that radius is at most `½(d_Xτ_max² + 1)^{1/2}`. -/
def cond_metric_ball : Prop :=
  ∀ (d : ℕ) (τmax εmin : ℝ) (τ : Fin d → ℝ) (ε : ℝ), 0 ≤ τmax → 0 < εmin → εmin < 1 / 2 →
    (∀ l, 0 ≤ τ l ∧ τ l ≤ τmax) → εmin ≤ ε → ε ≤ 1 - εmin →
      Real.sqrt (∑ l, (τ l - τmax / 2) ^ 2 + (ε - 1 / 2) ^ 2) ≤
          (1 / 2) * Real.sqrt (d * τmax ^ 2 + (1 - 2 * εmin) ^ 2) ∧
        (1 / 2) * Real.sqrt (d * τmax ^ 2 + (1 - 2 * εmin) ^ 2) ≤ (1 / 2) * Real.sqrt (d * τmax ^ 2 + 1)

/-! ### SB `thm:decay`: `G_ε ≥ W₂(R₀,R₁)`, and the refutation of "with equality only at `ε = 0`" -/

/-- The sentence after `def:glued`, "always `G_ε ≥ W₂(R₀, R₁)`": for the printed plans `π_s = π*_ε(R_s, ν)` (any `ε`),
`W₂(R₀, R₁)² ≤ G_ε²`. -/
def decay_ge_W2 : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (R₀ R₁ ν : Measure (Eu d)) (π₀ π₁ : Measure ((Eu d) × (Eu d))),
    IsProbabilityMeasure R₀ → IsProbabilityMeasure R₁ →
    IsPrintedPlan ε R₀ ν π₀ → IsPrintedPlan ε R₁ ν π₁ →
      wassersteinEDist 2 R₀ R₁ ^ 2 ≤ Gsq π₀ π₁

/-- Equal groups: for `R₀ = R₁ = R` under `def:repair` (`R, ν ∈ 𝒫₂`, `C_ε(R, ν) < ∞`) and every `ε > 0`, the printed
plans coincide and `G_ε² = 0 = W₂(R₀, R₁)²`: equality at a positive `ε`. -/
def decay_equal_groups : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (R ν : Measure (Eu d)) (π₀ π₁ : Measure ((Eu d) × (Eu d))), 0 < ε →
    IsProbabilityMeasure R → IsProbabilityMeasure ν →
    Integrable (fun x : Eu d => ‖x‖ ^ 2) R → Integrable (fun y : Eu d => ‖y‖ ^ 2) ν → entCost ε R ν < ⊤ →
    IsPrintedPlan ε R ν π₀ → IsPrintedPlan ε R ν π₁ →
      π₀ = π₁ ∧ Gsq π₀ π₁ = 0 ∧ wassersteinEDist 2 R R = 0 ∧ Gsq π₀ π₁ = wassersteinEDist 2 R R ^ 2

/-- REFUTATION of `thm:decay`'s caveat "`G_ε ≥ W₂(R₀,R₁)` with equality only at `ε = 0`" (long `:2311`): it is NOT
the case that for every `ε > 0` and all data satisfying `def:repair` the printed plans give `G_ε² ≠ W₂(R₀,R₁)²`.
(Witness used: `R₀ = R₁ = ν = N(0, I_1)`, `ε = 1`; by `decay_equal_groups` any `R₀ = R₁` under `def:repair`, any
`ε > 0`, is a witness.) -/
def decay_eq_refuted : Prop :=
  ¬ ∀ (d : ℕ) (ε : ℝ) (R₀ R₁ ν : Measure (Eu d)) (π₀ π₁ : Measure ((Eu d) × (Eu d))), 0 < ε →
      IsProbabilityMeasure R₀ → IsProbabilityMeasure R₁ → IsProbabilityMeasure ν →
      Integrable (fun x : Eu d => ‖x‖ ^ 2) R₀ → Integrable (fun x : Eu d => ‖x‖ ^ 2) R₁ →
      Integrable (fun y : Eu d => ‖y‖ ^ 2) ν → entCost ε R₀ ν < ⊤ → entCost ε R₁ ν < ⊤ →
      IsPrintedPlan ε R₀ ν π₀ → IsPrintedPlan ε R₁ ν π₁ →
        Gsq π₀ π₁ ≠ wassersteinEDist 2 R₀ R₁ ^ 2

/-! ### SB `prop:randpenalty` at `t = 1`, for the printed entropic plan -/

/-- `prop:randpenalty`, "strictly positive for `t ∈ (0,1]` when `ε > 0`", the case `t = 1` for the paper's kernel: in
the scalar case (`d = 1`), for `ε > 0`, `R, ν ∈ 𝒫₂` with `C_ε(R, ν) < ∞` (`def:repair`) and the printed plan
`π = π*_ε(R, ν)`, the mean conditional variance `E[Var(X₁ | X₀)] = ∫ Var[X₁; π | σ(X₀)] dπ` is strictly positive. (At
`t = 1` the bridge kernel's variance is `Var(X₁ | X₀ = u)`, certified `randpenalty_bridge_var`.) -/
def randpenalty_printed_one : Prop :=
  ∀ (ε : ℝ) (R ν : Measure (Eu 1)) (π : Measure ((Eu 1) × (Eu 1))), 0 < ε →
    IsProbabilityMeasure R → IsProbabilityMeasure ν →
    Integrable (fun x : Eu 1 => ‖x‖ ^ 2) R → Integrable (fun y : Eu 1 => ‖y‖ ^ 2) ν → entCost ε R ν < ⊤ →
    IsPrintedPlan ε R ν π →
      0 < ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
        (fun p : (Eu 1) × (Eu 1) => p.2 0) π p ∂π

/-- The same in every dimension `d ≥ 1` for the trace: `E[tr Cov(X₁ | X₀)] = Σ_i ∫ Var[X₁ⁱ; π | σ(X₀)] dπ > 0`. -/
def randpenalty_printed_trace : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (R ν : Measure (Eu d)) (π : Measure ((Eu d) × (Eu d))), 0 < d → 0 < ε →
    IsProbabilityMeasure R → IsProbabilityMeasure ν →
    Integrable (fun x : Eu d => ‖x‖ ^ 2) R → Integrable (fun y : Eu d => ‖y‖ ^ 2) ν → entCost ε R ν < ⊤ →
    IsPrintedPlan ε R ν π →
      0 < ∑ i : Fin d, ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
        (fun p : (Eu d) × (Eu d) => p.2 i) π p ∂π

/-! ### SB journal `lem:quantiles` at the endpoints of `[0,1]` -/

/-- With the printed convention `F^{-1}(p) = inf{x : F(x) ≥ p}` (`s_setting.tex:30`), `F^{-1}(0) = −∞` for every
probability measure, so `Q̃_n(0) − F^{-1}(0) = +∞` for every sample. -/
def quantiles_zero_printed : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) (x : Fin n → ℝ),
    quantE F 0 = ⊥ ∧ ((interpQuant x 0 : ℝ) : EReal) - quantE F 0 = ⊤

/-- REFUTATION of the printed `sup_{u∈[0,1]} |Q̃_n(u) − F^{-1}(u)| ≤ L(ε_n + 2/n)` under `ass:marg` with the printed
`F^{-1}` (`EReal`-valued, so the absolute difference is bounded by a real number iff both one-sided differences are). -/
def quantiles_printed_refuted : Prop :=
  ¬ ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (L : ℝ≥0) (a b : ℝ) (n : ℕ) (x : Fin n → ℝ) (ε : ℝ),
      AssMarg L a b F → 1 ≤ n → (∀ i, x i ∈ Icc a b) → (∀ t, |empCdf x t - cdf F t| ≤ ε) →
        ∀ u ∈ Icc (0 : ℝ) 1, ((interpQuant x u : ℝ) : EReal) - quantE F u ≤ ((L * (ε + 2 / n) : ℝ) : EReal) ∧
          quantE F u - ((interpQuant x u : ℝ) : EReal) ≤ ((L * (ε + 2 / n) : ℝ) : EReal)

/-- `lem:quantiles`, corrected endpoint form, under `ass:marg` with the sample in `[a, b]` and `ε ≥ sup|F_n − F|`:
on `(0,1]` the printed `F^{-1}` is real and equals Tau Ceti's quantile, `F^{-1}(1) = b`, and
`|Q̃_n(u) − F^{-1}(u)| ≤ L(ε + 2/n)` for every `u ∈ (0,1]`; at `u = 0`, with `F^{-1}(0) := a`
(the left end of the support, `= lim_{u↓0} F^{-1}(u)` since `|F^{-1}(u) − a| ≤ Lu`), `|Q̃_n(0) − a| ≤ L(ε + 2/n)`. -/
def quantiles_closed : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (L : ℝ≥0) (a b : ℝ) (n : ℕ) (x : Fin n → ℝ) (ε : ℝ),
    AssMarg L a b F → 1 ≤ n → (∀ i, x i ∈ Icc a b) → (∀ t, |empCdf x t - cdf F t| ≤ ε) →
      (∀ u ∈ Ioc (0 : ℝ) 1, quantE F u = ((F.quantile u : ℝ) : EReal)) ∧ F.quantile 1 = b ∧
      (∀ u ∈ Ioc (0 : ℝ) 1, |interpQuant x u - F.quantile u| ≤ L * (ε + 2 / n)) ∧
      (∀ u ∈ Ioo (0 : ℝ) 1, |F.quantile u - a| ≤ L * u) ∧
      |interpQuant x 0 - a| ≤ L * (ε + 2 / n)

/-! ### Paper 2 `thm:npmle`, general Feller kernel -/

/-- `thm:npmle`, duality, for a Feller kernel `κ` from a compact metric `L` to a compact `K` with `0 < κ(y,K) ≤ 1` and
continuous exponents (e.g. a continuous rule `h`): a maximiser `m*` of `L(m) = n⁻¹Σ log ∫ψ_i dm` over `𝒫(L)` exists, and
at every maximiser the printed supremum over `𝒩` equals `L(m*)`, `v_i = 1/∫ψ_i dm*` is dual feasible with dual value
`L(m*)`, and `L(m*)` is the minimum of the dual problem. -/
def npmle_gen_duality : Prop :=
  ∀ (K L : Type) [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [MetricSpace L] [CompactSpace L] [MeasurableSpace L] [BorelSpace L] [Nonempty L]
    (n : ℕ) (κ : ProbabilityTheory.Kernel L K) (φ : Fin n → K → ℝ),
    MixSettingK κ φ → (∀ i, Continuous (φ i)) →
    (∀ g : K → ℝ, Continuous g → Continuous fun y => ∫ x, g x ∂(κ y)) →
      (∃ ms : Measure L, IsProbabilityMeasure ms ∧
          ∀ m : Measure L, IsProbabilityMeasure m → npmleK κ φ m ≤ npmleK κ φ ms) ∧
      ∀ ms : Measure L, IsProbabilityMeasure ms →
        (∀ m : Measure L, IsProbabilityMeasure m → npmleK κ φ m ≤ npmleK κ φ ms) →
          lambdaK κ φ {m | IsProbabilityMeasure m} = npmleK κ φ ms ∧
          (∀ y, (1 / n : ℝ) * ∑ i, (1 / ∫ y', psiK κ φ i y' ∂ms) * psiK κ φ i y ≤ 1) ∧
          -((1 / n : ℝ) * ∑ i, Real.log (1 / ∫ y', psiK κ φ i y' ∂ms)) = npmleK κ φ ms ∧
          IsLeast {D | ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
              (∀ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ≤ 1) ∧ D = -((1 / n : ℝ) * ∑ i, Real.log (v i))}
            (npmleK κ φ ms)

/-- `thm:npmle`, `sup = min` for every bounded MEASURABLE rule (no continuity of the exponents): for a Feller kernel
from a compact metric `L` with `0 < κ(y,K) ≤ 1`, the printed supremum over `𝒩` is the minimum of the dual problem, and
the minimum is attained (the primal supremum need not be, `npmle_attain_refuted`). -/
def npmle_gen_strong : Prop :=
  ∀ (K L : Type) [TopologicalSpace K] [MeasurableSpace K]
    [MetricSpace L] [CompactSpace L] [MeasurableSpace L] [BorelSpace L] [Nonempty L]
    (n : ℕ) (κ : ProbabilityTheory.Kernel L K) (φ : Fin n → K → ℝ),
    MixSettingK κ φ → (∀ g : K → ℝ, Continuous g → Continuous fun y => ∫ x, g x ∂(κ y)) →
      IsLeast {D | ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
          (∀ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ≤ 1) ∧ D = -((1 / n : ℝ) * ∑ i, Real.log (v i))}
        (lambdaK κ φ {m | IsProbabilityMeasure m})

/-- `thm:npmle`, weak duality (bounded measurable exponents, any measurable spaces): for every probability `m` and every
dual feasible `v`, `L(m) ≤ −n⁻¹ Σ log v_i`. -/
def npmle_weak : Prop :=
  ∀ (K L : Type) [MeasurableSpace K] [MeasurableSpace L] (n : ℕ) (κ : ProbabilityTheory.Kernel L K)
    (φ : Fin n → K → ℝ) (m : Measure L) (v : Fin n → ℝ),
    MixSettingK κ φ → IsProbabilityMeasure m → (∀ i, 0 < v i) →
    (∀ y, (1 / n : ℝ) * ∑ i, v i * psiK κ φ i y ≤ 1) →
      npmleK κ φ m ≤ -((1 / n : ℝ) * ∑ i, Real.log (v i))

/-- REFUTATION of the maximiser clause of `thm:npmle` ("attained at `v_i = 1/∫ψ_i dm*` for a maximiser `m*`") for the
Conventions' rules (bounded measurable `h`): at the free end on `K = L = [−1, 1]` (`κ = δ`, compact, Feller) with one
anchor `x₀ = 0`, not every bounded measurable `h` (and `λ, ε > 0`) has a maximiser of `L` over `𝒫(L)`. -/
def npmle_attain_refuted : Prop :=
  ¬ ∀ (h : Icc (-1 : ℝ) 1 → ℝ) (lam ε : ℝ), Measurable h → (∃ H, ∀ x, |h x| ≤ H) → 0 < lam → 0 < ε →
      ∃ ms : Measure (Icc (-1 : ℝ) 1), IsProbabilityMeasure ms ∧
        ∀ m : Measure (Icc (-1 : ℝ) 1), IsProbabilityMeasure m →
          npmleK ProbabilityTheory.Kernel.id (phiRule h lam ε fun _ : Fin 1 => ⟨0, by norm_num⟩) m ≤
            npmleK ProbabilityTheory.Kernel.id (phiRule h lam ε fun _ : Fin 1 => ⟨0, by norm_num⟩) ms

/-- `thm:npmle`, "every `Φ_y` is jointly convex in `(z, w, λ)`" for a general kernel `κ(y, ·)` on a compact `K ⊆ V`
(finite measures `κ(y, K) ≤ 1`), on `ℝⁿ × V × (0, ∞)`. -/
def npmle_gen_convex : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Type) [MeasurableSpace L] (K : Set V) (n : ℕ) (ε : ℝ) (κ : ProbabilityTheory.Kernel L K) (x : Fin n → V)
    (y : L), IsCompact K → 0 < n → 0 < ε → κ y univ ≤ 1 →
      ConvexOn ℝ (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi 0))
        (fun q : (Fin n → ℝ) × V × ℝ => PhiK K ε κ x q.1 q.2.1 q.2.2 y)

/-- `thm:npmle`, the certified correction for a general kernel: if `V₀ ≥ sup_y {Φ_y(z,w,λ)/λ + 1}` is certified, then
`z' = z − λε log max(1, V₀)` is feasible and `T^𝒩_s(w, λ) ≤ λ r − n⁻¹ Σ z'_i`. (`K ⊆ V` compact, `L` any nonempty
measurable space, `0 < κ(y,K) ≤ 1`.) -/
def npmle_gen_correction : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Type) [MeasurableSpace L] [Nonempty L] (K : Set V) (n : ℕ) (ε r l V₀ : ℝ)
    (κ : ProbabilityTheory.Kernel L K) (x : Fin n → V) (z : Fin n → ℝ) (w : V),
    IsCompact K → 0 < n → 0 < ε → 0 < l → (∀ y, 0 < κ y univ ∧ κ y univ ≤ 1) →
    (∀ y, PhiK K ε κ x z w l y / l + 1 ≤ V₀) →
      (∀ y, PhiK K ε κ x (fun i => z i - l * ε * Real.log (max 1 V₀)) w l y ≤ 0) ∧
      TK K ε r κ x w l ≤ l * r - (1 / (n : ℝ)) * ∑ i, (z i - l * ε * Real.log (max 1 V₀))

/-- `thm:npmle`, the convex semi-infinite programme for a linear rule and a general Feller kernel (`L` compact metric,
`K ⊆ V` compact, `0 < κ(y,K) ≤ 1`): for each `λ > 0`, `T^𝒩_s(w, λ)` is the minimum of `λ r − n⁻¹ Σ z_i` over
`{z : Φ_y(z, w, λ) ≤ 0 ∀ y ∈ L}` (attained); hence `N_s(w)² = inf_{λ>0} T^𝒩_s(w,λ)` equals
`inf{λ r − n⁻¹Σ z_i : λ > 0, Φ_y ≤ 0 ∀ y}` (as an `IsGLB` equivalence). -/
def npmle_gen_programme : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Type) [MetricSpace L] [CompactSpace L] [MeasurableSpace L] [BorelSpace L] [Nonempty L]
    (K : Set V) (n : ℕ) (ε r : ℝ) (κ : ProbabilityTheory.Kernel L K) (x : Fin n → V) (w : V),
    IsCompact K → 0 < n → 0 < ε → (∀ y, 0 < κ y univ ∧ κ y univ ≤ 1) →
    (∀ g : K → ℝ, Continuous g → Continuous fun y => ∫ ξ, g ξ ∂(κ y)) →
      (∀ l : ℝ, 0 < l →
        IsLeast {v | ∃ z : Fin n → ℝ, (∀ y, PhiK K ε κ x z w l y ≤ 0) ∧ v = l * r - (1 / (n : ℝ)) * ∑ i, z i}
          (TK K ε r κ x w l)) ∧
      ∀ N2 : ℝ,
        IsGLB {t | ∃ l : ℝ, 0 < l ∧ t = TK K ε r κ x w l} N2 ↔
          IsGLB {v | ∃ (l : ℝ) (z : Fin n → ℝ), 0 < l ∧ (∀ y, PhiK K ε κ x z w l y ≤ 0) ∧
            v = l * r - (1 / (n : ℝ)) * ∑ i, z i} N2

/-! ### Trimmed MMD `lem:trimmedmean` -/

/-- `lem:trimmedmean`, "the minimum is the same expression applied to the smallest such fraction":
`min_{w ∈ Δ_α(n)} Σ w_i v_i = c Σ_{i ≤ k} v_(i) + (1 − kc) v_(k+1)` (last term `0` when `k = n`). -/
def trimmedmean_min : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ), 0 < n → 0 ≤ α → α < 1 →
    IsLeast ((fun w => ∑ i, w i * v i) '' capped n α)
      (cap n α * ∑ j ∈ Finset.range (kfloor n α), ord v j +
        (if kfloor n α < n then (1 - kfloor n α * cap n α) * ord v (kfloor n α) else 0))

/-- `lem:trimmedmean`, sufficiency of the maximiser clause: every `w` of the capped simplex with `w_i = c` when
`v_i > v_(n−k)` and `w_i = 0` when `v_i < v_(n−k)` (the tied indices sharing the remaining mass in any way the caps
allow) is a maximiser. -/
def trimmedmean_suff : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ) (w : Fin n → ℝ), 0 < n → 0 ≤ α → α < 1 → kfloor n α < n →
    w ∈ capped n α →
    (∀ i, ord v (n - kfloor n α - 1) < v i → w i = cap n α) →
    (∀ i, v i < ord v (n - kfloor n α - 1) → w i = 0) →
      IsMaxOn (fun w => ∑ i, w i * v i) (capped n α) w

/-- `lem:trimmedmean`, uniqueness: with distinct values the maximiser is unique; in general (`k < n`) two maximisers
agree at every index whose value differs from `v_(n−k)` (unique up to the redistribution among the tied indices); for
`k = n` the capped simplex is the single point `w ≡ 1/n`. -/
def trimmedmean_unique : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (α : ℝ) (w w' : Fin n → ℝ), 0 < n → 0 ≤ α → α < 1 →
    w ∈ capped n α → w' ∈ capped n α →
    IsMaxOn (fun w => ∑ i, w i * v i) (capped n α) w → IsMaxOn (fun w => ∑ i, w i * v i) (capped n α) w' →
      (Function.Injective v → w = w') ∧
      (kfloor n α < n → ∀ i, v i ≠ ord v (n - kfloor n α - 1) → w i = w' i) ∧
      (kfloor n α = n → w = fun _ => 1 / (n : ℝ))

/-! ### Trimmed MMD `prop:witnessstab`: no structure on `𝒳`, and the rate -/

open StatFormal.TrimmedMMD.Concentration (region) in
open StatFormal.TrimmedMMD.Projection (IsMinNorm) in
open StatFormal.Wave4b (witness etaNM) in
/-- `prop:witnessstab` under `ass:regularity` as printed (a measurable space `𝒳` with NO further structure, in
particular no measurable singletons): on one measurable event of probability `≥ 1 − δ`, every empirical witness
satisfies `|D̂ − D| ≤ η`, `‖d̂ − d*‖ ≤ η + √(2η min(D,D̂) + η²) ≤ √(2ηD) + 2η`, and `sup_x |d̂(x) − d*(x)| ≤ κ‖d̂ − d*‖`. -/
def witnessstab_gen : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α β δ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → 1 ≤ n → 1 ≤ m →
    0 < δ → δ < 1 →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (p : (Fin n → ℝ) × (Fin m → ℝ)) (dstar : H),
          p ∈ capped n α ×ˢ capped m β →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m β) p →
          IsMinNorm (region φ α P - region φ β Q) dstar →
            |‖witness φ z.1 z.2 p‖ - ‖dstar‖| ≤ etaNM κ α β δ n m ∧
            ‖witness φ z.1 z.2 p - dstar‖ ≤ etaNM κ α β δ n m +
              √(2 * etaNM κ α β δ n m * min ‖dstar‖ ‖witness φ z.1 z.2 p‖ +
                etaNM κ α β δ n m ^ 2) ∧
            etaNM κ α β δ n m + √(2 * etaNM κ α β δ n m * min ‖dstar‖ ‖witness φ z.1 z.2 p‖ +
                etaNM κ α β δ n m ^ 2) ≤
              √(2 * etaNM κ α β δ n m * ‖dstar‖) + 2 * etaNM κ α β δ n m ∧
            ∀ x, |inner ℝ (witness φ z.1 z.2 p) (φ x) - inner ℝ dstar (φ x)| ≤
              κ * ‖witness φ z.1 z.2 p - dstar‖}

open StatFormal.TrimmedMMD.Concentration (region) in
open StatFormal.TrimmedMMD.Projection (IsMinNorm) in
open StatFormal.Wave4b (witness etaNM) in
/-- `prop:witnessstab`, "Since `η_{n,m} = O((n∧m)^{-1/2})` and `D ≤ 2κ`, `‖d̂ − d*‖ = O_P((n∧m)^{-1/4})`": every element of
`𝒞_α(P) − 𝒞_β(Q)` (so `D = ‖d*‖`) has norm `≤ 2κ`; for every `δ ∈ (0,1)` there is `C` with `η_{n,m} ≤ C(n∧m)^{-1/2}`
for all `n, m ≥ 1`; and there is one `M` such that for all `n, m ≥ 1`, on a measurable event of probability
`≥ 1 − δ`, every empirical witness is within `M (n∧m)^{-1/4}` of every minimum-norm `d*`. -/
def witnessstab_rate : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α β : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
      (∀ d ∈ region φ α P - region φ β Q, ‖d‖ ≤ 2 * κ) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (∃ C : ℝ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
          etaNM κ α β δ n m ≤ C * ((min n m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ∃ M : ℝ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
          ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ) ≤
              ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
            E ⊆ {z | ∀ (p : (Fin n → ℝ) × (Fin m → ℝ)) (dstar : H),
              p ∈ capped n α ×ˢ capped m β →
              IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m β) p →
              IsMinNorm (region φ α P - region φ β Q) dstar →
                ‖witness φ z.1 z.2 p - dstar‖ ≤ M * ((min n m : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))}

end Claims

end StatFormal.Wave30az
