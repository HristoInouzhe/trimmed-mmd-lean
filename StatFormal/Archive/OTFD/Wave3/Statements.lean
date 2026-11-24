import StatFormal.Archive.OTFD.Conformal.Statements
import StatFormal.Archive.OTFD.CalDepth.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Wave2.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.EReal.Basic

/-!
# FROZEN STATEMENTS — otfd wave 3 (conformal layer): B `lem:exch-quantile`, B `prop:cal-coverage`,
# B `cor:vector-tube-conformal`, C `prop:cond-cal-coverage`, T `prop:conformaldepth`, T `prop:conformal`;
# R `lem:spike`, R `prop:width-contam`, B `prop:ext-K-selection`, B `prop:rk-scenario-set`,
# C `prop:cond-scenario-set`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`,
`otfd-T_tangent.md`, `otfd-R_robustness.md`; paths below are under `otfd/papers/`):
* B `lem:exch-quantile` (`B_bands/supplement.tex:5784-5791`).
* B `prop:cal-coverage` (`B_bands/main.tex:912-925`), with `def:cal-score` (`main.tex:881-905`: `c`, `w`, the score
  `V(x) = sup_t |x(t) − c(t)|/w(t)`, the band `B̂^ω = [c − ωw, c + ωw]`, `ω̂_α` the `⌈(n₂+1)(1−α)⌉`-th order
  statistic, `+∞` past `n₂`).
* B `cor:vector-tube-conformal` (`B_bands/supplement.tex:2961-3000`), with the directional tube
  `eq:vector-directional-tube` (`supplement.tex:2800-2806`) and the componentwise band
  `eq:vector-componentwise-band` (`:2810-2814`); proof `:3002-3025`.
* C `prop:cond-cal-coverage` (`C_conditional/main.tex:820-826`), with `def:cond-cal-score` (`main.tex:796-810`).
* T `prop:conformaldepth` (unlabelled, `T_tangent/sec_tangent_theory.tex:217-229`).
* T `prop:conformal` (`T_tangent/sec_tangent_theory.tex:603-613`, label `eq:conformal`), with the score `eq:score`
  (`:592-595`) and the calibrated tube `eq:conftube` (`:598-601`).
* R `lem:spike` (`R_robustness/sections/s6_references.tex:104-109`), with `TD`, `β` of `eq:TDH`.
* R `prop:width-contam` (`R_robustness/sections/s85_tuning.tex:73-78`), relative to B `prop:width` (`main.tex:943`).
* B `prop:ext-K-selection` (`B_bands/supplement.tex:5923-5963`).
* B `prop:rk-scenario-set` (`B_bands/supplement.tex:5377-5390`), with `def:rk-scenario-score` (`:5356-5375`),
  `def:cal-depth` (`main.tex:1001`) and `def:depth-family` (`main.tex:502`, `c_K^{-1}`).
* C `prop:cond-scenario-set` (`C_conditional/supplement.tex:2189-2203`), with `def:cond-scenario-score`
  (`supplement.tex:2176-2187`).
Reuses the frozen `OTFD/Conformal/Statements.lean` (`Exch`), `OTFD/CalDepth/Statements.lean` (`calDepth`),
`OTFD/Wave1/Statements.lean` (`tukeyDepth`, `regionDepth`), `OTFD/Wave2/Statements.lean` (`mnorm`) and, through it,
`OTFD/Bands2/Statements.lean` (`curve`), imported, not copied.

Abstraction (as in the frozen `OTFD/Conformal` and `OTFD/CalDepth` files): every fitted object (`c`, `w`, `c_v`, `w_v`,
`H_p`, `c_M`, `R`, the depth `D̂`) is computed on the training/fitting fold and is a **fixed** function conditionally
on it. The claims are stated for that conditional law: the data are arbitrary maps `X : Ω → Fin (n+1) → 𝒳`
(index `0` the new curve/pair, `i.succ` the calibration ones) and the hypotheses are that the score vector
`ω ↦ (score(X ω i))_i` is measurable and **exchangeable** (law invariant under every permutation of `Fin (n+1)`) —
which is what "the calibration curves and the new curve are exchangeable conditionally on `𝓘₁`" together with "the
scores are random variables" gives. Unconditioning (the tower property) is not formalised.

Covered:
* B `lem:exch-quantile`: `exch_quantile_lower`, `exch_quantile_upper` (`[0,∞]`-valued scores, `k ≤ N` as in the
  paper).
* B `prop:cal-coverage`: `band_mem_iff` (`x ∈ B̂^ω ⇔ V(x) ≤ ω`, every `ω ∈ [0,∞]`, simultaneous in `t`);
  `cal_coverage_lower`, `cal_coverage_upper` (the band is for the original curve; `ω̂ = +∞` past `n₂` included).
* B `cor:vector-tube-conformal`: `vec_tube_mem_iff`; `vec_tube_coverage_lower`, `vec_tube_coverage_upper`;
  `vec_componentwise` (a); `vec_directional` (b: the two thresholds `±c_v + ω w_v`, and `T̂¹ = B_{p,𝒱∪(−𝒱)}`);
  `vec_floor_mono` (a floor `w_v ∨ w_min` only enlarges every `T̂^ω`, hence `T̂¹ ⊇ B_{p,𝒱∪(−𝒱)}`).
* C `prop:cond-cal-coverage`: `cond_cal_coverage_lower`, `cond_cal_coverage_upper` (each score at its own covariate;
  the probability averages over the covariate).
* T `prop:conformaldepth`: `depth_region_lower` (`p ≤ P`), `depth_region_upper` (`≤ p + 1/(n_c+1)` under a.s.
  distinct depths), `depth_region_nested` (`Ĉ_p ⊆ Ĉ_{p'}` for `p ≤ p'`).
* T `prop:conformal`: `tube_mem_iff` (score event = tube membership for all `t`), `tube_coverage` (`eq:conformal`),
  `tube_coverage_upper_score` (the measurable upper score `S⁺ ≥ S`).
* R `lem:spike`: `spike_bound` (`TD(r e_k) ≥ ½ P(X_k ≥ r)`, every `k`, `r ≥ 0`), `spike_crosspolytope`
  (`β(CP(r)) ≥ α/2`).
* R `prop:width-contam`: `width_contam_sandwich` (ranks `k ∓ ℓ`), `width_contam_bounded` (`k + ℓ ≤ n₂`),
  `width_contam_coverage` (coverage drop `≤ ℓ/(n₂+1)`, see encodings).
* B `prop:ext-K-selection`: `extK_union` ((i), and every `K̂`), `extK_finite_iff` (both finiteness criteria),
  `extK_single_lower`, `extK_single_upper` ((ii)), `extK_depth` ((iii), both forms).
* B `prop:rk-scenario-set`: `rk_scenario_set`. C `prop:cond-scenario-set`: `cond_scenario_set` (both containments and
  `eq:cond-functionals`, both directions, simultaneously for every Lipschitz `ℓ`).

Not covered (declared):
* Unconditioning ("and hence also unconditionally"); the "no multiplicity correction is needed" sentence (it is the
  fact that the claims bound a single simultaneous event); the remark on `w̃` modulations beyond `vec_floor_mono`
  (any `w̃ ≥ 0` is an instance of the claims, which take arbitrary `w ≥ 0`).
* B (vector): the identities `w_v ≥ 0` from `prop:vector-directional-reduction`, the substitution of `H̄_p`, `H̲_p`
  (the claims hold for every threshold function `H`, so they cover them), "`d = 1`, `𝒱 = {1}` is `prop:cal-coverage`"
  (a remark), the measurability remark (entered as a hypothesis), continuity of the curves `C(𝒯; ℝ^d)` (unused).
* T `prop:conformaldepth`: "for every temperature, sieve dimension and reference" (the claims are for every fitted
  `D̂`); "each is a set of whole curves ordered by the transport depth" (informal).
* R `prop:width-contam`: the DKW/selection bound of `prop:width`(i) itself (the drop is shown for the exchangeable
  coverage `1 − α` of a fixed, recalibrated candidate); "for contamination fractions below about `α`" (informal).
* B `prop:ext-K-selection`: the closing sentences ("the same holds verbatim for any finite menu", "without a correction,
  selecting on `𝓘₂` voids…"): the menu `ι` is any finite type, so the first is an instance; the second is not a claim.
* Scenario sets: the computation of `F̂`, `Q̂`, `Ĝ_e`, `Ĝ` and the fact that `c_K` is the CDF of `ρ` under `μ_K`
  (the claims hold for any functions with the stated properties); C "for linear `ℓ` the supremum is certified by the
  caps" (that is `prop:conditional-certificate`).
* T `prop:conformal`: the measurability of tube membership over uncountable `t` (entered through the measurability
  of the score vector); the sentences after the proposition (grid correction, `rem:tubeshape`).

Encodings (see card):
* Scores in `[0,∞]` are `ℝ≥0∞`; ratios use `ENNReal` division `ofReal a / ofReal w`, which is exactly the paper's
  `0/0 := 0`, `a/0 := +∞` (`a > 0`); `sup_t` is `⨆` (complete lattice, no junk; `+∞` allowed).
* `ordStat k s = sInf {t | k ≤ #{j | s_j ≤ t}}` is the `k`-th smallest (with ties) in any complete linear order;
  `⊤` (`+∞`) when `k` exceeds the number of scores. On `EReal` with `k = 0` it is `⊥ = −∞` (T depth convention);
  on `EReal`-coerced reals it is the frozen `Conformal.kthCal`.
* `calIdx n α = ⌈(n+1)(1−α)⌉₊`; `depthIdx n p = ⌊(n+1)(1−p)⌋₊`.
* Bands/tubes at `ω = ⊤` are the whole space (the paper's `B̂^{+∞}`, `T̂^{+∞}`, `𝒯_cal` with `q̂ = +∞`); for finite
  `ω` they use `ω.toReal`. Half-widths `w ≥ 0` (B, C; the paper has `w > 0` for B/C, `w ≥ 0` for the vector
  corollary — a generalisation for B/C), `w > 0` for T (as printed, "positive continuous scale"; `w ≥ 0` would
  suffice, `w < 0` would not: the score clamps `ofReal w = 0` while the ball shrinks).
* Exchangeability: `ExchVec P S` (`P.map (S · ∘ τ) = P.map S` for all `τ`), the frozen `Exch` for real vectors.
  "iid calibration and future trajectories" (T) is weakened to exchangeable scores (a generalisation).
* Lower bounds are for a measurable event (`MeasurableSet E ∧ 1 − α ≤ P E`) where the event itself is measurable,
  and in the measurable-subset form `∃ E ⊆ event` for `tube_coverage_upper_score` (there `S(X_new)` need not be
  measurable). Upper bounds are for the raw event.
* "Ties occur with probability zero" = the score vector is a.s. injective.
* Vector curves take values in `EuclideanSpace ℝ (Fin d)`; `v^⊤ y = ⟪v, y⟫`; `𝒱 ⊆ 𝕊^{d−1}` nonempty;
  `c_v(t) = c t v`, `w_v(t) = w t v`; `−𝒱` is the image of `𝒱` under negation; the componentwise directions are
  `EuclideanSpace.single a 1`. T curves take values in any pseudometric space `M` (only `d_M` is used).
* `lem:spike`: `X : Ω → EuclideanSpace ℝ (Fin K)` measurable, coordinates `iIndepFun`, each symmetric
  (`law(−X_k) = law(X_k)`); `ν = P.map X`; `CP(r)` with all `r_k > 0`; `α ∈ [0,∞]`.
* `prop:width-contam`: "`ℓ` curves replaced" = the contaminated calibration score vector differs from the clean one in at
  most `ℓ` coordinates (`nDiff`), with no measurability or dependence restriction on the replaced scores; ranks `k − ℓ`
  use ℕ subtraction (`ordStat 0 = 0`, the bottom of `[0,∞]`), ranks past `n₂` give `+∞`. The coverage claim is the
  exchangeable (recalibrated, `prop:cal-coverage`) version: `1 − α − ℓ/(n₂+1)` (`≤` the paper's loss `ℓ/n₂`).
* `prop:ext-K-selection`: the menu is a finite nonempty type `ι` with `J = card ι`; exchangeability is assumed for each
  `K`'s score vector separately (weaker than joint exchangeability of the curves); `K̂ : Ω → ι` arbitrary (no
  measurability); `ω̃_K > 0` real; `B̂^{ω̂ω̃_K}` uses `ω̂ * ofReal ω̃_K` (`= +∞` when `ω̂ = +∞`); `min_K` is `⨅` over the
  finite type (no junk); `D̃_K` is the frozen `calDepth` of the level-`K` real score vector.
* Scenario sets: `Π_K` any map `(𝒯 → ℝ) → ℝ^K`; reconstruction `x_{[z]} = curve 𝔪 e z` (frozen); `‖·‖_{M_K}` is the
  frozen `mnorm` (no positivity of `M` needed); the residual ECDFs are any `Ĝ_e, Ĝ : [0,∞] → [0,∞]` (residuals are
  `[0,∞]`-valued sups; on nonnegative residuals `sup{η ≥ 0 : Ĝ(η) ≤ s}` equals the paper's sup over `η ∈ ℝ`);
  `η̂ = sSup` in `[0,∞]` (no junk); `H = ofReal(c_K(ρ(F̂ z)))`; `A_{K,s} = {u ∈ 𝒰 : ρ(u) ≤ c_K^{-1}(s)}` with
  `c_K^{-1}(s) = inf{t ∈ [0,1] : c_K(t) ≥ s}` (nonempty for `s < 1` since `c_K(1) = 1`); "`min_{u∈A} … ≤ η̂`" is
  `∃ u ∈ A`; conclusions on `{ŝ < 1}` (vacuous otherwise, as stated). **Hypothesis:** for some `b ≤ 1`,
  `ρ(𝒰) ⊆ [0,b]` and `c_K` strictly increasing on `[0,b]` (with `c_K(1) = 1`; e.g. the cubic law, `ρ_box` range
  `[0, D_K/D_∞]`, `c_K ≡ 1` beyond). For B this *corrects* the printed "strictly increasing on the range of `ρ` over
  `𝒰_K`", which is insufficient (critic notes); for C it is *added* — the printed statement has no such hypothesis, it
  appears only in the proof (`C_conditional/supplement.tex:2213`). C: `e_x(z) = sup_t |⟨e(t), z − Q̂_x(F̂_x z)⟩|`; `F̂_x(z) ∈ 𝒰` for all `x, z`;
  `Λ`-Lipschitz = `SupLip`, `Λ ≥ 0`; `sup/inf_{u∈A} ℓ(x_u)` are `EReal` `⨆/⨅`; the functional bounds are stated when
  both radii are finite, with their real values.
Critic notes: `exch_quantile_*` keep the paper's `k ≤ N`; `cal_coverage_*` drop it (the `+∞` branch is the
"probability `1`" sentence of the corollary's proof). `depth_region_upper` is a non-strict `≤`, as printed. Scenario sets: with the printed hypothesis the head step
`H ≤ ŝ ⇒ F̂z ∈ A_{K,ŝ}` fails. Counterexample: `𝒰 = {½ ≤ ‖u‖ ≤ 1}`, `ρ = ‖·‖`, `c_K(τ) = max(0, 2τ − 1)` (strictly
increasing on the range `[½,1]`), `F̂` constant on the inner sphere `‖u‖ = ½` (so `F̂` lands in `𝒰`, as the paper's
proof says), `Ĝ_e = Ĝ = 0`. Then every score is `0`, `ŝ = 0`, `c_K^{-1}(0) = 0`, `A_{K,0} = ∅`, and the conclusion (a
min over `∅`) fails with probability `1` (cf. DEFECTS #7 endpoint). `spike_crosspolytope` does not use `lem:convex`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatFormal.OTFD.Wave3

/-! ### Shared -/

/-- Exchangeability of a random vector with values in any measurable space. -/
def ExchVec {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω) {m : ℕ}
    (S : Ω → Fin m → β) : Prop :=
  ∀ τ : Equiv.Perm (Fin m), P.map (fun ω => S ω ∘ τ) = P.map S

/-- The `k`-th smallest of `s_1, …, s_N` (with ties), `⊤` if `k > N`. -/
def ordStat {β : Type*} [CompleteLinearOrder β] {N : ℕ} (k : ℕ) (s : Fin N → β) : β :=
  sInf {t : β | k ≤ #(univ.filter fun j => s j ≤ t)}

/-- The conformal index `⌈(n+1)(1−α)⌉`. -/
def calIdx (n : ℕ) (α : ℝ) : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊

/-- The depth index `⌊(n+1)(1−p)⌋`. -/
def depthIdx (n : ℕ) (p : ℝ) : ℕ := ⌊((n : ℝ) + 1) * (1 - p)⌋₊

/-- The calibration threshold `ω̂_α`: the `⌈(n+1)(1−α)⌉`-th smallest calibration score (indices `i.succ`). -/
def calQ {n : ℕ} (α : ℝ) (s : Fin (n + 1) → ℝ≥0∞) : ℝ≥0∞ :=
  ordStat (calIdx n α) fun i : Fin n => s i.succ

/-! ### B `def:cal-score`, `prop:cal-coverage` -/

/-- The modulated sup score `V(x) = sup_t |x(t) − c(t)|/w(t) ∈ [0,∞]` (`0/0 = 0`, `a/0 = ∞`). -/
def bandScore {T : Type*} (c w : T → ℝ) (x : T → ℝ) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal |x t - c t| / ENNReal.ofReal (w t)

/-- The inflated band `B̂^ω = [c − ωw, c + ωw]` (all curves for `ω = +∞`). -/
def inflBand {T : Type*} (c w : T → ℝ) (ω : ℝ≥0∞) : Set (T → ℝ) :=
  if ω = ⊤ then Set.univ else {x | ∀ t, c t - ω.toReal * w t ≤ x t ∧ x t ≤ c t + ω.toReal * w t}

/-! ### B `cor:vector-tube-conformal` -/

/-- `V(x) = sup_{t ∈ 𝒯, v ∈ 𝒱} |v^⊤x(t) − c_v(t)|/w_v(t) ∈ [0,∞]`. -/
def vecScore {T : Type*} {d : ℕ} (𝒱 : Set (EuclideanSpace ℝ (Fin d)))
    (c w : T → EuclideanSpace ℝ (Fin d) → ℝ) (x : T → EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ t, ⨆ v ∈ 𝒱, ENNReal.ofReal |⟪v, x t⟫_ℝ - c t v| / ENNReal.ofReal (w t v)

/-- `T̂^ω = {x : |v^⊤x(t) − c_v(t)| ≤ ω w_v(t) ∀ t, v}` (all curves for `ω = +∞`). -/
def vecTube {T : Type*} {d : ℕ} (𝒱 : Set (EuclideanSpace ℝ (Fin d)))
    (c w : T → EuclideanSpace ℝ (Fin d) → ℝ) (ω : ℝ≥0∞) : Set (T → EuclideanSpace ℝ (Fin d)) :=
  if ω = ⊤ then Set.univ else {x | ∀ t, ∀ v ∈ 𝒱, |⟪v, x t⟫_ℝ - c t v| ≤ ω.toReal * w t v}

/-- The uncalibrated directional tube `B_{p,W} = {x : v^⊤x(t) ≤ H(t,v) ∀ t, v ∈ W}`. -/
def dirTube {T : Type*} {d : ℕ} (H : T → EuclideanSpace ℝ (Fin d) → ℝ) (W : Set (EuclideanSpace ℝ (Fin d))) :
    Set (T → EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ t, ∀ v ∈ W, ⟪v, x t⟫_ℝ ≤ H t v}

/-! ### T `prop:conformal` -/

/-- `S(x) = sup_t (d_M(x(t), c_M(t)) − R(t))_+/w(t)`. -/
def tubeScore {T M : Type*} [PseudoMetricSpace M] (cM : T → M) (R w : T → ℝ) (x : T → M) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal (max (dist (x t) (cM t) - R t) 0) / ENNReal.ofReal (w t)

/-- `𝒯_cal(t) = B̄_M(c_M(t), R(t) + q w(t))` (all of `M` for `q = +∞`). -/
def calTube {T M : Type*} [PseudoMetricSpace M] (cM : T → M) (R w : T → ℝ) (q : ℝ≥0∞) (t : T) : Set M :=
  if q = ⊤ then Set.univ else Metric.closedBall (cM t) (R t + q.toReal * w t)

/-! ### T `prop:conformaldepth` -/

/-- `q̂_p = D̂_(k)`, `k = ⌊(n_c+1)(1−p)⌋` (`−∞` if `k = 0`). -/
def depthQ {n : ℕ} (p : ℝ) (c : Fin n → ℝ) : EReal :=
  ordStat (depthIdx n p) fun j => ((c j : ℝ) : EReal)

/-- The conformal depth region `Ĉ_p = {x : D̂(x) ≥ q̂_p}`. -/
def depthRegion {𝒳 : Type*} {n : ℕ} (D : 𝒳 → ℝ) (p : ℝ) (c : Fin n → ℝ) : Set 𝒳 :=
  {x | depthQ p c ≤ ((D x : ℝ) : EReal)}

/-! ### R `prop:width-contam` -/

/-- Number of coordinates where two score vectors differ (`ℓ` replaced calibration curves). -/
def nDiff {N : ℕ} (s s' : Fin N → ℝ≥0∞) : ℕ := #(univ.filter fun j => s' j ≠ s j)

/-! ### B `prop:ext-K-selection` -/

/-- `V_max(x) = max_K V_K(x)/ω̃_K` over a finite menu `ι`. -/
def vMax {ι T : Type*} (c w : ι → T → ℝ) (ωt : ι → ℝ) (x : T → ℝ) : ℝ≥0∞ :=
  ⨆ K, bandScore (c K) (w K) x / ENNReal.ofReal (ωt K)

/-! ### B `prop:rk-scenario-set`, C `prop:cond-scenario-set` -/

/-- `c_K^{-1}(s) = inf{t ∈ [0,1] : c_K(t) ≥ s}`. -/
def cInv (cK : ℝ → ℝ) (s : ℝ) : ℝ := sInf {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ s ≤ cK t}

/-- The rank region `A_{K,s} = {u ∈ 𝒰_K : ρ(u) ≤ c_K^{-1}(s)}`. -/
def rankRegion {K : ℕ} (U : Set (Fin K → ℝ)) (ρ : (Fin K → ℝ) → ℝ) (cK : ℝ → ℝ) (s : ℝ) :
    Set (Fin K → ℝ) :=
  {u | u ∈ U ∧ ρ u ≤ cInv cK s}

/-- `η̂ = sup{η : Ĝ(η) ≤ s}` (in `[0,∞]`). -/
def radius (G : ℝ≥0∞ → ℝ≥0∞) (s : ℝ≥0∞) : ℝ≥0∞ := sSup {η | G η ≤ s}

/-- Truncation residual `r_K(x) = ‖x − x_{[Π_K x]}‖_∞ = sup_t |x(t) − 𝔪(t) − ⟨e(t), Π_K x⟩|`. -/
def truncResid {K : ℕ} {T : Type} (mo : T → ℝ) (e : T → Fin K → ℝ) (Pi : (T → ℝ) → Fin K → ℝ)
    (x : T → ℝ) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal |x t - Bands2.curve mo e (Pi x) t|

/-- B `def:rk-scenario-score`: `V^sc(x) = max{H(x), E(x), T(x)}` with `H = c_K(ρ(F̂(Π_K x)))`,
`E = Ĝ_e(‖Π_K x − Q̂(F̂(Π_K x))‖_{M_K})`, `T = Ĝ(r_K(x))`. -/
def scenScore {K : ℕ} {T : Type} (mo : T → ℝ) (e : T → Fin K → ℝ) (Pi : (T → ℝ) → Fin K → ℝ)
    (F Q : (Fin K → ℝ) → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (ρ : (Fin K → ℝ) → ℝ)
    (cK : ℝ → ℝ) (Ge G : ℝ≥0∞ → ℝ≥0∞) (x : T → ℝ) : ℝ≥0∞ :=
  max (max (ENNReal.ofReal (cK (ρ (F (Pi x)))))
    (Ge (ENNReal.ofReal (Wave2.mnorm M (Pi x - Q (F (Pi x))))))) (G (truncResid mo e Pi x))

/-- C conditional inverse residual on curves `e_x(z) = sup_t |⟨e(t), z − Q̂_x(F̂_x z)⟩|`. -/
def condInvResid {K : ℕ} {T 𝒳 : Type} (e : T → Fin K → ℝ) (F Q : 𝒳 → (Fin K → ℝ) → Fin K → ℝ)
    (x : 𝒳) (z : Fin K → ℝ) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal |e t ⬝ᵥ (z - Q x (F x z))|

/-- C `def:cond-scenario-score`: `S^sc(y|x) = max{A(y|x), E(y|x), B(y)}`. -/
def condScenScore {K : ℕ} {T 𝒳 : Type} (mo : T → ℝ) (e : T → Fin K → ℝ) (Pi : (T → ℝ) → Fin K → ℝ)
    (F Q : 𝒳 → (Fin K → ℝ) → Fin K → ℝ) (ρ : (Fin K → ℝ) → ℝ) (cK : ℝ → ℝ)
    (Ge G : ℝ≥0∞ → ℝ≥0∞) (x : 𝒳) (y : T → ℝ) : ℝ≥0∞ :=
  max (max (ENNReal.ofReal (cK (ρ (F x (Pi y))))) (Ge (condInvResid e F Q x (Pi y))))
    (G (truncResid mo e Pi y))

/-- `Λ`-Lipschitz for the sup norm. -/
def SupLip {T : Type} (ℓ : (T → ℝ) → ℝ) (Λ : ℝ) : Prop :=
  ∀ x y : T → ℝ, ∀ r : ℝ, (∀ t, |x t - y t| ≤ r) → |ℓ x - ℓ y| ≤ Λ * r

namespace Claims

/-! #### B `lem:exch-quantile` -/

/-- `lem:exch-quantile`, lower bound: `P(S_{N+1} ≤ S^cal_(k)) ≥ 1 − α` for exchangeable `[0,∞]`-valued scores. -/
def exch_quantile_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (S : Ω → Fin (N + 1) → ℝ≥0∞),
    Measurable S → ExchVec P S → ∀ α : ℝ, 0 < α → α < 1 → calIdx N α ≤ N →
      MeasurableSet {ω | S ω 0 ≤ calQ α (S ω)} ∧
        ENNReal.ofReal (1 - α) ≤ P {ω | S ω 0 ≤ calQ α (S ω)}

/-- `lem:exch-quantile`, upper bound: with a.s. no ties, `P(S_{N+1} ≤ S^cal_(k)) ≤ 1 − α + 1/(N+1)`. -/
def exch_quantile_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (S : Ω → Fin (N + 1) → ℝ≥0∞),
    Measurable S → ExchVec P S → (∀ᵐ ω ∂P, Function.Injective (S ω)) →
    ∀ α : ℝ, 0 < α → α < 1 → calIdx N α ≤ N →
      P {ω | S ω 0 ≤ calQ α (S ω)} ≤ ENNReal.ofReal (1 - α + 1 / (N + 1))

/-! #### B `prop:cal-coverage` -/

/-- Score event = band event: `x ∈ B̂^ω ⇔ V(x) ≤ ω` for every `ω ∈ [0,∞]` (simultaneously in `t`). -/
def band_mem_iff : Prop :=
  ∀ (T : Type) (c w : T → ℝ), (∀ t, 0 ≤ w t) → ∀ (x : T → ℝ) (ω : ℝ≥0∞),
    x ∈ inflBand c w ω ↔ bandScore c w x ≤ ω

/-- `prop:cal-coverage`, lower bound: `P(X_{n+1} ∈ B̂^{ω̂_α}) ≥ 1 − α`. -/
def cal_coverage_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : Type) (n₂ : ℕ) (c w : T → ℝ),
    (∀ t, 0 ≤ w t) → ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    Measurable (fun ω i => bandScore c w (X ω i)) → ExchVec P (fun ω i => bandScore c w (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | X ω 0 ∈ inflBand c w (calQ α fun i => bandScore c w (X ω i))} ∧
        ENNReal.ofReal (1 - α) ≤ P {ω | X ω 0 ∈ inflBand c w (calQ α fun i => bandScore c w (X ω i))}

/-- `prop:cal-coverage`, upper bound: with a.s. distinct scores, `P(X_{n+1} ∈ B̂^{ω̂_α}) ≤ 1 − α + 1/(n₂+1)`. -/
def cal_coverage_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : Type) (n₂ : ℕ) (c w : T → ℝ),
    (∀ t, 0 ≤ w t) → ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    Measurable (fun ω i => bandScore c w (X ω i)) → ExchVec P (fun ω i => bandScore c w (X ω i)) →
    (∀ᵐ ω ∂P, Function.Injective fun i => bandScore c w (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | X ω 0 ∈ inflBand c w (calQ α fun i => bandScore c w (X ω i))} ≤
        ENNReal.ofReal (1 - α + 1 / (n₂ + 1))

/-! #### B `cor:vector-tube-conformal` -/

/-- `x ∈ T̂^ω ⇔ V(x) ≤ ω` for every `ω ∈ [0,∞]`, with `0/0 = 0`, `a/0 = ∞`. -/
def vec_tube_mem_iff : Prop :=
  ∀ (T : Type) (d : ℕ) (𝒱 : Set (EuclideanSpace ℝ (Fin d))) (c w : T → EuclideanSpace ℝ (Fin d) → ℝ),
    (∀ t v, 0 ≤ w t v) → ∀ (x : T → EuclideanSpace ℝ (Fin d)) (ω : ℝ≥0∞),
      x ∈ vecTube 𝒱 c w ω ↔ vecScore 𝒱 c w x ≤ ω

/-- `cor:vector-tube-conformal`, lower bound: `P(X_{n+1} ∈ T̂^{ω̂_α}) ≥ 1 − α`. -/
def vec_tube_coverage_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : Type) (d n₂ : ℕ)
    (𝒱 : Set (EuclideanSpace ℝ (Fin d))) (c w : T → EuclideanSpace ℝ (Fin d) → ℝ),
    𝒱.Nonempty → 𝒱 ⊆ Metric.sphere 0 1 → (∀ t v, 0 ≤ w t v) →
    ∀ X : Ω → Fin (n₂ + 1) → T → EuclideanSpace ℝ (Fin d),
    Measurable (fun ω i => vecScore 𝒱 c w (X ω i)) → ExchVec P (fun ω i => vecScore 𝒱 c w (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | X ω 0 ∈ vecTube 𝒱 c w (calQ α fun i => vecScore 𝒱 c w (X ω i))} ∧
        ENNReal.ofReal (1 - α) ≤ P {ω | X ω 0 ∈ vecTube 𝒱 c w (calQ α fun i => vecScore 𝒱 c w (X ω i))}

/-- `cor:vector-tube-conformal`, upper bound under a.s. distinct scores. -/
def vec_tube_coverage_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : Type) (d n₂ : ℕ)
    (𝒱 : Set (EuclideanSpace ℝ (Fin d))) (c w : T → EuclideanSpace ℝ (Fin d) → ℝ),
    𝒱.Nonempty → 𝒱 ⊆ Metric.sphere 0 1 → (∀ t v, 0 ≤ w t v) →
    ∀ X : Ω → Fin (n₂ + 1) → T → EuclideanSpace ℝ (Fin d),
    Measurable (fun ω i => vecScore 𝒱 c w (X ω i)) → ExchVec P (fun ω i => vecScore 𝒱 c w (X ω i)) →
    (∀ᵐ ω ∂P, Function.Injective fun i => vecScore 𝒱 c w (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | X ω 0 ∈ vecTube 𝒱 c w (calQ α fun i => vecScore 𝒱 c w (X ω i))} ≤
        ENNReal.ofReal (1 - α + 1 / (n₂ + 1))

/-- (a) componentwise: with `𝒱 = {ε_1, …, ε_d}`, `V(x) = sup_{t,a} |x_a(t) − c_{ε_a}(t)|/w_{ε_a}(t)`. -/
def vec_componentwise : Prop :=
  ∀ (T : Type) (d : ℕ) (c w : T → EuclideanSpace ℝ (Fin d) → ℝ) (x : T → EuclideanSpace ℝ (Fin d)),
    vecScore (Set.range fun a : Fin d => EuclideanSpace.single a (1 : ℝ)) c w x =
      ⨆ t, ⨆ a : Fin d, ENNReal.ofReal |x t a - c t (EuclideanSpace.single a 1)| /
        ENNReal.ofReal (w t (EuclideanSpace.single a 1))

/-- (b) directional: with `c_v = (H(t,v) − H(t,−v))/2`, `w_v = (H(t,v) + H(t,−v))/2`, for finite `ω` the tube
`T̂^ω` has threshold `c_v + ω w_v` in direction `v` and `−c_v + ω w_v` in direction `−v`, and
`T̂¹ = B_{p,𝒱∪(−𝒱)}`. -/
def vec_directional : Prop :=
  ∀ (T : Type) (d : ℕ) (𝒱 : Set (EuclideanSpace ℝ (Fin d))) (H : T → EuclideanSpace ℝ (Fin d) → ℝ),
    let c := fun t v => (H t v - H t (-v)) / 2
    let w := fun t v => (H t v + H t (-v)) / 2
    (∀ (ω : ℝ≥0∞), ω ≠ ⊤ → ∀ x : T → EuclideanSpace ℝ (Fin d),
      x ∈ vecTube 𝒱 c w ω ↔ ∀ t, ∀ v ∈ 𝒱,
        ⟪v, x t⟫_ℝ ≤ c t v + ω.toReal * w t v ∧ ⟪-v, x t⟫_ℝ ≤ -c t v + ω.toReal * w t v) ∧
    vecTube 𝒱 c w 1 = dirTube H (𝒱 ∪ (fun v => -v) '' 𝒱)

/-- Floors only enlarge: `w ≤ w'` pointwise gives `T̂^ω_w ⊆ T̂^ω_{w'}` (so `T̂¹_{w ∨ w_min} ⊇ B_{p,𝒱∪(−𝒱)}`). -/
def vec_floor_mono : Prop :=
  ∀ (T : Type) (d : ℕ) (𝒱 : Set (EuclideanSpace ℝ (Fin d))) (c w w' : T → EuclideanSpace ℝ (Fin d) → ℝ),
    (∀ t v, w t v ≤ w' t v) → ∀ ω : ℝ≥0∞, vecTube 𝒱 c w ω ⊆ vecTube 𝒱 c w' ω

/-! #### C `prop:cond-cal-coverage` -/

/-- `prop:cond-cal-coverage`, lower bound: `P{Y_new ∈ B̂^{ς̂_α}(·|X_new)} ≥ 1 − α`, each calibration score at its own
covariate. -/
def cond_cal_coverage_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) →
    ∀ (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ExchVec P (fun ω i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
          (calQ α fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i))} ∧
      ENNReal.ofReal (1 - α) ≤ P {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
          (calQ α fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i))}

/-- `prop:cond-cal-coverage`, upper bound `1 − α + 1/(n₂+1)` under a.s. distinct scores. -/
def cond_cal_coverage_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) →
    ∀ (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ExchVec P (fun ω i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    (∀ᵐ ω ∂P, Function.Injective fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
          (calQ α fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i))} ≤
        ENNReal.ofReal (1 - α + 1 / (n₂ + 1))

/-! #### T `prop:conformaldepth` -/

/-- Lower bound `p ≤ P{D̂(X) ≥ q̂_p}` (no tie assumption). -/
def depth_region_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 : Type) (n : ℕ) (D : 𝒳 → ℝ)
    (X : Ω → Fin (n + 1) → 𝒳),
    Measurable (fun ω i => D (X ω i)) → Conformal.Exch P (fun ω i => D (X ω i)) →
    ∀ p : ℝ, 0 < p → p < 1 →
      MeasurableSet {ω | X ω 0 ∈ depthRegion D p fun i => D (X ω i.succ)} ∧
        ENNReal.ofReal p ≤ P {ω | X ω 0 ∈ depthRegion D p fun i => D (X ω i.succ)}

/-- Upper bound `P{D̂(X) ≥ q̂_p} ≤ p + 1/(n_c+1)` when the `n_c+1` depths are a.s. distinct. -/
def depth_region_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 : Type) (n : ℕ) (D : 𝒳 → ℝ)
    (X : Ω → Fin (n + 1) → 𝒳),
    Measurable (fun ω i => D (X ω i)) → Conformal.Exch P (fun ω i => D (X ω i)) →
    (∀ᵐ ω ∂P, Function.Injective fun i => D (X ω i)) →
    ∀ p : ℝ, 0 < p → p < 1 →
      P {ω | X ω 0 ∈ depthRegion D p fun i => D (X ω i.succ)} ≤ ENNReal.ofReal (p + 1 / (n + 1))

/-- The regions `Ĉ_p` are nested in `p`. -/
def depth_region_nested : Prop :=
  ∀ (𝒳 : Type) (n : ℕ) (D : 𝒳 → ℝ) (c : Fin n → ℝ) (p p' : ℝ), p ≤ p' →
    depthRegion D p c ⊆ depthRegion D p' c

/-! #### T `prop:conformal` -/

/-- The score event is tube membership: `(∀ t, x(t) ∈ 𝒯_q(t)) ⇔ S(x) ≤ q` (`w > 0`, every `q ∈ [0,∞]`). -/
def tube_mem_iff : Prop :=
  ∀ (T M : Type) [PseudoMetricSpace M] (cM : T → M) (R w : T → ℝ), (∀ t, 0 < w t) →
    ∀ (x : T → M) (q : ℝ≥0∞), (∀ t, x t ∈ calTube cM R w q t) ↔ tubeScore cM R w x ≤ q

/-- `eq:conformal`: `P{X_new(t) ∈ 𝒯_cal(t) ∀ t} ≥ 1 − α`. -/
def tube_coverage : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T M : Type) [PseudoMetricSpace M]
    (N : ℕ) (cM : T → M) (R w : T → ℝ), (∀ t, 0 < w t) → ∀ X : Ω → Fin (N + 1) → T → M,
    Measurable (fun ω i => tubeScore cM R w (X ω i)) → ExchVec P (fun ω i => tubeScore cM R w (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | ∀ t, X ω 0 t ∈ calTube cM R w (calQ α fun i => tubeScore cM R w (X ω i)) t} ∧
        ENNReal.ofReal (1 - α) ≤
          P {ω | ∀ t, X ω 0 t ∈ calTube cM R w (calQ α fun i => tubeScore cM R w (X ω i)) t}

/-- The same with a measurable upper score `S⁺ ≥ S` and the quantile computed from `S⁺`. -/
def tube_coverage_upper_score : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T M : Type) [PseudoMetricSpace M]
    (N : ℕ) (cM : T → M) (R w : T → ℝ), (∀ t, 0 < w t) → ∀ (Splus : (T → M) → ℝ≥0∞),
    (∀ x, tubeScore cM R w x ≤ Splus x) → ∀ X : Ω → Fin (N + 1) → T → M,
    Measurable (fun ω i => Splus (X ω i)) → ExchVec P (fun ω i => Splus (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ P E ∧
        E ⊆ {ω | ∀ t, X ω 0 t ∈ calTube cM R w (calQ α fun i => Splus (X ω i)) t}

/-! #### R `lem:spike` -/

/-- `lem:spike`: independent coordinates, each symmetric about `0`, give `TD(r e_k) ≥ ½ P(X_k ≥ r)`. -/
def spike_bound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin K)), Measurable X → iIndepFun (fun k ω => X ω k) P →
    (∀ k, P.map (fun ω => -X ω k) = P.map (fun ω => X ω k)) →
    ∀ (k : Fin K) (r : ℝ), 0 ≤ r →
      2⁻¹ * P {ω | r ≤ X ω k} ≤ Wave1.tukeyDepth (P.map X) (EuclideanSpace.single k r)

/-- `lem:spike`, consequence: if `P(X_k ≥ r_k) ≥ α` for every `k`, the cross-polytope
`CP(r) = {u : Σ_k |u_k|/r_k ≤ 1}` has `β(CP(r)) ≥ α/2`. -/
def spike_crosspolytope : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin K)), Measurable X → iIndepFun (fun k ω => X ω k) P →
    (∀ k, P.map (fun ω => -X ω k) = P.map (fun ω => X ω k)) →
    ∀ (r : Fin K → ℝ) (α : ℝ≥0∞), (∀ k, 0 < r k) → (∀ k, α ≤ P {ω | r k ≤ X ω k}) →
      α / 2 ≤ Wave1.regionDepth (P.map X) {u | ∑ k, |u k| / r k ≤ 1}

/-! #### R `prop:width-contam` -/

/-- Rank sandwich: replacing `ℓ` calibration scores moves the `k`-th order statistic between the clean
order statistics of ranks `k − ℓ` and `k + ℓ` (`0` resp. `+∞` past the ends). -/
def width_contam_sandwich : Prop :=
  ∀ (n ℓ k : ℕ) (s s' : Fin n → ℝ≥0∞), nDiff s s' ≤ ℓ →
    ordStat (k - ℓ) s ≤ ordStat k s' ∧ ordStat k s' ≤ ordStat (k + ℓ) s

/-- The contaminated threshold (hence the selected width) stays bounded when `k + ℓ ≤ n₂`. -/
def width_contam_bounded : Prop :=
  ∀ (n ℓ k : ℕ) (s s' : Fin n → ℝ≥0∞), nDiff s s' ≤ ℓ → k + ℓ ≤ n → (∀ j, s j ≠ ⊤) →
    ordStat k s' ≠ ⊤

/-- Coverage loss: with exchangeable clean scores and `ℓ` arbitrarily replaced calibration scores
(any dependence), the coverage `1 − α` drops by at most `ℓ/(n₂+1) ≤ ℓ/n₂`. -/
def width_contam_coverage : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n ℓ : ℕ)
    (S : Ω → Fin (n + 1) → ℝ≥0∞) (S' : Ω → Fin n → ℝ≥0∞),
    Measurable S → ExchVec P S → (∀ ω, nDiff (fun i => S ω i.succ) (S' ω) ≤ ℓ) →
    ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α - ℓ / (n + 1)) ≤ P E ∧
        E ⊆ {ω | S ω 0 ≤ ordStat (calIdx n α) (S' ω)}

/-! #### B `prop:ext-K-selection` -/

/-- (i) union correction at `α/J`: the simultaneous event has probability `≥ 1 − α`, and it is contained in
`{X_{n+1} ∈ B̂_{K̂}^{ω̂_{K̂}}}` for **every** `K̂` (any dependence on the data). -/
def extK_union : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type) [Fintype ι]
    [Nonempty ι] (T : Type) (n₂ : ℕ) (c w : ι → T → ℝ), (∀ K t, 0 ≤ w K t) →
    ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    (∀ K, Measurable fun ω i => bandScore (c K) (w K) (X ω i)) →
    (∀ K, ExchVec P fun ω i => bandScore (c K) (w K) (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          (calQ (α / Fintype.card ι) fun i => bandScore (c K) (w K) (X ω i))} ∧
      ENNReal.ofReal (1 - α) ≤ P {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          (calQ (α / Fintype.card ι) fun i => bandScore (c K) (w K) (X ω i))} ∧
      ∀ Khat : Ω → ι, {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          (calQ (α / Fintype.card ι) fun i => bandScore (c K) (w K) (X ω i))} ⊆
        {ω | X ω 0 ∈ inflBand (c (Khat ω)) (w (Khat ω))
          (calQ (α / Fintype.card ι) fun i => bandScore (c (Khat ω)) (w (Khat ω)) (X ω i))}

/-- Finiteness of the order-statistic index: `⌈(n₂+1)(1−α/J)⌉ ≤ n₂ ⇔ n₂ ≥ J/α − 1` ((i)), and
`⌈(n₂+1)(1−α)⌉ ≤ n₂ ⇔ n₂ ≥ 1/α − 1` ((ii)). -/
def extK_finite_iff : Prop :=
  ∀ (n₂ J : ℕ) (α : ℝ), 0 < α → 0 < J →
    (calIdx n₂ (α / J) ≤ n₂ ↔ (J : ℝ) / α - 1 ≤ n₂) ∧ (calIdx n₂ α ≤ n₂ ↔ 1 / α - 1 ≤ n₂)

/-- (ii) a single score `V_max = max_K V_K/ω̃_K`: the simultaneous event `{X ∈ B̂_K^{ω̂ ω̃_K} ∀ K}` has probability
`≥ 1 − α`, and it is contained in `{X_{n+1} ∈ B̂_{K̂}^{ω̂ ω̃_{K̂}}}` for every `K̂`. -/
def extK_single_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type) [Fintype ι]
    (T : Type) (n₂ : ℕ) (c w : ι → T → ℝ) (ωt : ι → ℝ), (∀ K t, 0 ≤ w K t) → (∀ K, 0 < ωt K) →
    ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    Measurable (fun ω i => vMax c w ωt (X ω i)) → ExchVec P (fun ω i => vMax c w ωt (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          ((calQ α fun i => vMax c w ωt (X ω i)) * ENNReal.ofReal (ωt K))} ∧
      ENNReal.ofReal (1 - α) ≤ P {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          ((calQ α fun i => vMax c w ωt (X ω i)) * ENNReal.ofReal (ωt K))} ∧
      ∀ Khat : Ω → ι, {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          ((calQ α fun i => vMax c w ωt (X ω i)) * ENNReal.ofReal (ωt K))} ⊆
        {ω | X ω 0 ∈ inflBand (c (Khat ω)) (w (Khat ω))
          ((calQ α fun i => vMax c w ωt (X ω i)) * ENNReal.ofReal (ωt (Khat ω)))}

/-- (ii) upper bound `1 − α + 1/(n₂+1)` for the simultaneous event when the `V_max` scores are a.s. distinct. -/
def extK_single_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type) [Fintype ι]
    (T : Type) (n₂ : ℕ) (c w : ι → T → ℝ) (ωt : ι → ℝ), (∀ K t, 0 ≤ w K t) → (∀ K, 0 < ωt K) →
    ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    Measurable (fun ω i => vMax c w ωt (X ω i)) → ExchVec P (fun ω i => vMax c w ωt (X ω i)) →
    (∀ᵐ ω ∂P, Function.Injective fun i => vMax c w ωt (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      P {ω | ∀ K, X ω 0 ∈ inflBand (c K) (w K)
          ((calQ α fun i => vMax c w ωt (X ω i)) * ENNReal.ofReal (ωt K))} ≤
        ENNReal.ofReal (1 - α + 1 / (n₂ + 1))

/-- (iii) depth: `P(min_K D̃_K(X_{n+1}) ≤ α/J) ≤ α` for `α ∈ (0,1)`, and `min{1, J min_K D̃_K}` is exact-scale
(`P(· ≤ α) ≤ α` for every `α`). `D̃_K` is the frozen `CalDepth.calDepth` of the level-`K` score vector `S K`. -/
def extK_depth : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type) [Fintype ι]
    [Nonempty ι] (m : ℕ) (S : ι → Ω → Fin (m + 1) → ℝ),
    (∀ K, Measurable (S K)) → (∀ K, Conformal.Exch P (S K)) →
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | (⨅ K, CalDepth.calDepth (fun i : Fin m => S K ω i.succ) (S K ω 0)) ≤ α / Fintype.card ι}
          ≤ ENNReal.ofReal α) ∧
      (∀ α : ℝ, P {ω | min 1 ((Fintype.card ι : ℝ) *
          ⨅ K, CalDepth.calDepth (fun i : Fin m => S K ω i.succ) (S K ω 0)) ≤ α} ≤ ENNReal.ofReal α)

/-! #### B `prop:rk-scenario-set` -/

/-- `prop:rk-scenario-set`: with probability `≥ 1 − α` (a measurable event), on `{ŝ_α < 1}`,
`min_{u∈A_{K,ŝ}} ‖Π_K X_{n+1} − Q̂(u)‖_{M_K} ≤ η̂_e` and `‖X_{n+1} − x_{[Π_K X_{n+1}]}‖_∞ ≤ η̂_r`. -/
def rk_scenario_set : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (T : Type) (n₂ : ℕ)
    (mo : T → ℝ) (e : T → Fin K → ℝ) (Pi : (T → ℝ) → Fin K → ℝ) (F Q : (Fin K → ℝ) → Fin K → ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ) (ρ : (Fin K → ℝ) → ℝ) (cK : ℝ → ℝ) (U : Set (Fin K → ℝ))
    (Ge G : ℝ≥0∞ → ℝ≥0∞) (b : ℝ), b ≤ 1 →
    StrictMonoOn cK (Set.Icc 0 b) → cK 1 = 1 → (∀ u ∈ U, ρ u ∈ Set.Icc (0 : ℝ) b) → (∀ z, F z ∈ U) →
    ∀ X : Ω → Fin (n₂ + 1) → T → ℝ,
    Measurable (fun ω i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i)) →
    ExchVec P (fun ω i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ P E ∧
        E ⊆ {ω | (calQ α fun i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i)) < 1 →
          (∃ u ∈ rankRegion U ρ cK (calQ α fun i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i)).toReal,
            ENNReal.ofReal (Wave2.mnorm M (Pi (X ω 0) - Q u)) ≤
              radius Ge (calQ α fun i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i))) ∧
          ∀ t, ENNReal.ofReal |X ω 0 t - Bands2.curve mo e (Pi (X ω 0)) t| ≤
              radius G (calQ α fun i => scenScore mo e Pi F Q M ρ cK Ge G (X ω i))}

/-! #### C `prop:cond-scenario-set` -/

/-- `prop:cond-scenario-set`: with probability `≥ 1 − α`, on `{ŝ_α < 1}`, the reconstructed curve is within
`η̂_e` (sup norm) of the reconstruction of some `Q̂_{X_new}(u)`, `u ∈ A_{K,ŝ}`, `‖Y_new − P_K Y_new‖_∞ ≤ η̂_r`,
and (when both radii are finite) simultaneously for every `Λ`-Lipschitz functional `ℓ`,
`inf_{u∈A} ℓ(x_u) − Λ(η̂_r + η̂_e) ≤ ℓ(Y_new) ≤ sup_{u∈A} ℓ(x_u) + Λ(η̂_r + η̂_e)` (eq:cond-functionals). -/
def cond_scenario_set : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (T 𝒳 : Type)
    (n₂ : ℕ) (mo : T → ℝ) (e : T → Fin K → ℝ) (Pi : (T → ℝ) → Fin K → ℝ)
    (F Q : 𝒳 → (Fin K → ℝ) → Fin K → ℝ) (ρ : (Fin K → ℝ) → ℝ) (cK : ℝ → ℝ) (U : Set (Fin K → ℝ))
    (Ge G : ℝ≥0∞ → ℝ≥0∞) (b : ℝ), b ≤ 1 →
    StrictMonoOn cK (Set.Icc 0 b) → cK 1 = 1 → (∀ u ∈ U, ρ u ∈ Set.Icc (0 : ℝ) b) →
    (∀ x z, F x z ∈ U) →
    ∀ (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => condScenScore mo e Pi F Q ρ cK Ge G (X ω i) (Y ω i)) →
    ExchVec P (fun ω i => condScenScore mo e Pi F Q ρ cK Ge G (X ω i) (Y ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ P E ∧
        E ⊆ {ω | let s := calQ α fun i => condScenScore mo e Pi F Q ρ cK Ge G (X ω i) (Y ω i)
          s < 1 →
          (∃ u ∈ rankRegion U ρ cK s.toReal, ∀ t,
            ENNReal.ofReal |Bands2.curve mo e (Pi (Y ω 0)) t - Bands2.curve mo e (Q (X ω 0) u) t| ≤
              radius Ge s) ∧
          (∀ t, ENNReal.ofReal |Y ω 0 t - Bands2.curve mo e (Pi (Y ω 0)) t| ≤ radius G s) ∧
          (radius Ge s ≠ ⊤ → radius G s ≠ ⊤ → ∀ (ℓ : (T → ℝ) → ℝ) (Λ : ℝ), 0 ≤ Λ → SupLip ℓ Λ →
            ((ℓ (Y ω 0) : ℝ) : EReal) ≤ (⨆ u ∈ rankRegion U ρ cK s.toReal,
                ((ℓ (Bands2.curve mo e (Q (X ω 0) u)) : ℝ) : EReal)) +
              ((Λ * ((radius G s).toReal + (radius Ge s).toReal) : ℝ) : EReal) ∧
            (⨅ u ∈ rankRegion U ρ cK s.toReal, ((ℓ (Bands2.curve mo e (Q (X ω 0) u)) : ℝ) : EReal)) -
                ((Λ * ((radius G s).toReal + (radius Ge s).toReal) : ℝ) : EReal) ≤
              ((ℓ (Y ω 0) : ℝ) : EReal))}

end Claims
end StatFormal.OTFD.Wave3
