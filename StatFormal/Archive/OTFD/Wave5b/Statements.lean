import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Wave2.Statements
import StatFormal.Archive.OTFD.Wave3.Statements
import StatFormal.Archive.OTFD.Ranks.Statements
import StatFormal.Archive.SBFairness.Stability.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FROZEN STATEMENTS — otfd wave 5b: C `prop:cond-cal-mondrian`, C `cor:witness-reuse`,
# C `prop:lse-certificate`, G `lem:stability`, T "Fixed-sieve distribution-free hard labels"

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-C_conditional.md`, `otfd-G_geodesic.md`,
`otfd-T_tangent.md`; current text of 2026-10-14, paths below are under `otfd/papers/`):
* C `prop:cond-cal-mondrian` (`C_conditional/main.tex:833-856`), with `def:cond-cal-score` (`main.tex:797-810`).
* C `cor:witness-reuse` (`C_conditional/main.tex:565-600`), with `L_i`, `δ_i` of `prop:conditional-certificate`
  (`main.tex:533-554`), `D_f` of `prop:conditional-perturbation` (`main.tex:609-619`), `A_{K,p}` (`main.tex:271-276`).
* C `prop:lse-certificate` (`C_conditional/supplement.tex:1425-1478`, proof `:1486-1546`), with the network
  `eq:conditional-lse-network` (`main.tex:718-721`).
* G `lem:stability` (`G_geodesic/supp_moved.tex:161-176`, proof `:178-192`).
* T `prop:hardranks` "Fixed-sieve distribution-free hard labels" (`T_tangent/supp_moved.tex:638-660`, unlabelled in
  the inventory).
Reuses the frozen `OTFD/Bands/Statements.lean` (`simplex`, `softmax`, `score`, `gap`), `OTFD/Bands2/Statements.lean`
(`edgeUp`, `edgeLo`, `curve`, `band`, `calInv`), `OTFD/Wave2/Statements.lean` (`condA`, `condB`, `condGap`,
`condWitness`, `potOsc`, `condMapEnt`, `entWeights`, `cappedSimplex`, `IsGreedyFill`, `eucl`),
`OTFD/Wave3/Statements.lean` (`ExchVec`, `calIdx`, `bandScore`, `inflBand`), `OTFD/Ranks/Statements.lean`
(`IsMin`, `UniqueMin`) and `SBFairness/Stability/Statements.lean` (`tv`), imported, not copied.

Covered:
* C `prop:cond-cal-mondrian`: `mond_threshold_top` (`⌈(n_j+1)(1−α)⌉ > n_j ⇔ n_j < (1−α)/α`, and then
  `ς̂_{α,j} = +∞`); `mond_cell_lower`, `mond_cell_exact` (conditionally on the cell-label vector `L` of all `n₂+1`
  covariates, coverage `≥ ⌈(n_j+1)(1−α)⌉/(n_j+1)`, with equality under a.s. distinct scores);
  `mond_coverage_lower` (the displayed `≥ 1 − α` given `X_new ∈ 𝒳_j`, measurable event);
  `mond_coverage_upper` (`≤ 1 − α + E[1/(n_j+1) | X_new ∈ 𝒳_j]` under a.s. distinct scores).
* C `cor:witness-reuse`: (a) `witness_valid` (`L_i(ω,x') ≤ δ_i(p|x')` over the retained set, and `max{0,L} ≤ δ`),
  `witness_update` (the update formula), `witness_gauge` (gauge-freeness); (b) `witness_restrict` (`ω'` lies in
  the simplex over `I_{x'}`), `witness_restrict_supp` (the support-function bound), `witness_trivial`
  (`L_i(e_i,x') = 0`); (c) `witness_tight` (both displayed inequalities), `witness_minimax` (`δ_i = max_ω L_i`,
  attained, for convex `A`), `witness_reuse_optimal`.
* C `prop:lse-certificate`: (i) `lse_grad` (`∇φ = Σ softmax(s^NN/(2τ))_j α_j`, `φ` convex), `lse_is_oos` (the map is
  `condMapEnt` at `ε = 2τ` with atoms `α_j`, potential `f_j = 2β_j + ‖α_j‖²`, intercepts `2β_j`, and
  `φ = (ε/2) log Σ e^{s_j/ε}`); (ii) `lse_sup_attained`, `lse_validity`, `lse_gap_witness`, `lse_caps`,
  `lse_outer_edges`; (iii) `lse_minimax`; (iv) `lse_gap_shift`, `lse_witness_shift`, `lse_map_shift`,
  `lse_reduction` (`Δα = 0` gives `D_f = 2D_β`).
* G `lem:stability`: `stab_pythagoras` (`eq:pythagoras`, both KLs finite); (a) `stab_tv_osc`, `stab_separable`;
  (b) `stab_tv_integrable`; (c) `stab_mean` (any bounded `ψ`, constant `2 sup‖ψ‖`), `stab_rank` (`ψ = id`,
  `‖v‖ ≤ 1` `μ`-a.e.).
* T: `hard_unique_ae` (a.s. unique matching), `hard_rank_uniform` (uniform rank permutation), `hard_labels_df`
  (labels that are functions of the rank permutation are distribution-free), `hard_labels_conditional` (the
  same conditionally on an independent training sample, as independence of the labels from it).

Not covered (declared):
* C Mondrian: the remarks after the proposition (Vovk/Lei–Wasserman, marginal coverage by averaging, compatibility
  with `thm:cond-cal-impossible`); unconditioning on the fitting fold (as in the frozen Wave 3, all fitted objects
  `c`, `w`, the partition are fixed functions); that the partition is Borel (it enters through measurability of
  the cell-label vector).
* C witness reuse: the operation count `O(|supp ω|)`; the comparison sentence "never worse than `L_i(ω,x) − 2D_f`"
  (that is the frozen Wave 2 `cond_witness_shift`); the interpretive sentences after the corollary.
* C LSE: "the certificate concerns the fitted law only" and the sentences after the proposition; that `A_{K,p}` is
  `{u ∈ 𝒰 : g(u) ≤ c_K^{-1}(p)}` for the ball/cubic references (the region is any set with the stated properties,
  or `{u ∈ 𝒰 : g u ≤ calInv}` in `lse_validity`); "computed by filling caps in order" beyond the threshold form;
  nestedness in `p`.
* G: that the entropic plans exist and have the Gibbs form (Nutz Thm 4.2) — entered as hypotheses; the remark
  after the lemma (Eckstein–Nutz comparison, numerical factors).
* T: "It is a hard-assignment assertion, not an assertion about soft ranks" (a remark); the sentences after the
  proof (finite-dimensional references, hypersurface-null Hilbert laws, estimated-basis preprocessing).

Encodings (see card):
* C Mondrian: as in the frozen Wave 3 (`cond_cal_coverage_*`): index `0` is the new pair, `i.succ` the
  calibration pairs, scores `S(Y_i|X_i) = bandScore (c X_i) (w X_i) Y_i ∈ [0,∞]`, `w ≥ 0`. Cells: any
  `cell : 𝒳 → ℕ` (a finite or countable partition, labels in `ℕ`). Exchangeability of the pairs is weakened to
  exchangeability of the (cell label, score) vector (`ExchVec`, a generalisation), measurable. `n_j(L)` =
  `cellCount L j`; `ς̂_{α,j} = ordStatOn (calIdx n_j α) (cellCal L j) (scores)`, the `k`-th smallest of the
  calibration scores in cell `j`, `= ⊤` (`+∞`, `sInf ∅`) when `k > n_j` (the paper's convention, not junk).
  Conditional probabilities are `ProbabilityTheory.cond` on events of positive probability (no division junk);
  `E[1/(n_j+1) | ·]` is a lower integral against the conditional measure. "Simultaneously in `t`" is the frozen
  `inflBand`. "Almost surely distinct scores" = the score vector is a.s. injective.
* C witness reuse: rows `Fin n`; retained sets `I_x, I_{x'}` are `Finset (Fin n)`, potentials are total
  (`f : Fin n → ℝ`, values off the retained set unused); "the simplex over `I`" = `simplexOn I` (simplex weights
  vanishing off `I`). `L_i` is the frozen `condWitness` (exact support function, `sSup`, no junk on compact
  nonempty `A`); `δ_i` over a retained set is `condGapOn` (`sSup` of a finite nonempty set inside an `sInf` bounded
  below by `0`); in (c) `I_x = I_{x'} = Fin n` and `δ_i` is the frozen `condGap`. `r_{K,p}` is any `r ≥ ‖u‖` on `A`,
  `diam{Z_k : k ∈ supp ω}` any `D ≥ ‖Z_k − Z_l‖` on `supp ω`, `max_k Δ_k = ⨆ k` (finite, `n ≥ 1` since
  `ω ∈ Δ`), `D_f` the frozen `potOsc`. `A_{K,p}` enters as any compact nonempty `A`, **convex** for the minimax
  claim (DEFECTS #26: convexity of `A_{K,p}` is part of the setting, `main.tex:275`). The update formula is
  stated for every `ω` (algebraic identity; the support hypothesis only makes `f(x')` defined on `supp ω`).
* C LSE: `ℝ^K = Fin K → ℝ`, atoms `α : Fin J → ℝ^K`, `β : Fin J → ℝ` at the fixed query (two queries: `α, β`
  and `α', β'`); `s^NN = score (2β) (2α)`; `q = entWeights (2β) (2α) (2τ)` (`softmax(s^NN/(2τ))`);
  `T = lseMap`; `δ^NN = gap (2β) (2α) A` (frozen); `L^NN = lseWitness` with the exact support function;
  gradient = `HasFDerivAt φ ⟨T(u), ·⟩ u`. Validity: `U ∼ μ_K` measurable, the region `{u ∈ 𝒰 : g(u) ≤ c_K^{-1}(p)}`
  with `𝒰` compact of full mass, `g` continuous, `0 < p ≤ 1` (as in the frozen Bands2 `guarantee_*`), band
  event = frozen `band` of `edgeLo/edgeUp`, measurable. Caps: any `δ̲_j ≤ δ^NN_j`; outer edges: frozen
  `IsGreedyFill` (threshold form of "filling caps in order"). (iv): `D_β = potOsc β β'`, `D_α`, `R_p`, `R_α`,
  `Δ_α` any upper bounds of the printed maxima (Euclidean `eucl`).
* G: `μ` on any measurable `V`, `P` on any measurable `𝒳`, both probability measures; bounded measurable costs
  `c, c' : V × 𝒳 → ℝ` (bounded and measurable everywhere, a specialisation of "on `supp μ × supp P`"); "the
  corresponding entropic plans" = Gibbs plans `dπ = e^{(f ⊕ g − c)/ε} d(μ⊗P)` with **bounded measurable
  potentials** and marginals `μ`, `P` (`GibbsHyp`; the proof's "densities bounded above and below"). `KL` is
  Mathlib's `klDiv` (`ℝ≥0∞`; finiteness is part of the conclusion, then `toReal`); `TV` is the frozen
  `Stability.tv` (`sup_A |π(A) − π'(A)|`). (a): `osc(ω)` = `b − a` for any bounds `a ≤ ω ≤ b`; the decomposition
  holds `μ⊗P`-a.e., `u ∈ L¹(μ)`, `w ∈ L¹(P)`. (c): the conditional law of a Gibbs plan is
  `π(dv|x) = e^{(f(v)+g(x)−c(v,x))/ε} μ(dv)`, so `F(x) = gibbsMean … ψ x` (Bochner, integrable since everything is
  bounded); `∫ ‖F' − F‖ dP` is a lower integral of `‖·‖ₑ` (no junk); `ψ` strongly measurable, `‖ψ‖ ≤ M` `μ`-a.e.
* T: `ℝ^K` generalised to any real inner-product space `E`, Borel, second countable; "zero mass to affine
  hyperplanes" = `ν{z : ⟨a,z⟩ = b} = 0` for all `a ≠ 0`, `b`; iid sample = `P.map Z = Measure.pi (fun _ => ν)`;
  `n` distinct reference points = `u` injective; the matching is the frozen `Ranks` cost with any Borel selection
  `sel` of a minimiser (as in the frozen `fixedK_df`). "Labels derived from it" = any `ℓ : S_n → β` of the rank
  permutation (the rank vector `(u_{σ̂(i)})_i` is the case `ℓ σ = u ∘ σ`); distribution-free = the law is the
  image of the uniform law: `P(ℓ(σ̂) ∈ B) = #{h : ℓ h ∈ B}/n!`, for every `B` (no measurability needed).
  Conditional version: training `W : Ω → 𝒲`, `law(W, Z) = law(W) ⊗ κ` with `κ` a Markov kernel and, for
  `law(W)`-a.e. `w`, `κ w = ν_w^{⊗n}` with `ν_w` a hyperplane-null probability (the hyperplane condition holds
  conditionally); conclusion `P(W ∈ A, ℓ(σ̂) ∈ B) = P(W ∈ A) · #{h : ℓ h ∈ B}/n!` for measurable `A`.

Critic notes:
* C `cor:witness-reuse`(c): the minimax identity needs `A` convex (non-convex `A`: `σ_A = σ_{conv A}`, so
  `max_ω L_i = min_{conv A} max_k [s_k − s_i]` can be `< δ_i`); it is stated with convexity, as in the setting.
* C `cor:witness-reuse`(c): `witness_tight`, `witness_reuse_optimal` take the common retained set to be all rows
  (`I = Fin n`, frozen `condGap`), a specialisation; (a)'s update identity needs no support hypothesis here.
* G: "the corresponding entropic plans" is the Gibbs form with bounded measurable potentials (`GibbsHyp`), a
  hypothesis (Nutz Thm 4.2 is not formalised); given it, `eq:pythagoras` is an exact computation
  (`llr(π'|π) = h' − h`), not the citation of Nutz Prop 4.6. `supp μ`, `supp P` play no role (costs bounded
  everywhere).
* T: the a.s.-uniqueness hypothesis of the frozen `fixedK_df` is derived here from the hyperplane condition.
* No statement of the five items was found false; all 36 claims have proof routes (`Route*.lean`).
* Critic (2026-10-14): `witness_tight`/`witness_reuse_optimal` lose nothing by taking `I` = all rows — every quantity in
  (c) involves only rows in `I`, so reindexing to `Fin |I|` recovers the general case. `GibbsHyp` (Gibbs-form plan
  with the right marginals) is satisfiable and is the unique entropic optimiser; its existence for bounded costs is
  Nutz, Thm 4.2 (not formalised), so the G `lem:stability` conclusions transfer to the paper's plans.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Set InformationTheory
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave5b

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2 StatFormal.OTFD.Wave2 StatFormal.OTFD.Wave3

/-! ### C `prop:cond-cal-mondrian` -/

/-- The `k`-th smallest (with ties) of the values `s_i`, `i ∈ I`; `⊤` if `k > #I`. -/
def ordStatOn {ι β : Type*} [CompleteLinearOrder β] (k : ℕ) (I : Finset ι) (s : ι → β) : β :=
  sInf {t : β | k ≤ #(I.filter fun j => s j ≤ t)}

/-- Calibration indices in cell `j`: `{i : L(i+1) = j}` (index `0` is the new pair). -/
def cellCal {n : ℕ} (L : Fin (n + 1) → ℕ) (j : ℕ) : Finset (Fin n) :=
  univ.filter fun i => L i.succ = j

/-- `n_j`: number of calibration pairs in cell `j`. -/
def cellCount {n : ℕ} (L : Fin (n + 1) → ℕ) (j : ℕ) : ℕ := #(cellCal L j)

/-- `ς̂_{α,j}`: the `⌈(n_j+1)(1−α)⌉`-th smallest calibration score in cell `j` (`+∞` past `n_j`). -/
def mondQ {n : ℕ} (α : ℝ) (L : Fin (n + 1) → ℕ) (s : Fin (n + 1) → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ordStatOn (calIdx (cellCount L j) α) (cellCal L j) fun i => s i.succ

/-! ### C `cor:witness-reuse` -/

/-- The simplex over a retained set `I`: simplex weights vanishing off `I`. -/
def simplexOn {n : ℕ} (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {ω | ω ∈ simplex n ∧ ∀ k, k ∉ I → ω k = 0}

/-- `δ_i(p|x) = min_{u∈A} max_{k∈I} [s_k(u|x) − s_i(u|x)]` over a retained set `I`. -/
def condGapOn {n K : ℕ} (I : Finset (Fin n)) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) (i : Fin n) : ℝ :=
  sInf ((fun u => sSup ((fun k => score (condA f Z) (condB Z) k u) '' (I : Set (Fin n))) -
    score (condA f Z) (condB Z) i u) '' A)

/-- Support function `σ_A(v) = sup_{u∈A} ⟨v, u⟩`. -/
def suppA {K : ℕ} (A : Set (Fin K → ℝ)) (v : Fin K → ℝ) : ℝ := sSup ((fun u => v ⬝ᵥ u) '' A)

/-- `v_i(ω) = 2Z_i − 2Σ_k ω_k Z_k`. -/
def witDir {n K : ℕ} (Z : Fin n → Fin K → ℝ) (ω : Fin n → ℝ) (i : Fin n) : Fin K → ℝ :=
  condB Z i - ∑ k, ω k • condB Z k

/-- `ω' = ω 1_J / ω(J)`. -/
def restrictW {n : ℕ} (J : Finset (Fin n)) (ω : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if k ∈ J then ω k / ∑ l ∈ J, ω l else 0

/-! ### C `prop:lse-certificate` -/

/-- The linear functional `y ↦ ⟨g, y⟩` as a continuous linear map. -/
def dotL {K : ℕ} (g : Fin K → ℝ) : (Fin K → ℝ) →L[ℝ] ℝ :=
  ∑ k, g k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k

/-- `φ(u;x) = τ log Σ_j exp{(⟨α_j(x), u⟩ + β_j(x))/τ}`. -/
def lseNet {J K : ℕ} (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (u : Fin K → ℝ) : ℝ :=
  τ * Real.log (∑ j, Real.exp ((α j ⬝ᵥ u + β j) / τ))

/-- Intercepts `2β_j` of the neural scores. -/
def lseA {J : ℕ} (β : Fin J → ℝ) : Fin J → ℝ := fun j => 2 * β j

/-- Slopes `2α_j` of the neural scores. -/
def lseB {J K : ℕ} (α : Fin J → Fin K → ℝ) : Fin J → Fin K → ℝ := fun j => (2 : ℝ) • α j

/-- `T(u,x) = Σ_j q_j(u|x) α_j(x)`, `q = softmax(s^NN/(2τ))`. -/
def lseMap {J K : ℕ} (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (u : Fin K → ℝ) : Fin K → ℝ :=
  ∑ j, entWeights (lseA β) (lseB α) (2 * τ) u j • α j

/-- Response potential `f_j = 2β_j + ‖α_j‖²`. -/
def lsePot {J K : ℕ} (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) : Fin J → ℝ :=
  fun j => 2 * β j + α j ⬝ᵥ α j

/-- `L^NN_j(ω,x) = 2{Σ_k ω_k β_k − β_j − σ_A(α_j − Σ_k ω_k α_k)}`. -/
def lseWitness {J K : ℕ} (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ))
    (ω : Fin J → ℝ) (j : Fin J) : ℝ :=
  2 * (∑ k, ω k * β k - β j - sSup ((fun u => (α j - ∑ k, ω k • α k) ⬝ᵥ u) '' A))

/-! ### G `lem:stability` -/

section Stability

variable {V 𝒳 : Type*} [MeasurableSpace V] [MeasurableSpace 𝒳]

/-- The Gibbs density `e^{(f(v)+g(x)−c(v,x))/ε}`. -/
def gibbsDens (ε : ℝ) (c : V × 𝒳 → ℝ) (f : V → ℝ) (g : 𝒳 → ℝ) (z : V × 𝒳) : ℝ :=
  Real.exp ((f z.1 + g z.2 - c z) / ε)

/-- The Gibbs plan `dπ = e^{(f ⊕ g − c)/ε} d(μ ⊗ P)`. -/
def gibbsPlan (μ : Measure V) (P : Measure 𝒳) (ε : ℝ) (c : V × 𝒳 → ℝ) (f : V → ℝ) (g : 𝒳 → ℝ) :
    Measure (V × 𝒳) :=
  (μ.prod P).withDensity fun z => ENNReal.ofReal (gibbsDens ε c f g z)

/-- `π = gibbsPlan μ P ε c f g` is an entropic plan in `Π(μ, P)` with bounded measurable potentials. -/
def GibbsHyp (μ : Measure V) (P : Measure 𝒳) (ε : ℝ) (c : V × 𝒳 → ℝ) (f : V → ℝ) (g : 𝒳 → ℝ) :
    Prop :=
  Measurable f ∧ Measurable g ∧ (∃ C, ∀ v, |f v| ≤ C) ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
    (gibbsPlan μ P ε c f g).map Prod.fst = μ ∧ (gibbsPlan μ P ε c f g).map Prod.snd = P

/-- Conditional mean `F(x) = ∫ ψ(v) π(dv|x)`, `π(dv|x) = e^{(f(v)+g(x)−c(v,x))/ε} μ(dv)`. -/
def gibbsMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure V) (ε : ℝ)
    (c : V × 𝒳 → ℝ) (f : V → ℝ) (g : 𝒳 → ℝ) (ψ : V → E) (x : 𝒳) : E :=
  ∫ v, gibbsDens ε c f g (v, x) • ψ v ∂μ

end Stability

namespace Claims

/-! ### C `prop:cond-cal-mondrian` -/

/-- `⌈(n+1)(1−α)⌉ > n ⇔ n < (1−α)/α`, and then `ς̂_{α,j} = +∞`. -/
def mond_threshold_top : Prop :=
  ∀ (n : ℕ) (α : ℝ), 0 < α → α < 1 →
    (n < calIdx n α ↔ (n : ℝ) < (1 - α) / α) ∧
    ∀ (L : Fin (n + 1) → ℕ) (s : Fin (n + 1) → ℝ≥0∞) (j : ℕ),
      cellCount L j < calIdx (cellCount L j) α → mondQ α L s j = ⊤

/-- Conditionally on the cell labels `L` of all `n₂+1` covariates (`P(cells = L) > 0`), the coverage in the new
pair's cell `j = L₀` is at least `⌈(n_j+1)(1−α)⌉/(n_j+1)`. -/
def mond_cell_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) → ∀ (cell : 𝒳 → ℕ)
    (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ExchVec P (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ∀ α : ℝ, 0 < α → α < 1 → ∀ L : Fin (n₂ + 1) → ℕ,
      0 < P {ω | (fun i => cell (X ω i)) = L} →
      MeasurableSet {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
          (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) (L 0))} ∧
      (calIdx (cellCount L (L 0)) α : ℝ≥0∞) / ((cellCount L (L 0) : ℝ≥0∞) + 1) ≤
        cond P {ω | (fun i => cell (X ω i)) = L}
          {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
            (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) (L 0))}

/-- With a.s. distinct scores the cell-conditional coverage equals `⌈(n_j+1)(1−α)⌉/(n_j+1)`. -/
def mond_cell_exact : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) → ∀ (cell : 𝒳 → ℕ)
    (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ExchVec P (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    (∀ᵐ ω ∂P, Function.Injective fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 → ∀ L : Fin (n₂ + 1) → ℕ,
      0 < P {ω | (fun i => cell (X ω i)) = L} →
      cond P {ω | (fun i => cell (X ω i)) = L}
          {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
            (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) (L 0))} =
        (calIdx (cellCount L (L 0)) α : ℝ≥0∞) / ((cellCount L (L 0) : ℝ≥0∞) + 1)

/-- `P{Y_new ∈ B̂^{ς̂_{α,j}}(·|X_new) | X_new ∈ 𝒳_j} ≥ 1 − α` for every cell with `P(X_new ∈ 𝒳_j) > 0`. -/
def mond_coverage_lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) → ∀ (cell : 𝒳 → ℕ)
    (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ExchVec P (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ∀ α : ℝ, 0 < α → α < 1 → ∀ j : ℕ, 0 < P {ω | cell (X ω 0) = j} →
      MeasurableSet {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
          (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) j)} ∧
      ENNReal.ofReal (1 - α) ≤
        cond P {ω | cell (X ω 0) = j}
          {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
            (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) j)}

/-- With a.s. distinct scores the cell coverage is at most `1 − α + E[1/(n_j+1) | X_new ∈ 𝒳_j]`. -/
def mond_coverage_upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 T : Type) (n₂ : ℕ)
    (c w : 𝒳 → T → ℝ), (∀ x t, 0 ≤ w x t) → ∀ (cell : 𝒳 → ℕ)
    (X : Ω → Fin (n₂ + 1) → 𝒳) (Y : Ω → Fin (n₂ + 1) → T → ℝ),
    Measurable (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    ExchVec P (fun ω i => (cell (X ω i), bandScore (c (X ω i)) (w (X ω i)) (Y ω i))) →
    (∀ᵐ ω ∂P, Function.Injective fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) →
    ∀ α : ℝ, 0 < α → α < 1 → ∀ j : ℕ, 0 < P {ω | cell (X ω 0) = j} →
      cond P {ω | cell (X ω 0) = j}
          {ω | Y ω 0 ∈ inflBand (c (X ω 0)) (w (X ω 0))
            (mondQ α (fun i => cell (X ω i)) (fun i => bandScore (c (X ω i)) (w (X ω i)) (Y ω i)) j)} ≤
        ENNReal.ofReal (1 - α) +
          ∫⁻ ω, ((cellCount (fun i => cell (X ω i)) j : ℝ≥0∞) + 1)⁻¹ ∂(cond P {ω | cell (X ω 0) = j})

/-! ### C `cor:witness-reuse` -/

/-- (a) `L_i(ω,x') ≤ δ_i(p|x')` for `ω` in the simplex over `I_{x'}`, `i ∈ I_{x'}`; hence `max{0, L} ≤ δ`. -/
def witness_valid : Prop :=
  ∀ (n K : ℕ) (I : Finset (Fin n)) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (ω : Fin n → ℝ) (i : Fin n),
    IsCompact A → A.Nonempty → i ∈ I → ω ∈ simplexOn I →
      condWitness f Z A ω i ≤ condGapOn I f Z A i ∧ max 0 (condWitness f Z A ω i) ≤ condGapOn I f Z A i

/-- (a) Update formula `L_i(ω,x') = L_i(ω,x) + Σ_k ω_k Δ_k − Δ_i`, `Δ_k = f_k(x') − f_k(x)`. -/
def witness_update : Prop :=
  ∀ (n K : ℕ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n),
    condWitness f' Z A ω i = condWitness f Z A ω i + ∑ k, ω k * (f' k - f k) - (f' i - f i)

/-- (a) Gauge-freeness: `L_i(ω, ·)` is unchanged by `f ↦ f + c𝟏` (`ω` in the simplex). -/
def witness_gauge : Prop :=
  ∀ (n K : ℕ) (f : Fin n → ℝ) (c : ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n),
    ω ∈ simplex n → condWitness (fun k => f k + c) Z A ω i = condWitness f Z A ω i

/-- (b) If `ω` is in the simplex over `I_x` and `ω(J) > 0`, `J = I_x ∩ I_{x'}`, then `ω' = ω𝟏_J/ω(J)` is in the
simplex over `I_{x'}`. -/
def witness_restrict : Prop :=
  ∀ (n : ℕ) (Ix Ix' : Finset (Fin n)) (ω : Fin n → ℝ),
    ω ∈ simplexOn Ix → 0 < ∑ k ∈ Ix ∩ Ix', ω k → restrictW (Ix ∩ Ix') ω ∈ simplexOn Ix'

/-- (b) `σ_i(ω') ≤ σ_i(ω) + 2(1 − ω(J)) r_{K,p} diam{Z_k : k ∈ supp ω}`. -/
def witness_restrict_supp : Prop :=
  ∀ (n K : ℕ) (J : Finset (Fin n)) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n) (r D : ℝ),
    A.Nonempty → (∀ u ∈ A, eucl u ≤ r) → (∀ k l, ω k ≠ 0 → ω l ≠ 0 → eucl (Z k - Z l) ≤ D) →
    ω ∈ simplex n → 0 < ∑ k ∈ J, ω k →
      suppA A (witDir Z (restrictW J ω) i) ≤
        suppA A (witDir Z ω i) + 2 * (1 - ∑ k ∈ J, ω k) * r * D

/-- (b) `L_i(e_i, x') = 0` (the cap `κ_i = 1`). -/
def witness_trivial : Prop :=
  ∀ (n K : ℕ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (i : Fin n),
    A.Nonempty → condWitness f Z A (Pi.single i 1) i = 0

/-- (c) With a common retained set: `δ_i(x') − L_i(ω,x') ≤ [δ_i(x) − L_i(ω,x)] + max_k Δ_k − Σ_k ω_k Δ_k`,
and `max_k Δ_k − Σ_k ω_k Δ_k ≤ 2D_f`. -/
def witness_tight : Prop :=
  ∀ (n K : ℕ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n),
    A.Nonempty → ω ∈ simplex n →
      condGap f' Z A i - condWitness f' Z A ω i ≤
        (condGap f Z A i - condWitness f Z A ω i) +
          ((⨆ k, (f' k - f k)) - ∑ k, ω k * (f' k - f k)) ∧
      (⨆ k, (f' k - f k)) - ∑ k, ω k * (f' k - f k) ≤ 2 * potOsc f f'

/-- (c) For compact convex nonempty `A`: `δ_i(p|x) = max_ω L_i(ω,x)`, the maximum being attained. -/
def witness_minimax : Prop :=
  ∀ (n K : ℕ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (i : Fin n),
    IsCompact A → Convex ℝ A → A.Nonempty →
      (∀ ω ∈ simplex n, condWitness f Z A ω i ≤ condGap f Z A i) ∧
      ∃ ω ∈ simplex n, condWitness f Z A ω i = condGap f Z A i

/-- (c) A witness optimal at `x`, re-evaluated at `x'`, is within `max_k Δ_k − Σ_k ω_k Δ_k ≤ 2D_f` of the exact gap. -/
def witness_reuse_optimal : Prop :=
  ∀ (n K : ℕ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n),
    A.Nonempty → ω ∈ simplex n → condWitness f Z A ω i = condGap f Z A i →
      condGap f' Z A i - condWitness f' Z A ω i ≤ (⨆ k, (f' k - f k)) - ∑ k, ω k * (f' k - f k) ∧
      (⨆ k, (f' k - f k)) - ∑ k, ω k * (f' k - f k) ≤ 2 * potOsc f f'

/-! ### C `prop:lse-certificate` -/

/-- (i) `φ` is convex and `∇_u φ(u;x) = Σ_j softmax_j(s^NN(u|x)/(2τ)) α_j(x)`. -/
def lse_grad : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ),
    0 < J → 0 < τ →
      ConvexOn ℝ univ (lseNet τ α β) ∧ ∀ u, HasFDerivAt (lseNet τ α β) (dotL (lseMap τ α β u)) u

/-- (i) `T` is the entropic out-of-sample map with atoms `α_j`, potential `f_j = 2β_j + ‖α_j‖²` (intercepts
`a_j = 2β_j`) and `ε = 2τ`; and `φ = (ε/2) log Σ_j e^{s^NN_j/ε}`. -/
def lse_is_oos : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ),
    0 < τ →
      lseMap τ α β = condMapEnt (2 * τ) (lsePot α β) α ∧ condA (lsePot α β) α = lseA β ∧
      condB α = lseB α ∧
      ∀ u, lseNet τ α β u = (2 * τ) / 2 * Real.log (∑ j, Real.exp (score (lseA β) (lseB α) j u / (2 * τ)))

/-- (ii) The band supremum of the neural map is attained on `∂A` (`A` compact nonempty, `K ≥ 1`). -/
def lse_sup_attained : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < J → 0 < K → 0 < τ → IsCompact A → A.Nonempty →
      ∃ u' ∈ frontier A, ∀ u ∈ A, v ⬝ᵥ lseMap τ α β u ≤ v ⬝ᵥ lseMap τ α β u'

/-- (ii) Fitted-law validity: for `U ∼ μ_K`, the reconstruction of `T(U,x)` lies in the neural band of
`A_{K,p} = {u ∈ 𝒰 : g u ≤ c_K^{-1}(p)}` with probability at least `p`, simultaneously in `t` (measurable event). -/
def lse_validity : Prop :=
  ∀ (J K : ℕ) (𝒯 Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (τ : ℝ)
    (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (U : Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ)
    (𝒰 : Set (Fin K → ℝ)) (p : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ),
    0 < J → 0 < τ → Measurable U → Continuous g → IsCompact 𝒰 → P.map U 𝒰 = 1 → 0 < p → p ≤ 1 →
      MeasurableSet {ω | curve mo e (lseMap τ α β (U ω)) ∈
        band (fun t => edgeLo (lseMap τ α β) {u | u ∈ 𝒰 ∧ g u ≤ calInv (P.map U) g p} (mo t) (e t))
          (fun t => edgeUp (lseMap τ α β) {u | u ∈ 𝒰 ∧ g u ≤ calInv (P.map U) g p} (mo t) (e t))} ∧
      ENNReal.ofReal p ≤ P {ω | curve mo e (lseMap τ α β (U ω)) ∈
        band (fun t => edgeLo (lseMap τ α β) {u | u ∈ 𝒰 ∧ g u ≤ calInv (P.map U) g p} (mo t) (e t))
          (fun t => edgeUp (lseMap τ α β) {u | u ∈ 𝒰 ∧ g u ≤ calInv (P.map U) g p} (mo t) (e t))}

/-- (ii) `eq:lse-gap-witness`: `δ^NN_j(p|x) ≥ L^NN_j(ω,x)` for every `ω ∈ Δ_J`. -/
def lse_gap_witness : Prop :=
  ∀ (J K : ℕ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin J → ℝ) (j : Fin J),
    IsCompact A → A.Nonempty → ω ∈ simplex J → lseWitness α β A ω j ≤ gap (lseA β) (lseB α) A j

/-- (ii) Caps: for `u ∈ A` and verified `δ̲_j ≤ δ^NN_j`, `q(u|x) ∈ 𝒫_κ`, `κ_j = e^{−δ̲_j/(2τ)}`. -/
def lse_caps : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ)) (δlow : Fin J → ℝ)
    (u : Fin K → ℝ),
    0 < J → 0 < τ → u ∈ A → (∀ j, δlow j ≤ gap (lseA β) (lseB α) A j) →
      entWeights (lseA β) (lseB α) (2 * τ) u ∈ cappedSimplex (fun j => Real.exp (-δlow j / (2 * τ)))

/-- (ii) Outer edges: greedy fills `q⁺` (values `c_j = 𝔪 + ⟨v, α_j⟩`) and `q⁻` (values `−c`) of the capped
simplex give `x̂↑ ≤ Σ q⁺_j c_j` and `Σ q⁻_j c_j ≤ x̂↓` for the neural band. -/
def lse_outer_edges : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ)) (δlow : Fin J → ℝ)
    (mo : ℝ) (v : Fin K → ℝ) (qhi qlo : Fin J → ℝ),
    0 < J → 0 < τ → (∀ j, δlow j ≤ gap (lseA β) (lseB α) A j) →
    IsGreedyFill (fun j => Real.exp (-δlow j / (2 * τ))) (fun j => mo + v ⬝ᵥ α j) qhi →
    IsGreedyFill (fun j => Real.exp (-δlow j / (2 * τ))) (fun j => -(mo + v ⬝ᵥ α j)) qlo →
      edgeUp (lseMap τ α β) A mo v ≤ ((∑ j, qhi j * (mo + v ⬝ᵥ α j) : ℝ) : EReal) ∧
      ((∑ j, qlo j * (mo + v ⬝ᵥ α j) : ℝ) : EReal) ≤ edgeLo (lseMap τ α β) A mo v

/-- (iii) For compact convex nonempty `A`: `δ^NN_j = max_{ω ∈ Δ_J} L^NN_j(ω)`, attained. -/
def lse_minimax : Prop :=
  ∀ (J K : ℕ) (α : Fin J → Fin K → ℝ) (β : Fin J → ℝ) (A : Set (Fin K → ℝ)) (j : Fin J),
    IsCompact A → Convex ℝ A → A.Nonempty →
      ∃ ω ∈ simplex J, lseWitness α β A ω j = gap (lseA β) (lseB α) A j

/-- (iv) `|δ^NN_j(p|x) − δ^NN_j(p|x')| ≤ 4D_β + 2R_p D_α`. -/
def lse_gap_shift : Prop :=
  ∀ (J K : ℕ) (α α' : Fin J → Fin K → ℝ) (β β' : Fin J → ℝ) (A : Set (Fin K → ℝ)) (j : Fin J) (R D : ℝ),
    A.Nonempty → (∀ u ∈ A, eucl u ≤ R) →
    (∀ k l, eucl ((α k - α' k) - (α l - α' l)) ≤ D) →
      |gap (lseA β) (lseB α) A j - gap (lseA β') (lseB α') A j| ≤ 4 * potOsc β β' + 2 * R * D

/-- (iv) `|L^NN_j(ω,x) − L^NN_j(ω,x')| ≤ 4D_β + 2R_p D_α` for every `ω ∈ Δ_J`. -/
def lse_witness_shift : Prop :=
  ∀ (J K : ℕ) (α α' : Fin J → Fin K → ℝ) (β β' : Fin J → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin J → ℝ)
    (j : Fin J) (R D : ℝ),
    A.Nonempty → (∀ u ∈ A, eucl u ≤ R) →
    (∀ k l, eucl ((α k - α' k) - (α l - α' l)) ≤ D) → ω ∈ simplex J →
      |lseWitness α β A ω j - lseWitness α' β' A ω j| ≤ 4 * potOsc β β' + 2 * R * D

/-- (iv) `sup_{u∈A} ‖T(u,x) − T(u,x')‖ ≤ (R_α/τ)(D_β + R_p D_α/2) + Δ_α`. -/
def lse_map_shift : Prop :=
  ∀ (J K : ℕ) (τ : ℝ) (α α' : Fin J → Fin K → ℝ) (β β' : Fin J → ℝ) (A : Set (Fin K → ℝ))
    (R D Rα Δα : ℝ),
    0 < J → 0 < τ → (∀ u ∈ A, eucl u ≤ R) →
    (∀ k l, eucl ((α k - α' k) - (α l - α' l)) ≤ D) → (∀ k, eucl (α k) ≤ Rα) →
    (∀ k, eucl (α k - α' k) ≤ Δα) →
      ∀ u ∈ A, eucl (lseMap τ α β u - lseMap τ α' β' u) ≤ Rα / τ * (potOsc β β' + R * D / 2) + Δα

/-- (iv) With `Δα = 0`: `D_f = 2D_β`. -/
def lse_reduction : Prop :=
  ∀ (J K : ℕ) (α : Fin J → Fin K → ℝ) (β β' : Fin J → ℝ),
    potOsc (lsePot α β) (lsePot α β') = 2 * potOsc β β'

/-! ### G `lem:stability` -/

/-- `eq:pythagoras`: `ε{KL(π'|π) + KL(π|π')} = ∫(c − c') d(π' − π)` (both KLs finite). -/
def stab_pythagoras : Prop :=
  ∀ (V 𝒳 : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] (μ : Measure V) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ)
    (g g' : 𝒳 → ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
      klDiv (gibbsPlan μ P ε c' f' g') (gibbsPlan μ P ε c f g) ≠ ⊤ ∧
      klDiv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g') ≠ ⊤ ∧
      ε * ((klDiv (gibbsPlan μ P ε c' f' g') (gibbsPlan μ P ε c f g)).toReal +
          (klDiv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g')).toReal) =
        ∫ z, (c z - c' z) ∂(gibbsPlan μ P ε c' f' g') - ∫ z, (c z - c' z) ∂(gibbsPlan μ P ε c f g)

/-- (a) If `c − c' = u ⊕ w + ω` with `u ∈ L¹(μ)`, `w ∈ L¹(P)`, `a ≤ ω ≤ b`, then `TV(π, π') ≤ (b − a)/(4ε)`. -/
def stab_tv_osc : Prop :=
  ∀ (V 𝒳 : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] (μ : Measure V) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ)
    (g g' : 𝒳 → ℝ) (u : V → ℝ) (w : 𝒳 → ℝ) (ω : V × 𝒳 → ℝ) (a b : ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
    Integrable u μ → Integrable w P → Measurable ω → (∀ z, ω z ∈ Icc a b) →
    (∀ᵐ z ∂(μ.prod P), c z - c' z = u z.1 + w z.2 + ω z) →
      SBFairness.Stability.tv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g') ≤ (b - a) / (4 * ε)

/-- (a) A separable perturbation (`ω = 0`) does not change the plan. -/
def stab_separable : Prop :=
  ∀ (V 𝒳 : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] (μ : Measure V) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ)
    (g g' : 𝒳 → ℝ) (u : V → ℝ) (w : 𝒳 → ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
    Integrable u μ → Integrable w P → (∀ᵐ z ∂(μ.prod P), c z - c' z = u z.1 + w z.2) →
      gibbsPlan μ P ε c f g = gibbsPlan μ P ε c' f' g'

/-- (b) If `|c − c'| ≤ u ⊕ w` with `u, w ≥ 0` integrable, `TV(π, π') ≤ {(μ(u) + P(w))/(2ε)}^{1/2}`. -/
def stab_tv_integrable : Prop :=
  ∀ (V 𝒳 : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] (μ : Measure V) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ)
    (g g' : 𝒳 → ℝ) (u : V → ℝ) (w : 𝒳 → ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
    Integrable u μ → Integrable w P → (∀ v, 0 ≤ u v) → (∀ x, 0 ≤ w x) →
    (∀ᵐ z ∂(μ.prod P), |c z - c' z| ≤ u z.1 + w z.2) →
      SBFairness.Stability.tv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g') ≤
        Real.sqrt ((∫ v, u v ∂μ + ∫ x, w x ∂P) / (2 * ε))

/-- (c) For a bounded `ψ` (`‖ψ‖ ≤ M` `μ`-a.e.): `∫ ‖F'_ψ(x) − F_ψ(x)‖ dP(x) ≤ 2M TV(π, π')`. -/
def stab_mean : Prop :=
  ∀ (V 𝒳 E : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure V) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ) (g g' : 𝒳 → ℝ) (ψ : V → E) (M : ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
    StronglyMeasurable ψ → (∀ᵐ v ∂μ, ‖ψ v‖ ≤ M) →
      ∫⁻ x, ‖gibbsMean μ ε c' f' g' ψ x - gibbsMean μ ε c f g ψ x‖ₑ ∂P ≤
        ENNReal.ofReal (2 * M * SBFairness.Stability.tv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g'))

/-- (c) Rank maps (`ψ = id`, `‖v‖ ≤ 1` `μ`-a.e.): `∫ ‖F'(x) − F(x)‖ dP(x) ≤ 2 TV(π, π')`. -/
def stab_rank : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] (μ : Measure H) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (ε : ℝ) (c c' : H × 𝒳 → ℝ) (f f' : H → ℝ) (g g' : 𝒳 → ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
      ∫⁻ x, ‖gibbsMean μ ε c' f' g' id x - gibbsMean μ ε c f g id x‖ₑ ∂P ≤
        ENNReal.ofReal (2 * SBFairness.Stability.tv (gibbsPlan μ P ε c f g) (gibbsPlan μ P ε c' f' g'))

/-! ### T fixed-sieve distribution-free hard labels -/

/-- For an iid sample from a law with null affine hyperplanes and distinct reference points, the quadratic optimal
matching is a.s. unique. -/
def hard_unique_ae : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (n : ℕ) (ν : Measure E) [IsProbabilityMeasure ν] (u : Fin n → E),
    Function.Injective u → (∀ a : E, a ≠ 0 → ∀ b : ℝ, ν {z | ⟪a, z⟫_ℝ = b} = 0) →
      ∀ᵐ z ∂(Measure.pi fun _ : Fin n => ν), Ranks.UniqueMin u z

/-- The (Borel-selected) hard rank permutation is uniform over the `n!` permutations. -/
def hard_rank_uniform : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (ν : Measure E) [IsProbabilityMeasure ν] (u : Fin n → E) (Z : Ω → Fin n → E)
    (sel : (Fin n → E) → Equiv.Perm (Fin n)),
    Function.Injective u → (∀ a : E, a ≠ 0 → ∀ b : ℝ, ν {z | ⟪a, z⟫_ℝ = b} = 0) →
    Measurable Z → P.map Z = Measure.pi (fun _ : Fin n => ν) →
    (∀ z, Ranks.IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
      ∀ h, P {ω | sel (Z ω) = h} = (Nat.factorial n : ℝ≥0∞)⁻¹

/-- Labels that are functions of the rank permutation are distribution-free:
`P(ℓ(σ̂) ∈ B) = #{h : ℓ h ∈ B}/n!`. -/
def hard_labels_df : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (ν : Measure E) [IsProbabilityMeasure ν] (u : Fin n → E) (Z : Ω → Fin n → E)
    (sel : (Fin n → E) → Equiv.Perm (Fin n)),
    Function.Injective u → (∀ a : E, a ≠ 0 → ∀ b : ℝ, ν {z | ⟪a, z⟫_ℝ = b} = 0) →
    Measurable Z → P.map Z = Measure.pi (fun _ : Fin n => ν) →
    (∀ z, Ranks.IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
      ∀ (β : Type) (ℓ : Equiv.Perm (Fin n) → β) (B : Set β),
        P {ω | ℓ (sel (Z ω)) ∈ B} =
          (Nat.card {h : Equiv.Perm (Fin n) // ℓ h ∈ B} : ℝ≥0∞) / (Nat.factorial n : ℝ≥0∞)

/-- Conditionally on an independent training sample `W` (the sample is conditionally iid from a hyperplane-null
law `ν_W`), the labels are distribution-free: `P(W ∈ A, ℓ(σ̂) ∈ B) = P(W ∈ A) · #{h : ℓ h ∈ B}/n!`. -/
def hard_labels_conditional : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (Ω 𝒲 : Type) [MeasurableSpace Ω] [MeasurableSpace 𝒲] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (u : Fin n → E) (W : Ω → 𝒲) (Z : Ω → Fin n → E)
    (κ : Kernel 𝒲 (Fin n → E)) [IsMarkovKernel κ] (sel : (Fin n → E) → Equiv.Perm (Fin n)),
    Function.Injective u → Measurable W → Measurable Z →
    P.map (fun ω => (W ω, Z ω)) = (P.map W) ⊗ₘ κ →
    (∀ᵐ w ∂(P.map W), ∃ ν : Measure E, IsProbabilityMeasure ν ∧
      (∀ a : E, a ≠ 0 → ∀ b : ℝ, ν {z | ⟪a, z⟫_ℝ = b} = 0) ∧ κ w = Measure.pi (fun _ : Fin n => ν)) →
    (∀ z, Ranks.IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
      ∀ (A : Set 𝒲), MeasurableSet A → ∀ (β : Type) (ℓ : Equiv.Perm (Fin n) → β) (B : Set β),
        P ({ω | W ω ∈ A} ∩ {ω | ℓ (sel (Z ω)) ∈ B}) =
          P {ω | W ω ∈ A} *
            ((Nat.card {h : Equiv.Perm (Fin n) // ℓ h ∈ B} : ℝ≥0∞) / (Nat.factorial n : ℝ≥0∞))

end Claims
end StatFormal.OTFD.Wave5b
