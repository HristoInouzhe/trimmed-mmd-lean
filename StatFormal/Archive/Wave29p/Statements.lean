import StatFormal.Archive.Wave29m.Statements
import StatFormal.Archive.Wave29b.Statements
import StatFormal.Archive.Wave15b.Statements
import StatFormal.Archive.Wave26b.Statements
import StatFormal.Archive.Wave29a.Statements

/-!
# FROZEN STATEMENTS — wave 29p: otfd C `cor:conditional-uniform-x` (last sentence: self-transport weights,
# supported grids and exact response fits satisfy the uniform premises); B `thm:consistency` (`c'_K = 1/D_∞` for the
# cubic law, the `ϖ_K` modulus bound, the rate transfer); A `thm:consistency` (the printed homeomorphism hypothesis)

Sources (current text of 2026-10-20, `otfd/papers/`):
* C `cor:conditional-uniform-x` (`C_conditional/supplement.tex:2773-2783`, last sentence `:2780-2783`; proof
  `:1149-1156`, last line "The last assertion follows from `thm:self-localization`, `lem:weighted-duality`"), with
  `ass:conditional-oos` (`main.tex:678-685`), `eq:weighted-hard-gap` and `lem:weighted-duality` (`supplement.tex:955-1042`:
  the exact entropic fit "is at least the hard cost", `ζ ≤ r + ε log N`, `|g − χ| ≤ ε log N/2`; quadratic
  `0 ≤ χ − g ≤ λ/4`, `ζ ≤ r^Q + λ/2`), `thm:self-localization` (`main.tex:522-`) and
  `prop:metric-uniform-localization` (`supplement.tex:727-`).
* B `thm:consistency` (`B_bands/supplement.tex:6145-6187`, proof `:6189-6218`): `c'_K = 1/D_∞` for the cubic law, the
  calibrated bound `ϖ_K(c'_K ε_n(𝒦))` ("`ϖ_K` … tends to `0` at `0`. Both right-hand sides therefore tend to `0` almost
  surely"), the rate transfer (`c'_K r_n`, `Lip(c_K) c'_K r_n`).
* A `thm:consistency` (`A_sieves/supplement.tex:5156-5180`) with `thm:app-ghosalsen-rate` (`:2768-2790`: `μ_K ≪ Leb`
  on a compact convex `S_K`, `P_K ≪ Leb` with support `𝒴_K`, "the population quantile map `Q_{+,K} : int S_K →
  int 𝒴_K` is a homeomorphism").
Imports the frozen statement files of waves 29m (`UnifWeightedFit`, and through it WaveL1 `Euc`, `IsCMMapAE`, WaveL4
`WeightedFit`), 29b (`cons_general_M`, and through it Wave 8c `rhoBox`, `mvec`, Wave 22a `IsSubgrad`, WaveP3c
`consistency_A_gs`, `ghosal_sen_uniform`, Tau Ceti `empiricalMeasure`), 15b (`w2sq`, `phiSoft`, `phiHard`, `phiQuad`,
`gQuad`, `chiI`, `posRows`), 26b (`GLq`, `LocModel`, `locEmp`, `entW`, `IsEmpSelfPot`) and 29a (`quadW`, `locEmpQ`,
`IsEmpQuadPot`); not copied. New definitions: `entSemiDual`, `quadSemiDual` (the soft semi-dual values of
`lem:weighted-duality`, as printed), `gEnt` (`(‖·‖² − φ̂)/2`), `modCont` (`ϖ`).

Covered:
* C `cor:conditional-uniform-x`, last sentence (the Wave 29m gap: the uniform gap and fit-closeness clauses):
  `cuxw_ent_exact`, `cuxw_quad_exact` (EXACT entropic / quadratic response fits — maximisers of the soft semi-dual —
  have soft gap `0`, hence hard gap `ε log N`, resp. `λ/2`); `cuxw_unif_entropic`, `cuxw_unif_quadratic` (supported
  grids + `W₁`-uniform weighted targets + fits with uniformly vanishing soft gaps give the frozen `UnifWeightedFit`);
  `cuxw_selfloc_ent`, `cuxw_selfloc_quad` (the FULL discharge: entropic, resp. quadratic, self-transport weights along
  the certified schedules of `prop:metric-uniform-localization` (i) — estimated metric and scale, which include the
  fixed-metric `thm:self-localization` — with supported grids and exact entropic or exact quadratic response fits
  satisfy `UnifWeightedFit` almost surely). With the certified Wave 29m `cux_potentials`/`cux_maps`/`cux_bands`
  (applied per realisation) the corollary holds for these estimators.
* B `thm:consistency`: `consB_cubic_cprime` (`c'_K = 1/D_∞`, maximal on the sphere and smallest constant);
  `consB_cubic_depth` (the certified `cons_general_M` for the cubic gauge, any SPD `M_K`, gauge hypotheses discharged);
  `consB_varpi` (`ϖ_K` nondecreasing, `ϖ_K(δ) → 0` as `δ ↓ 0`, `|D̂^prob − D^prob| ≤ ϖ_K(c'_K e)` for every bound
  `e ≥ sup_𝒦 ‖F̂ − F‖`); `consB_varpi_as` (a.s. both right-hand sides `c'_K ε_n(𝒦)`, `ϖ_K(c'_K ε_n(𝒦)) → 0` and
  eventually bound the depth errors uniformly); `consB_rate` (an a.s. rate `ε_n = O(r_n)` transfers as `c'_K C r_n`
  and `L_c c'_K C r_n`).
* A `thm:consistency` under the PRINTED homeomorphism hypothesis: `consA_homeo` (no differentiability hypothesis;
  `F = Q⁻¹` a.e., `ψ` differentiable on `int 𝒴_K` with gradient `Q⁻¹`, and a.s. `F̂_n → Q⁻¹` uniformly on `𝒦` and
  depth convergence uniformly over `{x : Π_K x ∈ 𝒦}`).

Not covered (declared):
* C: existence of exact fits (maximisers of the soft semi-duals; standard — `J^E` is concave with first-order
  conditions solvable, e.g. explicitly for one grid point — not formalised); the n_eff clause of
  `prop:metric-uniform-localization` (not needed by `UnifWeightedFit`); fits with nonzero soft residuals along the
  self-transport schedules (covered by `cuxw_unif_*` given the `W₁` clause, not restated with the schedules).
* B: the printed homeomorphism hypothesis for general `M_K` (the frozen `cons_general_M` keeps "`ψ` differentiable on
  `𝒦` with gradient `M_K F`"; the `consA_homeo` argument transfers through `L = M_K^{1/2}`, not done); `ϖ_K` for
  CDFs that are not constant outside a compact interval (not needed: all three gauges are bounded on the reference
  support).
* A: compactness and nonempty interior of `S_K` are not used (generalisation); the moment-free uniqueness needs only
  `μ_K` carried by `B̄(0, M)` (frozen hypothesis kept).

Encodings (to be checked by the critic):
* Exact fits: `∀ f', J(f') ≤ J(f)` with `J = entSemiDual` (log-mean-exp gauge on `I = {w > 0}`, the frozen
  `phiSoft`) or `quadSemiDual` (frozen `phiQuad`, `λ > 0`); "soft gap `r`" is the frozen Wave 15b form
  `W₂² − r ≤ J(f)`. Grid weights `β ≥ 0`, `Σβ = 1` (C: `b_j = 1/m`; generalisation).
* `cuxw_unif_*`: one grid for all queries (as printed), `W₁(μ_{K,m_n}, μ_K) → 0` (`W₁` the Tau Ceti extended
  distance); per-query atomic targets on a common response sample `Z_{n,·}` with weights `w_{n,·}(x)`; the
  `W₁`-uniform target clause is an INPUT here (it is the third conjunct of `UnifWeightedFit` verbatim) and is
  DISCHARGED in `cuxw_selfloc_*`. The grid clause (`W₁(μ_{K,m_n}, μ_K) → 0`, grids in `𝒰_K`) is an input in all four
  `cuxw_unif_*`/`cuxw_selfloc_*` claims and reappears as the second conjunct of `UnifWeightedFit` (the grid does not
  depend on `x`): "supported grids" are grids satisfying the grid premise of `ass:conditional-oos`, as printed. Soft residuals bounded uniformly in `x` by `r_n ≥ 0`, `r_n → 0`; strengths `ε_n > 0`
  with `ε_n log N_n → 0` (C: `ε_n log n → 0`, `N_n = n`), resp. `λ_n ≥ 0`, `λ_n → 0` (C: `λ_n = γ_n/m_n`). Output
  potentials: `χ_{n,x} = chiI (posRows w)` (frozen), `g = (‖·‖² − φ̂)/2`, resp. the frozen `gQuad`; gaps
  `ζ_{n,x} = r_n + ε_n log N_n`, resp. `r_n + λ_n/2`.
* `cuxw_selfloc_*`: sample size `n + 1` at index `n` (avoids the empty sample; a reindexing); the targets `ν` are
  probability measures EQUAL to the frozen `locEmp`/`locEmpQ` (satisfiable: the weights are probability vectors,
  proved in the route); `D₀ ⊆ D_X = supp P_X` (as printed: `D₀ ⊂ D`, `D = supp P_C`, `main.tex:507`; no compactness
  needed); `P_{K,x} = κ x`; the strengths and metrics
  quantified exactly as in the frozen `metric_uniform_localization`/`metricloc_quad_uniform` (i); for the quadratic
  weights the scales are POSITIVE everywhere (`ŝ_n > 0`, as printed in `prop:metric-uniform-localization` (i),
  `supplement.tex:740`; needed for `quadW` to be a probability vector at every `n`, hence for exact fits to exist; the
  frozen claim allows arbitrary `ŝ_n` outside the eventual compact subset of `(0, ∞)`).
* `modCont c δ = sSup {|c s − c t| : |s − t| ≤ δ}` (real `sSup` of a nonempty bounded set for `δ ≥ 0` under the
  hypotheses; arguments used are `≥ 0`); "`c_K` extended by `1` above its range" is "`c_K` constant below `a` and
  above `b`". `c'_K ≥ 0` is assumed in `consB_varpi*`, `consB_rate` (needed at `K = 0`; automatic for `K ≥ 1`).
  `ε_n(𝒦) = sSup` of the image of `𝒦` (real `sSup`, proved to be of a bounded set eventually; `0` for `𝒦 = ∅`).
  The rate: `∃ C`, a.s. eventually `sup_𝒦 ‖F̂_n − F‖ ≤ C r_n`; Lipschitz `c_K`: `|c_K s − c_K t| ≤ L_c|s − t|`.
* `consA_homeo`: the homeomorphism `Q : int S_K → int 𝒴_K` is `ContinuousOn Q (int S)`, `ContinuousOn G (int 𝒴)`,
  `MapsTo` both ways and mutually inverse (`𝒴 = supp P_K`); `Q` the population quantile map (Borel, `Q#μ = P`,
  `μ`-a.e. cyclically monotone — "optimal"); `μ ≪ Leb` carried by a convex `S`. The conclusion is stated for the
  continuous version `G = Q⁻¹` of the rank map (see Paper notes (3)).

Proof notes (untrusted; `#print axioms`: propext, Classical.choice, Quot.sound for all 12 claims):
* Library `Foundations/ExactFits/{Entropic,Quadratic}.lean`: at a maximiser the derivative along `f + t e_i` vanishes
  (entropic: explicit `HasDerivAt` of log-sum-exp; quadratic: the `λ`-strong concavity bound
  `t q⋆_i ≤ 2g_{f+te_i} − 2g_f ≤ t q⋆_i + t²/(2λ)`, no derivative), so the Gibbs (resp. simplex-maximiser) plan has the
  target marginals; its cost is `J(f) − ε Σ_j β_j KL(g_j ‖ Unif(I)) ≤ J(f)` (resp. `≤ J(f) − (λ/2)Σβ_j‖q⋆_j‖²`).
* Routes `RouteCuxw` (the certified Wave 15b `weighted_entropic`, `weighted_quadratic`, Wave 26b
  `metric_uniform_localization`, Wave 29a `metricloc_quad_uniform`, library `UniformQuery/W1Weak`), `RouteConsB`
  (certified Wave 29b `cons_general_M`; Heine–Cantor for `ϖ`), `RouteConsA` (certified WaveL7
  `brenierUniq_of_bdd_target`, WaveP3c `ghosal_sen_uniform`, `consistency_A_gs`; Mathlib `Convex.addHaar_frontier`).
* No tautology: no conclusion is a hypothesis except the declared `W₁` target clause of `cuxw_unif_*` and the grid
  clause of `cuxw_unif_*`/`cuxw_selfloc_*` (declared under Encodings). No junk: `Measure.map`
  only of Borel maps; `sSup`s as above; `Real.log` of cardinalities `≥ 1` or of `n + 1`.
* Nonvacuity: `cuxw_*` — exact fits exist whenever `w` is a probability vector (both semi-duals are concave,
  invariant under `f ↦ f + c`, and tend to `−∞` on `{max_I f = 0}` as some `f_i → −∞`, `i ∈ I`, since
  `φ̂, φ^Q ≤ ‖u − Z_{i⋆}‖² − f_{i⋆} + (ε log N, resp. λ/2)`; the entropic and quadratic self-transport weights are
  probability vectors — softmax, resp. `quadW` with `ŝ_n > 0`). One grid point `u` (`m = 1`): entropic
  `f_i = ‖u − Z_i‖² + ε log w_i` on `I` (Gibbs weights `= w`, zero gradient); quadratic
  `f_i = λ w_i + ‖Z_i‖² − 2⟨Z_i, u⟩` on `I` (scores `s_i(u) = λ w_i`, simplex maximiser `q⋆ = w`); the localisation hypotheses are the frozen ones (nonvacuous, Wave 26b/29a cards); `consB_*` — the cubic
  law; `consA_homeo` — Ghosal–Sen Prop. 3.1 (uniform law on a box, as A remarks).

Paper notes:
(1) C `cor:conditional-uniform-x`: the last sentence holds as printed. Uniformity of the gap and fit clauses is
  automatic because the bounds `ε_n log N ≤ ε_n log n`, `λ_n/2`, `ε_n log N/2`, `λ_n/4` do not depend on `x`; only the
  `W₁` clause needs `thm:self-localization`. "Exact" is used in the strong sense (maximiser of the soft semi-dual
  in the log-mean-exp gauge on `I_{n,x}`); its zero soft gap follows from the first-order conditions alone (no duality
  theorem). The two side conditions used — query set in `D_X` and positive scales — are both printed (`D₀ ⊂ D`,
  `D = supp P_C`; `ŝ_n > 0`); no manuscript change is needed.
(2) B `thm:consistency`: confirmed as printed (`c'_K = 1/D_∞` for every `M_K`; `ϖ_K` finite and `→ 0` because `c_K`
  is continuous and constant outside a compact interval; the rate transfer is the deterministic bound).
(3) A `thm:consistency`: the printed homeomorphism DOES give the differentiability used by the frozen WaveP3c claims —
  for the continuous version `G = Q_{+,K}^{-1}` of the rank map: `F = G` `P_K`-a.e. (McCann uniqueness, `Q` optimal),
  `G(y) ∈ ∂ψ(y)` at every `y ∈ int 𝒴_K` (density of `P_K`-a.e. points in `int 𝒴_K ⊆ supp P_K`, closed subdifferential
  graph), and then `ψ` is differentiable on `int 𝒴_K`. It does not hold for an arbitrary a.e.-version of `F` (changing
  `F` at one point of `𝒦` breaks uniform convergence on `𝒦`), and it would fail if `Q` were a homeomorphism not linked to
  `F` by optimality. A defines `F_{+,K} = ∇φ_K` (`main.tex:335-337`, taken on the differentiability set,
  `supplement.tex:1866`); on `int 𝒴_K` this gradient is canonical (two potentials with a.e.-equal gradients differ
  by a locally constant function there) and, by the argument above, defined everywhere and equal to `Q_{+,K}^{-1}`.
  So the printed statement is correct with A's own convention; the a.e.-version issue is one of the frozen Lean
  encoding (an arbitrary measurable `F`). An optional clarifying clause (not a defect): "(under these conditions
  `φ_K` is differentiable on `int 𝒴_K` and `F_{+,K}=\nabla\varphi_K=Q_{+,K}^{-1}` there)".
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29p

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.Wave29m (UnifWeightedFit)
open StatFormal.Wave15b (w2sq phiSoft phiHard phiQuad gQuad chiI posRows)
open StatFormal.Wave26b (GLq LocModel locEmp entW IsEmpSelfPot)
open StatFormal.Wave29a (quadW locEmpQ IsEmpQuadPot)
open StatFormal.OTFD.Wave8c (rhoBox mvec)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open TauCeti.Probability (empiricalMeasure)

/-! ### Definitions -/

/-- The entropic soft semi-dual value of C `lem:weighted-duality` (log-mean-exp gauge on the retained rows
`I = {i : w_i > 0}`): `J^E(f) = Σ_j β_j φ̂_f(u_j) + Σ_i w_i f_i`, `φ̂` the frozen Wave 15b `phiSoft`. -/
def entSemiDual {K m n : ℕ} (ε : ℝ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) : ℝ :=
  ∑ j, β j * phiSoft ε (posRows w) Z f (ug j) + ∑ i, w i * f i

/-- The quadratic soft semi-dual value: `J^Q(f) = Σ_j β_j φ^Q_f(u_j) + Σ_i w_i f_i`, `φ^Q` the frozen Wave 15b
`phiQuad` (`‖u‖² − 2g`, `g = gQuad`). -/
def quadSemiDual {K m n : ℕ} (lam : ℝ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) : ℝ :=
  ∑ j, β j * phiQuad lam (posRows w) Z f (ug j) + ∑ i, w i * f i

/-- The entropic fitted potential `g = (‖·‖² − φ̂)/2` (C `lem:weighted-duality`). -/
def gEnt {K n : ℕ} (ε : ℝ) (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  (‖u‖ ^ 2 - phiSoft ε I Z f u) / 2

/-- The modulus of continuity `ϖ(δ) = sup{|c(s) − c(t)| : |s − t| ≤ δ}` of `c : ℝ → ℝ` (B `thm:consistency`; a real
`sSup`, of a nonempty set for `δ ≥ 0`, bounded when `c` is bounded — both hold where it is used). -/
def modCont (c : ℝ → ℝ) (δ : ℝ) : ℝ := sSup {e | ∃ s t : ℝ, |s - t| ≤ δ ∧ e = |c s - c t|}

namespace Claims

/-! #### C `cor:conditional-uniform-x`, last sentence: exact response fits -/

/-- C `lem:weighted-duality`, "for an exact entropic fit … its soft semi-dual value … is at least the hard cost":
if the dual vector `f` maximises the entropic soft semi-dual `J^E` (an exact entropic response fit, any grid weights
`β ≥ 0` summing to one), then `W₂²(μ_{K,m}, P̂_{K,n,x}) ≤ J^E(f)` (soft gap `r = 0`), and hence the hard semi-dual
gap `eq:weighted-hard-gap` holds with `ζ = ε log N`, `N = |{i : w_i > 0}|`. -/
def cuxw_ent_exact : Prop :=
  ∀ (K m n : ℕ) (ε : ℝ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ),
    0 < ε → (∀ j, 0 ≤ β j) → ∑ j, β j = 1 → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
    (∀ f' : Fin n → ℝ, entSemiDual ε β ug w Z f' ≤ entSemiDual ε β ug w Z f) →
      w2sq β ug w Z ≤ entSemiDual ε β ug w Z f ∧
      w2sq β ug w Z - ε * Real.log (posRows w).card ≤
        ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i

/-- C `lem:weighted-duality`, quadratic: if `f` maximises the quadratic soft semi-dual `J^Q` at strength `λ > 0` (an
exact quadratic response fit), then `W₂² ≤ J^Q(f)` (soft gap `r^Q = 0`), and hence `eq:weighted-hard-gap` holds with
`ζ = λ/2`. -/
def cuxw_quad_exact : Prop :=
  ∀ (K m n : ℕ) (lam : ℝ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ),
    0 < lam → (∀ j, 0 ≤ β j) → ∑ j, β j = 1 → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
    (∀ f' : Fin n → ℝ, quadSemiDual lam β ug w Z f' ≤ quadSemiDual lam β ug w Z f) →
      w2sq β ug w Z ≤ quadSemiDual lam β ug w Z f ∧
      w2sq β ug w Z - lam / 2 ≤ ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i

/-! #### C `cor:conditional-uniform-x`, last sentence: the uniform gap and fit-closeness clauses -/

/-- Supported grids, `W₁`-uniform weighted targets and entropic response fits with uniformly vanishing soft gaps
satisfy the uniform-in-`x` premises (`UnifWeightedFit`, frozen Wave 29m): grids `μ_{K,m_n} = Σ_j β_{n,j} δ_{u_{n,j}}`
in `𝒰_K` with `W₁(μ_{K,m_n}, μ_K) → 0` (one grid for all queries, as printed); at each query `x ∈ D₀` a weighted
target `P̂_{K,n,x} = Σ_i w_{n,i}(x) δ_{Z_{n,i}}` with `sup_{x∈D₀} W₁(P̂_{K,n,x}, P_{K,x}) → 0`; entropic dual vectors
`f_n(x)` with soft semi-dual gaps `≤ r_n` uniformly in `x` (`r_n ≥ 0`, `r_n → 0`) and `ε_n log N_n → 0`. Then
`UnifWeightedFit` holds with the Laguerre potentials `χ_{n,x}`, the fitted potentials `g_{n,x} = (‖·‖² − φ̂)/2` and the
gaps `ζ_{n,x} = r_n + ε_n log N_n`. -/
def cuxw_unif_entropic : Prop :=
  ∀ (K : ℕ) (X : Type) (D0 : Set X) (μ : ProbabilityMeasure (Euc K)) (P : X → ProbabilityMeasure (Euc K))
    (U : Set (Euc K)) (α : ℕ → ProbabilityMeasure (Euc K)) (m : ℕ → ℕ) (β : (n : ℕ) → Fin (m n) → ℝ)
    (ug : (n : ℕ) → Fin (m n) → Euc K) (N : ℕ → ℕ) (ν : ℕ → X → ProbabilityMeasure (Euc K))
    (w : (n : ℕ) → X → Fin (N n) → ℝ) (Z : (n : ℕ) → Fin (N n) → Euc K) (εf r : ℕ → ℝ)
    (f : (n : ℕ) → X → Fin (N n) → ℝ),
    (∀ n, (∀ j, 0 ≤ β n j) ∧ ∑ j, β n j = 1 ∧ ∀ j, ug n j ∈ U) →
    (∀ n, (α n : Measure (Euc K)) = ∑ j, ENNReal.ofReal (β n j) • Measure.dirac (ug n j)) →
    Tendsto (fun n => TauCeti.wassersteinEDist 1 (α n : Measure (Euc K)) (μ : Measure (Euc K))) atTop (𝓝 0) →
    (∀ n, ∀ x ∈ D0, (∀ i, 0 ≤ w n x i) ∧ ∑ i, w n x i = 1 ∧
      (ν n x : Measure (Euc K)) = ∑ i, ENNReal.ofReal (w n x i) • Measure.dirac (Z n i)) →
    (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0,
      TauCeti.wassersteinEDist 1 (ν n x : Measure (Euc K)) (P x : Measure (Euc K)) ≤ ε) →
    (∀ n, 0 < εf n) → Tendsto (fun n => εf n * Real.log (N n)) atTop (𝓝 0) →
    (∀ n, 0 ≤ r n) → Tendsto r atTop (𝓝 0) →
    (∀ n, ∀ x ∈ D0, w2sq (β n) (ug n) (w n x) (Z n) - r n ≤ entSemiDual (εf n) (β n) (ug n) (w n x) (Z n) (f n x)) →
      UnifWeightedFit D0 μ P U (fun n _ => α n) ν (fun n x => chiI (posRows (w n x)) (Z n) (f n x))
        (fun n x => gEnt (εf n) (posRows (w n x)) (Z n) (f n x)) (fun n _ => r n + εf n * Real.log (N n))

/-- The same with quadratic response fits: soft gaps `≤ r_n` uniformly in `x` and `λ_n = γ_n/m_n → 0` (`λ_n ≥ 0`);
`UnifWeightedFit` holds with `g_{n,x}` the frozen `gQuad` and `ζ_{n,x} = r_n + λ_n/2`. -/
def cuxw_unif_quadratic : Prop :=
  ∀ (K : ℕ) (X : Type) (D0 : Set X) (μ : ProbabilityMeasure (Euc K)) (P : X → ProbabilityMeasure (Euc K))
    (U : Set (Euc K)) (α : ℕ → ProbabilityMeasure (Euc K)) (m : ℕ → ℕ) (β : (n : ℕ) → Fin (m n) → ℝ)
    (ug : (n : ℕ) → Fin (m n) → Euc K) (N : ℕ → ℕ) (ν : ℕ → X → ProbabilityMeasure (Euc K))
    (w : (n : ℕ) → X → Fin (N n) → ℝ) (Z : (n : ℕ) → Fin (N n) → Euc K) (lam r : ℕ → ℝ)
    (f : (n : ℕ) → X → Fin (N n) → ℝ),
    (∀ n, (∀ j, 0 ≤ β n j) ∧ ∑ j, β n j = 1 ∧ ∀ j, ug n j ∈ U) →
    (∀ n, (α n : Measure (Euc K)) = ∑ j, ENNReal.ofReal (β n j) • Measure.dirac (ug n j)) →
    Tendsto (fun n => TauCeti.wassersteinEDist 1 (α n : Measure (Euc K)) (μ : Measure (Euc K))) atTop (𝓝 0) →
    (∀ n, ∀ x ∈ D0, (∀ i, 0 ≤ w n x i) ∧ ∑ i, w n x i = 1 ∧
      (ν n x : Measure (Euc K)) = ∑ i, ENNReal.ofReal (w n x i) • Measure.dirac (Z n i)) →
    (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0,
      TauCeti.wassersteinEDist 1 (ν n x : Measure (Euc K)) (P x : Measure (Euc K)) ≤ ε) →
    (∀ n, 0 ≤ lam n) → Tendsto lam atTop (𝓝 0) →
    (∀ n, 0 ≤ r n) → Tendsto r atTop (𝓝 0) →
    (∀ n, ∀ x ∈ D0, w2sq (β n) (ug n) (w n x) (Z n) - r n ≤ quadSemiDual (lam n) (β n) (ug n) (w n x) (Z n) (f n x)) →
      UnifWeightedFit D0 μ P U (fun n _ => α n) ν (fun n x => chiI (posRows (w n x)) (Z n) (f n x))
        (fun n x => gQuad (lam n) (posRows (w n x)) (Z n) (f n x)) (fun n _ => r n + lam n / 2)

/-! #### C `cor:conditional-uniform-x`, last sentence: self-transport weights (the full discharge) -/

/-- C `cor:conditional-uniform-x`, last sentence, ENTROPIC self-transport weights (`thm:self-localization`, also with
an estimated metric, `prop:metric-uniform-localization`): in the standing model `LocModel` (frozen Wave 26b) there
is a deterministic localisation schedule `ε_{X,n} ↓ 0` such that, for any empirical self-potentials, any metrics
`Λ̂_n` and scales `ŝ_n` admissible as in the frozen `metric_uniform_localization` (eventually in a compact subset of
`GL_q × (0,∞)`, or convergent there), every query set `D₀ ⊆ D_X`, every supported grid with `W₁(μ_{K,m_n}, μ_K) → 0`,
and the self-transport weighted targets `P̂_{K,n,x} = P̂^E_{K,n,x}[Λ̂_n, ŝ_n ε_{X,n}]` (sample size `n + 1`):
(a) EXACT entropic response fits (maximisers of `J^E` at every `x ∈ D₀`) with `ε_n log(n+1) → 0`, and
(b) EXACT quadratic response fits (maximisers of `J^Q`) with `0 < λ_n → 0`,
satisfy, almost surely, the uniform premises `UnifWeightedFit` (with `ζ_{n,x} = ε_n log(n+1)`, resp. `λ_n/2`). -/
def cuxw_selfloc_ent : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel Pr PX κ R Xs Zs →
    ∃ εX : ℕ → ℝ, (∀ n, 0 < εX n) ∧ Antitone εX ∧ Tendsto εX atTop (𝓝 0) ∧
      ∀ Fn : (n : ℕ) → GLq q → ℝ → Ω → Fin n → ℝ,
        (∀ n Λ ε ω, 0 < ε → IsEmpSelfPot Λ ε (fun i : Fin n => Xs i ω) (Fn n Λ ε ω)) →
      ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ),
        ((∀ᵐ ω ∂Pr, ∃ Cs : Set (GLq q × ℝ), IsCompact Cs ∧ (∀ p ∈ Cs, 0 < p.2) ∧
            ∀ᶠ n in atTop, (Λh n ω, sh n ω) ∈ Cs) ∨
          (∀ᵐ ω ∂Pr, ∃ (Λ : GLq q) (s : ℝ), 0 < s ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ, s)))) →
      ∀ (D0 : Set (Euc q)) (μ : ProbabilityMeasure (Euc K)) (P : Euc q → ProbabilityMeasure (Euc K))
        (U : Set (Euc K)) (α : ℕ → ProbabilityMeasure (Euc K)) (m : ℕ → ℕ) (β : (n : ℕ) → Fin (m n) → ℝ)
        (ug : (n : ℕ) → Fin (m n) → Euc K) (ν : ℕ → Ω → Euc q → ProbabilityMeasure (Euc K)),
        D0 ⊆ PX.support → (∀ x, (P x : Measure (Euc K)) = κ x) →
        (∀ n, (∀ j, 0 ≤ β n j) ∧ ∑ j, β n j = 1 ∧ ∀ j, ug n j ∈ U) →
        (∀ n, (α n : Measure (Euc K)) = ∑ j, ENNReal.ofReal (β n j) • Measure.dirac (ug n j)) →
        Tendsto (fun n => TauCeti.wassersteinEDist 1 (α n : Measure (Euc K)) (μ : Measure (Euc K))) atTop (𝓝 0) →
        (∀ n ω x, (ν n ω x : Measure (Euc K)) =
          locEmp (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) (fun i : Fin (n + 1) => Xs i ω) (fun i => Zs i ω)
            (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x) →
        (∀ (εf : ℕ → ℝ) (f : (n : ℕ) → Ω → Euc q → Fin (n + 1) → ℝ),
          (∀ n, 0 < εf n) → Tendsto (fun n => εf n * Real.log ((n : ℝ) + 1)) atTop (𝓝 0) →
          (∀ n ω, ∀ x ∈ D0, ∀ f' : Fin (n + 1) → ℝ,
            entSemiDual (εf n) (β n) (ug n)
                (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x) (fun i => Zs i ω) f' ≤
              entSemiDual (εf n) (β n) (ug n)
                (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x) (fun i => Zs i ω) (f n ω x)) →
          ∀ᵐ ω ∂Pr, UnifWeightedFit D0 μ P U (fun n _ => α n) (fun n x => ν n ω x)
            (fun n x => chiI (posRows (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n x => gEnt (εf n) (posRows (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n _ => εf n * Real.log ((n : ℝ) + 1))) ∧
        (∀ (lam : ℕ → ℝ) (f : (n : ℕ) → Ω → Euc q → Fin (n + 1) → ℝ),
          (∀ n, 0 < lam n) → Tendsto lam atTop (𝓝 0) →
          (∀ n ω, ∀ x ∈ D0, ∀ f' : Fin (n + 1) → ℝ,
            quadSemiDual (lam n) (β n) (ug n)
                (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x) (fun i => Zs i ω) f' ≤
              quadSemiDual (lam n) (β n) (ug n)
                (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x) (fun i => Zs i ω) (f n ω x)) →
          ∀ᵐ ω ∂Pr, UnifWeightedFit D0 μ P U (fun n _ => α n) (fun n x => ν n ω x)
            (fun n x => chiI (posRows (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n x => gQuad (lam n) (posRows (entW (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Fn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * εX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n _ => lam n / 2))

/-- C `cor:conditional-uniform-x`, last sentence, QUADRATIC self-transport weights (`eq:self-quad-weights`, also with
an estimated metric; frozen Wave 29a `metricloc_quad_uniform`): in `LocModel` there is a deterministic schedule
`η_n ↓ 0` with `nη_n/log n → ∞` such that, for the empirical quadratic self-potentials, admissible metrics `Λ̂_n` and
POSITIVE scales `ŝ_n`, every `D₀ ⊆ D_X`, every supported grid and the quadratic self-transport targets
`P̂^Q_{K,n,x}[Λ̂_n, ŝ_n η_n]` (sample size `n + 1`), exact entropic (`ε_n log(n+1) → 0`) and exact quadratic
(`0 < λ_n → 0`) response fits satisfy `UnifWeightedFit` almost surely. -/
def cuxw_selfloc_quad : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel Pr PX κ R Xs Zs →
    ∃ ηX : ℕ → ℝ, (∀ n, 0 < ηX n) ∧ Antitone ηX ∧ Tendsto ηX atTop (𝓝 0) ∧
      (∀ C : ℝ, ∀ᶠ n : ℕ in atTop, C * Real.log (n : ℝ) ≤ n * ηX n) ∧
      ∀ Hn : (n : ℕ) → GLq q → ℝ → Ω → Euc q → ℝ,
        (∀ n Λ η ω, 0 < n → 0 < η → IsEmpQuadPot Λ η (fun i : Fin n => Xs i ω) (Hn n Λ η ω)) →
      ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ), (∀ n ω, 0 < sh n ω) →
        ((∀ᵐ ω ∂Pr, ∃ Cs : Set (GLq q × ℝ), IsCompact Cs ∧ (∀ p ∈ Cs, 0 < p.2) ∧
            ∀ᶠ n in atTop, (Λh n ω, sh n ω) ∈ Cs) ∨
          (∀ᵐ ω ∂Pr, ∃ (Λ : GLq q) (s : ℝ), 0 < s ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ, s)))) →
      ∀ (D0 : Set (Euc q)) (μ : ProbabilityMeasure (Euc K)) (P : Euc q → ProbabilityMeasure (Euc K))
        (U : Set (Euc K)) (α : ℕ → ProbabilityMeasure (Euc K)) (m : ℕ → ℕ) (β : (n : ℕ) → Fin (m n) → ℝ)
        (ug : (n : ℕ) → Fin (m n) → Euc K) (ν : ℕ → Ω → Euc q → ProbabilityMeasure (Euc K)),
        D0 ⊆ PX.support → (∀ x, (P x : Measure (Euc K)) = κ x) →
        (∀ n, (∀ j, 0 ≤ β n j) ∧ ∑ j, β n j = 1 ∧ ∀ j, ug n j ∈ U) →
        (∀ n, (α n : Measure (Euc K)) = ∑ j, ENNReal.ofReal (β n j) • Measure.dirac (ug n j)) →
        Tendsto (fun n => TauCeti.wassersteinEDist 1 (α n : Measure (Euc K)) (μ : Measure (Euc K))) atTop (𝓝 0) →
        (∀ n ω x, (ν n ω x : Measure (Euc K)) =
          locEmpQ (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) (fun i : Fin (n + 1) => Xs i ω) (fun i => Zs i ω)
            (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x) →
        (∀ (εf : ℕ → ℝ) (f : (n : ℕ) → Ω → Euc q → Fin (n + 1) → ℝ),
          (∀ n, 0 < εf n) → Tendsto (fun n => εf n * Real.log ((n : ℝ) + 1)) atTop (𝓝 0) →
          (∀ n ω, ∀ x ∈ D0, ∀ f' : Fin (n + 1) → ℝ,
            entSemiDual (εf n) (β n) (ug n)
                (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x) (fun i => Zs i ω) f' ≤
              entSemiDual (εf n) (β n) (ug n)
                (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x) (fun i => Zs i ω) (f n ω x)) →
          ∀ᵐ ω ∂Pr, UnifWeightedFit D0 μ P U (fun n _ => α n) (fun n x => ν n ω x)
            (fun n x => chiI (posRows (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n x => gEnt (εf n) (posRows (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n _ => εf n * Real.log ((n : ℝ) + 1))) ∧
        (∀ (lam : ℕ → ℝ) (f : (n : ℕ) → Ω → Euc q → Fin (n + 1) → ℝ),
          (∀ n, 0 < lam n) → Tendsto lam atTop (𝓝 0) →
          (∀ n ω, ∀ x ∈ D0, ∀ f' : Fin (n + 1) → ℝ,
            quadSemiDual (lam n) (β n) (ug n)
                (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x) (fun i => Zs i ω) f' ≤
              quadSemiDual (lam n) (β n) (ug n)
                (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) (fun i : Fin (n + 1) => Xs i ω)
                  (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x) (fun i => Zs i ω) (f n ω x)) →
          ∀ᵐ ω ∂Pr, UnifWeightedFit D0 μ P U (fun n _ => α n) (fun n x => ν n ω x)
            (fun n x => chiI (posRows (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n x => gQuad (lam n) (posRows (quadW (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1))
              (fun i : Fin (n + 1) => Xs i ω) (Hn (n + 1) (Λh (n + 1) ω) (sh (n + 1) ω * ηX (n + 1)) ω) x))
              (fun i => Zs i ω) (f n ω x))
            (fun n _ => lam n / 2))


/-! #### B `thm:consistency`: `c'_K = 1/D_∞` for the cubic law, the modulus `ϖ_K`, the rate transfer -/

/-- B `thm:consistency`, "`c'_K := max_{‖u‖₂=1} g_K(u)` … is `1/D_∞` for the cubic law, the smallest constant with
`g_K ≤ c'_K‖·‖₂`": for the cubic gauge `g_K = ρ_box = ‖·‖₂/D_∞` (frozen Wave 8c `rhoBox`, `prop:calibrations`(c);
independent of `M_K`), `1/D_∞` is the maximum of `g_K` on the Euclidean unit sphere, and `g_K ≤ c‖·‖₂` iff
`c ≥ 1/D_∞` (`K ≥ 1`, `D_∞ > 0`). -/
def consB_cubic_cprime : Prop :=
  ∀ (K : ℕ) (Dinf : ℝ), 0 < K → 0 < Dinf →
    IsGreatest {c | ∃ u : Fin K → ℝ, Real.sqrt (∑ k, u k ^ 2) = 1 ∧ c = rhoBox Dinf u} (1 / Dinf) ∧
      ∀ c : ℝ, (∀ u : Fin K → ℝ, rhoBox Dinf u ≤ c * Real.sqrt (∑ k, u k ^ 2)) ↔ 1 / Dinf ≤ c

/-- B `thm:consistency` for the CUBIC law, any symmetric positive definite `M_K`: the conclusions of the frozen Wave 29b
`cons_general_M` (deterministic geometric depth bound, a.s. `ε_n(𝒦) → 0`, uniform convergence of both depths) with
the cubic gauge `g_K = ρ_box` (frozen Wave 8c, read on `ℝ^K` coordinates) and `c'_K = 1/D_∞` — the gauge hypotheses of
`cons_general_M` (subadditive, symmetric, `g_K ≤ c'_K‖·‖₂`) discharged. -/
def consB_cubic_depth : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (MK : Matrix (Fin K) (Fin K) ℝ) (ψ : Euc K → ℝ) (F : Euc K → Euc K)
    (R L L' : ℝ) (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K))
    (Fh : ℕ → Ω → Euc K → Euc K) (𝒦 : Set (Euc K)) (PiK : H → Euc K) (Dinf : ℝ) (cK : ℝ → ℝ),
    MK.PosDef → 0 < Dinf →
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 R)ᶜ = 0 → (∀ u ∈ Metric.closedBall (0 : Euc K) R, ‖mvec MK u‖ ≤ L') →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (F x))) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (mvec MK (F x)) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 (mvec MK p.2)}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ L' * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (mvec MK (Fh n ω x))) →
    Continuous cK → (∀ z ∈ 𝒦, rhoBox Dinf (WithLp.ofLp (F z)) ≤ 1) →
      (∀ n ω x, |(1 - rhoBox Dinf (WithLp.ofLp (Fh n ω (PiK x)))) - (1 - rhoBox Dinf (WithLp.ofLp (F (PiK x))))| ≤
        1 / Dinf * ‖Fh n ω (PiK x) - F (PiK x)‖) ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦 ∧
        TendstoUniformlyOn (fun n x => 1 - rhoBox Dinf (WithLp.ofLp (Fh n ω (PiK x))))
          (fun x => 1 - rhoBox Dinf (WithLp.ofLp (F (PiK x)))) atTop {x | PiK x ∈ 𝒦} ∧
        TendstoUniformlyOn (fun n x => 1 - cK (rhoBox Dinf (WithLp.ofLp (Fh n ω (PiK x)))))
          (fun x => 1 - cK (rhoBox Dinf (WithLp.ofLp (F (PiK x))))) atTop {x | PiK x ∈ 𝒦}

/-- B `thm:consistency`, the calibrated-depth bound: for a gauge `g_K` (subadditive, symmetric, `g_K ≤ c'_K‖·‖₂`) and
a continuous CDF `c_K` constant below `a` and above `b` ("extended by `c_K ≡ 1` above its range"), the modulus of
continuity `ϖ_K` is nondecreasing on `[0, ∞)`, tends to `0` at `0⁺`, and for any maps `F̂`, `F` and any bound `e` on
`sup_𝒦 ‖F̂ − F‖₂` (in particular `e = ε_n(𝒦)`), `|D̂^prob − D^prob| ≤ ϖ_K(c'_K e)` at every point of `𝒦`
(`D^prob = 1 − c_K(g_K(·))`). -/
def consB_varpi : Prop :=
  ∀ (K : ℕ) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' a b : ℝ),
    (∀ x y, g (x + y) ≤ g x + g y) → (∀ x, g (-x) = g x) → 0 ≤ c' → (∀ x, g x ≤ c' * ‖x‖) →
    Continuous cK → (∀ s, s ≤ a → cK s = cK a) → (∀ s, b ≤ s → cK s = cK b) →
      MonotoneOn (modCont cK) (Ici 0) ∧ Tendsto (modCont cK) (𝓝[≥] 0) (𝓝 0) ∧
      ∀ (𝒦 : Set (Euc K)) (Fh F : Euc K → Euc K) (e : ℝ), (∀ z ∈ 𝒦, ‖Fh z - F z‖ ≤ e) →
        ∀ z ∈ 𝒦, |(1 - cK (g (Fh z))) - (1 - cK (g (F z)))| ≤ modCont cK (c' * e)

/-- B `thm:consistency`, "both right-hand sides therefore tend to `0` almost surely", for general SPD `M_K`: in the
setting of the frozen Wave 29b `cons_general_M` with `c_K` constant below `a` and above `b`, almost surely
`ε_n(𝒦) = sup_{z∈𝒦} ‖F̂_n(z) − F(z)‖₂` is eventually a genuine supremum (of a bounded set), `ε_n(𝒦) → 0`,
`ϖ_K(c'_K ε_n(𝒦)) → 0`, and eventually, uniformly over `{x : Π_K x ∈ 𝒦}`,
`|D̂^geom − D^geom| ≤ c'_K ε_n(𝒦)` and `|D̂^prob − D^prob| ≤ ϖ_K(c'_K ε_n(𝒦))`. -/
def consB_varpi_as : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (MK : Matrix (Fin K) (Fin K) ℝ) (ψ : Euc K → ℝ) (F : Euc K → Euc K)
    (R L L' : ℝ) (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K))
    (Fh : ℕ → Ω → Euc K → Euc K) (𝒦 : Set (Euc K)) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ)
    (c' a b : ℝ),
    MK.PosDef →
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 R)ᶜ = 0 → (∀ u ∈ Metric.closedBall (0 : Euc K) R, ‖mvec MK u‖ ≤ L') →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (F x))) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (mvec MK (F x)) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 (mvec MK p.2)}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ L' * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (mvec MK (Fh n ω x))) →
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → 0 ≤ c' → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ s, s ≤ a → cK s = cK a) → (∀ s, b ≤ s → cK s = cK b) →
      ∀ᵐ ω ∂Pr,
        (∀ᶠ n in atTop, BddAbove ((fun z => ‖Fh n ω z - F z‖) '' 𝒦)) ∧
        Tendsto (fun n => sSup ((fun z => ‖Fh n ω z - F z‖) '' 𝒦)) atTop (𝓝 0) ∧
        Tendsto (fun n => modCont cK (c' * sSup ((fun z => ‖Fh n ω z - F z‖) '' 𝒦))) atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ∀ x, PiK x ∈ 𝒦 →
          |(1 - g (Fh n ω (PiK x))) - (1 - g (F (PiK x)))| ≤ c' * sSup ((fun z => ‖Fh n ω z - F z‖) '' 𝒦) ∧
          |(1 - cK (g (Fh n ω (PiK x)))) - (1 - cK (g (F (PiK x))))| ≤
            modCont cK (c' * sSup ((fun z => ‖Fh n ω z - F z‖) '' 𝒦))

/-- B `thm:consistency`, the rate transfer: "any rate `r_n` established for `ε_n(𝒦)` … transfers to the geometric depth
as `c'_K r_n`, and to the calibrated depth as `Lip(c_K) c'_K r_n` when `c_K` is Lipschitz". For any random maps
`F̂_n`, if almost surely `ε_n(𝒦) ≤ C r_n` eventually (`ε_n = O(r_n)` a.s.), then almost surely, eventually and
uniformly over `{x : Π_K x ∈ 𝒦}`, `|D̂^geom − D^geom| ≤ c'_K C r_n` and, for `c_K` `L_c`-Lipschitz,
`|D̂^prob − D^prob| ≤ L_c c'_K C r_n`. -/
def consB_rate : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (Fh : ℕ → Ω → Euc K → Euc K) (F : Euc K → Euc K)
    (𝒦 : Set (Euc K)) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' Lc C : ℝ) (r : ℕ → ℝ),
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → 0 ≤ c' → (∀ a, g a ≤ c' * ‖a‖) →
    0 ≤ Lc → (∀ s t, |cK s - cK t| ≤ Lc * |s - t|) →
    (∀ᵐ ω ∂Pr, ∀ᶠ n in atTop, ∀ z ∈ 𝒦, ‖Fh n ω z - F z‖ ≤ C * r n) →
      ∀ᵐ ω ∂Pr, ∀ᶠ n in atTop, ∀ x, PiK x ∈ 𝒦 →
        |(1 - g (Fh n ω (PiK x))) - (1 - g (F (PiK x)))| ≤ c' * (C * r n) ∧
        |(1 - cK (g (Fh n ω (PiK x)))) - (1 - cK (g (F (PiK x))))| ≤ Lc * (c' * (C * r n))

/-! #### A `thm:consistency` under the printed homeomorphism hypothesis -/

/-- A `thm:consistency` (with `thm:app-ghosalsen-rate`) under the PRINTED hypothesis: `μ_K ≪ Leb` carried by a convex
set `S_K` (and by `B̄(0, M)`), `P_K ≪ Leb` with support `𝒴_K`, the population quantile map `Q_{+,K}` (Borel,
`Q#μ_K = P_K`, `μ_K`-a.e. cyclically monotone) a homeomorphism `int S_K → int 𝒴_K` with inverse `G` (continuous on
`int 𝒴_K`, mutually inverse, each mapping into the other interior), and the population rank map `F` of the frozen
WaveP3c `consistency_A_gs` (Borel, `F#P_K = μ_K`, `P_K`-a.e. a subgradient of the convex Lipschitz `ψ`) — but NOT the
frozen differentiability hypothesis `∇ψ = F` on `𝒦`. Then `F = G` `P_K`-a.e. (`G` is the continuous version of the
rank map), `ψ` is differentiable at every point of `int 𝒴_K` with gradient `G`, and, for the semi-discrete estimator of
the frozen claim, almost surely `F̂_n → G` uniformly on `𝒦` and the depth `1 − ‖F̂_n(Π_K x)‖_{M_K}` converges to
`D_K(x) = 1 − ‖G(Π_K x)‖_{M_K}` uniformly over `{x : Π_K x ∈ 𝒦}` (`‖·‖_{M_K} = ‖L_m ·‖`, as in the frozen claim). -/
def consA_homeo : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (ψ : Euc K → ℝ) (F : Euc K → Euc K) (M L : ℝ)
    (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (Fh : ℕ → Ω → Euc K → Euc K)
    (𝒦 : Set (Euc K)) (PiK : H → Euc K) (Lm : Euc K →L[ℝ] Euc K) (S : Set (Euc K)) (Q G : Euc K → Euc K),
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 M)ᶜ = 0 →
    (μ : Measure (Euc K)) ≪ volume → Convex ℝ S → (μ : Measure (Euc K)) Sᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (F x)) →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (Euc K)) Q →
    ContinuousOn Q (interior S) → ContinuousOn G (interior (P : Measure (Euc K)).support) →
    MapsTo Q (interior S) (interior (P : Measure (Euc K)).support) →
    MapsTo G (interior (P : Measure (Euc K)).support) (interior S) →
    (∀ u ∈ interior S, G (Q u) = u) → (∀ y ∈ interior (P : Measure (Euc K)).support, Q (G y) = y) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 p.2}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ M * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (Fh n ω x)) →
      (∀ᵐ y ∂(P : Measure (Euc K)), F y = G y) ∧
      (∀ y ∈ interior (P : Measure (Euc K)).support, HasGradientAt ψ (G y) y) ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) G atTop 𝒦 ∧
        TendstoUniformlyOn (fun n x => 1 - ‖Lm (Fh n ω (PiK x))‖) (fun x => 1 - ‖Lm (G (PiK x))‖) atTop
          {x | PiK x ∈ 𝒦}

end Claims

end StatFormal.Wave29p
