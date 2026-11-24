import StatFormal.Archive.OTFD.Wave14c.Statements
import StatFormal.Archive.RobustEquality.SemidualStrong.Statements
import StatFormal.Archive.RobustEquality.Paper2.Alternating.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# FROZEN STATEMENTS — wave 15b (QUEUE rows 143–150): otfd B `lem:app-dual-sandwich`,
# B `prop:vector-directional-certificate`, C `lem:weighted-duality`; robust equality JASA `lem:cert-odds`,
# `lem:nc-voronoi`; paper2 `cor:oracle`, `prop:nominal`; TM `prop:otstructure`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`,
`robust-equality-jasa.md`, `robust-equality-paper2.md`, `trimmed-mmd.md`; current text after the 2026-10-13/14
corrections; paths under `research-lines/`):
* B `lem:app-dual-sandwich` (`otfd/papers/B_bands/supplement.tex:1819-1828`, proof `:1830-1849`), with Step 1
  (`:1782-1817`: `ℓ_i`, `f̃_i`, `χ_n`, `χ̂_n`, `X_n = (χ_n + ι_𝒰)^*`, `eq:app-soft-hard-sandwich`) and
  `ass:fixedK-oos`(iii)–(iv) (`:743-775`).
* B `prop:vector-directional-certificate` (`otfd/papers/B_bands/supplement.tex:2906-2934`, proof `:2936-2945`), with
  `eq:vector-reachability-gap`, `eq:vector-weight-polytope`, `eq:vector-certified-support` (`:2875-2904`),
  `x_u(t)`, `𝒳_p`, `S_p(t)`, `H_p(t,v)` (`:2740-2760`) and `eq:vector-directional-tube` (`:2790-2797`).
* C `lem:weighted-duality` (`otfd/papers/C_conditional/supplement.tex:971-990`, proof `:992-1042`), with the
  set-up `:957-969` (`I_{n,x}`, `N_{n,x}`, `χ_{n,x}`, `φ⁰_{n,x}`, `eq:weighted-hard-gap`), the scores
  `s_i(u|x) = f_i(x) − ‖Z_i‖² + 2⟨Z_i, u⟩` (`C_conditional/main.tex:395-397`, `eq:conditional-map`) and
  `ass:conditional-oos` (`main.tex:653-661`: "the reference grids lie in `𝒰_K`").
* robust equality `lem:cert-odds` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_calibration.tex:
  488-493`, proof `:495-498`), with `lem:cert-structure` (`:474-480`: `π`, `π_f`, (ii) `∇J_P(f) = a − E_Pπ_f`,
  (iii) `E_Pπ(i|Y) = a_i`) and the semi-dual notation of `supp_proofs.tex:35-45` (frozen `Semidual`).
* robust equality `lem:nc-voronoi` (`jasa/supp_cases_new.tex:84-94`, proof `:96-101`).
* paper2 `cor:oracle` (`paper2/main.tex:565-578`, proof `app_proofs.tex:209-215`), with `prop:band`
  (`main.tex:557-562`) as a hypothesis.
* paper2 `prop:nominal` (`paper2/main.tex:408-417`), with `Δ(w)` (`main.tex:218`), `M_γ` and `lem:delta-inf`
  (`:296-302`), `G = Δ + N₀ + N₁` (`thm:seminorm`(iii)).
* TM `prop:otstructure` (`trimmed-mmd/paper.tex:1498-1512`), with `eq:ptp` (`:1483-1493`).
Reuses, imported and not copied: `vecCurve`, `knapUp`, `entCaps`, `quadCaps` (frozen OTFD Wave 14c); `gap`, `Qent`,
`softmax`, `IsSimplexProj` (Bands); `cappedSimplex` (Wave 2); `oosA`, `oosB`, `rawScore`, `baryMap` (Wave 7a);
`gsoft`, `Jdual`, `Setting` (RobustEquality `Semidual`/`SemidualStrong`); `Plans`, `quad`, `centre`, `proj`
(Paper2 `Alternating`), `Deltafin` (Paper2 `Seminorm`); Tau Ceti's `wassersteinEDist` (via `Alternating`).
No `Foundations` library file is imported directly.

Covered:
* `lem:app-dual-sandwich`: `dual_sandwich` (both inequalities, any grid `μ_{K,m} = Σ_j β_j δ_{u_j}` supported in
  `𝒰`, empirical `P̂_{K,n}`, the semi-dual near-optimality `(iv)` with residual `r`).
* `prop:vector-directional-certificate`: `vec_cert_ent`, `vec_cert_quad` ((i): the weights `q(u)` lie in `P_κ(p)`
  and reconstruct `Q̂(u)`, `P_κ(p) ≠ ∅`, `S_p(t) ⊆ Y_κ(t)`, `H_p ≤ H̄_p`, for the entropic resp. quadratic map, caps
  from any lower bounds `δ̲_j ≤ δ_j(p)`); `vec_knapsack_greedy` ((i): sorting and filling under the caps attains
  `H̄_p`); `vec_cert_outer` ((ii): `T_{p,V}(t) ⊆ T̄_{p,V}(t)`, `B_{p,V} ⊆ B̄_{p,V}`, `P(X ∈ B̄_{p,V}) ≥ p` as a
  measurable event, and a violated certified inequality excludes the curve from `𝒳_p`); `vec_cert_hull` ((ii):
  `T̄_{p,V}(t) = Y_κ(t)` for every `V ⊆ 𝕊^{d−1}` dense in the sphere, in particular `V = 𝕊^{d−1}`);
  `vec_cert_inner` ((iii): `H̲_p ≤ H_p` for every map, and with the certified caps `H_p ≤ H̄_p`,
  `0 ≤ H̄_p − H̲_p` and `H̄_p − H_p ≤ H̄_p − H̲_p`).
* `lem:weighted-duality`: `weighted_duality` (the sandwich `0 ≤ ∫X^* + ∫X − 𝒞 ≤ ζ/2`, **with the grid in `𝒰_K`**);
  `weighted_duality_grid_needed` (without "grid ⊂ `𝒰_K`" the upper bound fails: see the critic notes);
  `weighted_entropic` (`0 ≤ φ̂ − φ⁰ ≤ ε log N`, `|g − χ| ≤ ε log N / 2`, `ζ ≤ r + ε log N` with `N ≤ n`);
  `weighted_quadratic` (`0 ≤ χ − g ≤ λ/4`, the quadratic transform is at most `λ/2` above `φ⁰`, `ζ ≤ r^Q + λ/2`);
  `weighted_entropy_gauge` (`eq:weighted-entropy-gauge`, and both relative entropies are `≥ 0`, so the soft value
  is at least the hard cost `⟨C, π⟩`); `weighted_counting_gauge` (the counting-gauge column potential differs from
  `φ̂(u_j)` by `ε log(N m)`).
* `lem:cert-odds`: `cert_odds_phi` (`φ_0(p) = p`, `φ_s` increasing in `s`, values in `[0, 1]`);
  `cert_odds_pointwise` (`π(U|y) ≥ φ_s(p_U(y))` for every `y`, any `f*`); `cert_odds_mean` (for a maximiser `f*`
  of `J_P`: `m_s(U) ≤ a(U)`, `G(U) = a(U) − m_0(U)`, `m_0(U) ≤ m_s(U)`, hence `G(U) ≥ m_s(U) − m_0(U) ≥ 0`).
* `lem:nc-voronoi`: `nc_voronoi` (the grid bound), `nc_voronoi_simple` (the "in particular").
* `cor:oracle`: `oracle_sets` (`𝒞^{(2)}(δ) ⊆ 𝒞_n(δ) ⊆ {Δ_P ≤ √δ}` on the band event), `oracle_ineq` (`ŵ` is
  certified, and the oracle inequality), `oracle_ball` (`𝒞_n(δ) ⊆ {|w| ≤ √δ/(c₀+c₁)}`).
* `prop:nominal`: `nominal_nonconvex` ((i), exact values `0, 0, 1`, and `Δ` is not convex);
  `nominal_bounds` ((ii), `|⟨w, m₀ − m₁⟩| ≤ Δ(w) ≤ |M_γ^{1/2} w|` for every coupling); `nominal_translate`
  ((ii), equality when `P̂₁` is a translate of `P̂₀`, as measures); `nominal_sets` ((iii): `C_γ(δ)` convex,
  `C_γ(δ) ⊆ 𝒞(δ)`, `𝒞(δ) = ⋃_γ C_γ(δ) = ⋃_{γ vertex} C_γ(δ)`, finitely many vertices).
* `prop:otstructure`: `ot_weak_duality`, `ot_optimal_of_gap` (a zero-gap feasible pair is a primal–dual optimal
  pair), `otstructure` (`r_i < θ ⇒ w_i = a_i`, `r_i > θ ⇒ w_i = 0`, the same for `v` with `s_j`, and only the tie
  sets carry fractional weight).

Not covered (declared):
* `lem:app-dual-sandwich`: the normalisation `X_n(0) = 0` (the middle term is invariant under it: shifting all
  `f_i` by `−2a` adds `a` to `X_n` and `−a` to `X_n^*`, and leaves the semi-dual hypothesis unchanged); the rest of
  `ass:fixedK-oos` (limits); measurability in the sample (the lemma is deterministic, per realisation).
* `prop:vector-directional-certificate`: the closing sentence ("the `n` reference-space convex programs and their
  dual bounds are shared by all times and directions") is encoded structurally (the caps `κ` do not depend on
  `(t, v)`), not stated; continuity of the curves in `B_{p,V}` (all functions `𝒯 → ℝ^d` are allowed — the
  containments restrict to `C(𝒯; ℝ^d)`); the calibration `μ(A_p) ≥ p` enters as a hypothesis `P(U ∈ A) ≥ p`.
* `lem:weighted-duality`: the limit sentence ("`r → 0` and `ε_n log n → 0` suffice", "`r^Q → 0` and `λ_n → 0`
  suffice") is covered through its quantitative content (`ζ ≤ r + ε log N ≤ r + ε log n`, `|g − χ| ≤ ε log N/2`;
  `ζ ≤ r^Q + λ/2`, `0 ≤ χ − g ≤ λ/4`), not as a statement about sequences; "the column-optimal dual variable is
  `φ̂(u_j)`" and "its exact semi-dual value equals `⟨C,π⟩ + (γ/2)‖π‖²_F`" (identification of solver outputs);
  the normalisation `X(0) = 0` (as above).
* `lem:cert-odds`: `lem:cert-structure`(ii) itself: `∇J_P(f)` is encoded by its formula `a − E_Pπ_f(·|Y)` (`gradJ`),
  not as the derivative of `J_P`.
* `lem:nc-voronoi`: nothing (distinctness of the `u_k` is not needed and not assumed — a generalisation).
* `cor:oracle`: `prop:band` itself (the band enters as a hypothesis, already with `√T_s` replaced by its infimum
  `N_s`; the proof's first sentence); the last two sentences (the ball is fixed given an independent certification
  sample; the Rademacher control of `sup_{𝒞_n} |𝓡_n − 𝓡|` — a pointer to Bartlett–Mendelson).
* `prop:nominal`: the sentence after it (the remark on biconvexity).
* `prop:otstructure`: LP strong duality (the existence of a zero-gap pair; Mathlib has no LP duality theorem):
  "optimal primal and dual solutions" is encoded as a feasible pair with zero duality gap, which is equivalent to
  optimality of both given the LP duality theorem (`ot_weak_duality` and `ot_optimal_of_gap` give the easy direction).

Encodings (see card):
* Finitely supported laws are weighted atom lists: the grid `μ_{K,m} = Σ_j β_j δ_{u_j}` (`β ∈ Δ_m`, any weights —
  generalises the uniform grid), the empirical law `P̂_{K,n}` (`unifW n`, weights `1/n`) and the weighted law
  `P̂_{K,n,x} = Σ_i w_i δ_{Z_i}` (`w ∈ Δ_n`), on `ℝ^K = EuclideanSpace ℝ (Fin K)`. Couplings are the frozen
  transport polytope `Plans β w` (matrices with the two marginals; every coupling of the two measures is the image
  of such a matrix, and conversely, so `sup`/`inf` over couplings are over `Plans`). `𝒞` is `maxCorr` (`sSup` of
  `Σ π_ji ⟨u_j, Z_i⟩`) and `W₂²` is `w2sq` (`sInf` of `Σ π_ji ‖u_j − Z_i‖²`); the polytope is nonempty (product
  plan) and compact, so both are genuine (no junk).
* `χ_n`, `χ_{n,x}` are `chiI I` (`max_{i∈I} ℓ_i`, `ℓ_i(u) = ⟨u, Z_i⟩ − ½(‖Z_i‖² − f_i)`), with `I = univ` (paper B)
  resp. `I = {i : w_i > 0}` (`posRows`; nonempty since `Σ w = 1`). `X = (χ + ι_𝒰)^*` is `conjU 𝒰 χ`
  (`sup_{u∈𝒰} {⟨u,z⟩ − χ(u)}`, a real `sSup` over a nonempty bounded set: genuine). `X^*` is the Fenchel conjugate
  `conjE X` in `EReal` (`+∞` allowed), and the middle term `∫X^* dμ + ∫X dP̂` is `midTerm` in `EReal`
  (`Σ_j β_j X^*(u_j) + Σ_i w_i X(Z_i)`, with `0 · (+∞) = 0` for null atoms, the measure-theoretic convention).
  `𝒰_K` is any bounded set (`Bornology.IsBounded`; the paper's compact convex support — a generalisation) containing
  every grid atom. `φ̂` is `phiSoft ε I` (log-mean-exp over `I`, `N = |I|`), `φ⁰ = ‖u‖² − 2χ` (`phiHard`),
  `g = (‖·‖² − φ̂)/2`; the quadratic `g` is `gQuad λ I` (`½ max_{q ∈ Δ_I} {Σ q_i s_i(u) − (λ/2)‖q‖²}`, a real `sSup`
  over the compact simplex `simplexOn I`: genuine), `φ^Q = ‖u‖² − 2g` (`phiQuad`). Relative entropies of finite
  arrays are `Σ p log(p/q)` with `0 log 0 = 0` (`klVec`, `klMat`); `Unif(I)` is `unifOn I`, the grid weights
  `b_j > 0`.
* Vector certificate: frozen Wave 14c conventions (`ℝ^D = Fin D → ℝ`, outputs `Fin d → ℝ`, dot products, the
  reconstruction at a fixed `t` is `vecCurve (𝔪 t) (E t)`, `y_j(t) = vecCurve (𝔪 t) (E t) Z_j`). `H_p(t,v)` is the
  `EReal` supremum `vecHE` (equal to the attained maximum of the paper when `A_p` is compact and `Q̂` continuous;
  never junk), `H̄_p = certH = knapUp κ (vᵀy_j(t))` (frozen), `Y_κ(t) = capHull`, `T_{p,V}(t) = tubeAt`,
  `B_{p,V} = tubeB` (all curves `𝒯 → ℝ^d`), `H̲_p = innerH` (max over a nonempty `Finset`, in `EReal`).
  `𝕊^{d−1} = {v : vᵀv = 1}` (`unitSphere`), "dense family" is `V ⊆ 𝕊^{d−1} ⊆ closure V`. The maps: entropic
  `Qent ε M Z f` and quadratic `baryMap (q u) Z` with `q(u)` a simplex projection of `rawScore (γ/m)` (frozen Wave 7a
  forms, `M ≻ 0`); scores `oosA`, `oosB`; `δ_j(p) = gap` (frozen Bands); lower bounds `δ̲_j ≤ δ_j(p)` (the paper's
  `0 ≤ δ̲_j` is not needed — a generalisation). `CappedRep Q A κ Z` (every `Q̂(u)`, `u ∈ A`, is `Σ_j q_j Z_j` with
  `q ∈ P_κ`) is what (i) proves and what (ii), (iii) use. The greedy fill is `greedyFill κ σ` for any permutation
  `σ` that sorts the objective coefficients decreasingly (`Antitone (c ∘ σ)`, ties broken arbitrarily):
  `q_{σ k} = min(κ_{σ k}, (1 − Σ_{l<k} κ_{σ l})_+)`. The probability statement: `U` is a measurable reference draw
  on any probability space with `P(U ∈ A) ≥ p` (`A` measurable) — the event `{U ∈ A}` is the measurable subset.
* `lem:cert-odds`: frozen `Semidual` setting (labels `Fin k`, weights `a_i > 0`, `Σ a = 1`, bounded measurable costs
  `c_i` on any measurable `K`, `ε > 0`, `P` a probability). `π_f(i|y) = a_i e^{(f_i + g_f(y) − c_i(y))/ε}`
  (`piCond`), `π = π_{f*}`; "`f*` is the population potential" is "`f*` maximises `J_P`" (frozen `Jdual`); the upper
  level set `U` with gap `s` is any nonempty `U` with `s ≤ u_i − u_j` for `i ∈ U`, `j ∉ U` (`u = f* − f`; this is
  "`s ≤ min_U u − max_{U^c} u`", and covers `U^c = ∅`); `φ_s(p) = (1 + ((1−p)/p) e^{−s/ε})^{-1}` (`phiOdds`, used
  at `p = p_U(y) ∈ (0, 1]`, so no `/0`); `m_s(U) = ∫ φ_s(p_U) dP`, `G(U) = Σ_{i∈U} ∇J_P(f)_i` (`gradJ`).
* `lem:nc-voronoi`: `ℝ^p = EuclideanSpace ℝ (Fin p)`, the grid `ρ : Fin (M+1) → ℝ` strictly increasing with
  `ρ_0 = 0`; `sup_z D(z) ≤ B` is `∀ z, D(z) ≤ B`; the bound is `vorBound` with the inner maximum as a real `⨆` over
  `Fin J × Fin M` (for `M = 0` or `J = 0` it is `0`, below the second term `(Σ W)e^{−βρ_M²} ≥ 0`, so the `max` is
  the paper's value).
* `cor:oracle`: rules `w` in any real inner-product space `E`; `Δ = Deltafin` of the two centres (frozen); `N₀, N₁`
  any nonnegative functions (the seminorms at the calibrated radii); `Δ_P(w) = W₂(w#P₀, w#P₁)` is Tau Ceti's
  `wassersteinEDist 2` in `ℝ≥0∞` for arbitrary laws `P_s` (no `toReal`; `E` Borel, so `w ↦ ⟨w, ·⟩` is measurable and
  `Measure.map` is not the junk `0`); the band event `E` enters as
  `BandHolds` (`|Δ_P − Δ| ≤ N₀ + N₁` for every `w`, as two `ℝ≥0∞` inequalities); `𝒞^{(2)}(δ)` and
  `{Δ_P ≤ √δ}` are `ℝ≥0∞` sublevel sets; `inf_{𝒞^{(2)}} 𝓡 + 2 sup_{𝒞_n} |𝓡_n − 𝓡|` is "`𝓡(ŵ) ≤ 𝓡(w') + 2B`
  for every `w' ∈ 𝒞^{(2)}(δ)` and every bound `B` of `|𝓡_n − 𝓡|` on `𝒞_n(δ)`" (the same statement, without
  `sSup`/`sInf` junk); `ŵ` is any minimiser (`IsMinOn`); `0 ≤ δ`; in `oracle_ball` `c_s ≥ 0`, `c₀ + c₁ > 0`.
* `prop:nominal`: frozen Paper2 encodings (`Deltafin` = `Δ`, `quad x₀ x₁ w γ = wᵀM_γw`, `Plans`, `centre`); the
  example in `EuclideanSpace ℝ (Fin 2)` with `e₁, e₂` the standard basis (`EuclideanSpace.single`); `m_s = Σ_i a_i x_i`;
  "translate" is `centre a₁ x₁ = (centre a₀ x₀).map (· + b)` (measures; Borel `E`); `N₀, N₁` any seminorms;
  `0 ≤ δ`; vertices are `Set.extremePoints ℝ (Plans a₀ a₁)`.
* `prop:otstructure`: any costs `C`, caps `a, b` (the paper's `a_i = [n(1−α)]^{-1}`, `b_j = [m(1−β)]^{-1}`,
  `C_ij = ‖X_i − Y_j‖^p` — a generalisation); the dual of `eq:ptp` is the standard one, `max θ − ⟨a,u⟩ − ⟨b,z⟩` s.t.
  `u, z ≥ 0`, `θ − u_i − z_j ≤ C_ij` (signs as in the paper: `u, z ≥ 0` for the `≤` constraints, `θ` free);
  `w = P1`, `v = Pᵀ1`; `r_i = min_j (C_ij + z_j)` is a real `⨅` over `Fin m` with `m ≥ 1` (genuine minimum).
* All types are in `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* **`lem:weighted-duality` needs "the grid lies in `𝒰_K`"** (QUEUE row 145 note 5): the lemma says only "Under
  `eq:weighted-hard-gap`"; the premise is in `ass:conditional-oos`, not in the lemma. `weighted_duality_grid_needed`:
  `K = 1`, `𝒰 = [−1, 1]` (the support of `Unif[−1,1]`), one grid atom at `u = 2`, one data atom `Z = 0`, `f = 0`:
  `eq:weighted-hard-gap` holds with `ζ = 0` (`φ⁰(2) = 4 = W₂²(δ₂, δ₀)`), but `X(z) = |z|` and `X^*(2) = +∞`, so the
  middle term is `+∞ > 𝒞 + ζ/2 = 0`. Harmless in context (every use is under `ass:conditional-oos`); fix: "Under
  `eq:weighted-hard-gap`, with `μ_{K,m_n}` supported in `𝒰_K`". The B lemma states its premise (`(iii)`).
* `lem:app-dual-sandwich`: exactly as printed (with `ε > 0`; `r ≥ 0` is not needed).
* `prop:vector-directional-certificate` holds as printed; `δ̲_j ≥ 0` is not needed for (i).
* `lem:cert-odds` holds as printed; `U` must be nonempty (implicit in "`min_U u`").
* `lem:nc-voronoi` holds as printed, also without distinctness.
* `cor:oracle` holds as printed given `prop:band` (hypothesis); `oracle_ball` needs `c₀ + c₁ > 0`.
* `prop:nominal` holds as printed.
* `prop:otstructure` holds as printed for the standard dual; conditional on the LP duality theorem (zero gap).
* Critic (2026-10-14): ACCEPT / ACCEPT-WITH-NOTE, all 28 TRUE. Vector certificate: `P(X ∈ B̄) ≥ p` is an inner
  probability (curves carry no topology). C `lem:weighted-duality` needs the grid in `𝒰_K` (stated only in
  `ass:conditional-oos`, which the lemma does not invoke): standalone counterexample `K = 1`, `𝒰 = [−1,1]`, grid `δ₂`,
  data `δ₀`, `f = 0` (middle term `+∞`, hard gap 0) — paper S3 (DEFECTS #58), harmless in context. `cert-odds`: `U ≠ ∅` is
  implicit in "min_U". `cor:oracle` is CONDITIONAL on paper2 `prop:band` (uncertified; entered as a hypothesis);
  `c₀ + c₁ > 0` is needed (`x/0 = 0`). `prop:otstructure`: zero-gap pairs are exactly the paper's optimal pairs whenever
  an optimal pair exists; LP strong duality itself is not certified.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset Matrix TauCeti
open scoped InnerProductSpace ENNReal

namespace StatFormal.Wave15b

open StatFormal.OTFD.Bands (gap Qent IsSimplexProj)
open StatFormal.OTFD.Wave2 (cappedSimplex)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap)
open StatFormal.OTFD.Wave14c (vecCurve knapUp entCaps quadCaps)
open StatFormal.RobustEquality.Semidual (gsoft)
open StatFormal.RobustEquality.SemidualStrong (Jdual Setting)
open StatFormal.RobustEquality.Paper2.Alternating (Plans quad centre)
open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin)

/-! ### B `lem:app-dual-sandwich`, C `lem:weighted-duality` -/

section Duality

variable {K m n : ℕ}

/-- `ℓ_i(u) = ⟨u, Z_i⟩ − ½(‖Z_i‖² − f_i)`. -/
def ellAff (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (i : Fin n)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ⟪u, Z i⟫_ℝ - (‖Z i‖ ^ 2 - f i) / 2

/-- Laguerre potential over the rows `I`: `χ(u) = max_{i∈I} ℓ_i(u)` (used with `I ≠ ∅`). -/
def chiI (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ⨆ i : I, ellAff Z f i u

/-- The retained rows `I = {i : w_i > 0}`. -/
def posRows (w : Fin n → ℝ) : Finset (Fin n) := univ.filter fun i => 0 < w i

/-- Empirical weights `1/n`. -/
def unifW (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- `X(z) = (χ + ι_𝒰)^*(z) = sup_{u∈𝒰} {⟨u, z⟩ − χ(u)}` (used on a nonempty bounded `𝒰`). -/
def conjU (U : Set (EuclideanSpace ℝ (Fin K))) (χ : EuclideanSpace ℝ (Fin K) → ℝ)
    (z : EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup ((fun u => ⟪u, z⟫_ℝ - χ u) '' U)

/-- The Fenchel conjugate `X^*(u) = sup_z {⟨u, z⟩ − X(z)} ∈ (−∞, +∞]`. -/
def conjE (X : EuclideanSpace ℝ (Fin K) → ℝ) (u : EuclideanSpace ℝ (Fin K)) : EReal :=
  ⨆ z : EuclideanSpace ℝ (Fin K), ((⟪u, z⟫_ℝ - X z : ℝ) : EReal)

/-- `∫ X^* dμ + ∫ X dP̂` for `μ = Σ_j β_j δ_{u_j}`, `P̂ = Σ_i w_i δ_{Z_i}`. -/
def midTerm (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (X : EuclideanSpace ℝ (Fin K) → ℝ) : EReal :=
  (∑ j, ((β j : ℝ) : EReal) * conjE X (ug j)) + ((∑ i, w i * X (Z i) : ℝ) : EReal)

/-- `∫ ⟨u, z⟩ dπ` for a plan `π` (rows: grid atoms, columns: data atoms). -/
def corrSum (ug : Fin m → EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (π : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, ∑ i, π j i * ⟪ug j, Z i⟫_ℝ

/-- `∫ ‖u − z‖² dπ`. -/
def costSum (ug : Fin m → EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (π : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, ∑ i, π j i * ‖ug j - Z i‖ ^ 2

/-- Maximal correlation `𝒞(μ, P̂) = sup_{π ∈ Π(μ, P̂)} ∫ ⟨u, z⟩ dπ`. -/
def maxCorr (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) : ℝ :=
  sSup (corrSum ug Z '' Plans β w)

/-- `W₂²(μ, P̂) = inf_{π ∈ Π(μ, P̂)} ∫ ‖u − z‖² dπ`. -/
def w2sq (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) : ℝ :=
  sInf (costSum ug Z '' Plans β w)

/-- Soft `c`-transform in the log-mean-exp gauge on `I`:
`φ̂(u) = −ε log(N⁻¹ Σ_{i∈I} e^{(f_i − ‖u − Z_i‖²)/ε})`, `N = |I|`. -/
def phiSoft (ε : ℝ) (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  -ε * Real.log ((1 / (I.card : ℝ)) * ∑ i ∈ I, Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε))

/-- Hard cost transform `φ⁰(u) = ‖u‖² − 2χ(u)`. -/
def phiHard (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ‖u‖ ^ 2 - 2 * chiI I Z f u

/-- Scores `s_i(u) = f_i − ‖Z_i‖² + 2⟨Z_i, u⟩` (`eq:conditional-map`). -/
def scoreC (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (i : Fin n)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  f i - ‖Z i‖ ^ 2 + 2 * ⟪Z i, u⟫_ℝ

/-- The simplex `Δ_I` over the rows `I`. -/
def simplexOn (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∀ i, i ∉ I → q i = 0) ∧ ∑ i, q i = 1}

/-- Quadratic potential `g(u) = ½ max_{q∈Δ_I} {Σ_i q_i s_i(u) − (λ/2)‖q‖²}`. -/
def gQuad (lam : ℝ) (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  (1 / 2) * sSup ((fun q : Fin n → ℝ => ∑ i, q i * scoreC Z f i u - lam / 2 * ∑ i, q i ^ 2) '' simplexOn I)

/-- The quadratic soft cost transform `φ^Q = ‖u‖² − 2g(u)`. -/
def phiQuad (lam : ℝ) (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ‖u‖ ^ 2 - 2 * gQuad lam I Z f u

/-- `Unif(I)`. -/
def unifOn (I : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ I then 1 / (I.card : ℝ) else 0

/-- `KL(p ‖ q) = Σ_i p_i log(p_i/q_i)` for finite arrays (`0 log 0 = 0`). -/
def klVec (p q : Fin n → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- `KL(π ‖ ρ) = Σ_{i,j} π_ij log(π_ij/ρ_ij)` for finite arrays (`0 log 0 = 0`). -/
def klMat (π ρ : Fin n → Fin m → ℝ) : ℝ := ∑ i, ∑ j, π i j * Real.log (π i j / ρ i j)

end Duality

/-! ### B `prop:vector-directional-certificate` -/

section VecCert

variable {d D n : ℕ}

/-- `H_p(t,v) = sup_{u∈A} vᵀx_u(t)` (in `EReal`), at a fixed `t` (`mo = 𝔪(t)`, `E = E(t)`). -/
def vecHE (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ) : EReal :=
  ⨆ u ∈ A, ((v ⬝ᵥ vecCurve mo E (Q u) : ℝ) : EReal)

/-- `H̄_p(t,v) = max_{q∈P_κ} Σ_j q_j vᵀy_j(t)`, `y_j(t) = 𝔪(t) + E(t)Z_j`. -/
def certH (κ : Fin n → ℝ) (Z : Fin n → Fin D → ℝ) (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ)
    (v : Fin d → ℝ) : EReal :=
  knapUp κ (fun j => v ⬝ᵥ vecCurve mo E (Z j))

/-- `Y_κ(t) = {Σ_j q_j y_j(t) : q ∈ P_κ}`. -/
def capHull (κ : Fin n → ℝ) (Z : Fin n → Fin D → ℝ) (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ) :
    Set (Fin d → ℝ) :=
  (fun q : Fin n → ℝ => ∑ j, q j • vecCurve mo E (Z j)) '' cappedSimplex κ

/-- `H̲_p(t,v) = max_{u∈F} vᵀx_u(t)` over a finite set of candidates. -/
def innerH (Q : (Fin D → ℝ) → Fin D → ℝ) (F : Finset (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ) : EReal :=
  ⨆ u ∈ F, ((v ⬝ᵥ vecCurve mo E (Q u) : ℝ) : EReal)

/-- `T(t) = ⋂_{v∈V} {y : vᵀy ≤ H(v)}` for a threshold function `H`. -/
def tubeAt (H : (Fin d → ℝ) → EReal) (V : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {y | ∀ v ∈ V, ((v ⬝ᵥ y : ℝ) : EReal) ≤ H v}

/-- `B = {x : x(t) ∈ T(t) ∀ t}`. -/
def tubeB {T : Type} (H : T → (Fin d → ℝ) → EReal) (V : Set (Fin d → ℝ)) : Set (T → Fin d → ℝ) :=
  {x | ∀ t, x t ∈ tubeAt (H t) V}

/-- The Euclidean unit sphere `𝕊^{d−1} = {v : vᵀv = 1}`. -/
def unitSphere (d : ℕ) : Set (Fin d → ℝ) := {v | v ⬝ᵥ v = 1}

/-- Greedy fill in the order `σ`: `q_{σ k} = min(κ_{σ k}, (1 − Σ_{l<k} κ_{σ l})_+)`. -/
def greedyFill (κ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Fin n → ℝ := fun j =>
  min (κ j) (max 0 (1 - ∑ l ∈ univ.filter (fun l => σ.symm l < σ.symm j), κ l))

/-- Every `Q̂(u)`, `u ∈ A`, is `Σ_j q_j Z_j` with weights `q ∈ P_κ` (what (i) proves). -/
def CappedRep (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (κ : Fin n → ℝ)
    (Z : Fin n → Fin D → ℝ) : Prop :=
  ∀ u ∈ A, ∃ q ∈ cappedSimplex κ, Q u = ∑ j, q j • Z j

end VecCert

/-! ### robust equality `lem:cert-odds` -/

section CertOdds

variable {Y : Type*} [MeasurableSpace Y] {k : ℕ}

/-- `π_f(i|y) = a_i e^{(f_i + g_f(y) − c_i(y))/ε}`. -/
def piCond (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → Y → ℝ) (y : Y) (i : Fin k) : ℝ :=
  a i * Real.exp ((f i + gsoft ε a f c y - c i y) / ε)

/-- `φ_s(p) = (1 + ((1 − p)/p) e^{−s/ε})^{-1}`. -/
def phiOdds (ε s p : ℝ) : ℝ := (1 + (1 - p) / p * Real.exp (-s / ε))⁻¹

/-- `∇J_P(f) = a − E_P π_f(·|Y)` (the formula of `lem:cert-structure`(ii)). -/
def gradJ (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → Y → ℝ) (P : Measure Y) (i : Fin k) : ℝ :=
  a i - ∫ y, piCond ε a f c y i ∂P

/-- `m_s(U) = E_P φ_s(p_U(Y))`, `p_U(y) = π_f(U|y)`. -/
def mOdds (ε s : ℝ) (a f : Fin k → ℝ) (c : Fin k → Y → ℝ) (P : Measure Y) (U : Finset (Fin k)) : ℝ :=
  ∫ y, phiOdds ε s (∑ i ∈ U, piCond ε a f c y i) ∂P

end CertOdds

/-! ### robust equality `lem:nc-voronoi` -/

section Voronoi

variable {p J M : ℕ}

/-- `D(z) = Σ_k W_k e^{−β‖z − u_k‖²}`. -/
def gmix (u : Fin J → EuclideanSpace ℝ (Fin p)) (W : Fin J → ℝ) (β : ℝ) (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ k, W k * Real.exp (-β * ‖z - u k‖ ^ 2)

/-- The right-hand side of `lem:nc-voronoi`. -/
def vorBound (u : Fin J → EuclideanSpace ℝ (Fin p)) (W : Fin J → ℝ) (β : ℝ) (ρ : Fin (M + 1) → ℝ) : ℝ :=
  max (⨆ (j : Fin J) (l : Fin M), ∑ k, W k * Real.exp (-β *
      (max (max (dist (u j) (u k) / 2) (ρ l.castSucc)) (dist (u j) (u k) - ρ l.succ)) ^ 2))
    ((∑ k, W k) * Real.exp (-β * ρ (Fin.last M) ^ 2))

end Voronoi

/-! ### paper2 `cor:oracle`, `prop:nominal` -/

section Paper2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {n₀ n₁ : ℕ}

/-- `Δ_P(w) = W₂(w#P₀, w#P₁)` (in `ℝ≥0∞`). -/
def deltaPop (P₀ P₁ : Measure E) (w : E) : ℝ≥0∞ :=
  wassersteinEDist 2 (P₀.map (fun x => ⟪w, x⟫_ℝ)) (P₁.map (fun x => ⟪w, x⟫_ℝ))

/-- The band of `prop:band`, with `√T_s` replaced by its infimum `N_s`: `|Δ_P(w) − Δ(w)| ≤ N₀(w) + N₁(w)`. -/
def BandHolds (P₀ P₁ : Measure E) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (N₀ N₁ : E → ℝ) : Prop :=
  ∀ w, deltaPop P₀ P₁ w ≤ ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w) ∧
    ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) ≤ deltaPop P₀ P₁ w + ENNReal.ofReal (N₀ w + N₁ w)

/-- `𝒞_n(δ) = {w : Δ(w) + N₀(w) + N₁(w) ≤ √δ}`. -/
def certSetN (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : E → ℝ)
    (δ : ℝ) : Set E :=
  {w | Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w ≤ √δ}

/-- `𝒞^{(2)}(δ) = {w : Δ_P(w) + 2(N₀ + N₁)(w) ≤ √δ}`. -/
def certSet2 (P₀ P₁ : Measure E) (N₀ N₁ : E → ℝ) (δ : ℝ) : Set E :=
  {w | deltaPop P₀ P₁ w + ENNReal.ofReal (2 * (N₀ w + N₁ w)) ≤ ENNReal.ofReal √δ}

/-- `C_γ(δ) = {w : |M_γ^{1/2} w| + N₀(w) + N₁(w) ≤ √δ}`. -/
def certSetG (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (N₀ N₁ : E → ℝ) (δ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) :
    Set E :=
  {w | √(quad x₀ x₁ w γ) + N₀ w + N₁ w ≤ √δ}

/-- Weights `(½, ½)` of the example of `prop:nominal`(i). -/
def exA : Fin 2 → ℝ := fun _ => 1 / 2

/-- Atoms `(1,1), (−1,−1)` of `P̂₀` in the example of `prop:nominal`(i). -/
def exP0 : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![!₂[(1 : ℝ), 1], !₂[(-1 : ℝ), -1]]

/-- Atoms `(1,−1), (−1,1)` of `P̂₁` in the example of `prop:nominal`(i). -/
def exP1 : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![!₂[(1 : ℝ), -1], !₂[(-1 : ℝ), 1]]

/-- The group mean `m = Σ_i a_i x_i`. -/
def meanC {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) : E := ∑ i, a i • x i

end Paper2

/-! ### TM `prop:otstructure` -/

section OT

variable {n m : ℕ}

/-- Feasibility for `eq:ptp`: `P ≥ 0`, `P1 ≤ a`, `Pᵀ1 ≤ b`, `1ᵀP1 = 1`. -/
def PtpFeasible (a : Fin n → ℝ) (b : Fin m → ℝ) (P : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j ≤ a i) ∧ (∀ j, ∑ i, P i j ≤ b j) ∧ ∑ i, ∑ j, P i j = 1

/-- `⟨P, C⟩`. -/
def ptpCost (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ) : ℝ := ∑ i, ∑ j, P i j * C i j

/-- Dual feasibility: `u, z ≥ 0`, `θ − u_i − z_j ≤ C_ij`. -/
def PtpDualFeasible (C : Fin n → Fin m → ℝ) (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ z j) ∧ ∀ i j, θ - u i - z j ≤ C i j

/-- Dual value `θ − ⟨a, u⟩ − ⟨b, z⟩`. -/
def ptpDualVal (a : Fin n → ℝ) (b : Fin m → ℝ) (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ) : ℝ :=
  θ - ∑ i, a i * u i - ∑ j, b j * z j

/-- Row reduced cost `r_i = min_j (C_ij + z_j)`. -/
def rowRed (C : Fin n → Fin m → ℝ) (z : Fin m → ℝ) (i : Fin n) : ℝ := ⨅ j, (C i j + z j)

/-- Column reduced cost `s_j = min_i (C_ij + u_i)`. -/
def colRed (C : Fin n → Fin m → ℝ) (u : Fin n → ℝ) (j : Fin m) : ℝ := ⨅ i, (C i j + u i)

end OT

namespace Claims

/-! ### B `lem:app-dual-sandwich` -/

/-- `𝒞_n ≤ ∫X_n^* dμ_{K,m} + ∫X_n dP̂_{K,n} ≤ 𝒞_n + ½(ε log n + r)`, for a grid supported in `𝒰` and a data-side
dual vector `f` with semi-dual residual `r`. -/
def dual_sandwich : Prop :=
  ∀ (K m n : ℕ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (f : Fin n → ℝ) (U : Set (EuclideanSpace ℝ (Fin K))) (ε r : ℝ),
    0 < n → (∀ j, 0 ≤ β j) → ∑ j, β j = 1 → Bornology.IsBounded U → (∀ j, ug j ∈ U) → 0 < ε →
    w2sq β ug (unifW n) Z - r ≤ ∑ j, β j * phiSoft ε univ Z f (ug j) + (1 / (n : ℝ)) * ∑ i, f i →
      ((maxCorr β ug (unifW n) Z : ℝ) : EReal) ≤ midTerm β ug (unifW n) Z (conjU U (chiI univ Z f)) ∧
      midTerm β ug (unifW n) Z (conjU U (chiI univ Z f)) ≤
        ((maxCorr β ug (unifW n) Z + (ε * Real.log n + r) / 2 : ℝ) : EReal)

/-! ### B `prop:vector-directional-certificate` -/

/-- (i), entropic map: with caps `κ_j = e^{−δ̲_j/ε}` from lower bounds `δ̲_j ≤ δ_j(p)`, the weights reconstruct
`Q̂(u)` inside `P_κ(p)` (so `P_κ(p) ≠ ∅`), `S_p(t) ⊆ Y_κ(t)` and `H_p(t,v) ≤ H̄_p(t,v)` for every `v`. -/
def vec_cert_ent : Prop :=
  ∀ (d D n : ℕ) (ε : ℝ) (M : Matrix (Fin D) (Fin D) ℝ) (Z : Fin n → Fin D → ℝ) (f : Fin n → ℝ)
    (A : Set (Fin D → ℝ)) (δl : Fin n → ℝ) (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ),
    0 < n → 0 < ε → M.PosDef → A.Nonempty → (∀ j, δl j ≤ gap (oosA M f Z) (oosB M Z) A j) →
      CappedRep (Qent ε M Z f) A (entCaps ε δl) Z ∧ (cappedSimplex (entCaps ε δl)).Nonempty ∧
      (fun u => vecCurve mo E (Qent ε M Z f u)) '' A ⊆ capHull (entCaps ε δl) Z mo E ∧
      ∀ v, vecHE (Qent ε M Z f) A mo E v ≤ certH (entCaps ε δl) Z mo E v

/-- (i), quadratic map (`λ = γ/m`, any selection of the simplex projection): caps `(1 − mδ̲_j/γ)_+`. -/
def vec_cert_quad : Prop :=
  ∀ (d D n m : ℕ) (γ : ℝ) (M : Matrix (Fin D) (Fin D) ℝ) (Z : Fin n → Fin D → ℝ) (f : Fin n → ℝ)
    (q : (Fin D → ℝ) → Fin n → ℝ) (A : Set (Fin D → ℝ)) (δl : Fin n → ℝ) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ),
    0 < γ → 0 < m → M.PosDef → A.Nonempty → (∀ u, IsSimplexProj (rawScore (γ / m) M f Z u) (q u)) →
    (∀ j, δl j ≤ gap (oosA M f Z) (oosB M Z) A j) →
      CappedRep (fun u => baryMap (q u) Z) A (quadCaps m γ δl) Z ∧ (cappedSimplex (quadCaps m γ δl)).Nonempty ∧
      (fun u => vecCurve mo E (baryMap (q u) Z)) '' A ⊆ capHull (quadCaps m γ δl) Z mo E ∧
      ∀ v, vecHE (fun u => baryMap (q u) Z) A mo E v ≤ certH (quadCaps m γ δl) Z mo E v

/-- (i), the fractional knapsack: when `P_κ ≠ ∅`, sorting the coefficients decreasingly (`σ`) and filling to total
weight one under the caps gives a point of `P_κ` attaining `max_{q∈P_κ} Σ_j q_j c_j`. -/
def vec_knapsack_greedy : Prop :=
  ∀ (n : ℕ) (κ c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
    (cappedSimplex κ).Nonempty → Antitone (fun k => c (σ k)) →
      greedyFill κ σ ∈ cappedSimplex κ ∧ ((∑ j, greedyFill κ σ j * c j : ℝ) : EReal) = knapUp κ c

/-- (ii): for any map with `CappedRep` (caps shared by all `t, v`), the certified sets contain the exact ones,
`P(X ∈ B̄_{p,V}) ≥ p` for `X = x_U` with `P(U ∈ A) ≥ p`, and a violated certified inequality excludes the curve. -/
def vec_cert_outer : Prop :=
  ∀ (d D n : ℕ) (T : Type) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (κ : Fin n → ℝ)
    (Z : Fin n → Fin D → ℝ) (mo : T → Fin d → ℝ) (E : T → Matrix (Fin d) (Fin D) ℝ) (V : Set (Fin d → ℝ)),
    CappedRep Q A κ Z →
      (∀ t, tubeAt (vecHE Q A (mo t) (E t)) V ⊆ tubeAt (certH κ Z (mo t) (E t)) V) ∧
      tubeB (fun t => vecHE Q A (mo t) (E t)) V ⊆ tubeB (fun t => certH κ Z (mo t) (E t)) V ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Uref : Ω → Fin D → ℝ) (p : ℝ),
        Measurable Uref → MeasurableSet A → ENNReal.ofReal p ≤ P (Uref ⁻¹' A) →
        ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal p ≤ P S ∧
          S ⊆ {ω | (fun t => vecCurve (mo t) (E t) (Q (Uref ω))) ∈ tubeB (fun t => certH κ Z (mo t) (E t)) V}) ∧
      ∀ y : T → Fin d → ℝ, (∃ t, ∃ v ∈ V, certH κ Z (mo t) (E t) v < ((v ⬝ᵥ y t : ℝ) : EReal)) →
        ∀ u ∈ A, y ≠ fun t => vecCurve (mo t) (E t) (Q u)

/-- (ii): for every family `V` of unit directions dense in `𝕊^{d−1}` (in particular `V = 𝕊^{d−1}`),
`T̄_{p,V}(t) = Y_κ(t)`. -/
def vec_cert_hull : Prop :=
  ∀ (d D n : ℕ) (κ : Fin n → ℝ) (Z : Fin n → Fin D → ℝ) (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ)
    (V : Set (Fin d → ℝ)),
    (cappedSimplex κ).Nonempty → V ⊆ unitSphere d → unitSphere d ⊆ closure V →
      tubeAt (certH κ Z mo E) V = capHull κ Z mo E

/-- (iii): for every map and every nonempty finite `F ⊆ A`, `H̲_p ≤ H_p`; with certified caps also `H_p ≤ H̄_p`,
`0 ≤ H̄_p − H̲_p` and `H̄_p − H_p ≤ H̄_p − H̲_p`. -/
def vec_cert_inner : Prop :=
  ∀ (d D n : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (F : Finset (Fin D → ℝ)) (κ : Fin n → ℝ)
    (Z : Fin n → Fin D → ℝ) (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ),
    F.Nonempty → (↑F : Set (Fin D → ℝ)) ⊆ A →
      innerH Q F mo E v ≤ vecHE Q A mo E v ∧
      (CappedRep Q A κ Z →
        vecHE Q A mo E v ≤ certH κ Z mo E v ∧ 0 ≤ certH κ Z mo E v - innerH Q F mo E v ∧
        certH κ Z mo E v - vecHE Q A mo E v ≤ certH κ Z mo E v - innerH Q F mo E v)

/-! ### C `lem:weighted-duality` -/

/-- Under `eq:weighted-hard-gap` (gap `ζ`), with the grid in `𝒰`:
`0 ≤ ∫X^* dμ + ∫X dP̂_x − 𝒞(μ, P̂_x) ≤ ζ/2`, `X = (χ + ι_𝒰)^*`, `χ = max_{i∈I} ℓ_i`. -/
def weighted_duality : Prop :=
  ∀ (K m n : ℕ) (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (w : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ) (U : Set (EuclideanSpace ℝ (Fin K))) (ζ : ℝ),
    (∀ j, 0 ≤ β j) → ∑ j, β j = 1 → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
    Bornology.IsBounded U → (∀ j, ug j ∈ U) →
    w2sq β ug w Z - ζ ≤ ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i →
      ((maxCorr β ug w Z : ℝ) : EReal) ≤ midTerm β ug w Z (conjU U (chiI (posRows w) Z f)) ∧
      midTerm β ug w Z (conjU U (chiI (posRows w) Z f)) ≤ ((maxCorr β ug w Z + ζ / 2 : ℝ) : EReal)

/-- Without "grid ⊂ `𝒰_K`" the upper bound fails: `K = 1`, `𝒰 = [−1, 1]`, grid `δ₂`, data `δ₀`, `f = 0`;
`eq:weighted-hard-gap` holds with `ζ = 0`, the middle term is `+∞`. -/
def weighted_duality_grid_needed : Prop :=
  w2sq (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]] - 0 ≤
      ∑ j, (fun _ : Fin 1 => (1 : ℝ)) j *
          phiHard (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]] (fun _ => 0) (![!₂[(2 : ℝ)]] j) +
        ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i * (fun _ : Fin 1 => (0 : ℝ)) i ∧
    midTerm (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]]
        (conjU (Metric.closedBall 0 1) (chiI (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]] (fun _ => 0))) = ⊤ ∧
    ¬ midTerm (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]]
        (conjU (Metric.closedBall 0 1) (chiI (posRows (fun _ : Fin 1 => (1 : ℝ))) ![!₂[(0 : ℝ)]] (fun _ => 0))) ≤
      ((maxCorr (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(2 : ℝ)]] (fun _ : Fin 1 => (1 : ℝ)) ![!₂[(0 : ℝ)]] + 0 / 2 : ℝ) : EReal)

/-- Entropic fits: `0 ≤ φ̂ − φ⁰ ≤ ε log N`, `|g − χ| ≤ ε log N/2` with `g = (‖·‖² − φ̂)/2`, and a soft semi-dual gap
`r` gives the hard gap `ζ = r + ε log N` (`N = |I| ≤ n`). -/
def weighted_entropic : Prop :=
  ∀ (K m n : ℕ) (ε : ℝ) (w : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ),
    0 < ε → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      (posRows w).card ≤ n ∧
      (∀ u, 0 ≤ phiSoft ε (posRows w) Z f u - phiHard (posRows w) Z f u ∧
        phiSoft ε (posRows w) Z f u - phiHard (posRows w) Z f u ≤ ε * Real.log (posRows w).card) ∧
      (∀ u, |(‖u‖ ^ 2 - phiSoft ε (posRows w) Z f u) / 2 - chiI (posRows w) Z f u| ≤
        ε * Real.log (posRows w).card / 2) ∧
      ∀ (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (r : ℝ), (∀ j, 0 ≤ β j) → ∑ j, β j = 1 →
        w2sq β ug w Z - r ≤ ∑ j, β j * phiSoft ε (posRows w) Z f (ug j) + ∑ i, w i * f i →
        w2sq β ug w Z - (r + ε * Real.log (posRows w).card) ≤
          ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i

/-- Quadratic fits (`λ ≥ 0`): `0 ≤ χ − g ≤ λ/4`, `0 ≤ φ^Q − φ⁰ ≤ λ/2`, and a soft gap `r^Q` gives `ζ = r^Q + λ/2`. -/
def weighted_quadratic : Prop :=
  ∀ (K m n : ℕ) (lam : ℝ) (w : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ),
    0 ≤ lam → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      (∀ u, 0 ≤ chiI (posRows w) Z f u - gQuad lam (posRows w) Z f u ∧
        chiI (posRows w) Z f u - gQuad lam (posRows w) Z f u ≤ lam / 4) ∧
      (∀ u, 0 ≤ phiQuad lam (posRows w) Z f u - phiHard (posRows w) Z f u ∧
        phiQuad lam (posRows w) Z f u - phiHard (posRows w) Z f u ≤ lam / 2) ∧
      ∀ (β : Fin m → ℝ) (ug : Fin m → EuclideanSpace ℝ (Fin K)) (r : ℝ), (∀ j, 0 ≤ β j) → ∑ j, β j = 1 →
        w2sq β ug w Z - r ≤ ∑ j, β j * phiQuad lam (posRows w) Z f (ug j) + ∑ i, w i * f i →
        w2sq β ug w Z - (r + lam / 2) ≤ ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i

/-- `eq:weighted-entropy-gauge`: for `π ≥ 0` with row sums `w` (`w_i > 0` exactly on `I`) and grid weights `b > 0`,
`KL(π ‖ Unif(I) ⊗ b) = KL(π ‖ w ⊗ b) + KL(w ‖ Unif(I))`; if the column sums are `b` and `Σ b = 1`, all three are
`≥ 0` (so the soft value `⟨C, π⟩ + ε KL(π ‖ Unif(I) ⊗ b)`, `ε ≥ 0`, is at least `⟨C, π⟩`). -/
def weighted_entropy_gauge : Prop :=
  ∀ (n m : ℕ) (π : Fin n → Fin m → ℝ) (w : Fin n → ℝ) (b : Fin m → ℝ),
    (∀ i j, 0 ≤ π i j) → (∀ i, ∑ j, π i j = w i) → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → (∀ j, 0 < b j) →
      klMat π (fun i j => unifOn (posRows w) i * b j) = klMat π (fun i j => w i * b j) + klVec w (unifOn (posRows w)) ∧
      ((∀ j, ∑ i, π i j = b j) → ∑ j, b j = 1 →
        0 ≤ klMat π (fun i j => w i * b j) ∧ 0 ≤ klVec w (unifOn (posRows w)) ∧
        0 ≤ klMat π (fun i j => unifOn (posRows w) i * b j))

/-- The counting-gauge column potential `ε log b_j − ε log Σ_{i∈I} e^{(f_i − ‖u_j − Z_i‖²)/ε}` (`b_j = 1/m`) equals
`φ̂(u_j) − ε log(N m)`. -/
def weighted_counting_gauge : Prop :=
  ∀ (K m n : ℕ) (ε : ℝ) (I : Finset (Fin n)) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (f : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin K)),
    0 < m → I.Nonempty →
      ε * Real.log (1 / (m : ℝ)) - ε * Real.log (∑ i ∈ I, Real.exp ((f i - ‖u - Z i‖ ^ 2) / ε)) =
        phiSoft ε I Z f u - ε * Real.log ((I.card : ℝ) * m)

/-! ### robust equality `lem:cert-odds` -/

/-- `φ_0(p) = p`, `φ_s(p)` is nondecreasing in `s ≥ 0` and lies in `[0, 1]`, for `p ∈ (0, 1]`. -/
def cert_odds_phi : Prop :=
  ∀ (ε p : ℝ), 0 < ε → 0 < p → p ≤ 1 →
    phiOdds ε 0 p = p ∧ (∀ s s' : ℝ, s ≤ s' → phiOdds ε s p ≤ phiOdds ε s' p) ∧
    ∀ s : ℝ, 0 ≤ phiOdds ε s p ∧ phiOdds ε s p ≤ 1

/-- Pointwise: for a nonempty `U` with gap `s ≥ 0` below it (for `u = f* − f`), `π(U|y) ≥ φ_s(p_U(y))`. -/
def cert_odds_pointwise : Prop :=
  ∀ (Y : Type) (k : ℕ) (ε : ℝ) (a fs f : Fin k → ℝ) (c : Fin k → Y → ℝ) (U : Finset (Fin k)) (s : ℝ) (y : Y),
    0 < ε → (∀ i, 0 < a i) → U.Nonempty → 0 ≤ s →
    (∀ i ∈ U, ∀ j ∉ U, s ≤ (fs i - f i) - (fs j - f j)) →
      phiOdds ε s (∑ i ∈ U, piCond ε a f c y i) ≤ ∑ i ∈ U, piCond ε a fs c y i

/-- For a maximiser `f*` of `J_P`: `m_s(U) ≤ a(U)`, `G(U) = a(U) − m_0(U)` and `m_0(U) ≤ m_s(U)`
(so `G(U) ≥ m_s(U) − m_0(U) ≥ 0`). -/
def cert_odds_mean : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y] (k : ℕ) (ε : ℝ) (a fs f : Fin k → ℝ) (c : Fin k → Y → ℝ) (P : Measure Y)
    [IsProbabilityMeasure P] (U : Finset (Fin k)) (s : ℝ),
    Setting ε a c → (∀ g, Jdual ε a c P g ≤ Jdual ε a c P fs) → U.Nonempty → 0 ≤ s →
    (∀ i ∈ U, ∀ j ∉ U, s ≤ (fs i - f i) - (fs j - f j)) →
      mOdds ε s a f c P U ≤ ∑ i ∈ U, a i ∧
      ∑ i ∈ U, gradJ ε a f c P i = ∑ i ∈ U, a i - mOdds ε 0 a f c P U ∧
      mOdds ε 0 a f c P U ≤ mOdds ε s a f c P U

/-! ### robust equality `lem:nc-voronoi` -/

/-- `sup_z D(z) ≤ max{max_j max_{m<M} Σ_k W_k e^{−β max(d_jk/2, ρ_m, d_jk − ρ_{m+1})²}, (Σ_k W_k) e^{−βρ_M²}}`. -/
def nc_voronoi : Prop :=
  ∀ (p J M : ℕ) (u : Fin J → EuclideanSpace ℝ (Fin p)) (W : Fin J → ℝ) (β : ℝ) (ρ : Fin (M + 1) → ℝ),
    (∀ k, 0 ≤ W k) → 0 < β → StrictMono ρ → ρ 0 = 0 →
      ∀ z, gmix u W β z ≤ vorBound u W β ρ

/-- In particular `sup_z D(z) ≤ max_j Σ_k W_k e^{−β d_jk²/4}`. -/
def nc_voronoi_simple : Prop :=
  ∀ (p J : ℕ) (u : Fin J → EuclideanSpace ℝ (Fin p)) (W : Fin J → ℝ) (β : ℝ),
    (∀ k, 0 ≤ W k) → 0 < β →
      ∀ z, gmix u W β z ≤ ⨆ j, ∑ k, W k * Real.exp (-β * dist (u j) (u k) ^ 2 / 4)

/-! ### paper2 `cor:oracle` -/

/-- On the band event: `𝒞^{(2)}(δ) ⊆ 𝒞_n(δ) ⊆ {w : Δ_P(w) ≤ √δ}`. -/
def oracle_sets : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (P₀ P₁ : Measure E)
    (N₀ N₁ : E → ℝ) (δ : ℝ),
    (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) → 0 ≤ δ → BandHolds P₀ P₁ a₀ x₀ a₁ x₁ N₀ N₁ →
      certSet2 P₀ P₁ N₀ N₁ δ ⊆ certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ ∧
      certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ ⊆ {w | deltaPop P₀ P₁ w ≤ ENNReal.ofReal √δ}

/-- On the band event, a minimiser `ŵ` of `𝓡_n` over `𝒞_n(δ)` is certified, and
`𝓡(ŵ) ≤ 𝓡(w') + 2B` for every `w' ∈ 𝒞^{(2)}(δ)` and every bound `B ≥ sup_{𝒞_n(δ)} |𝓡_n − 𝓡|`. -/
def oracle_ineq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (P₀ P₁ : Measure E)
    (N₀ N₁ : E → ℝ) (δ : ℝ) (R Rn : E → ℝ) (wh : E),
    (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) → 0 ≤ δ → BandHolds P₀ P₁ a₀ x₀ a₁ x₁ N₀ N₁ →
    wh ∈ certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ → IsMinOn Rn (certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ) wh →
      deltaPop P₀ P₁ wh ≤ ENNReal.ofReal √δ ∧
      ∀ w' ∈ certSet2 P₀ P₁ N₀ N₁ δ, ∀ B : ℝ, (∀ w ∈ certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ, |Rn w - R w| ≤ B) →
        R wh ≤ R w' + 2 * B

/-- If `N_s(w) ≥ c_s |w|` (`c_s ≥ 0`, `c₀ + c₁ > 0`), then `𝒞_n(δ) ⊆ {|w| ≤ √δ/(c₀ + c₁)}`. -/
def oracle_ball : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : E → ℝ) (δ c₀ c₁ : ℝ),
    0 ≤ c₀ → 0 ≤ c₁ → 0 < c₀ + c₁ → (∀ w, c₀ * ‖w‖ ≤ N₀ w) → (∀ w, c₁ * ‖w‖ ≤ N₁ w) →
      certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ ⊆ Metric.closedBall 0 (√δ / (c₀ + c₁))

/-! ### paper2 `prop:nominal` -/

/-- (i) For `P̂₀ = ½(δ_{(1,1)} + δ_{(−1,−1)})`, `P̂₁ = ½(δ_{(1,−1)} + δ_{(−1,1)})`: `Δ(e₁) = Δ(e₂) = 0`,
`Δ(½(e₁ + e₂)) = 1`, so `Δ` is not convex. -/
def nominal_nonconvex : Prop :=
  Deltafin exA exP0 exA exP1 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 0 ∧
  Deltafin exA exP0 exA exP1 (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 0 ∧
  Deltafin exA exP0 exA exP1
      ((1 / 2 : ℝ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) = 1 ∧
  ¬ ConvexOn ℝ Set.univ (Deltafin exA exP0 exA exP1)

/-- (ii) `|⟨w, m₀ − m₁⟩| ≤ Δ(w) ≤ |M_γ^{1/2} w|` for every coupling `γ`. -/
def nominal_bounds : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      |⟪w, meanC a₀ x₀ - meanC a₁ x₁⟫_ℝ| ≤ Deltafin a₀ x₀ a₁ x₁ w ∧
      ∀ γ ∈ Plans a₀ a₁, Deltafin a₀ x₀ a₁ x₁ w ≤ √(quad x₀ x₁ w γ)

/-- (ii) The left bound is attained when `P̂₁` is a translate of `P̂₀`. -/
def nominal_translate : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (b w : E),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
    centre a₁ x₁ = (centre a₀ x₀).map (fun x => x + b) →
      Deltafin a₀ x₀ a₁ x₁ w = |⟪w, meanC a₀ x₀ - meanC a₁ x₁⟫_ℝ|

/-- (iii) `C_γ(δ)` is convex and contained in `𝒞(δ) = {G ≤ √δ}`, and `𝒞(δ) = ⋃_γ C_γ(δ)`, a finite union over the
vertices of the transport polytope. -/
def nominal_sets : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E) (δ : ℝ),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 → 0 ≤ δ →
      (∀ γ ∈ Plans a₀ a₁, Convex ℝ (certSetG x₀ x₁ N₀ N₁ δ γ) ∧
        certSetG x₀ x₁ N₀ N₁ δ γ ⊆ certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ) ∧
      certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ = ⋃ γ ∈ Plans a₀ a₁, certSetG x₀ x₁ N₀ N₁ δ γ ∧
      certSetN a₀ x₀ a₁ x₁ N₀ N₁ δ = ⋃ γ ∈ Set.extremePoints ℝ (Plans a₀ a₁), certSetG x₀ x₁ N₀ N₁ δ γ ∧
      (Set.extremePoints ℝ (Plans a₀ a₁)).Finite

/-! ### TM `prop:otstructure` -/

/-- Weak duality for `eq:ptp`: every dual-feasible value is at most every primal-feasible cost. -/
def ot_weak_duality : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ)
    (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ),
    PtpFeasible a b P → PtpDualFeasible C u z θ → ptpDualVal a b u z θ ≤ ptpCost C P

/-- A feasible pair with zero duality gap is a pair of optimal primal and dual solutions. -/
def ot_optimal_of_gap : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ)
    (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ),
    PtpFeasible a b P → PtpDualFeasible C u z θ → ptpCost C P = ptpDualVal a b u z θ →
      (∀ P', PtpFeasible a b P' → ptpCost C P ≤ ptpCost C P') ∧
      ∀ u' z' θ', PtpDualFeasible C u' z' θ' → ptpDualVal a b u' z' θ' ≤ ptpDualVal a b u z θ

/-- `prop:otstructure`, for an optimal primal–dual pair (zero gap): `r_i < θ ⇒ w_i = a_i`, `r_i > θ ⇒ w_i = 0`,
symmetrically for `v` with `s_j`, and fractional weight only on the tie sets. -/
def otstructure : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ)
    (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ),
    0 < n → 0 < m → PtpFeasible a b P → PtpDualFeasible C u z θ → ptpCost C P = ptpDualVal a b u z θ →
      (∀ i, (rowRed C z i < θ → ∑ j, P i j = a i) ∧ (θ < rowRed C z i → ∑ j, P i j = 0)) ∧
      (∀ j, (colRed C u j < θ → ∑ i, P i j = b j) ∧ (θ < colRed C u j → ∑ i, P i j = 0)) ∧
      (∀ i, 0 < ∑ j, P i j → ∑ j, P i j < a i → rowRed C z i = θ) ∧
      (∀ j, 0 < ∑ i, P i j → ∑ i, P i j < b j → colRed C u j = θ)

end Claims
end StatFormal.Wave15b
