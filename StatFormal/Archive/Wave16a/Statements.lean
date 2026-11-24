import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.Wave14a.Statements
import StatFormal.Archive.OTFD.Wave12a.Statements
import StatFormal.Archive.OTFD.Wave8c.Statements
import TauCeti.MeasureTheory.OptimalTransport.Coupling
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.Support

/-!
# FROZEN STATEMENTS — wave 16a (QUEUE rows 151–158): TM `prop:selection`; ICL `lem:cond-types`;
# robust equality paper 2 `prop:wrm`; otfd T `eq:dualmap-mult`, A `prop:lift-consistency`,
# R `lem:divergence`, R `cor:cubic`, B `prop:rk-sign-test`

Sources (verbatim in `lean-formalisation/inventory/extracted/trimmed-mmd.md`, `context-distribution-icl.md`,
`robust-equality-paper2.md`, `otfd-T_tangent.md`, `otfd-A_sieves.md`, `otfd-R_robustness.md`, `otfd-B_bands.md`;
current text after the 2026-10-13/14 corrections; paths under `research-lines/`):
* TM `prop:selection` (`trimmed-mmd/paper.tex:1459-1476`, `eq:least`), with `Δ_α(n)` (`:1377`), `eq:qp`
  (`:612`) and `eq:trimset-emp` (`:1380-1386`: `𝒯_α`, own levels `α, β`), the frozen `TrimmedMMD/BangBang`
  (`capped`, `qp`).
* ICL `lem:cond-types` (`context-distribution-ICL/paper/v3/supp/proofs_conditional.tex:422-434`, proof `:436-455`),
  with the paragraph "Mixing weights" (`:417-420`: `𝖠`, `g^α`, `binom(M,α)`) and the pool notation (`:45-49`:
  `G(z;w) = Σ_{|T|=M} Π_w(T) L(z;z_T)`, `G^iid(z;w) = Σ_𝐣 Π_k w_{j_k} L(z;z_𝐣)`, `ℋ`, `ℋ^iid`), the conditional
  Poisson law `Π_w(T) = Π_{j∈T} w_j / e_M(w)` (`sections/03_framework.tex:60-64`).
* robust equality `prop:wrm` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:538-544`), with
  `c(x,x') = |x − x'|²` (`:216`) and `f_h(x₀,x) = (h(x) − h(x₀))²` (`:246`); the frozen `Wave14a` `lagr`
  (`f_h(x₀,·) − λ c(x₀,·)`).
* otfd T `lem:mapcost-mult` / `eq:dualmap-mult` (`otfd/papers/T_tangent/supp_moved.tex:128-149`, proof
  `app_proofs.tex:356-371`), setting of `lem:mapcost` (`supp_moved.tex:107-118`).
* otfd A `prop:lift-consistency` (`otfd/papers/A_sieves/supplement.tex:5454-5465`, proof `:4862-4878`), with
  `prop:lift-dual`(i)–(ii) (`:5414-5432`).
* otfd R `lem:divergence` (`otfd/papers/R_robustness/sections/appendix_a.tex:96-102`, proof `:104-120`).
* otfd R `cor:cubic` (`R_robustness/sections/s5_families.tex:17-22`), with the cubic law (`s2_setting.tex:18-19`:
  independent `Unif(−λ_k/2, λ_k/2)`), `β(A;ν) = inf_A TD` (`s2_setting.tex:75`), `def:bp` (`:53`), `lem:boundary`
  (`s5_families.tex:6-15`) and `thm:region-breakdown` (`s4_regions.tex:75-93`); the frozen `OTFD/Wave1`
  (`regionDepth`, `tukeyDepth`), `OTFD/Wave6b` (`dMinus`, `EntSetting`, `regionSup`), `OTFDR` (`Qhat`),
  `OTFDR/Lift` (`Contam`, `BP`), `OTFD/Wave8c` (`cubicLaw`), and the certified unconditional Wave 12a
  `thm:region-breakdown` (used by the route only).
* otfd B `prop:rk-sign-test` (`otfd/papers/B_bands/main.tex:1171-1188`, proof `supplement.tex:5241-5245`).
Reuses the frozen `TrimmedMMD/BangBang`, `Wave14a`, `OTFD/Wave12a` (with `Wave1`, `Wave6b`, `OTFDR`, `OTFDR/Lift`)
and `OTFD/Wave8c` statements, imported, not copied; Tau Ceti's `IsCoupling`. No `Foundations` library file is
imported (the sign-test route imports `Foundations/Exchangeable/Permutation`). None of the eight labels has a target
in `certify/targets.toml` (checked 2026-10-14); `cor:cubic` extends the certified Wave 12a region breakdown.

Covered:
* `prop:selection`: `selection_unique` (the minimiser of `eq:least` over `𝒯_α` exists and is unique),
  `selection_reg_unique` (for `λ > 0` the regularised minimiser exists and is unique), `selection_limit`
  (`(w_λ, v_λ) → (ŵ, v̂)` as `λ ↓ 0`).
* `lem:cond-types`: `cond_types_i` ((i)), `cond_types_ii` ((ii), with `e_M(w(x)) > 0` and a positive normaliser).
* `prop:wrm`: `wrm_concave` (`2(λ − λ₀)`-strong concavity on `S`), `wrm_sup` (the certificate
  `sup φ ≤ φ(x) + |∇φ(x)|²/{4(λ − λ₀)}` for a strongly concave `φ`), `wrm_cert` (both together on `S`, with the
  explicit gradient).
* `eq:dualmap-mult`: `mapcost_mult` (both bounds, with integrability), `mapcost_mult_one` (the `a⁻² − 1` case).
* `prop:lift-consistency`: `lift_consistency_sep` (tail of `prop:lift-dual`(i)), `lift_consistency_quad`
  (tail of (ii)), `lift_tail_vanish` (`∫‖u − ι_KΠ_Ku‖²dμ → 0`).
* `lem:divergence`: `divergence`.
* `cor:cubic`: `cubic_depth` (`β(A_{K,p}) = 0`), `cubic_single` (the band explodes with one replaced curve),
  `cubic_bp` (`BP ≤ 1/n`).
* `prop:rk-sign-test`: `rk_sign_test`.

Not covered (declared):
* `prop:selection`: the sentence after it (warm-start computation).
* `lem:cond-types`: nothing of the lemma; the sentence after it (the law of the type of `ϱ ∼ g^{⊗M}`).
* `prop:wrm`: the paragraph after it (Sinha et al., spectral architectures).
* `eq:dualmap-mult`: `lem:mapcost` itself (QUEUE row 161, separate); the remark after the lemma.
* `prop:lift-consistency`: the inequality for `T = ∞` (series tails in `H`; only the tail term's limit is stated in
  `H`); "Hence along every schedule … so do their lifts" (a corollary conditional on `thm:app-hard-diagonal`,
  `thm:app-entropic-diagonal`, which are not certified; given them it is the squeeze `a_K + 3 s_K → 0`).
* `cor:cubic`: "for `λ_k = 1/k` this holds for every `p` of interest from `K = 2` on" (informal; the radius
  condition is frozen instead, as the queue note asks).
* `prop:rk-sign-test`: "this is a two-sample test; it is not a test of `G`-invariance" (a remark).

Encodings (to be checked by the critic):
* `prop:selection`: feature vectors `x_i = φ(X_i)`, `y_j = φ(Y_j)` in an arbitrary real inner-product space `E`
  (generalisation; the RKHS is a case), `F = qp x y = ‖Σ w_i x_i − Σ v_j y_j‖²` (`= wᵀK_XXw + vᵀK_YYv − 2wᵀK_XYv`),
  `Δ_α(n) = capped n α` (frozen), `0 ≤ α, β < 1`, `n, m ≥ 1`. `𝒯_α = trimSet` (the `IsMinOn` minimisers over
  `D = Δ_α(n) × Δ_β(m)`), "`(ŵ, v̂) = argmin_{𝒯_α} R`" is `IsLeastTrim` (a minimiser, then `∃!`), the regularised
  minimiser is `IsRegMin` (`∃!`); the limit is stated for every choice `λ ↦ (w_λ, v_λ)` of regularised minimisers
  (`λ > 0`), along `𝓝[>] 0`, in the product topology of `ℝ^n × ℝ^m` (= the Euclidean one). No `argmin` junk.
* `lem:cond-types`: the pool `z_1, …, z_n` enters only through the functions `L(·; z_𝐣)` (`Lj : [n]^M → (𝒵 → ℝ)`)
  and `L(·; z_T)` (`LT : Finset (Fin n) → (𝒵 → ℝ)`, used on `M`-subsets); `𝒵` any type, functions compared
  pointwise. `w_r ∈ Δ^{n−1}` is `simplexW`; `𝖠 = typesA R M = piAntidiag univ M`; `binom(M,α)` is Mathlib's
  `Nat.multinomial univ α`; `g^α = gpow g α`; `conv` is `convexHull ℝ` in `𝒵 → ℝ`; `Δ_𝖠` is "`t ≥ 0` on `𝖠`,
  `Σ_𝖠 t = 1`". "Not depending on `x` or `g`": `∃ h (t) ∀ g`. (i) is stated for every `g : Fin R → ℝ`
  (generalisation of `g(x) ∈ Δ^{R−1}`), (ii) for every `g` with positive entries (generalisation: `Σ_r g_r = 1` is not
  needed). "`⋃_r supp w_r` has at least `M` elements" is `M ≤ #{j : ∃ r, w_{r,j} ≠ 0}`. `G` divides by `e_M(w)`
  (`gcps`); the claim also asserts `e_M(w(x)) > 0` and `Σ_β t_β g^β > 0`, so neither division is junk.
* `prop:wrm`: `S` a convex subset of `ℝ^d = EuclideanSpace ℝ (Fin d)`, `x₀ ∈ S` (the anchor; see the critic notes),
  `φ = lagr h λ x₀` (frozen: `(h(x) − h(x₀))² − λ dist(x,x₀)²`). "Twice differentiable on `S` with `|∇h| ≤ L`,
  `‖∇²h‖_op ≤ β_h`" is `HasFDerivWithinAt h (h' x) S x`, `HasFDerivWithinAt h' (h'' x) S x`, `‖h' x‖ ≤ L`,
  `‖h'' x‖ ≤ β_h` for `x ∈ S` (operator norms; for the symmetric Hessian `‖h''‖` is `‖∇²h‖_op`); `osc_S(h)` is any
  `osc` with `|h(x) − h(y)| ≤ osc` on `S` (the paper's `sup − inf` is the least one, no `sSup`). Strong concavity is
  Mathlib's `StrongConcaveOn S m` (`φ + (m/2)‖·‖²` concave, i.e. `∇²φ ≤ −mI`), `m = 2(λ − λ₀)`, `λ > λ₀`. In
  `wrm_sup`, `sup φ ≤ …` is stated pointwise for every `y ∈ S` (`S = univ` is the paper's `ℝ^d`; generalisation to a
  convex `S`), `∇φ(x)` is any `φ'` with `HasFDerivWithinAt φ φ' S x`, `|∇φ(x)| = ‖φ'‖`.
* `eq:dualmap-mult`: `U, V` second countable Borel spaces, `V` normed (the paper's tangent spaces), `μ, ν`
  probability measures, `π₀ = (Id, Q₀)#μ` with `Q₀` measurable, costs measurable, `c₀ ≥ 0`. "Optimal for `c`" is
  `IsOptPlan`: a Tau Ceti coupling with `∫⁻ c⁺ dπ ≤ ∫⁻ c⁺ dπ'` for every coupling `π'` (costs compared in `[0,∞]`;
  `c₁ ≥ θ₋²c₀ ≥ 0` on `supp μ × supp ν`, which carries every coupling, so this is the paper's notion). "Integrable
  optimal dual potentials" is `f ∈ L¹(μ)`, `g ∈ L¹(ν)`, `∫f dμ + ∫g dν = OT₀ = ∫c₀ dπ₀` (finite); dual
  feasibility on the supports follows from the gap hypothesis. Supports are Mathlib's `Measure.support`. The
  conclusions include the integrability of `c₀ − f − g` and `‖v − Q₀(u)‖²` under `π₁`, so the Bochner integrals are
  genuine.
* `prop:lift-consistency`: the truncated space `ℝ^T` as `Fin T → ℝ` with `‖v‖² = sqn v = Σ_k v_k²`, head `k < K`
  (0-indexed), `ι_KΠ_K` and `u_⊥ = tailPart K u`; data law `P`, reference `μ` (probability measures), `F` measurable
  with `F#P = μ` (the standing assumption of the section). The head map is any measurable `Fh` with values in
  `ι_Kℝ^K` (`IsHeadMap`; generalisation of `x ↦ ι_KF̂_K(x_K)`). Tails: (i) `IsSepTail` (each `t_k` measurable with
  `t_k#P_k = μ_k`, what `prop:lift-dual`(i) asserts of the population optimum); (ii) `quadTail`,
  `t_k(y) = λ_k(y − m_k)`, `m_k = E X_k`, `λ_k = (E U_k²/Var X_k)^{1/2}`, with `E X_k² < ∞`, `Var X_k > 0`,
  `E U_k² < ∞` (no `/0`, no non-integrable `∫`). Expectations are lower Lebesgue integrals of `ofReal`, so the
  inequality holds in `[0,∞]` without integrability hypotheses. `lift_tail_vanish`: `H` a real Hilbert space with a
  Hilbert basis `(b_k)_{k∈ℕ}` (`ι_KΠ_Ku = Σ_{k<K}⟨b_k,u⟩b_k`), `∫‖u‖²dμ < ∞` in `[0,∞]`.
* `lem:divergence`: events measurable, `P(A_k) ≥ α` in `ℝ≥0∞` (`ofReal α`), `β_k ≥ 0` real with `Σβ_k = ∞` as
  `¬ Summable β`; `Σ_k β_k 1_{A_k}` is the `ℝ≥0∞` series (index from `0`).
* `cor:cubic`: `cubeLaw λ` is the frozen `cubicLaw` with half-widths `λ_k/2`, moved to `EuclideanSpace` by
  `WithLp.toLp 2` (as the frozen `peakedLaw`); `λ_k > 0`; `A_{K,p} = cubicRegion λ ρ = closedBall 0 ρ ∩ box`,
  `ρ = τ_{K,p}D_∞`. "The ball's radius exceeds the smallest half-width `λ_K/2`" is `∃ k, λ_k/2 < ρ` (equivalent when
  `λ` is decreasing; generalisation otherwise). `β = regionDepth` (frozen, `ℝ≥0∞`). "Their bands break down with a
  single replaced curve" is stated twice, for the fitted entropic map of the frozen setting (`EntSetting`, `n ≥ 1`):
  `cubic_single` (`∀ M, ∃ Z' ∈ 𝔠₁(Z), ∃ u ∈ A, ‖Q̂_{Z'}(u)‖ > M`) and `cubic_bp` (`BP ≤ 1/n` for the frozen region
  estimator `regionSup`).
* `prop:rk-sign-test`: given `𝓘₁`, the pooled curves `(W_1, …, W_{n₂}, V_1, …, V_m)` have a law `μ` on `X^{n₂+m}`
  invariant under every permutation (exchangeability); the sign map `σ` is any measurable map into a measurable space
  `Y` (the value `S(F̂(Π_Kx))`, with an extra symbol where `F̂(Π_Kx) = 0`, as the queue note asks; generalisation);
  `T` any measurable statistic of the `n₂ + m` signs (generalisation: within-group symmetry is not needed). The
  p-value is `permPval = #{σ ∈ S_{n₂+m} : T(y∘σ) ≥ T(y)}/(n₂+m)!`; for a statistic symmetric within groups it equals
  the p-value over the `binom(n₂+m, m)` relabelings (each relabeling is hit by `n₂! m!` permutations; not formalised).
  Super-uniform: `μ(p ≤ α) ≤ α` for every real `α`.

Critic notes:
* `prop:selection`: as printed (rechecked: `R(ap + bq) = aR(p) + bR(q) − ab|p − q|²` gives uniqueness; the limit uses
  `F(p_λ) ≤ F* + λR(p̂)`, `R(p_λ) ≤ R(p̂)` and compactness, no Hoffman bound needed).
* `lem:cond-types`: as printed. The fibre sizes are identified with `binom(M,α)` by comparing polynomial identities
  (`MvPolynomial.funext`). (ii) needs the support hypothesis only for `e_M(w(x)) > 0`.
* `prop:wrm`: hidden hypothesis `x₀ ∈ S` (true in the paper: `x₀` is an anchor of `P̂_s`, in `K ⊆ S`). It is needed:
  `d = 1`, `S = [0,1]`, `h(x) = x|x|` (`L = 2`, `β_h = 2`, `osc = 1`, `λ₀ = 6`), `x₀ = −10`, `λ = 7`: then
  `φ''(x) = 12x² + 400 − 2λ > 0` on `S`, so `φ` is convex there. The constants are consistent with Mathlib's convention
  (`∇²φ ≤ −2(λ − λ₀)I` gives the `4(λ − λ₀)` denominator). No error.
* `eq:dualmap-mult`: as printed; `c₀ ≥ 0` is used (the queue note), and second countability is what makes the
  supports conull ("every coupling is concentrated on `supp μ × supp ν`").
* `prop:lift-consistency`: the current constant `3` is right (`4E‖U_⊥‖² − E‖U_⊥‖²`; the queue's `4` is the tail
  term alone). The proof needs only the equality of the tail second moments, not optimality of the tail.
* `lem:divergence`: as printed; the route uses the queue's dominated-convergence argument on `Z_n = T_n/B_n`.
* `cor:cubic`: as printed; the box-boundary point `(λ_k/2)e_k` has depth `0` because `{z_k ≥ λ_k/2}` is null
  (`lem:boundary` for this law, done directly).
* `prop:rk-sign-test`: as printed.
* Proof routes: `Wave16a/Route{Selection,CondTypes,Wrm,MapCost,Lift,Divergence,Cubic,SignTest}.lean`, all 18 claims,
  standard axioms `propext, Classical.choice, Quot.sound` only (the routes reuse the untrusted, certified
  `OTFD/Wave12a/RouteEntropic`, `OTFD/Wave8c/RouteCubic` and import `Foundations/Exchangeable/Permutation` — routes
  only).
* Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE, all 18 TRUE. `wrm`: `x₀ ∈ S` is needed (`S = [0,1]`, `h = x²`,
  `λ₀ = 6`: `φ″ = 12x² + 386 > 0`) and implicit in the paper (`x₀ ∼ P̂_s` takes values in `K ⊆ S`); paper S4: quantify
  "for `x₀ ∈ S`". `cubic_bp`: `BP ≥ 1/n` always, so `BP ≤ 1/n` means `BP = 1/n`; the claim concerns the region estimator
  (band = region rests on the paper's prose). TM `paper.tex:1473` uses `F(w,v)` without defining it in the paper (only
  `supplement.tex:551`) — paper S4 (DEFECTS #59).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology InnerProductSpace

namespace StatFormal.Wave16a

/-! ### TM `prop:selection` -/

section Selection

open StatFormal.TrimmedMMD.BangBang (capped qp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n m : ℕ}

/-- `‖w − n⁻¹𝟏‖₂² + ‖v − m⁻¹𝟏‖₂²`. -/
def devU (p : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  ∑ i, (p.1 i - 1 / n) ^ 2 + ∑ j, (p.2 j - 1 / m) ^ 2

/-- `𝒯_α` (`eq:trimset-emp`): the minimisers of `eq:qp` over `Δ_α(n) × Δ_β(m)`. -/
def trimSet (x : Fin n → E) (y : Fin m → E) (α β : ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | p ∈ capped n α ×ˢ capped m β ∧ IsMinOn (qp x y) (capped n α ×ˢ capped m β) p}

/-- `(ŵ, v̂)` is a minimiser of `eq:least` over `𝒯_α`. -/
def IsLeastTrim (x : Fin n → E) (y : Fin m → E) (α β : ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  p ∈ trimSet x y α β ∧ IsMinOn devU (trimSet x y α β) p

/-- `(w_λ, v_λ)` minimises `F + λ{‖w − n⁻¹𝟏‖² + ‖v − m⁻¹𝟏‖²}` over `Δ_α(n) × Δ_β(m)`. -/
def IsRegMin (x : Fin n → E) (y : Fin m → E) (α β lam : ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  p ∈ capped n α ×ˢ capped m β ∧
    IsMinOn (fun q => qp x y q + lam * devU q) (capped n α ×ˢ capped m β) p

end Selection

/-! ### ICL `lem:cond-types` -/

section CondTypes

variable {Z : Type*} {n M R : ℕ}

/-- `G^iid(·;w) = Σ_{𝐣 ∈ [n]^M} Π_k w_{j_k} L(·; z_𝐣)`; `Lj 𝐣 = L(·; z_𝐣)`. -/
def giid (Lj : (Fin M → Fin n) → Z → ℝ) (w : Fin n → ℝ) : Z → ℝ :=
  ∑ j : Fin M → Fin n, (∏ k, w (j k)) • Lj j

/-- `e_M(w) = Σ_{|T| = M} Π_{j ∈ T} w_j`. -/
def esymW (M : ℕ) (w : Fin n → ℝ) : ℝ :=
  ∑ T ∈ powersetCard M (univ : Finset (Fin n)), ∏ j ∈ T, w j

/-- `G(·;w) = Σ_{|T| = M} Π_w(T) L(·; z_T)`, `Π_w(T) = Π_{j∈T} w_j / e_M(w)`; `LT T = L(·; z_T)`. -/
def gcps (M : ℕ) (LT : Finset (Fin n) → Z → ℝ) (w : Fin n → ℝ) : Z → ℝ :=
  (esymW M w)⁻¹ • ∑ T ∈ powersetCard M (univ : Finset (Fin n)), (∏ j ∈ T, w j) • LT T

/-- The probability simplex `Δ^{ι}` (`Δ^{n−1}` for `ι = Fin n`). -/
def simplexW (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- `w(x) = Σ_r g_r(x) w_r`. -/
def mixW (g : Fin R → ℝ) (w : Fin R → Fin n → ℝ) : Fin n → ℝ := ∑ r, g r • w r

/-- `𝖠 = {α ∈ {0,…,M}^R : Σ_r α_r = M}`. -/
def typesA (R M : ℕ) : Finset (Fin R → ℕ) := piAntidiag (univ : Finset (Fin R)) M

/-- `g^α = Π_r g_r^{α_r}`. -/
def gpow (g : Fin R → ℝ) (α : Fin R → ℕ) : ℝ := ∏ r, g r ^ α r

end CondTypes

/-! ### otfd T `lem:mapcost-mult` (`eq:dualmap-mult`) -/

section MapCost

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-- `π` is an optimal coupling of `μ, ν` for the cost `c` (costs compared in `[0,∞]`). -/
def IsOptPlan (μ : Measure U) (ν : Measure V) (c : U × V → ℝ) (π : Measure (U × V)) : Prop :=
  TauCeti.IsCoupling π μ ν ∧
    ∀ π' : Measure (U × V), TauCeti.IsCoupling π' μ ν →
      ∫⁻ p, ENNReal.ofReal (c p) ∂π ≤ ∫⁻ p, ENNReal.ofReal (c p) ∂π'

end MapCost

/-! ### otfd A `prop:lift-consistency` -/

section Lift

variable {T : ℕ}

/-- `‖v‖² = Σ_k v_k²` on `ℝ^T`. -/
def sqn (v : Fin T → ℝ) : ℝ := ∑ k, v k ^ 2

/-- `u_⊥ = u − ι_K Π_K u`. -/
def tailPart (K : ℕ) (u : Fin T → ℝ) : Fin T → ℝ := fun k => if (k : ℕ) < K then 0 else u k

/-- `F̂^lift(x) = ι_K F̂_K(x_K) + Σ_{k>K} t_k(x_k) e_k`, with `Fh x = ι_K F̂_K(Π_K x)`. -/
def liftMap (K : ℕ) (Fh : (Fin T → ℝ) → Fin T → ℝ) (t : Fin T → ℝ → ℝ) (x : Fin T → ℝ) : Fin T → ℝ :=
  fun k => if (k : ℕ) < K then Fh x k else t k (x k)

/-- `Fh` takes values in `ι_K ℝ^K` (zero tail coordinates). -/
def IsHeadMap (K : ℕ) (Fh : (Fin T → ℝ) → Fin T → ℝ) : Prop :=
  ∀ x (k : Fin T), K ≤ (k : ℕ) → Fh x k = 0

/-- `prop:lift-dual`(i): each tail coordinate map pushes the `k`-th data marginal to the `k`-th
reference marginal. -/
def IsSepTail (P μ : Measure (Fin T → ℝ)) (K : ℕ) (t : Fin T → ℝ → ℝ) : Prop :=
  ∀ k : Fin T, K ≤ (k : ℕ) → Measurable (t k) ∧ P.map (fun x => t k (x k)) = μ.map (fun u => u k)

/-- `m_k = E X_k`. -/
def meanK (P : Measure (Fin T → ℝ)) (k : Fin T) : ℝ := ∫ x, x k ∂P

/-- `Var X_k`. -/
def varK (P : Measure (Fin T → ℝ)) (k : Fin T) : ℝ := ∫ x, (x k - meanK P k) ^ 2 ∂P

/-- `prop:lift-dual`(ii): `t_k(y) = λ_k (y − m_k)`, `λ_k = (E U_k² / Var X_k)^{1/2}`. -/
def quadTail (P μ : Measure (Fin T → ℝ)) (k : Fin T) (y : ℝ) : ℝ :=
  Real.sqrt ((∫ u, u k ^ 2 ∂μ) / varK P k) * (y - meanK P k)

end Lift

/-! ### otfd R `cor:cubic` -/

section Cubic

variable {K : ℕ}

/-- The cubic law: `⊗_k Unif[−λ_k/2, λ_k/2]` on `ℝ^K` (frozen Wave 8c `cubicLaw`, half-widths `λ_k/2`). -/
def cubeLaw (lam : Fin K → ℝ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  (StatFormal.OTFD.Wave8c.cubicLaw fun k => lam k / 2).map (WithLp.toLp 2)

/-- `A_{K,p}`: the closed Euclidean ball of radius `ρ = τ_{K,p} D_∞` intersected with
`Π_k [−λ_k/2, λ_k/2]`. -/
def cubicRegion (lam : Fin K → ℝ) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin K)) :=
  Metric.closedBall 0 ρ ∩ {u | ∀ k, |u k| ≤ lam k / 2}

end Cubic

/-! ### otfd B `prop:rk-sign-test` -/

section SignTest

/-- The permutation p-value `#{σ ∈ S_N : T(y∘σ) ≥ T(y)} / N!` over relabelings of the pooled sample. -/
def permPval {Y : Type*} {N : ℕ} (T : (Fin N → Y) → ℝ) (y : Fin N → Y) : ℝ :=
  ((univ.filter fun σ : Equiv.Perm (Fin N) => T y ≤ T (y ∘ σ)).card : ℝ) / (Nat.factorial N)

end SignTest

namespace Claims

open StatFormal.TrimmedMMD.BangBang (capped qp)
open StatFormal.OTFD.Wave1 (regionDepth)
open StatFormal.OTFD.Wave6b (EntSetting regionSup)
open StatFormal.OTFDR (Qhat)
open StatFormal.OTFDR.Lift (Contam BP)

/-! #### TM `prop:selection` -/

/-- **`prop:selection`**, the selection: the minimiser of `eq:least` over `𝒯_α` exists and is unique. -/
def selection_unique : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ), 0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
      ∃! p, IsLeastTrim x y α β p

/-- **`prop:selection`**, the regularised problems: for `λ > 0` the minimiser exists and is unique. -/
def selection_reg_unique : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β lam : ℝ), 0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → 0 < lam →
      ∃! p, IsRegMin x y α β lam p

/-- **`prop:selection`**, the Tikhonov limit: `(w_λ, v_λ) → (ŵ, v̂)` as `λ ↓ 0`. -/
def selection_limit : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) (pl : ℝ → (Fin n → ℝ) × (Fin m → ℝ)) (ph : (Fin n → ℝ) × (Fin m → ℝ)),
    0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
    (∀ lam, 0 < lam → IsRegMin x y α β lam (pl lam)) → IsLeastTrim x y α β ph →
      Tendsto pl (𝓝[>] 0) (𝓝 ph)

/-! #### ICL `lem:cond-types` -/

/-- **`lem:cond-types` (i)**: `G^iid(·; w(x)) = Σ_α binom(M,α) g(x)^α h_α` with `h_α ∈ conv(ℋ^iid)`
independent of `g`. -/
def cond_types_i : Prop :=
  ∀ (Z : Type) (n M R : ℕ) (Lj : (Fin M → Fin n) → Z → ℝ) (w : Fin R → Fin n → ℝ),
    (∀ r, w r ∈ simplexW (Fin n)) →
      ∃ h : (Fin R → ℕ) → Z → ℝ, (∀ α ∈ typesA R M, h α ∈ convexHull ℝ (Set.range Lj)) ∧
        ∀ g : Fin R → ℝ,
          giid Lj (mixW g w) = ∑ α ∈ typesA R M, ((Nat.multinomial univ α : ℝ) * gpow g α) • h α

/-- **`lem:cond-types` (ii)**: if `g(x) > 0` and `⋃_r supp w_r` has at least `M` elements,
`G(·; w(x)) = Σ_α c_α(x) h_α`, `c_α = t_α g^α / Σ_β t_β g^β`, with `h_α ∈ conv(ℋ)`, `t ∈ Δ_𝖠`
independent of `g`; the normalisers are positive. -/
def cond_types_ii : Prop :=
  ∀ (Z : Type) (n M R : ℕ) (LT : Finset (Fin n) → Z → ℝ) (w : Fin R → Fin n → ℝ),
    (∀ r, w r ∈ simplexW (Fin n)) →
    M ≤ (univ.filter fun j : Fin n => ∃ r, w r j ≠ 0).card →
      ∃ h : (Fin R → ℕ) → Z → ℝ, ∃ t : (Fin R → ℕ) → ℝ,
        (∀ α ∈ typesA R M, h α ∈ convexHull ℝ (LT '' {T | T.card = M})) ∧
        (∀ α ∈ typesA R M, 0 ≤ t α) ∧ ∑ α ∈ typesA R M, t α = 1 ∧
        ∀ g : Fin R → ℝ, (∀ r, 0 < g r) →
          0 < esymW M (mixW g w) ∧ 0 < ∑ β ∈ typesA R M, t β * gpow g β ∧
          gcps M LT (mixW g w) =
            ∑ α ∈ typesA R M, (t α * gpow g α / ∑ β ∈ typesA R M, t β * gpow g β) • h α

/-! #### robust equality paper 2 `prop:wrm` -/

open StatFormal.Wave14a (lagr) in
/-- **`prop:wrm`**, strong concavity: for `λ > λ₀ = L² + osc_S(h) β_h`, `x ↦ f_h(x₀,x) − λ c(x₀,x)` is
`2(λ − λ₀)`-strongly concave on `S`. -/
def wrm_concave : Prop :=
  ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (h' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (h'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (L βh osc lam : ℝ) (x0 : EuclideanSpace ℝ (Fin d)),
    Convex ℝ S → x0 ∈ S →
    (∀ x ∈ S, HasFDerivWithinAt h (h' x) S x) → (∀ x ∈ S, HasFDerivWithinAt h' (h'' x) S x) →
    (∀ x ∈ S, ‖h' x‖ ≤ L) → (∀ x ∈ S, ‖h'' x‖ ≤ βh) → (∀ x ∈ S, ∀ y ∈ S, |h x - h y| ≤ osc) →
    L ^ 2 + osc * βh < lam →
      StrongConcaveOn S (2 * (lam - (L ^ 2 + osc * βh))) (lagr h lam x0)

open StatFormal.Wave14a (lagr) in
/-- **`prop:wrm`**, the certificate: if `φ = f_h(x₀,·) − λc(x₀,·)` is `2(λ − λ₀)`-strongly concave on a
convex `S` (the paper: `S = ℝ^d`), then `sup_S φ ≤ φ(x) + |∇φ(x)|²/{4(λ − λ₀)}` at every `x ∈ S`. -/
def wrm_sup : Prop :=
  ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (L βh osc lam : ℝ) (x0 x : EuclideanSpace ℝ (Fin d)) (φ' : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
    Convex ℝ S → x ∈ S → L ^ 2 + osc * βh < lam →
    StrongConcaveOn S (2 * (lam - (L ^ 2 + osc * βh))) (lagr h lam x0) →
    HasFDerivWithinAt (lagr h lam x0) φ' S x →
      ∀ y ∈ S, lagr h lam x0 y ≤ lagr h lam x0 x + ‖φ'‖ ^ 2 / (4 * (lam - (L ^ 2 + osc * βh)))

open StatFormal.Wave14a (lagr) in
/-- **`prop:wrm`**, both parts on `S`: under the hypotheses of the first part, the explicit gradient
`∇φ(x) = 2(h(x) − h(x₀))∇h(x) − 2λ(x − x₀)` certifies `sup_S φ`. -/
def wrm_cert : Prop :=
  ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (h' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (h'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (L βh osc lam : ℝ) (x0 x : EuclideanSpace ℝ (Fin d)),
    Convex ℝ S → x0 ∈ S → x ∈ S →
    (∀ x ∈ S, HasFDerivWithinAt h (h' x) S x) → (∀ x ∈ S, HasFDerivWithinAt h' (h'' x) S x) →
    (∀ x ∈ S, ‖h' x‖ ≤ L) → (∀ x ∈ S, ‖h'' x‖ ≤ βh) → (∀ x ∈ S, ∀ y ∈ S, |h x - h y| ≤ osc) →
    L ^ 2 + osc * βh < lam →
      ∀ y ∈ S, lagr h lam x0 y ≤ lagr h lam x0 x +
        ‖(2 * (h x - h x0)) • h' x - (2 * lam) • innerSL ℝ (x - x0)‖ ^ 2 /
          (4 * (lam - (L ^ 2 + osc * βh)))

/-! #### otfd T `lem:mapcost-mult` -/

/-- **`lem:mapcost-mult`** (`eq:dualmap-mult`). -/
def mapcost_mult : Prop :=
  ∀ (U V : Type) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q0 : U → V) (c0 c1 : U × V → ℝ) (f : U → ℝ) (g : V → ℝ) (π1 : Measure (U × V)) (β θm θp : ℝ),
    Measurable Q0 → Measurable c0 → Measurable c1 → (∀ p, 0 ≤ c0 p) →
    IsOptPlan μ ν c0 (μ.map fun u => (u, Q0 u)) → Integrable c0 (μ.map fun u => (u, Q0 u)) →
    Integrable f μ → Integrable g ν →
    ∫ u, f u ∂μ + ∫ v, g v ∂ν = ∫ p, c0 p ∂(μ.map fun u => (u, Q0 u)) →
    0 < β → (∀ u ∈ μ.support, ∀ v ∈ ν.support, β * ‖v - Q0 u‖ ^ 2 ≤ c0 (u, v) - f u - g v) →
    IsOptPlan μ ν c1 π1 → 0 < θm → θm ≤ θp →
    (∀ u ∈ μ.support, ∀ v ∈ ν.support, θm ^ 2 * c0 (u, v) ≤ c1 (u, v) ∧ c1 (u, v) ≤ θp ^ 2 * c0 (u, v)) →
      Integrable (fun p => c0 p - f p.1 - g p.2) π1 ∧
      ∫ p, (c0 p - f p.1 - g p.2) ∂π1 ≤ (θp ^ 2 / θm ^ 2 - 1) * ∫ p, c0 p ∂(μ.map fun u => (u, Q0 u)) ∧
      Integrable (fun p => ‖p.2 - Q0 p.1‖ ^ 2) π1 ∧
      ∫ p, ‖p.2 - Q0 p.1‖ ^ 2 ∂π1 ≤
        (θp ^ 2 / θm ^ 2 - 1) * (∫ p, c0 p ∂(μ.map fun u => (u, Q0 u))) / β

/-- **`lem:mapcost-mult`**, "in particular": `a² c₀ ≤ c₁ ≤ c₀`, `0 < a ≤ 1`, factor `a⁻² − 1`. -/
def mapcost_mult_one : Prop :=
  ∀ (U V : Type) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q0 : U → V) (c0 c1 : U × V → ℝ) (f : U → ℝ) (g : V → ℝ) (π1 : Measure (U × V)) (β a : ℝ),
    Measurable Q0 → Measurable c0 → Measurable c1 → (∀ p, 0 ≤ c0 p) →
    IsOptPlan μ ν c0 (μ.map fun u => (u, Q0 u)) → Integrable c0 (μ.map fun u => (u, Q0 u)) →
    Integrable f μ → Integrable g ν →
    ∫ u, f u ∂μ + ∫ v, g v ∂ν = ∫ p, c0 p ∂(μ.map fun u => (u, Q0 u)) →
    0 < β → (∀ u ∈ μ.support, ∀ v ∈ ν.support, β * ‖v - Q0 u‖ ^ 2 ≤ c0 (u, v) - f u - g v) →
    IsOptPlan μ ν c1 π1 → 0 < a → a ≤ 1 →
    (∀ u ∈ μ.support, ∀ v ∈ ν.support, a ^ 2 * c0 (u, v) ≤ c1 (u, v) ∧ c1 (u, v) ≤ c0 (u, v)) →
      ∫ p, (c0 p - f p.1 - g p.2) ∂π1 ≤ (1 / a ^ 2 - 1) * ∫ p, c0 p ∂(μ.map fun u => (u, Q0 u)) ∧
      ∫ p, ‖p.2 - Q0 p.1‖ ^ 2 ∂π1 ≤ (1 / a ^ 2 - 1) * (∫ p, c0 p ∂(μ.map fun u => (u, Q0 u))) / β

/-! #### otfd A `prop:lift-consistency` -/

/-- **`prop:lift-consistency`**, separable tails (`prop:lift-dual`(i)):
`E‖F̂^lift(X) − F(X)‖² ≤ E‖ι_K F̂_K(X_K) − F(X)‖² + 3 E‖U_⊥‖²`. -/
def lift_consistency_sep : Prop :=
  ∀ (T K : ℕ) (P μ : Measure (Fin T → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F Fh : (Fin T → ℝ) → Fin T → ℝ) (t : Fin T → ℝ → ℝ),
    Measurable F → P.map F = μ → Measurable Fh → IsHeadMap K Fh → IsSepTail P μ K t →
      ∫⁻ x, ENNReal.ofReal (sqn (liftMap K Fh t x - F x)) ∂P ≤
        ∫⁻ x, ENNReal.ofReal (sqn (Fh x - F x)) ∂P + 3 * ∫⁻ u, ENNReal.ofReal (sqn (tailPart K u)) ∂μ

/-- **`prop:lift-consistency`**, diagonal quadratic tails (`prop:lift-dual`(ii)). -/
def lift_consistency_quad : Prop :=
  ∀ (T K : ℕ) (P μ : Measure (Fin T → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F Fh : (Fin T → ℝ) → Fin T → ℝ),
    Measurable F → P.map F = μ → Measurable Fh → IsHeadMap K Fh →
    (∀ k : Fin T, K ≤ (k : ℕ) → Integrable (fun x => x k ^ 2) P ∧ 0 < varK P k ∧
      Integrable (fun u => u k ^ 2) μ) →
      ∫⁻ x, ENNReal.ofReal (sqn (liftMap K Fh (quadTail P μ) x - F x)) ∂P ≤
        ∫⁻ x, ENNReal.ofReal (sqn (Fh x - F x)) ∂P + 3 * ∫⁻ u, ENNReal.ofReal (sqn (tailPart K u)) ∂μ

/-- **`prop:lift-consistency`**, the tail term: `∫‖u − ι_K Π_K u‖² dμ → 0` as `K → ∞` (any Hilbert
basis, `∫‖u‖² dμ < ∞`). -/
def lift_tail_vanish : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (μ : Measure H),
    ∫⁻ u, ‖u‖ₑ ^ 2 ∂μ < ⊤ →
      Tendsto (fun K : ℕ => ∫⁻ u, ‖u - ∑ k ∈ range K, ⟪b k, u⟫_ℝ • b k‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

/-! #### otfd R `lem:divergence` -/

/-- **`lem:divergence`**: `P(A_k) ≥ α > 0`, `β_k ≥ 0`, `Σ β_k = ∞` ⟹ `P(Σ_k β_k 1_{A_k} = ∞) ≥ α`. -/
def divergence : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (α : ℝ) (β : ℕ → ℝ),
    (∀ k, MeasurableSet (A k)) → 0 < α → (∀ k, ENNReal.ofReal α ≤ P (A k)) → (∀ k, 0 ≤ β k) →
    ¬ Summable β →
      ENNReal.ofReal α ≤ P {ω | ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (β k)) ω = ⊤}

/-! #### otfd R `cor:cubic` -/

/-- **`cor:cubic`**, depth: `β(A_{K,p}) = 0` as soon as the ball's radius exceeds a half-width
`λ_k/2` (in particular the smallest one, `λ_K/2`). -/
def cubic_depth : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ) (ρ : ℝ), (∀ k, 0 < lam k) → (∃ k, lam k / 2 < ρ) →
    regionDepth (cubeLaw lam) (cubicRegion lam ρ) = 0

/-- **`cor:cubic`**, bands: the entropic band of `A_{K,p}` breaks down with a single replaced curve. -/
def cubic_single : Prop :=
  ∀ (K n : ℕ) (lam : Fin K → ℝ) (ρ ε : ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)),
    (∀ k, 0 < lam k) → (∃ k, lam k / 2 < ρ) → 1 ≤ n → EntSetting (cubeLaw lam) ε fsel →
      ∀ M : ℝ, ∃ Z' ∈ Contam Z 1, ∃ u ∈ cubicRegion lam ρ, M < ‖Qhat Z' (fsel Z') ε u‖

/-- **`cor:cubic`**, breakdown point: `BP ≤ 1/n` for the region estimator `sup_{u ∈ A_{K,p}} ‖Q̂(u)‖`. -/
def cubic_bp : Prop :=
  ∀ (K n : ℕ) (lam : Fin K → ℝ) (ρ ε : ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)),
    (∀ k, 0 < lam k) → (∃ k, lam k / 2 < ρ) → 1 ≤ n → EntSetting (cubeLaw lam) ε fsel →
      BP (regionSup ε fsel (cubicRegion lam ρ)) Z ≤ 1 / n

/-! #### otfd B `prop:rk-sign-test` -/

/-- **`prop:rk-sign-test`**: under exchangeability of the `n₂ + m` pooled curves (given `𝓘₁`), the
permutation p-value of any statistic of the signs is super-uniform. -/
def rk_sign_test : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (n₂ m : ℕ)
    (μ : Measure (Fin (n₂ + m) → X)) [IsProbabilityMeasure μ] (sgn : X → Y)
    (T : (Fin (n₂ + m) → Y) → ℝ),
    Measurable sgn → Measurable T →
    (∀ σ : Equiv.Perm (Fin (n₂ + m)), μ.map (fun x => x ∘ σ) = μ) →
      ∀ α : ℝ, μ {x | permPval T (sgn ∘ x) ≤ α} ≤ ENNReal.ofReal α

end Claims

end StatFormal.Wave16a
