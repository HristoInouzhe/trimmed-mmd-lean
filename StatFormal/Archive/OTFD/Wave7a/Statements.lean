import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Wave4.Statements
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — otfd wave 7a: B `lem:oos-potential`, C `prop:cond-sign-pivot`,
# C `thm:neural-band-consistency`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-B_bands.md`, `otfd-C_conditional.md`; current text
of 2026-10-14, paths below are under `otfd/papers/`):
* B `lem:oos-potential` (`B_bands/main.tex:664-695`), with the maps of `subsec:oos-menu` (`main.tex:586-618`) and the
  Karp/Moreau–Yosida notation of `prop:ext-karp-certificate` (`B_bands/supplement.tex:5003-5015`: `φ(y) =
  max_j(⟨β_j,y⟩ − ϑ_j)`, `Q̂_Karp(u) = σ⁻¹L_K⁻¹∇φ_{ε₀}(L_Ku)`, `φ_{ε₀}(y) = min_z{φ(z) + ‖z−y‖²/(2ε₀)}`; Step 1 of its
  proof, `:5062-5075`, gives `∇φ_{ε₀}(y) = (y − P(y))/ε₀`).
* C `prop:cond-sign-pivot` (`C_conditional/supplement.tex:2257-2299`, proof `:2301-2332`), with the example
  `rem:cond-sign-imbalance` (`:2334-2350`).
* C `thm:neural-band-consistency` (`C_conditional/main.tex:738-756`), with the population band
  `eq:conditional-pop-band` (`main.tex:626-640`, standing assumption: `μ_K` with compact convex topological support
  `𝒰_K`, every open set meeting `𝒰_K` has positive mass), `E_K` (`main.tex:265`), and the certified
  `lem:neural-witness-ball` (`C_conditional/supplement.tex:2814-2826`; frozen `Wave4.Claims.neural_witness_ball`).
Reuses the frozen `OTFD/Bands/Statements.lean` (`simplex`, `softmax`, `mnormSq`, `Qent`, `score`, `IsSimplexProj`)
and `OTFD/Wave4/Statements.lean` (`dotCLM`), imported, not copied.

Covered:
* B (a): `oos_ent_affine` (the entropic map is `Σ_j softmax(s(u)/ε)_j Z_j` with the affine scores
  `s_j = a_j + ⟨b_j,u⟩`, `a_j = f_j − ‖Z_j‖²_M`, `b_j = 2MZ_j`); `oos_quad_affine` (the projection of the raw
  quadratic scores onto `Δ_n` is that of `s(u)/λ`: an `iff`, every `λ`); `simplex_proj_exists_unique` (the projection
  exists and is unique, so the quadratic map is well defined).
  (b): `oos_ent_potential`, `oos_quad_potential` (`ψ(u) = λΦ(s(u)/λ)` with `Φ` the log-sum-exp, resp.
  `Φ(x) = max_{q∈Δ_n}{⟨q,x⟩ − ½‖q‖²}`, is convex, differentiable with `∇ψ(u) = Σ_j q_j(u)b_j`, and
  `Σ_j q_j(u)b_j = 2M Q̂(u)`).
  (c): `karp_prox_unique` (the proximal point exists and is unique), `karp_env_grad` (`φ_{ε₀}` is differentiable with
  `∇φ_{ε₀}(y) = (y − P(y))/ε₀`), `karp_potential` (`ψ(u) = (2/σ)φ_{ε₀}(L_Ku)` is convex and differentiable with
  `∇ψ = 2M Q̂_Karp`, and `∇ψ` is Lipschitz). The closing sentence ("in every case `Q̂ = ½M⁻¹∇ψ`, `ψ` convex") is the
  conjunction of `oos_ent_potential`, `oos_quad_potential`, `karp_potential`.
* C `prop:cond-sign-pivot`: (i) `pivot_joint` (the law of `(C, F(C,Z))` is `π ⊗ μ_K`), `pivot_indep`
  (`F(C,Z) ∼ μ_K`, independent of `C`), `pivot_sign` (the same for `s(F(C,Z))` with law `s#μ_K`), every `π`;
  (ii) `groups_mix` (sign law `= ∫ k_g dπ_g`), `groups_const_iff`, `groups_ref_iff`, `groups_fitted`; (iii)
  `diff_shows` (first sentence), `imbalance_example` (second sentence, an explicit example consistent with the
  standing setting); (iv) `common_law`, `reweight`.
* C `thm:neural-band-consistency`: `neural_band_uniform` (deterministic core: for every `ε > 0` there is `η > 0` such
  that every monotone `T` with `𝓡 ≤ η` has all band edges within `ε` of the population edges, uniformly in `t` and
  `0 < p ≤ 1−δ`); `neural_band_ae` (a.s. premise ⇒ a.s. conclusion), `neural_band_prob` (in-probability premise ⇒
  in-probability conclusion); `neural_band_rate` (`eq:neural-band-rate`, `C_{K,ρ}` depending on `K, ρ` only).

Not covered (declared):
* B: the sentence "Indeed …" of (a) (its proof); "in particular this map need not be treated as a degenerate
  `λ → 0` limit" (interpretive). That `φ` is the Laguerre potential *of the fitted hard assignment* (any slopes
  `β_j` and offsets `ϑ_j` are allowed: generalisation).
* C sign pivot: McCann's theorem (existence and a.e. uniqueness of the rank map `F_{K,c}`) and the measurable selection
  `F` — both are the proposition's own hypotheses ("assume a Borel map `F` …"), entered as `F` Borel on
  `ℝ^q × ℝ^K` with `F(c,·)#P_{K,c} = μ_K` for `c ∈ 𝒳_ac`; the remarks before and after the proposition (versions of
  the conditional law, `W₁`-continuous versions).
* C neural: `lem:full-support-region`(i) is **not certified** (no target in `certify/targets.toml`). Its conclusion
  for the regions, `supp(μ_K|_{A_{K,p}}) = A_{K,p}` for `0 < p ≤ 1−δ`, enters as the explicit hypothesis
  `hsupp` (it is what turns the sup over `A_{K,p}` of the continuous `⟨v,Q⟩` into the essential sup of
  `eq:conditional-pop-band`; without it the two-sided limit fails in general, see the critic notes). The last
  sentence of the theorem (coverage conclusions via `cor:conditional-test-coverage`). That the networks are exact
  gradients of convex potentials enters only through monotonicity of `T` on `O` (generalisation).

Encodings (see card):
* B: `ℝ^K = Fin K → ℝ`, `⟨·,·⟩ = dotProduct`, `‖x‖²_M = xᵀMx` (`mnormSq`), `M.PosDef`; `∇ψ(u) = g` is
  `HasFDerivAt ψ (dotCLM g) u` (frozen Wave 4); `Q̂ = ½M⁻¹∇ψ` is written `∇ψ(u) = 2 • (M *ᵥ Q̂(u))`. `Φ` for the
  quadratic map is `sSup` of `⟨q,x⟩ − ½‖q‖²` over the simplex (nonempty compact for `n ≥ 1`: no junk); the quadratic
  map is `Σ_j q_j(u)Z_j` for a selection `q(u)` of the projection of the raw scores `(f_j − ‖u−Z_j‖²_M)/λ`, with
  `λ > 0` arbitrary (the paper's `λ = γ/m`). Karp: `L` with `LᵀL = M`, `L_K⁻¹` the matrix inverse (invertible since
  `M` is positive definite), `‖·‖₂² = dotProduct`, `φ_{ε₀} = ⨅_z` (bounded below: no junk), `P` any selection of
  minimisers (unique by `karp_prox_unique`); `Q̂_Karp(u) = σ⁻¹L⁻¹((L u − P(L u))/ε₀)`, i.e. `σ⁻¹L⁻¹∇φ_{ε₀}(Lu)` by
  `karp_env_grad`. "Lipschitz gradient" is `∃ C, LipschitzWith C ∇ψ` (sup norm on `Fin K → ℝ`; all norms are
  equivalent). `n ≥ 1` throughout (for `n = 0` the maps are empty sums).
* C sign pivot: covariates `ℝ^q = Fin q → ℝ`, responses `ℝ^K = Fin K → ℝ`, `P_{K,c}` a Markov kernel `κ`; "`Z | C = c ∼
  P_{K,c}` for `π`-a.e. `c`" is `law(C,Z) = π ⊗ₘ κ`. The sign map `s` is any Borel map `ℝ^K → 𝒮` (generalisation of
  `u ↦ u/ρ_{μ_K}(u)`; `μ_K({0}) = 0` and absolute continuity of `P_{K,c}` are then unused and dropped, the rank-map
  identity being a hypothesis). `k_g(c) = (P^g_c).map (s ∘ F(c,·))` (`kLaw`), the group's sign law is
  `(π_g ⊗ₘ P^g).map (s ∘ F)` (`signLaw`), and `∫ k_g dπ` is the set function `E ↦ ∫⁻ k_g(c)(E) dπ(c)`. "Covariate
  laws carried by `𝒳_ac`" are probability measures `π` with `π(𝒳_ac) = 1`. "`P^g_c ≠ P_{K,c}` on a set of positive
  `π_g`-measure" is `¬ ∀ᵐ c ∂π_g, P^g_c = P_{K,c}` (no measurability of that set is needed). The expectation in (iv)
  is a lower Lebesgue integral with the `ℝ≥0∞`-valued `dπ*/dπ_g` (nonnegative integrand). In `imbalance_example`
  `K = q = 1`; a single witness (`μ = Unif[−½,½]`, `P_{1,c} = μ`, `F(c,z) = z`, group kernel `δ_c`, covariate
  laws `δ_{±1}`) works for the sign map `s(u) = ρ(u)⁻¹u` with **every** Borel `ρ > 0` off `0` (`∃` witness, then
  `∀ ρ`), so in particular for the gauge `ρ_{μ}` of its own reference; it satisfies the standing setting (`μ`
  absolutely continuous, `μ{0} = 0`, `P_{K,c}` absolutely continuous, `F(c,·)#P_{K,c} = μ`, `F(c,·)` monotone,
  i.e. the McCann map in `K = 1`). The optional `P^g_c ≪ P_{K,c}` is not imposed (the Dirac group kernel fails it).
* C neural: `ℝ^K = EuclideanSpace ℝ (Fin K)`; the query `x` is fixed and suppressed (`Q = Q_{K,x}`, `T = T_ϑ(·,x)`).
  Regions `A : ℝ → Set ℝ^K` (`A p = A_{K,p}`), `S = A(1−δ)` compact, `A p ⊆ S` for `0 < p ≤ 1−δ` (nestedness), each
  `A p` measurable. "`S ⊂ O ⊂ int 𝒰_K`" plus the standing support assumption is: `O` open, `S ⊆ O`, and every ball
  centred in `O` has positive `μ_K`-mass. `μ_K` is a probability measure. Edges are `EReal`-valued
  (`𝔪(t) ± h(±e(t))`), `h^NN(v) = sup_{u∈A_{K,p}}⟨v,T(u)⟩` (`nnSup`), `h^pop(v) = μ_K-ess sup_{u∈A_{K,p}}⟨v,Q(u)⟩`
  (`popSup`: `essSup` w.r.t. `μ_K|_{A_{K,p}}` in `EReal`, no junk); "`|x − y| ≤ η`" is `x ≤ y + η ∧ y ≤ x + η`
  (`EClose`). `E_K` is any `E ≥ sup_t‖e(t)‖`. `𝓡 = ∫⁻_O ‖T − Q‖² dμ_K` (`risk`, as in the frozen witness-ball lemma).
  Modes: a.s. is `∀ᵐ ω` of `𝓡_n(ω) → 0`; in probability uses the measurable-event convention on both sides
  (for all `η, δ' > 0`, eventually some measurable `E ⊆ {𝓡_n ≤ η}` has `P(E) ≥ 1 − δ'`). Rate: "locally
  `L`-Lipschitz and density `≥ ρ` near `S`" is an open `O' ⊇ S`, `O' ⊆ O`, with `‖Q x − Q y‖ ≤ L‖x − y‖` on `O'` and
  `μ_K(B) ≥ ρ·Leb(B)` for Borel `B ⊆ O'`; `L > 0`; "for small risk" is `∃ R₀ > 0` (depending on the data) such that the
  bound holds for every `R ∈ (0, R₀]` with `𝓡 ≤ R` (risk `0` is covered by letting `R ↓ 0`); `C_{K,ρ}` is chosen before
  the data. Powers are `Real.rpow`.

Critic notes:
* B (c) holds for every convex `φ` with proximal points (`RouteOOS`: `prox_VI`, `prox_firm`, `env_subgrad`); the Laguerre form is used only for their existence.
* C `prop:cond-sign-pivot` needs neither absolute continuity nor `μ_K({0}) = 0` once the Borel rank map `F` with
  `F(c,·)#P_{K,c} = μ_K` is given; the "only if" halves of (ii) use Dirac covariate laws, which are carried by `𝒳_ac`.
* C `thm:neural-band-consistency` does not state the support condition `supp(μ_K|_{A_{K,p}}) = A_{K,p}` that turns
  the sup over `A_{K,p}` into the **ess-sup** of `eq:conditional-pop-band` (ranking note 3). In the paper's standing
  setting it follows from `lem:full-support-region`(i) when `A_{K,p}` is convex with nonempty interior, so this is
  an unstated dependency on an uncertified lemma, not an error. It cannot be dropped from the encoding: if
  `μ_K(A ∩ N) = 0` for an open `N` meeting `A` where `⟨v,Q⟩` is maximal (e.g. `A` with a thin spike outside the
  bulk), the neural edge, a sup with `T → Q` uniformly on `S`, tends to `sup_A⟨v,Q⟩`, which is strictly larger than
  the ess-sup. Here it is the hypothesis `hsupp`.
* Degenerate edge case of `eq:neural-band-rate`: for `L = 0` (locally constant `Q`) the printed bound is `0`, which
  is false (`T = Q + c` is monotone, with risk `‖c‖²μ_K(O)` and error `‖c‖ > 0`); the claim takes `L > 0`, and the
  threshold `R₀` depends on `L`, `S` and `O'`.
* `hsupp` follows from the paper's setting: `μ_K ≪ Leb` and `μ_K(A_{K,p}) = p > 0` give `A_{K,p}` (convex)
  nonempty interior, so `lem:full-support-region`(i) applies; it is a declared conditional, not a paper defect.
* S3, `eq:neural-band-rate` misses `L > 0`: `K = 1`, `μ = Unif[−1,1]`, `P_{K,x} = δ₀` (`Q ≡ 0`, `0`-Lipschitz),
  `O = (−0.9, 0.9)`, `T ≡ c`: risk `0.9c² → 0` while the error `|c|‖e(t)‖` stays positive and the bound is `0`.
* In `imbalance_example` the covariates `±1` put the group's responses outside `supp P_{K,c} = [−½,½]`, so the sign
  depends on how `F(c,·)` is extended there (here the identity), which the paper itself flags.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave7a

open StatFormal.OTFD.Bands (simplex softmax mnormSq Qent score IsSimplexProj)
open StatFormal.OTFD.Wave4 (dotCLM)

/-! ### B `lem:oos-potential` -/

section OOS
variable {n K : ℕ}

/-- Intercepts `a_j = f_j − ‖Z_j‖²_M`. -/
def oosA (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) : Fin n → ℝ :=
  fun j => f j - mnormSq M (Z j)

/-- Slopes `b_j = 2 M Z_j`. -/
def oosB (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) : Fin n → Fin K → ℝ :=
  fun j => (2 : ℝ) • (M *ᵥ Z j)

/-- Raw quadratic scores `(f_j − ‖u − Z_j‖²_M)/λ`. -/
def rawScore (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ)
    (u : Fin K → ℝ) : Fin n → ℝ :=
  fun j => (f j - mnormSq M (u - Z j)) / lam

/-- Log-sum-exp `Φ(x) = log Σ_k e^{x_k}`. -/
def lse (x : Fin n → ℝ) : ℝ := Real.log (∑ k, Real.exp (x k))

/-- `Φ(x) = max_{q∈Δ_n} {⟨q,x⟩ − ½‖q‖²}`. -/
def quadPhi (x : Fin n → ℝ) : ℝ :=
  sSup ((fun q : Fin n → ℝ => ∑ i, q i * x i - (∑ i, q i ^ 2) / 2) '' simplex n)

/-- `ψ(u) = λ Φ(s(u)/λ)` for a profile `Φ` and affine scores `s`. -/
def scorePot (Φ : (Fin n → ℝ) → ℝ) (lam : ℝ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ)
    (u : Fin K → ℝ) : ℝ :=
  lam * Φ (fun k => score a b k u / lam)

/-- Barycentric map `Σ_j q_j Z_j`. -/
def baryMap (q : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) : Fin K → ℝ := ∑ j, q j • Z j

/-- Laguerre potential `φ(y) = max_j (⟨β_j, y⟩ − ϑ_j)`. -/
def laguerre (β : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (y : Fin K → ℝ) : ℝ := ⨆ j, (β j ⬝ᵥ y - θ j)

/-- Proximal objective `φ(z) + ‖z − y‖²/(2ε₀)`. -/
def proxObj (φ : (Fin K → ℝ) → ℝ) (ε₀ : ℝ) (y z : Fin K → ℝ) : ℝ :=
  φ z + (z - y) ⬝ᵥ (z - y) / (2 * ε₀)

/-- Moreau envelope `φ_{ε₀}(y) = inf_z {φ(z) + ‖z − y‖²/(2ε₀)}`. -/
def moreauEnv (φ : (Fin K → ℝ) → ℝ) (ε₀ : ℝ) (y : Fin K → ℝ) : ℝ := ⨅ z, proxObj φ ε₀ y z

/-- `z` is a proximal point of `y`: it minimises the proximal objective. -/
def IsProx (φ : (Fin K → ℝ) → ℝ) (ε₀ : ℝ) (y z : Fin K → ℝ) : Prop :=
  ∀ z', proxObj φ ε₀ y z ≤ proxObj φ ε₀ y z'

/-- Karp/Moreau–Yosida map `Q̂(u) = σ⁻¹ L⁻¹ (L u − P(L u))/ε₀` for a proximal selection `P`. -/
def karpMap (σ ε₀ : ℝ) (L : Matrix (Fin K) (Fin K) ℝ) (P : (Fin K → ℝ) → Fin K → ℝ) (u : Fin K → ℝ) :
    Fin K → ℝ :=
  σ⁻¹ • (L⁻¹ *ᵥ (ε₀⁻¹ • (L *ᵥ u - P (L *ᵥ u))))

/-- Karp potential `ψ(u) = (2/σ) φ_{ε₀}(L u)`. -/
def karpPot (σ ε₀ : ℝ) (L : Matrix (Fin K) (Fin K) ℝ) (φ : (Fin K → ℝ) → ℝ) (u : Fin K → ℝ) : ℝ :=
  (2 / σ) * moreauEnv φ ε₀ (L *ᵥ u)

end OOS

/-! ### C `prop:cond-sign-pivot` -/

section Pivot
variable {q K : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮]

/-- `k_g(c) = s#(F(c,·)#P^g_c)`. -/
def kLaw (s : (Fin K → ℝ) → 𝒮) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ)
    (κ : Kernel (Fin q → ℝ) (Fin K → ℝ)) (c : Fin q → ℝ) : Measure 𝒮 :=
  (κ c).map (fun z => s (F (c, z)))

/-- Sign law of a group with covariate law `π` and conditional laws `κ`: the law of `s(F(C,Z))`. -/
def signLaw (s : (Fin K → ℝ) → 𝒮) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ)
    (π : Measure (Fin q → ℝ)) (κ : Kernel (Fin q → ℝ) (Fin K → ℝ)) : Measure 𝒮 :=
  (π ⊗ₘ κ).map (fun p => s (F p))

/-- `F` is a Borel joint rank map: `F(c,·)#P_{K,c} = μ_K` for every `c ∈ 𝒳_ac`. -/
def IsRankMap (μ : Measure (Fin K → ℝ)) (κ : Kernel (Fin q → ℝ) (Fin K → ℝ)) (X : Set (Fin q → ℝ))
    (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  Measurable F ∧ ∀ c ∈ X, (κ c).map (fun z => F (c, z)) = μ

end Pivot

/-! ### C `thm:neural-band-consistency` -/

section Neural
variable {K : ℕ}

/-- `h^NN(v) = sup_{u∈A} ⟨v, T(u)⟩` in `EReal`. -/
def nnSup (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K)))
    (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  ⨆ u ∈ A, ((⟪v, T u⟫_ℝ : ℝ) : EReal)

/-- `h^pop(v) = μ-ess sup_{u∈A} ⟨v, Q(u)⟩` in `EReal`. -/
def popSup (μ : Measure (EuclideanSpace ℝ (Fin K))) (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  essSup (fun u => ((⟪v, Q u⟫_ℝ : ℝ) : EReal)) (μ.restrict A)

/-- Upper edge `𝔪 + h(v)`. -/
def edgeUpE (h : EuclideanSpace ℝ (Fin K) → EReal) (mo : ℝ) (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  (mo : EReal) + h v

/-- Lower edge `𝔪 − h(−v)`. -/
def edgeLoE (h : EuclideanSpace ℝ (Fin K) → EReal) (mo : ℝ) (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  (mo : EReal) - h (-v)

/-- `|x − y| ≤ η` for extended reals: `x ≤ y + η` and `y ≤ x + η`. -/
def EClose (x y : EReal) (η : ℝ) : Prop := x ≤ y + (η : EReal) ∧ y ≤ x + (η : EReal)

/-- Integrated risk `𝓡 = ∫⁻_O ‖T − Q‖² dμ`. -/
def risk (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (T Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ∫⁻ u in O, ENNReal.ofReal (‖T u - Q u‖ ^ 2) ∂μ

/-- `T` is monotone on `O`. -/
def MonoOn (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (O : Set (EuclideanSpace ℝ (Fin K))) :
    Prop :=
  ∀ v ∈ O, ∀ w ∈ O, 0 ≤ ⟪T v - T w, v - w⟫_ℝ

/-- Both band edges at every `t` and every level `0 < p ≤ 1−δ` are within `ε` of the population edges. -/
def BandsClose {𝒯 : Type} (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (T Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (ε : ℝ) : Prop :=
  ∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
    EClose (edgeUpE (nnSup T (A p)) (mo t) (e t)) (edgeUpE (popSup μ Q (A p)) (mo t) (e t)) ε ∧
    EClose (edgeLoE (nnSup T (A p)) (mo t) (e t)) (edgeLoE (popSup μ Q (A p)) (mo t) (e t)) ε

/-- Standing setting of the theorem at a fixed query (see the encodings). -/
def NeuralSetting {𝒯 : Type} (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact (A (1 - δ)) ∧ IsOpen O ∧ A (1 - δ) ⊆ O ∧ ContinuousOn Q O ∧
    (∀ x ∈ O, ∀ r, 0 < r → 0 < μ (Metric.ball x r)) ∧
    (∀ p, 0 < p → p ≤ 1 - δ → A p ⊆ A (1 - δ) ∧ MeasurableSet (A p)) ∧
    (∀ t, ‖e t‖ ≤ E)

end Neural

namespace Claims

/-! ### B `lem:oos-potential` -/

/-- (a), entropic: `Q̂(u) = Σ_j softmax(s(u)/ε)_j Z_j` with `s_j(u) = a_j + ⟨b_j,u⟩`. -/
def oos_ent_affine : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (u : Fin K → ℝ),
    M.PosDef →
      Qent ε M Z f u = ∑ j, softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε) j • Z j

/-- (a), quadratic: the projection of the raw scores onto `Δ_n` is the projection of `s(u)/λ`. -/
def oos_quad_affine : Prop :=
  ∀ (n K : ℕ) (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (u : Fin K → ℝ) (q : Fin n → ℝ),
    M.PosDef →
      (IsSimplexProj (rawScore lam M f Z u) q ↔
        IsSimplexProj (fun k => score (oosA M f Z) (oosB M Z) k u / lam) q)

/-- The Euclidean projection onto `Δ_n` exists and is unique (`n ≥ 1`). -/
def simplex_proj_exists_unique : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), 0 < n → ∃! q, IsSimplexProj x q

/-- (b), entropic: `ψ = ε lse(s/ε)` is convex, `∇ψ(u) = Σ_j q_j(u) b_j = 2M Q̂(u)`. -/
def oos_ent_potential : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ),
    0 < n → 0 < ε → M.PosDef →
      ConvexOn ℝ Set.univ (scorePot lse ε (oosA M f Z) (oosB M Z)) ∧
      ∀ u, HasFDerivAt (scorePot lse ε (oosA M f Z) (oosB M Z))
          (dotCLM (∑ j, softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε) j • oosB M Z j)) u ∧
        ∑ j, softmax (fun k => score (oosA M f Z) (oosB M Z) k u / ε) j • oosB M Z j =
          (2 : ℝ) • (M *ᵥ Qent ε M Z f u)

/-- (b), quadratic: for the projection weights `q(u)`, `ψ = λΦ(s/λ)` is convex and
`∇ψ(u) = Σ_j q_j(u) b_j = 2M Q̂(u)`. -/
def oos_quad_potential : Prop :=
  ∀ (n K : ℕ) (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ),
    0 < n → 0 < lam → M.PosDef → (∀ u, IsSimplexProj (rawScore lam M f Z u) (q u)) →
      ConvexOn ℝ Set.univ (scorePot quadPhi lam (oosA M f Z) (oosB M Z)) ∧
      ∀ u, HasFDerivAt (scorePot quadPhi lam (oosA M f Z) (oosB M Z))
          (dotCLM (∑ j, q u j • oosB M Z j)) u ∧
        ∑ j, q u j • oosB M Z j = (2 : ℝ) • (M *ᵥ baryMap (q u) Z)

/-- (c): proximal points of the Laguerre potential exist and are unique. -/
def karp_prox_unique : Prop :=
  ∀ (n K : ℕ) (β : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (ε₀ : ℝ) (y : Fin K → ℝ),
    0 < n → 0 < ε₀ → ∃! z, IsProx (laguerre β θ) ε₀ y z

/-- (c): the Moreau envelope is differentiable with `∇φ_{ε₀}(y) = (y − P(y))/ε₀`. -/
def karp_env_grad : Prop :=
  ∀ (n K : ℕ) (β : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (ε₀ : ℝ) (P : (Fin K → ℝ) → Fin K → ℝ),
    0 < n → 0 < ε₀ → (∀ y, IsProx (laguerre β θ) ε₀ y (P y)) →
      ∀ y, HasFDerivAt (moreauEnv (laguerre β θ) ε₀) (dotCLM (ε₀⁻¹ • (y - P y))) y

/-- (c): `ψ(u) = (2/σ)φ_{ε₀}(L u)` is convex, differentiable with Lipschitz gradient, and `∇ψ = 2M Q̂_Karp`. -/
def karp_potential : Prop :=
  ∀ (n K : ℕ) (β : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (ε₀ σ : ℝ) (M L : Matrix (Fin K) (Fin K) ℝ)
    (P : (Fin K → ℝ) → Fin K → ℝ),
    0 < n → 0 < ε₀ → 0 < σ → M.PosDef → L.transpose * L = M →
    (∀ y, IsProx (laguerre β θ) ε₀ y (P y)) →
      ConvexOn ℝ Set.univ (karpPot σ ε₀ L (laguerre β θ)) ∧
      (∀ u, HasFDerivAt (karpPot σ ε₀ L (laguerre β θ)) (dotCLM ((2 : ℝ) • (M *ᵥ karpMap σ ε₀ L P u))) u) ∧
      ∃ C, LipschitzWith C (fun u => (2 : ℝ) • (M *ᵥ karpMap σ ε₀ L P u))

/-! ### C `prop:cond-sign-pivot` -/

/-- (i) The joint law of `(C, F(C,Z))` is `π ⊗ μ_K`. -/
def pivot_joint : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ] (κ : Kernel (Fin q → ℝ) (Fin K → ℝ))
    [IsMarkovKernel κ] (X : Set (Fin q → ℝ)) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ)
    (π : Measure (Fin q → ℝ)) [IsProbabilityMeasure π] (C : Ω → Fin q → ℝ) (Z : Ω → Fin K → ℝ),
    MeasurableSet X → IsRankMap μ κ X F → π X = 1 → Measurable C → Measurable Z →
    P.map (fun ω => (C ω, Z ω)) = π ⊗ₘ κ →
      P.map (fun ω => (C ω, F (C ω, Z ω))) = π.prod μ

/-- (i) `F(C,Z) ∼ μ_K`, independently of `C`. -/
def pivot_indep : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ] (κ : Kernel (Fin q → ℝ) (Fin K → ℝ))
    [IsMarkovKernel κ] (X : Set (Fin q → ℝ)) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ)
    (π : Measure (Fin q → ℝ)) [IsProbabilityMeasure π] (C : Ω → Fin q → ℝ) (Z : Ω → Fin K → ℝ),
    MeasurableSet X → IsRankMap μ κ X F → π X = 1 → Measurable C → Measurable Z →
    P.map (fun ω => (C ω, Z ω)) = π ⊗ₘ κ →
      IndepFun C (fun ω => F (C ω, Z ω)) P ∧ P.map (fun ω => F (C ω, Z ω)) = μ

/-- (i) `s(F(C,Z)) ∼ s#μ_K`, independently of `C`, for any Borel sign map `s`. -/
def pivot_sign : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ]
    (κ : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κ] (X : Set (Fin q → ℝ))
    (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮)
    (π : Measure (Fin q → ℝ)) [IsProbabilityMeasure π] (C : Ω → Fin q → ℝ) (Z : Ω → Fin K → ℝ),
    MeasurableSet X → IsRankMap μ κ X F → Measurable s → π X = 1 → Measurable C → Measurable Z →
    P.map (fun ω => (C ω, Z ω)) = π ⊗ₘ κ →
      IndepFun C (fun ω => s (F (C ω, Z ω))) P ∧ P.map (fun ω => s (F (C ω, Z ω))) = μ.map s

/-- (ii) The sign law of a group is the mixture `∫ k_g dπ_g`. -/
def groups_mix : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κg]
    (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮)
    (π : Measure (Fin q → ℝ)) [IsProbabilityMeasure π],
    Measurable F → Measurable s →
      ∀ E, MeasurableSet E → signLaw s F π κg E = ∫⁻ c, kLaw s F κg c E ∂π

/-- (ii) The sign law is the same for all covariate laws carried by `𝒳_ac` iff `k_g` is constant on `𝒳_ac`. -/
def groups_const_iff : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κg]
    (X : Set (Fin q → ℝ)) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮),
    MeasurableSet X → Measurable F → Measurable s →
      ((∀ π π' : Measure (Fin q → ℝ), IsProbabilityMeasure π → IsProbabilityMeasure π' →
          π X = 1 → π' X = 1 → signLaw s F π κg = signLaw s F π' κg) ↔
        ∀ c ∈ X, ∀ c' ∈ X, kLaw s F κg c = kLaw s F κg c')

/-- (ii) The sign law is `s#μ_K` for all covariate laws carried by `𝒳_ac` iff `k_g ≡ s#μ_K` on `𝒳_ac`. -/
def groups_ref_iff : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (μ : Measure (Fin K → ℝ))
    (κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κg]
    (X : Set (Fin q → ℝ)) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮),
    MeasurableSet X → Measurable F → Measurable s →
      ((∀ π : Measure (Fin q → ℝ), IsProbabilityMeasure π → π X = 1 → signLaw s F π κg = μ.map s) ↔
        ∀ c ∈ X, kLaw s F κg c = μ.map s)

/-- (ii) `k_g ≡ s#μ_K` on `𝒳_ac` when `P^g_c = P_{K,c}` for every `c ∈ 𝒳_ac`. -/
def groups_fitted : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (μ : Measure (Fin K → ℝ))
    (κ κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) (X : Set (Fin q → ℝ))
    (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮),
    IsRankMap μ κ X F → Measurable s → (∀ c ∈ X, κg c = κ c) → ∀ c ∈ X, kLaw s F κg c = μ.map s

/-- (iii) A sign law different from `s#μ_K` shows `P^g_c ≠ P_{K,c}` on a set of positive `π_g`-measure. -/
def diff_shows : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (μ : Measure (Fin K → ℝ)) [IsProbabilityMeasure μ]
    (κ κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κ] [IsMarkovKernel κg]
    (X : Set (Fin q → ℝ)) (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮)
    (π : Measure (Fin q → ℝ)) [IsProbabilityMeasure π],
    MeasurableSet X → IsRankMap μ κ X F → Measurable s → π X = 1 →
      signLaw s F π κg ≠ μ.map s → ¬ ∀ᵐ c ∂π, κg c = κ c

/-- (iii) Two groups with the same kernel and different covariate laws can have different sign laws
(`K = q = 1`, one witness, monotone rank map, sign map `u ↦ ρ(u)⁻¹u` for every Borel `ρ > 0` off `0`, in
particular the gauge of the witness's own `μ`). -/
def imbalance_example : Prop :=
  ∃ (μ : Measure (Fin 1 → ℝ)) (κ κg : Kernel (Fin 1 → ℝ) (Fin 1 → ℝ)) (X : Set (Fin 1 → ℝ))
    (F : (Fin 1 → ℝ) × (Fin 1 → ℝ) → Fin 1 → ℝ) (πg πh : Measure (Fin 1 → ℝ)),
    IsProbabilityMeasure μ ∧ μ ≪ volume ∧ μ {0} = 0 ∧ IsMarkovKernel κ ∧ IsMarkovKernel κg ∧
    MeasurableSet X ∧ (∀ c ∈ X, κ c ≪ volume) ∧ IsRankMap μ κ X F ∧
    (∀ c ∈ X, Monotone fun z => F (c, z)) ∧
    IsProbabilityMeasure πg ∧ IsProbabilityMeasure πh ∧ πg X = 1 ∧ πh X = 1 ∧
    ∀ ρ : (Fin 1 → ℝ) → ℝ, Measurable ρ → (∀ u, u ≠ 0 → 0 < ρ u) →
      signLaw (fun u => (ρ u)⁻¹ • u) F πg κg ≠ signLaw (fun u => (ρ u)⁻¹ • u) F πh κg

/-- (iv) Equal kernels `π*`-a.e. give equal sign laws under the common covariate law `π*`. -/
def common_law : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (κg κh : Kernel (Fin q → ℝ) (Fin K → ℝ))
    [IsMarkovKernel κg] [IsMarkovKernel κh] (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ)
    (s : (Fin K → ℝ) → 𝒮) (πs : Measure (Fin q → ℝ)) [IsProbabilityMeasure πs],
    Measurable F → Measurable s → (∀ᵐ c ∂πs, κg c = κh c) → signLaw s F πs κg = signLaw s F πs κh

/-- (iv) Reweighting: `E_g[(dπ*/dπ_g)(C) 1{s(F(C,Z)) ∈ E}] = ∫ k_g(c)(E) π*(dc)` when `π* ≪ π_g`. -/
def reweight : Prop :=
  ∀ (q K : ℕ) (𝒮 : Type) [MeasurableSpace 𝒮] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (κg : Kernel (Fin q → ℝ) (Fin K → ℝ)) [IsMarkovKernel κg]
    (F : (Fin q → ℝ) × (Fin K → ℝ) → Fin K → ℝ) (s : (Fin K → ℝ) → 𝒮)
    (πg πs : Measure (Fin q → ℝ)) [IsProbabilityMeasure πg] [IsProbabilityMeasure πs]
    (C : Ω → Fin q → ℝ) (Z : Ω → Fin K → ℝ),
    Measurable F → Measurable s → Measurable C → Measurable Z →
    P.map (fun ω => (C ω, Z ω)) = πg ⊗ₘ κg → πs ≪ πg →
      ∀ E, MeasurableSet E →
        ∫⁻ ω, πs.rnDeriv πg (C ω) * E.indicator 1 (s (F (C ω, Z ω))) ∂P = ∫⁻ c, kLaw s F κg c E ∂πs

/-! ### C `thm:neural-band-consistency` -/

/-- Deterministic core: small risk forces all band edges, uniformly in `t` and `0 < p ≤ 1−δ`, close to the
population (ess-sup) edges, under the support condition `hsupp` of `lem:full-support-region`(i). -/
def neural_band_uniform : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ),
    NeuralSetting μ O Q A δ e E →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N)) →
      ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal η → BandsClose μ T Q A δ mo e ε

/-- Almost-sure mode: `𝓡_n → 0` a.s. gives uniform convergence of the edges a.s. -/
def neural_band_ae : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    NeuralSetting μ O Q A δ e E →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N)) →
    (∀ n ω, MonoOn (T n ω) O) →
    (∀ᵐ ω ∂P, Tendsto (fun n => risk μ O (T n ω) Q) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ᶠ n in atTop, BandsClose μ (T n ω) Q A δ mo e ε

/-- In-probability mode (measurable-event convention on both sides). -/
def neural_band_prob : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    NeuralSetting μ O Q A δ e E →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N)) →
    (∀ n ω, MonoOn (T n ω) O) →
    (∀ η, 0 < η → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | risk μ O (T n ω) Q ≤ ENNReal.ofReal η} ∧ ENNReal.ofReal (1 - δ') ≤ P G) →
      ∀ ε, 0 < ε → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | BandsClose μ (T n ω) Q A δ mo e ε} ∧ ENNReal.ofReal (1 - δ') ≤ P G

/-- `eq:neural-band-rate`: with `Q` `L`-Lipschitz and density `≥ ρ` near `S`, for small risk the edge error is
at most `E_K C_{K,ρ} L^{K/(K+2)} 𝓡^{1/(K+2)}`. -/
def neural_band_rate : Prop :=
  ∀ (K : ℕ) (ρ : ℝ), 0 < K → 0 < ρ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O O' : Set (EuclideanSpace ℝ (Fin K)))
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
      (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E L : ℝ),
      NeuralSetting μ O Q A δ e E →
      (∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N)) →
      IsOpen O' → A (1 - δ) ⊆ O' → O' ⊆ O →
      (∀ B, MeasurableSet B → B ⊆ O' → ENNReal.ofReal ρ * volume B ≤ μ B) →
      0 < L → (∀ x ∈ O', ∀ y ∈ O', ‖Q x - Q y‖ ≤ L * ‖x - y‖) →
        ∃ R₀, 0 < R₀ ∧ ∀ R, 0 < R → R ≤ R₀ →
          ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal R →
              BandsClose μ T Q A δ mo e
                (E * Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)))

end Claims

end StatFormal.OTFD.Wave7a
