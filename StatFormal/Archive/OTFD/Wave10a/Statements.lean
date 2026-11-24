import StatFormal.Archive.OTFD.Ranks.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Wave7a.Statements
import TauCeti.Probability.Quantile
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull

/-!
# FROZEN STATEMENTS — otfd wave 10a: A `prop:rt-df`, A `prop:app-product-conditioning`,
# B `prop:ext-karp-certificate`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`, `otfd-B_bands.md`; current text of
2026-10-14, paths below are under `otfd/papers/`; the extracts index the items at the older lines `main.tex:1412`,
`supplement.tex:3136`, `supplement.tex:5021`):
* A `prop:rt-df` (`A_sieves/main.tex:1416-1453`), with the two-sample setting and pooled ranks (`main.tex:1378-1403`),
  `def:sieve-rank-test` (`main.tex:1405-1414`), the hard assignment of `subsec:hard-ot` (`main.tex:447-474`) and the
  certified `thm:fixedK-df` (`main.tex:496-512`); proof `A_sieves/supplement.tex:4194-4259`.
* A `prop:app-product-conditioning` (`A_sieves/supplement.tex:3141-3181`), with `ass:app-weak-conditioning`
  (`supplement.tex:2484-2498`), `ass:app-conditioning` (`supplement.tex:2967-2989`) and
  `rem:app-conditioning-support` (`supplement.tex:3103-3131`); proof `supplement.tex:3183-3229`.
* B `prop:ext-karp-certificate` (`B_bands/supplement.tex:5023-5059`), with its set-up paragraph (`supplement.tex:
  5003-5021`: `φ`, `β_j`, `s^K_j = a^K_j + ⟨b_j,·⟩`, `B_{M_K}`), `lem:oos-potential`(c) (`B_bands/main.tex:664-690`),
  `prop:band-certificate` (`main.tex:720-753`); proof `supplement.tex:5061-5123`; `rem:ext-karp-necessity`
  (`supplement.tex:5125-5146`).
Reuses the frozen `OTFD/Ranks/Statements.lean` (`IsMin`, `UniqueMin`), `OTFD/Wave1/Statements.lean` (`PellClass`,
`truncK`), `OTFD/Bands/Statements.lean` (`simplex`, `score`, `gap`, `mnormSq`), `OTFD/Bands2/Statements.lean`
(`edgeUp`, `edgeLo`) and `OTFD/Wave7a/Statements.lean` (`laguerre`, `IsProx`, `karpMap`, `oosB`), imported, not
copied; Tau Ceti's `Measure.quantile` (`TauCeti/Probability/Quantile.lean:103`); Mathlib's `cdf`, `gaussianPDFReal`.

Covered:
* `prop:rt-df`: (i) `rt_df_fixed_rank_law` (`𝒫^ℓ`, iid pooled curves, fixed basis, grid and `M_K`: the pooled rank
  vector is uniform over the `N!` arrangements; measurable event), `rt_df_fixed_size` (size `≤ α`); (ii)
  `rt_df_invariant`, `rt_df_invariant_size` (reordering-invariant Borel rule `b` + a.s. uniqueness ⇒ the conclusion
  of (i)); FPCA: `fpca_pooled_invariant` (`X̄`, `Ĉ`, score deviations are symmetric; covers the tied-eigenspace
  alternative "basis chosen by a rule depending on `Ĉ` alone"), `sign_rule_line` (`c(−v) = c(v)`), `fpca_unique`
  ((a)+(b) determine `λ̂_k` and `ê_k` from `Ĉ`), `fpca_invariant` (the FPCA + sign rule + pooled standardisation
  rule is invariant under reordering, scores are permuted); (iii) `rt_perm_pvalue` (super-uniform permutation
  `p`-value for equivariant rank maps, measurable event).
* `prop:app-product-conditioning`: proof facts `product_quantile_inverse` (`Q_j` is a genuine inverse: `Q_j(s) ∈ J_j`,
  `F_j(Q_j(s)) = A_j(s)`); (a) `product_mass` (`c_jℓ_j ≤ 1 ≤ C_jℓ_j`), `product_sandwich` (two-sided Bregman
  sandwich with the displayed `α_K`, `L_K`), `product_kappa` (`0 < α_K ≤ L_K`, `κ_K = L_K/α_K = max_{j,k}
  λ_kC_k/(λ_jc_j)`), `product_kappa_normalized` (`κ_K ≤ b²C^*/c_*` for every `K`); (b) `product_no_upper` (no
  finite `L_K` when some `J_j` is unbounded), `product_lower` (one-sided conditioning with `α_K = min_j
  1/(λ_j‖f_j‖_∞)`), `product_subgrad` (the coordinate quantiles are subgradients: the parenthetical on (ii)),
  `gaussian_alpha` (`‖f_j‖_∞ = (σ_j√(2π))⁻¹`, `α_K = √(2π) min_j σ_j/λ_j`).
* `prop:ext-karp-certificate`: (i) `karp_localize`; (ii) `ballM_support` (`σ_{B_{M_K}} = ‖·‖_{M_K⁻¹}`, attained),
  `karp_program` (`A ⊕ rB_{M_K}` convex compact, convex minimand, minimum attained, `δ_j ≥ 0`), `karp_dual_cert`,
  `karp_outer_index` (`Ĵ ⊇ J_{K,p}`); (iii) `karp_outer_band`, `knapsack01` (the knapsack with caps `1{j∈Ĵ}` has
  value `max_{j∈Ĵ} c_j`, resp. `min`); (iv) `karp_J_mono`, `karp_J_small`; last sentence and
  `rem:ext-karp-necessity`: `karp_necessity` (the remark's example, all of its numbers).

Not covered (declared):
* `prop:rt-df`: "exactly `α` when randomized" (the randomized test is not defined; cf. certified A
  `prop:rt-randomized`, which also covers the `\ext` sentence "randomized tie-breaking needs neither (a), (b) nor
  uniqueness"); "this requires `N ≥ K+1`" and the Okamoto footnote; **Borel measurability of the FPCA rule** (the
  proof's Weyl/power-iteration paragraph): `fpca_invariant` gives the reordering invariance, and feeding the FPCA
  rule into `rt_df_invariant` needs that measurability as an extra input; "Signs as returned by an SVD … do not
  qualify" (a negative remark); (iii) "the null law then depends on `P`" (no example formalised) and the claim that
  the entropic barycentric ranks are permutation-equivariant (equivariance is the hypothesis).
* `prop:app-product-conditioning`: the **Brenier layer**: that `ψ^*` is the Brenier potential `φ_K` of `P_K → μ_K`
  and `φ_K^* = ψ` (Zajíček, biconjugation, `∇ψ^*#P_K = μ_K`). The assumptions are stated for the explicit separable
  potential `ψ(u) = Σ_j ∫_{−λ_j/2}^{u_j} Q_j` with gradient `(Q_j(r_j))_j`; "(hence for every deterministic grid
  `⊆ supp μ_K`)" is immediate (the bounds hold for every `u` in the closed cube); `Q_j#Unif(I_j) = P_j` (used only
  through integrability, which is proved); "`m⁻¹Σ‖s_ℓ‖²` … finite for every grid in the open cube" (real-valued in
  the encoding); the closing "In words" paragraph; that Gaussian coordinates satisfy the (b) hypotheses.
* `prop:ext-karp-certificate`: "for the cubic law, the smaller of the ball and box values" (any upper bound `σA` is
  allowed, which covers it); "each `δ_j` is a convex program" beyond convexity + attainment; whether Karp's own `ε₀`
  can produce the remark's configuration (the remark leaves it open).

Encodings (see card):
* `prop:rt-df`: `H` a real inner-product space with its Borel `σ`-algebra; `H_0` (pooled curves iid from `P = Q`)
  is: `X : Ω → Fin N → H` measurable with `iIndepFun` coordinates of common law `P₀ ∈ 𝒫^ℓ(H)` (frozen
  `PellClass`); `n₁, n₂` and the labels enter only through the statistic `T`, so they are not separate parameters.
  `Π_K` is the frozen `truncK e K` for an orthonormal `e : ℕ → H`; `M_K = L_KᵀL_K` with `L_K : ℝ^K ≃L ℝ^K`, the cost
  is `Σ_i ‖L_K z_i − L_K u_{σ(i)}‖²` (`IsMin` of the whitened data), the grid `u` is injective ("`N` distinct
  points"); `σ̂` is any minimiser selection with measurable fibres (the paper's Borel tie rule). "Uniform over the
  `N!` arrangements" is `P(R ∈ S) = #{π : u∘π ∈ S}/N!` for every `S`, with the event asserted measurable; size:
  any `c` with `#{π : T(u∘π) > c} ≤ αN!`. (ii): `b : (Fin N → X) → B` measurable into any measurable space of
  "basis, centering, scaling", coefficient map `(b, x) ↦ A_b(x)` jointly measurable into the `M_K`-geometry `E` (any
  real inner-product space), invariance `∀τ, b(𝔛∘τ) = b(𝔛)` a.s., exchangeability `law(𝔛∘τ) = law(𝔛)`
  (generalises `H_0`). FPCA: `Ĉh = N⁻¹Σ⟨X_i − X̄,h⟩(X_i − X̄)` (`pooledCov`, a function `H → H`); (a) is `LeadSimple`
  (orthonormal eigenvectors for `λ_1 > ⋯ > λ_K`, and every eigenpair with eigenvalue `≥ λ_K` is `(λ_k, c e_k)`),
  (b) is any predicate `Sg : H → Prop` on the eigenfunction alone that never accepts both `v` and `−v` (the paper:
  "a rule depending on the eigenfunction alone"); its example is `SignRule f` for a system `f : ℕ → H` (finite
  systems and grid evaluations padded with zeros; orthonormality only enters through `⟨v,f_j⟩ → 0`); scores `⟨X_i − X̄, e_k⟩/sd_k` with `sd_k = (N⁻¹Σ⟨X_i − X̄,e_k⟩²)^{1/2}` (`fpcaScores`; `sd_k > 0` under
  (a) when `dim H > K`; equivariance does not depend on it). (iii): any measurable `R` with `R(𝔛∘τ) = R(𝔛)∘τ` a.s.,
  any measurable `T`, `p = #{π : T(R∘π) ≥ T(R)}/N!` (`permPValue`), every real `α`.
* `prop:app-product-conditioning`: `ℝ^K = Fin K → ℝ`, `‖u − r‖² = Σ_j (u_j − r_j)²` (`sqDist`, not the sup norm);
  `μ_K^cub = ⊗_j (λ_j⁻¹ Leb|_{I_j})` (`cubeRef`); `P_j` has density `f_j` (`P_j = Leb.withDensity (ofReal ∘ f_j)`,
  `f_j` measurable, probability); `Q_j = F_j^{-1} ∘ A_j` with `F_j^{-1}` **Tau Ceti's quantile function**
  (canonical, no hypothesis), `A_j(t) = (t + λ_j/2)/λ_j`. (a): `J_j = [a_j, a_j + ℓ_j]`, `ℓ_j > 0`,
  `P_j(J_jᶜ) = 0`, `c_j ≤ f_j ≤ C_j` pointwise on `J_j` (a version of the density), `0 < c_j`. (b): `J_j` an
  `OrdConnected` set with `P_j(J_jᶜ) = 0`, `f_j > 0` a.e. on `J_j`, finite first moment (`𝒫^ℓ` gives it); unbounded
  = `¬BddAbove ∨ ¬BddBelow`; `‖f_j‖_∞` is any `M_j > 0` with `f_j ≤ M_j` a.e. (covers the ess sup; generalisation).
  `α_K, L_K, κ_K` are `⨅`/`⨆` over `Fin K`, stated for `K ≥ 1` (genuine min/max, no `sInf ∅` junk). The
  sandwich/one-sided bounds hold for every `u` in the **closed** cube and every `r` in the **open** cube (a
  `μ_K`-full set; at `r_j = −λ_j/2` the quantile at level `0` is a junk value, so boundary `r` are excluded); the
  impossibility negates the weakest reading (`∀u ∈ cube, ∀ᵐ r`) of the upper half of `ass:app-conditioning`. The
  normalised bound keeps the paper's explicit `0 < c_j ≤ C_j < ∞` of (a) (needed: a negative `C_k` breaks it).
* `prop:ext-karp-certificate`: `ℝ^K = Fin K → ℝ`, `⟨·,·⟩ = dotProduct`, `M_K` positive definite, any `L_K` with
  `L_KᵀL_K = M_K`; `β_j = σL_KZ_j` (`karpBeta`), `a^K_j = −(2/σ)ϑ_j` (`karpA`), `b_j = 2M_KZ_j` (frozen `oosB`);
  `‖β_j‖₂ = √(β_j·β_j)`, `r ≥ ε₀‖β_j‖₂` for every `j`; `Q̂_Karp` is the frozen `karpMap` for any proximal selection
  `P` (unique by frozen `karp_prox_unique`); `A ⊕ rB_{M_K} = {u + rw : u ∈ A, w ᵀM_Kw ≤ 1}` (`enlarge`);
  `δ^K_j(p)` is the frozen `gap` (an `sInf`, nonempty and bounded below by `0`: no junk; `karp_program` shows it is
  attained when `A` is compact); `J_{K,p}`, `J^0_{K,p}` are `karpJ`, `karpJ0`; `A_{K,p}` is any nonempty compact set
  (convex where (ii) needs it). (ii)–(iv) are stated for arbitrary affine scores `a_j + ⟨b_j,·⟩` (generalisation;
  `(karpA, oosB)` is an instance); (iv) needs no compactness. Band edges are the frozen `edgeUp`/`edgeLo` (`EReal`
  suprema over `A`) at `v = e(t)`, `mo = 𝔪(t)`, `c_j(t) = ⟨e(t), Z_j⟩`; `Ĵ` any set with `J_{K,p} ⊆ Ĵ` (max/min over
  `Ĵ` as `EReal` `⨆`/`⨅`). In `karp_necessity` index `0` is the paper's `j = 1`.

Critic notes:
* Routes: all 28 claims are proved in `Wave10a/RouteRtDf.lean` (9), `Wave10a/RouteProduct.lean` (9) and
  `Wave10a/RouteKarp.lean` (10), axioms `propext, Classical.choice, Quot.sound` only.
* `prop:rt-df`(i) is a composition of certified pieces (`lem:app-pullback`, `fixedK_pell_atomless`,
  `fixedK_unique_of_atomless`, `fixedK_rank_law`); the `M_K`-whitening pulls hyperplanes back through `L_K^*`.
  Invariance (`fpca_unique`, `fpca_invariant`) uses only "`Sg` never accepts both `±v`", so it holds for every sign
  rule depending on the eigenfunction alone; for the example rule this is `sign_rule_line` (uses the tie-break).
* **S4 (wording, no effect on invariance or exactness):** the paper's fixed orthonormal system is not assumed
  complete. If a retained eigenfunction `v` is orthogonal to it, `c(v) = 0` and the proof's formula
  `E_kf_{j*}/‖E_kf_{j*}‖` is `0/0`. Example: `H = ℝ²`, system `{(1,0)}`, `Ĉ = diag(0,1)`, `K = 1`: `ê_1 = ±(0,1)` has
  all coefficients `0`. Suggested fix: "orthonormal basis" (for gridded curves the grid values are complete).
* The FPCA chain is not formalised end to end: the Borel measurability of the FPCA rule (Weyl/power iteration) is
  declared, so `fpca_invariant` cannot yet be fed into `rt_df_invariant` without it as an input.
* `prop:app-product-conditioning`: no continuity of `F_j` is needed for the slope bounds (the Galois relations of
  the quantile suffice); the impossibility uses one `u` (the centre) and boxes of positive `μ_K`-mass, so it holds
  under the weakest quantifier order. No paper defect found; the constants are exact.
* `prop:ext-karp-certificate`: the separation step is Mathlib's `geometric_hahn_banach_closed_point`; the remark's
  numbers (`P(0.5) = 0.6`, `Q̂_Karp(0.5) = −0.5`, `J^0 = {1}`, `J(0.2) = {1,2}`) are verified. In (iv) without
  compactness the paper's `min` is an infimum (the frozen `gap`); the two coincide for compact `A` (`karp_program`).
  No defect found.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave10a

open StatFormal.OTFD.Ranks (IsMin UniqueMin)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Bands (simplex score gap mnormSq)
open StatFormal.OTFD.Bands2 (edgeUp edgeLo)
open StatFormal.OTFD.Wave7a (laguerre IsProx karpMap oosB)

/-! ### A `prop:rt-df` -/

section RtDf
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pooled mean `X̄ = N⁻¹ Σ_i X_i`. -/
def pooledMean {N : ℕ} (x : Fin N → H) : H := (N : ℝ)⁻¹ • ∑ i, x i

/-- Pooled empirical covariance operator `Ĉ h = N⁻¹ Σ_i ⟨X_i − X̄, h⟩ (X_i − X̄)`. -/
def pooledCov {N : ℕ} (x : Fin N → H) (h : H) : H :=
  (N : ℝ)⁻¹ • ∑ i, ⟪x i - pooledMean x, h⟫_ℝ • (x i - pooledMean x)

/-- (a): `e_1, …, e_K` are orthonormal eigenvectors of `C` for `λ_1 > ⋯ > λ_K`, and every eigenvalue
`μ ≥ λ_K` of `C` is one of the `λ_k`, with eigenspace the line `ℝ e_k` (the `K` largest eigenvalues are
simple and separated from the rest). -/
def LeadSimple {K : ℕ} (C : H → H) (lam : Fin K → ℝ) (e : Fin K → H) : Prop :=
  Orthonormal ℝ e ∧ StrictAnti lam ∧ (∀ k, C (e k) = lam k • e k) ∧
    ∀ (μ : ℝ) (w : H), w ≠ 0 → C w = μ • w → (∃ k, lam k ≤ μ) →
      ∃ k, μ = lam k ∧ ∃ c : ℝ, w = c • e k

/-- (b), the paper's example sign rule: the largest-magnitude coefficient of `v` on the fixed system
`f = (f_j)_{j∈ℕ}`, ties broken by the smallest index, is positive (a finite system is one padded with zeros). -/
def SignRule (f : ℕ → H) (v : H) : Prop :=
  ∃ j, 0 < ⟪v, f j⟫_ℝ ∧ (∀ i, |⟪v, f i⟫_ℝ| ≤ ⟪v, f j⟫_ℝ) ∧ ∀ i, i < j → |⟪v, f i⟫_ℝ| < ⟪v, f j⟫_ℝ

/-- Pooled standard deviation of the scores on `v`, `(N⁻¹ Σ_i ⟨X_i − X̄, v⟩²)^{1/2}`. -/
def scoreSd {N : ℕ} (x : Fin N → H) (v : H) : ℝ :=
  √((N : ℝ)⁻¹ * ∑ i, ⟪x i - pooledMean x, v⟫_ℝ ^ 2)

/-- FPCA coefficients followed by pooled standardisation: `Z_{ik} = ⟨X_i − X̄, e_k⟩ / sd_k`. -/
def fpcaScores {N K : ℕ} (e : Fin K → H) (x : Fin N → H) : Fin N → EuclideanSpace ℝ (Fin K) :=
  fun i => WithLp.toLp 2 fun k => ⟪x i - pooledMean x, e k⟫_ℝ / scoreSd x (e k)

end RtDf

open scoped Classical in
/-- Permutation `p`-value `#{π : T(y∘π) ≥ T(y)} / N!` of a statistic `T` of the pooled ranks `y`. -/
def permPValue {Y : Type*} {N : ℕ} (T : (Fin N → Y) → ℝ) (y : Fin N → Y) : ℝ :=
  ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => T y ≤ T (y ∘ ⇑π)).card : ℝ) /
    (Nat.factorial N : ℝ)

/-! ### A `prop:app-product-conditioning` -/

section Product
variable {K : ℕ}

/-- `I = [−λ/2, λ/2]`. -/
def cubeI (lam : ℝ) : Set ℝ := Icc (-(lam / 2)) (lam / 2)

/-- The open interval `(−λ/2, λ/2)`. -/
def cubeIo (lam : ℝ) : Set ℝ := Ioo (-(lam / 2)) (lam / 2)

/-- `A(t) = (t + λ/2)/λ`, the increasing affine bijection of `I` onto `[0,1]`. -/
def affA (lam t : ℝ) : ℝ := (t + lam / 2) / lam

/-- The closed cube `Π_j I_j = supp μ_K^cub`. -/
def cube (lam : Fin K → ℝ) : Set (Fin K → ℝ) := Set.pi univ fun j => cubeI (lam j)

/-- The open cube `Π_j (−λ_j/2, λ_j/2)`. -/
def cubeO (lam : Fin K → ℝ) : Set (Fin K → ℝ) := Set.pi univ fun j => cubeIo (lam j)

/-- The cubic reference `μ_K^cub = ⊗_j Unif(I_j)`. -/
def cubeRef (lam : Fin K → ℝ) : Measure (Fin K → ℝ) :=
  Measure.pi fun j => (ENNReal.ofReal (lam j))⁻¹ • volume.restrict (cubeI (lam j))

/-- `Q = F^{-1} ∘ A` on `I`, with `F^{-1}` the (Tau Ceti) quantile function of `P_j`. -/
def quantA (Pj : Measure ℝ) (lam : ℝ) (s : ℝ) : ℝ := Pj.quantile (affA lam s)

/-- The coordinate quantile maps `Q_j = F_j^{-1} ∘ A_j`. -/
def prodQ (lam : Fin K → ℝ) (P : Fin K → Measure ℝ) (j : Fin K) (s : ℝ) : ℝ := quantA (P j) (lam j) s

/-- The separable potential `ψ(u) = Σ_j ∫_{−λ_j/2}^{u_j} Q_j(s) ds`. -/
def sepPot (lam : Fin K → ℝ) (Q : Fin K → ℝ → ℝ) (u : Fin K → ℝ) : ℝ :=
  ∑ j, ∫ s in (-(lam j / 2))..(u j), Q j s

/-- `D(u,r) = ψ(u) − ψ(r) − ⟨(Q_j(r_j))_j, u − r⟩`. -/
def sepBreg (lam : Fin K → ℝ) (Q : Fin K → ℝ → ℝ) (u r : Fin K → ℝ) : ℝ :=
  sepPot lam Q u - sepPot lam Q r - ∑ j, Q j (r j) * (u j - r j)

/-- Squared Euclidean distance `‖u − r‖² = Σ_j (u_j − r_j)²`. -/
def sqDist (u r : Fin K → ℝ) : ℝ := ∑ j, (u j - r j) ^ 2

/-- `α_K = min_j 1/(λ_j C_j)`. -/
def alphaK (lam C : Fin K → ℝ) : ℝ := ⨅ j, 1 / (lam j * C j)

/-- `L_K = max_j 1/(λ_j c_j)`. -/
def LK (lam c : Fin K → ℝ) : ℝ := ⨆ j, 1 / (lam j * c j)

/-- `κ_K = max_{j,k} λ_k C_k/(λ_j c_j)`. -/
def kappaK (lam c C : Fin K → ℝ) : ℝ := ⨆ j, ⨆ k, (lam k * C k) / (lam j * c j)

end Product

/-- `P_j` is a probability law on `ℝ` with Lebesgue density `f_j`. -/
def DensityLaw (Pj : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  IsProbabilityMeasure Pj ∧ Measurable f ∧ Pj = volume.withDensity fun y => ENNReal.ofReal (f y)

/-- (a): density bounded `c ≤ f ≤ C` on the compact interval `J = [a, a + ℓ]` supporting `P_j`. -/
def CompactLaw (Pj : Measure ℝ) (f : ℝ → ℝ) (a ℓ c C : ℝ) : Prop :=
  DensityLaw Pj f ∧ 0 < ℓ ∧ 0 < c ∧ Pj (Icc a (a + ℓ))ᶜ = 0 ∧
    ∀ y ∈ Icc a (a + ℓ), c ≤ f y ∧ f y ≤ C

/-- (b): density positive a.e. on an interval `J` supporting `P_j`, finite first moment. -/
def IntervalLaw (Pj : Measure ℝ) (f : ℝ → ℝ) (J : Set ℝ) : Prop :=
  DensityLaw Pj f ∧ J.OrdConnected ∧ Pj Jᶜ = 0 ∧ (∀ᵐ y ∂volume, y ∈ J → 0 < f y) ∧
    Integrable (fun x => x) Pj

/-! ### B `prop:ext-karp-certificate` -/

section Karp
variable {n K : ℕ}

/-- `β_j = σ L_K Z_j`. -/
def karpBeta (σ : ℝ) (L : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) : Fin n → Fin K → ℝ :=
  fun j => σ • (L *ᵥ Z j)

/-- Intercepts `a^K_j = −(2/σ) ϑ_j` (the slopes are `b_j = 2 M_K Z_j`, `oosB`). -/
def karpA (σ : ℝ) (θ : Fin n → ℝ) : Fin n → ℝ := fun j => -(2 / σ) * θ j

/-- `B_{M_K} = {w : ‖w‖_{M_K} ≤ 1}`. -/
def ballM (M : Matrix (Fin K) (Fin K) ℝ) : Set (Fin K → ℝ) := {w | mnormSq M w ≤ 1}

/-- `A ⊕ r B_{M_K}`. -/
def enlarge (M : Matrix (Fin K) (Fin K) ℝ) (A : Set (Fin K → ℝ)) (r : ℝ) : Set (Fin K → ℝ) :=
  {x | ∃ u ∈ A, ∃ w ∈ ballM M, x = u + r • w}

/-- `J_{K,p}(r) = {j : δ^K_j(p) = 0}`, `δ^K_j` the reachability gap of `s^K` over `A ⊕ rB_{M_K}`. -/
def karpJ (σ : ℝ) (θ : Fin n → ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) (r : ℝ) : Set (Fin n) :=
  {j | gap (karpA σ θ) (oosB M Z) (enlarge M A r) j = 0}

/-- `J^0_{K,p} = {j : min_{u∈A}[max_k s^K_k(u) − s^K_j(u)] = 0}`. -/
def karpJ0 (σ : ℝ) (θ : Fin n → ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) : Set (Fin n) :=
  {j | gap (karpA σ θ) (oosB M Z) A j = 0}

/-- `‖v‖_{M⁻¹} = (vᵀ M⁻¹ v)^{1/2}`. -/
def mInvNorm (M : Matrix (Fin K) (Fin K) ℝ) (v : Fin K → ℝ) : ℝ := √(v ⬝ᵥ (M⁻¹ *ᵥ v))

/-- The dual lower bound `Σ_k w_k a_k − a_j − σ_A(v^w_j) − r‖v^w_j‖_{M⁻¹}`, `v^w_j = b_j − Σ_k w_k b_k`,
with `σA` in the role of `σ_A(v^w_j)` (or any upper bound of it). -/
def dualLB (M : Matrix (Fin K) (Fin K) ℝ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (r : ℝ) (j : Fin n)
    (w : Fin n → ℝ) (σA : ℝ) : ℝ :=
  ∑ k, w k * a k - a j - σA - r * mInvNorm M (b j - ∑ k, w k • b k)

end Karp

/-- The standing setting of `prop:ext-karp-certificate`: `n ≥ 1` fitted points `Z_j`, weights `ϑ`,
`ε₀, σ > 0`, `M_K` positive definite with `L_KᵀL_K = M_K`, a selection `P` of proximal points of the
Laguerre potential `φ(y) = max_j(⟨β_j,y⟩ − ϑ_j)`, and `r ≥ ε₀ max_j ‖β_j‖₂`. -/
def KarpSetting {n K : ℕ} (Z : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (σ ε₀ r : ℝ)
    (M L : Matrix (Fin K) (Fin K) ℝ) (P : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  0 < n ∧ 0 < ε₀ ∧ 0 < σ ∧ M.PosDef ∧ L.transpose * L = M ∧
    (∀ y, IsProx (laguerre (karpBeta σ L Z) θ) ε₀ y (P y)) ∧
    ∀ j, ε₀ * √(karpBeta σ L Z j ⬝ᵥ karpBeta σ L Z j) ≤ r

/-- `rem:ext-karp-necessity`: the fitted points `Z = (−1, 1)` in `K = 1`. -/
def exZ : Fin 2 → Fin 1 → ℝ := ![fun _ => -1, fun _ => 1]

/-- `rem:ext-karp-necessity`: the weights `ϑ = (0, 1.2)`. -/
def exθ : Fin 2 → ℝ := ![0, 1.2]

/-- `rem:ext-karp-necessity`: the region `A_{K,p} = [−0.5, 0.5]`. -/
def exA : Set (Fin 1 → ℝ) := {u | u 0 ∈ Set.Icc (-0.5 : ℝ) 0.5}

namespace Claims

/-! ### A `prop:rt-df` -/

open scoped Classical in
/-- (i) Fixed basis and grid, `H_0` (the pooled curves are iid from `P ∈ 𝒫^ℓ(H)`), any `K`: the pooled rank
vector `R_i = u_{σ̂(i)}` (hard assignment of the projected curves `Π_K X_i` to `N` distinct grid points in the
`M_K`-geometry `‖v‖_{M_K} = ‖L_K v‖`, any Borel tie rule) is uniform over the `N!` arrangements of the grid:
the event is measurable and `P(R ∈ S) = #{π : u∘π ∈ S}/N!` for every `S`. -/
def rt_df_fixed_rank_law : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N K : ℕ)
    (e : ℕ → H) (P₀ : Measure H) (X : Ω → Fin N → H)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K))
    (u : Fin N → EuclideanSpace ℝ (Fin K))
    (sel : (Fin N → EuclideanSpace ℝ (Fin K)) → Equiv.Perm (Fin N)),
    Orthonormal ℝ e → PellClass P₀ → Measurable X → iIndepFun (fun i ω => X ω i) P →
    (∀ i, P.map (fun ω => X ω i) = P₀) → Function.Injective u →
    (∀ z, IsMin (fun j => L (u j)) (fun i => L (z i)) (sel z)) →
    (∀ h, MeasurableSet {z | sel z = h}) →
      ∀ S : Set (Fin N → EuclideanSpace ℝ (Fin K)),
        MeasurableSet {ω | (fun i => u (sel (fun i => truncK e K (X ω i)) i)) ∈ S} ∧
        P {ω | (fun i => u (sel (fun i => truncK e K (X ω i)) i)) ∈ S} =
          ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => u ∘ ⇑π ∈ S).card : ℝ≥0∞) *
            (Nat.factorial N : ℝ≥0∞)⁻¹

open scoped Classical in
/-- (i) Size: in the setting of `rt_df_fixed_rank_law`, for every sieve rank statistic `T` and every
critical value `c` with `#{π : T(u∘π) > c} ≤ α N!` (the defining property of `c_{N,α}`), the rank test
rejecting when `T(R) > c` has size `≤ α` (measurable rejection event). -/
def rt_df_fixed_size : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N K : ℕ)
    (e : ℕ → H) (P₀ : Measure H) (X : Ω → Fin N → H)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K))
    (u : Fin N → EuclideanSpace ℝ (Fin K))
    (sel : (Fin N → EuclideanSpace ℝ (Fin K)) → Equiv.Perm (Fin N))
    (T : (Fin N → EuclideanSpace ℝ (Fin K)) → ℝ) (c α : ℝ),
    Orthonormal ℝ e → PellClass P₀ → Measurable X → iIndepFun (fun i ω => X ω i) P →
    (∀ i, P.map (fun ω => X ω i) = P₀) → Function.Injective u →
    (∀ z, IsMin (fun j => L (u j)) (fun i => L (z i)) (sel z)) →
    (∀ h, MeasurableSet {z | sel z = h}) →
    ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => c < T (u ∘ ⇑π)).card : ℝ) ≤
      α * (Nat.factorial N : ℝ) →
      MeasurableSet {ω | c < T fun i => u (sel (fun i => truncK e K (X ω i)) i)} ∧
      P {ω | c < T fun i => u (sel (fun i => truncK e K (X ω i)) i)} ≤ ENNReal.ofReal α

open scoped Classical in
/-- (ii) Data-driven basis, centering and scaling `b(𝔛)` computed by a Borel rule that is invariant under
reordering (`b(𝔛∘τ) = b(𝔛)` a.s. for every `τ`), coefficients `Z_i = A_{b(𝔛)}(X_i)` (a jointly Borel map
`(b, x) ↦ A_b(x)` into the `M_K`-geometry `E`), exchangeable pooled sample (in particular `H_0`), a.s. unique
assignment: the rank vector is uniform over the arrangements of the grid (measurable event). -/
def rt_df_invariant : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (B : Type) [MeasurableSpace B]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (𝔛 : Ω → Fin N → X) (b : (Fin N → X) → B) (A : B → X → E) (u : Fin N → E)
    (sel : (Fin N → E) → Equiv.Perm (Fin N)),
    Measurable 𝔛 → Measurable b → Measurable (fun p : B × X => A p.1 p.2) →
    (∀ τ : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ ⇑τ) = P.map 𝔛) →
    (∀ τ : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, b (𝔛 ω ∘ ⇑τ) = b (𝔛 ω)) →
    (∀ z, IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
    (∀ᵐ ω ∂P, UniqueMin u fun i => A (b (𝔛 ω)) (𝔛 ω i)) →
      ∀ S : Set (Fin N → E),
        MeasurableSet {ω | (fun i => u (sel (fun i => A (b (𝔛 ω)) (𝔛 ω i)) i)) ∈ S} ∧
        P {ω | (fun i => u (sel (fun i => A (b (𝔛 ω)) (𝔛 ω i)) i)) ∈ S} =
          ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => u ∘ ⇑π ∈ S).card : ℝ≥0∞) *
            (Nat.factorial N : ℝ≥0∞)⁻¹

open scoped Classical in
/-- (ii) Size, as in (i), in the setting of `rt_df_invariant`. -/
def rt_df_invariant_size : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (B : Type) [MeasurableSpace B]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (𝔛 : Ω → Fin N → X) (b : (Fin N → X) → B) (A : B → X → E) (u : Fin N → E)
    (sel : (Fin N → E) → Equiv.Perm (Fin N)) (T : (Fin N → E) → ℝ) (c α : ℝ),
    Measurable 𝔛 → Measurable b → Measurable (fun p : B × X => A p.1 p.2) →
    (∀ τ : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ ⇑τ) = P.map 𝔛) →
    (∀ τ : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, b (𝔛 ω ∘ ⇑τ) = b (𝔛 ω)) →
    (∀ z, IsMin u z (sel z)) → (∀ h, MeasurableSet {z | sel z = h}) →
    (∀ᵐ ω ∂P, UniqueMin u fun i => A (b (𝔛 ω)) (𝔛 ω i)) →
    ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => c < T (u ∘ ⇑π)).card : ℝ) ≤
      α * (Nat.factorial N : ℝ) →
      MeasurableSet {ω | c < T fun i => u (sel (fun i => A (b (𝔛 ω)) (𝔛 ω i)) i)} ∧
      P {ω | c < T fun i => u (sel (fun i => A (b (𝔛 ω)) (𝔛 ω i)) i)} ≤ ENNReal.ofReal α

/-- (ii) FPCA: the pooled mean, the pooled covariance operator and the pooled score deviations are
invariant under reordering (so any basis chosen by a rule depending on `Ĉ` alone is). -/
def fpca_pooled_invariant : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (N : ℕ) (x : Fin N → H)
    (τ : Equiv.Perm (Fin N)),
    pooledMean (x ∘ ⇑τ) = pooledMean x ∧ pooledCov (x ∘ ⇑τ) = pooledCov x ∧
      ∀ v, scoreSd (x ∘ ⇑τ) v = scoreSd x v

/-- (ii)(b) The example sign rule never accepts both `v` and `−v` (so `c(−v) = c(v)`), and it accepts one of
them whenever the coefficients `⟨v, f_j⟩` tend to `0` (e.g. `f` orthonormal, Bessel) and one is nonzero
(the proof's "attained, since `⟨v,f_j⟩ → 0` and `v ≠ 0`"). -/
def sign_rule_line : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : ℕ → H) (v : H),
    ¬ (SignRule f v ∧ SignRule f (-v)) ∧
    (Tendsto (fun j => ⟪v, f j⟫_ℝ) atTop (𝓝 0) → (∃ j, ⟪v, f j⟫_ℝ ≠ 0) →
      SignRule f v ∨ SignRule f (-v))

/-- (ii)(a)+(b) Under (a) the leading eigenvalues and, with any sign rule `Sg` depending on the eigenfunction
alone (it never accepts both `v` and `−v`), the retained eigenvectors are determined by `C` alone. -/
def fpca_unique : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (K : ℕ) (C : H → H)
    (Sg : H → Prop) (lam lam' : Fin K → ℝ) (e e' : Fin K → H),
    (∀ v, ¬ (Sg v ∧ Sg (-v))) →
    LeadSimple C lam e → LeadSimple C lam' e' → (∀ k, Sg (e k)) → (∀ k, Sg (e' k)) →
      lam' = lam ∧ e' = e

/-- (ii) FPCA of the pooled sample with (a) and (b), followed by pooled standardisation, is invariant under
reordering: the retained basis of `𝔛∘τ` is that of `𝔛`, and the standardised scores are permuted. -/
def fpca_invariant : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (N K : ℕ) (x : Fin N → H)
    (τ : Equiv.Perm (Fin N)) (Sg : H → Prop) (lam lam' : Fin K → ℝ) (e e' : Fin K → H),
    (∀ v, ¬ (Sg v ∧ Sg (-v))) →
    LeadSimple (pooledCov x) lam e → LeadSimple (pooledCov (x ∘ ⇑τ)) lam' e' →
    (∀ k, Sg (e k)) → (∀ k, Sg (e' k)) →
      e' = e ∧ fpcaScores e' (x ∘ ⇑τ) = fpcaScores e x ∘ ⇑τ

/-- (iii) For a permutation-equivariant pooled rank map (`R(𝔛∘τ) = R(𝔛)∘τ` a.s.) and an exchangeable pooled
sample, the permutation `p`-value of any Borel statistic of the ranks is super-uniform: `P(p ≤ α) ≤ α`
(measurable event), for every `α`. -/
def rt_perm_pvalue : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (𝔛 : Ω → Fin N → X)
    (R : (Fin N → X) → Fin N → Y) (T : (Fin N → Y) → ℝ) (α : ℝ),
    Measurable 𝔛 → Measurable R → Measurable T →
    (∀ τ : Equiv.Perm (Fin N), P.map (fun ω => 𝔛 ω ∘ ⇑τ) = P.map 𝔛) →
    (∀ τ : Equiv.Perm (Fin N), ∀ᵐ ω ∂P, R (𝔛 ω ∘ ⇑τ) = R (𝔛 ω) ∘ ⇑τ) →
      MeasurableSet {ω | permPValue T (R (𝔛 ω)) ≤ α} ∧
      P {ω | permPValue T (R (𝔛 ω)) ≤ α} ≤ ENNReal.ofReal α

/-! ### A `prop:app-product-conditioning` -/

/-- (a), proof: `Q = F^{-1}∘A` is a genuine inverse on the open interval: `Q(s) ∈ J` and `F(Q(s)) = A(s)`. -/
def product_quantile_inverse : Prop :=
  ∀ (Pj : Measure ℝ) (f : ℝ → ℝ) (a ℓ c C lam : ℝ), 0 < lam → CompactLaw Pj f a ℓ c C →
    ∀ s ∈ cubeIo lam, quantA Pj lam s ∈ Icc a (a + ℓ) ∧ cdf Pj (quantA Pj lam s) = affA lam s

/-- (a) `1 = ∫ f_j` forces `c_j ℓ_j ≤ 1 ≤ C_j ℓ_j`. -/
def product_mass : Prop :=
  ∀ (Pj : Measure ℝ) (f : ℝ → ℝ) (a ℓ c C : ℝ), CompactLaw Pj f a ℓ c C → c * ℓ ≤ 1 ∧ 1 ≤ C * ℓ

/-- (a) The two-sided Bregman sandwich of `ass:app-conditioning` for the separable potential `ψ`, with
`α_K = min_j 1/(λ_jC_j)` and `L_K = max_j 1/(λ_jc_j)`, for every `u` in the closed cube and every `r` in the
open cube (`μ_K`-a.e. `r`). -/
def product_sandwich : Prop :=
  ∀ (K : ℕ) (lam a ℓ c C : Fin K → ℝ) (P : Fin K → Measure ℝ) (f : Fin K → ℝ → ℝ),
    0 < K → (∀ j, 0 < lam j) → (∀ j, CompactLaw (P j) (f j) (a j) (ℓ j) (c j) (C j)) →
      ∀ u ∈ cube lam, ∀ r ∈ cubeO lam,
        alphaK lam C / 2 * sqDist u r ≤ sepBreg lam (prodQ lam P) u r ∧
        sepBreg lam (prodQ lam P) u r ≤ LK lam c / 2 * sqDist u r

/-- (a) `0 < α_K ≤ L_K` and `κ_K = L_K/α_K = max_{j,k} λ_kC_k/(λ_jc_j)`. -/
def product_kappa : Prop :=
  ∀ (K : ℕ) (lam c C : Fin K → ℝ), 0 < K → (∀ j, 0 < lam j ∧ 0 < c j ∧ c j ≤ C j) →
    0 < alphaK lam C ∧ alphaK lam C ≤ LK lam c ∧ kappaK lam c C = LK lam c / alphaK lam C

/-- (a), normalised reading: `c_* ≤ ℓ_jc_j`, `ℓ_jC_j ≤ C^*`, `b⁻¹ ≤ λ_j/ℓ_j ≤ b` give `κ_K ≤ b²C^*/c_*`, for
every `K` (so `sup_K κ_K ≤ b²C^*/c_*`). -/
def product_kappa_normalized : Prop :=
  ∀ (K : ℕ) (lam ℓ c C : Fin K → ℝ) (b cs Cs : ℝ), 0 < K →
    (∀ j, 0 < lam j ∧ 0 < ℓ j ∧ 0 < c j ∧ c j ≤ C j) → 0 < cs → (∀ j, cs ≤ ℓ j * c j) →
    (∀ j, ℓ j * C j ≤ Cs) →
    (∀ j, b⁻¹ ≤ lam j / ℓ j ∧ lam j / ℓ j ≤ b) →
      kappaK lam c C ≤ b ^ 2 * Cs / cs

/-- (b) If some `J_j` is unbounded, no finite `L_K` exists: there is no `L` with
`D(u,r) ≤ (L/2)‖u − r‖²` for every `u` in the closed cube (`⊆` every admissible `Ω_K`) and `μ_K`-a.e. `r`. -/
def product_no_upper : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ) (P : Fin K → Measure ℝ) (f : Fin K → ℝ → ℝ) (J : Fin K → Set ℝ)
    (j₀ : Fin K), (∀ j, 0 < lam j) → (∀ j, IntervalLaw (P j) (f j) (J j)) →
    (¬ BddAbove (J j₀) ∨ ¬ BddBelow (J j₀)) →
      ¬ ∃ Lc : ℝ, ∀ u ∈ cube lam, ∀ᵐ r ∂(cubeRef lam),
        sepBreg lam (prodQ lam P) u r ≤ Lc / 2 * sqDist u r

/-- (b) With `f_j ≤ M_j` a.e. (e.g. `M_j = ‖f_j‖_∞`), `ass:app-weak-conditioning`(i) holds with
`α_K = min_j 1/(λ_jM_j)` for every `u` in the closed cube and every `r` in the open cube. -/
def product_lower : Prop :=
  ∀ (K : ℕ) (lam M : Fin K → ℝ) (P : Fin K → Measure ℝ) (f : Fin K → ℝ → ℝ) (J : Fin K → Set ℝ),
    0 < K → (∀ j, 0 < lam j) → (∀ j, IntervalLaw (P j) (f j) (J j)) →
    (∀ j, 0 < M j ∧ ∀ᵐ y ∂volume, f j y ≤ M j) →
      ∀ u ∈ cube lam, ∀ r ∈ cubeO lam, alphaK lam M / 2 * sqDist u r ≤ sepBreg lam (prodQ lam P) u r

/-- (b), last sentence: the vector of coordinate quantiles `(Q_j(r_j))_j` at a point `r` of the open cube is a
subgradient of `ψ` there, relative to the closed cube (`D(u,r) ≥ 0`). -/
def product_subgrad : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ) (P : Fin K → Measure ℝ) (f : Fin K → ℝ → ℝ) (J : Fin K → Set ℝ),
    (∀ j, 0 < lam j) → (∀ j, IntervalLaw (P j) (f j) (J j)) →
      ∀ u ∈ cube lam, ∀ r ∈ cubeO lam, 0 ≤ sepBreg lam (prodQ lam P) u r

/-- (b), Gaussian example: `‖f_j‖_∞ = (σ_j√(2π))⁻¹` (attained at the mean), so
`α_K = min_j 1/(λ_j‖f_j‖_∞) = √(2π) min_j σ_j/λ_j`. -/
def gaussian_alpha : Prop :=
  ∀ (K : ℕ) (lam σ m : Fin K → ℝ), 0 < K → (∀ j, 0 < lam j ∧ 0 < σ j) →
    (∀ j x, gaussianPDFReal (m j) (σ j ^ 2).toNNReal x ≤ (σ j * √(2 * Real.pi))⁻¹) ∧
    (∀ j, gaussianPDFReal (m j) (σ j ^ 2).toNNReal (m j) = (σ j * √(2 * Real.pi))⁻¹) ∧
    alphaK lam (fun j => (σ j * √(2 * Real.pi))⁻¹) = √(2 * Real.pi) * ⨅ j, σ j / lam j

/-! ### B `prop:ext-karp-certificate` -/

/-- (i) Localisation: for every `u ∈ A_{K,p}`, `Q̂_Karp(u) ∈ conv{Z_j : j ∈ J_{K,p}}`. -/
def karp_localize : Prop :=
  ∀ (n K : ℕ) (Z : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (σ ε₀ r : ℝ) (M L : Matrix (Fin K) (Fin K) ℝ)
    (P : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)),
    KarpSetting Z θ σ ε₀ r M L P → IsCompact A → A.Nonempty →
      ∀ u ∈ A, karpMap σ ε₀ L P u ∈ convexHull ℝ (Z '' karpJ σ θ M Z A r)

/-- (ii) `σ_{B_{M_K}}(v) = ‖v‖_{M_K⁻¹}`: the support function of the `M_K`-unit ball is attained. -/
def ballM_support : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (v : Fin K → ℝ), M.PosDef →
    IsGreatest ((fun w => v ⬝ᵥ w) '' ballM M) (mInvNorm M v)

/-- (ii) `A ⊕ rB_{M_K}` is convex and compact, the minimand of `δ_j` is convex on it, its minimum is attained
and `δ_j ≥ 0` (any affine scores `a_j + ⟨b_j,·⟩`). -/
def karp_program : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (A : Set (Fin K → ℝ)) (r : ℝ) (j : Fin n),
    M.PosDef → Convex ℝ A → IsCompact A → A.Nonempty → 0 ≤ r →
      Convex ℝ (enlarge M A r) ∧ IsCompact (enlarge M A r) ∧
      ConvexOn ℝ (enlarge M A r) (fun u => (⨆ k, score a b k u) - score a b j u) ∧
      (∃ u ∈ enlarge M A r, gap a b (enlarge M A r) j = (⨆ k, score a b k u) - score a b j u) ∧
      0 ≤ gap a b (enlarge M A r) j

/-- (ii) Dual certificate: for every `w ∈ Δ_n` and every `σA ≥ sup_{u∈A}⟨v^w_j,u⟩`,
`δ_j(A ⊕ rB_{M_K}) ≥ Σ_k w_k a_k − a_j − σA − r‖v^w_j‖_{M⁻¹}`. -/
def karp_dual_cert : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (A : Set (Fin K → ℝ)) (r : ℝ) (j : Fin n) (w : Fin n → ℝ) (σA : ℝ),
    M.PosDef → A.Nonempty → 0 ≤ r → w ∈ simplex n →
    (∀ u ∈ A, (b j - ∑ k, w k • b k) ⬝ᵥ u ≤ σA) →
      dualLB M a b r j w σA ≤ gap a b (enlarge M A r) j

/-- (ii) Every `Ĵ` containing the indices with no positive computed lower bound contains `J_{K,p}`. -/
def karp_outer_index : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (A : Set (Fin K → ℝ)) (r : ℝ) (Ĵ : Set (Fin n)),
    M.PosDef → A.Nonempty → 0 ≤ r →
    (∀ j ∉ Ĵ, ∃ w ∈ simplex n, ∃ σA : ℝ, (∀ u ∈ A, (b j - ∑ k, w k • b k) ⬝ᵥ u ≤ σA) ∧
      0 < dualLB M a b r j w σA) →
      {j | gap a b (enlarge M A r) j = 0} ⊆ Ĵ

/-- (iii) Certified outer band: for every `Ĵ ⊇ J_{K,p}` and every `t` (through `v = e(t)`, `mo = 𝔪(t)`),
`𝔪 + max_{j∈Ĵ} c_j ≥ x̂↑` and `𝔪 + min_{j∈Ĵ} c_j ≤ x̂↓` for the Karp map, `c_j = ⟨e(t), Z_j⟩`. -/
def karp_outer_band : Prop :=
  ∀ (n K : ℕ) (Z : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (σ ε₀ r : ℝ) (M L : Matrix (Fin K) (Fin K) ℝ)
    (P : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (Ĵ : Set (Fin n)),
    KarpSetting Z θ σ ε₀ r M L P → IsCompact A → A.Nonempty → karpJ σ θ M Z A r ⊆ Ĵ →
      ∀ (mo : ℝ) (v : Fin K → ℝ),
        edgeUp (karpMap σ ε₀ L P) A mo v ≤ (mo : EReal) + ⨆ j ∈ Ĵ, ((v ⬝ᵥ Z j : ℝ) : EReal) ∧
        (mo : EReal) + ⨅ j ∈ Ĵ, ((v ⬝ᵥ Z j : ℝ) : EReal) ≤ edgeLo (karpMap σ ε₀ L P) A mo v

/-- (iii) The fractional knapsack of `prop:band-certificate`(iv) with 0/1 caps `κ_j = 1{j ∈ Ĵ}` has value
`max_{j∈Ĵ} c_j` (and its minimising version `min_{j∈Ĵ} c_j`). -/
def knapsack01 : Prop :=
  ∀ (n : ℕ) (Ĵ : Finset (Fin n)) (hĴ : Ĵ.Nonempty) (c : Fin n → ℝ),
    IsGreatest {x | ∃ q ∈ simplex n, (∀ j, q j ≤ if j ∈ Ĵ then 1 else 0) ∧ x = ∑ j, q j * c j}
      (Ĵ.sup' hĴ c) ∧
    IsLeast {x | ∃ q ∈ simplex n, (∀ j, q j ≤ if j ∈ Ĵ then 1 else 0) ∧ x = ∑ j, q j * c j}
      (Ĵ.inf' hĴ c)

/-- (iv) `J(r)` is nondecreasing in `r ≥ 0` and contains `J^0` (any affine scores). -/
def karp_J_mono : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (A : Set (Fin K → ℝ)) (r r' : ℝ),
    M.PosDef → A.Nonempty → 0 ≤ r' → r' ≤ r →
      {j | gap a b (enlarge M A r') j = 0} ⊆ {j | gap a b (enlarge M A r) j = 0} ∧
      {j | gap a b A j = 0} ⊆ {j | gap a b (enlarge M A r) j = 0}

/-- (iv) There is `r₀ > 0` with `J(r) = J^0` for all `r ∈ (0, r₀]` (any affine scores). -/
def karp_J_small : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (A : Set (Fin K → ℝ)),
    M.PosDef → A.Nonempty →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r, 0 < r → r ≤ r₀ →
        {j | gap a b (enlarge M A r) j = 0} = {j | gap a b A j = 0}

/-- `rem:ext-karp-necessity`: `K = 1`, `M_K = L_K = 1`, `Z = (−1, 1)`, `σ = 1`, `ϑ = (0, 1.2)`,
`A = [−0.5, 0.5]`, `ε₀ = 0.2`. For every proximal selection, `Q̂_Karp(0.5) = −0.5`, `J^0 = {1}` (index `0`
here), so `Q̂_Karp(0.5) ∉ conv{Z_j : j ∈ J^0}` and the `J^0`-band misses it (`x̂↑ > 𝔪 + max_{J^0} c_j` at
`v = 1`, `𝔪 = 0`), while with `r = 0.2` the enlarged index set is everything. -/
def karp_necessity : Prop :=
  ∀ P : (Fin 1 → ℝ) → Fin 1 → ℝ,
    (∀ y, IsProx (laguerre (karpBeta 1 1 exZ) exθ) 0.2 y (P y)) →
      karpMap 1 0.2 1 P (fun _ => 0.5) = (fun _ => -0.5) ∧
      karpJ0 1 exθ 1 exZ exA = {0} ∧
      karpMap 1 0.2 1 P (fun _ => 0.5) ∉ convexHull ℝ (exZ '' karpJ0 1 exθ 1 exZ exA) ∧
      ((0 : ℝ) : EReal) + ⨆ j ∈ karpJ0 1 exθ 1 exZ exA, ((((fun _ => 1) : Fin 1 → ℝ) ⬝ᵥ exZ j : ℝ) : EReal) <
        edgeUp (karpMap 1 0.2 1 P) exA 0 (fun _ => 1) ∧
      karpJ 1 exθ 1 exZ exA 0.2 = Set.univ

end Claims

end StatFormal.OTFD.Wave10a
