import StatFormal.Archive.Wave30v.Statements
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# FROZEN STATEMENTS (DRAFT) — wave 30z: trimmed-mmd `thm:boundary` ("Theorem A", the UNCONDITIONAL limit law of
# `D̂_α` at fixed feature dimension, at every trimming level) and `cor:boundary-linear`

Source (read 2026-10-20, working tree): `trimmed-mmd/supplement.tex`, section `supp:boundary` (`:2745-`), setting
`supp:boundarystate` (`:2766-2822`: `φ : 𝒳 → ℝ^r`, `κ = sup‖φ‖`, `β = 1/(1−α)`, `A, B, D, D̂`, `N = n ∧ m`,
`c_P = 1 ∧ ρ^{-1/2}`, `c_Q = 1 ∧ ρ^{1/2}`, `ℓ_{f,t}`, `F_P`, `q_P`, `𝔾_P`, `H_P` (`eq:Hdef`), `T_S(z)`, `K°`),
`thm:boundary` (`:2824-2848`), `cor:boundary-linear` (`:2856-2900`), proof `supp:boundaryproof` (`:2911-`,
Steps 1–5, `lem:supdir`, `lem:Hprops`); definitions `paper.tex` `eq:region` (`:531`), `prop:georep` (`:547`),
`lem:cvar` (`:593`), `lem:separation` (`:983`).
Imports the frozen wave-30v statements (`supFun`, `supportFn`, `Ball`, `ballNeg`, `polarSet`, `coneHull`,
`tanCone`) and through them the frozen `TrimmedMMD/Unconditional` (`setDist`, `Dpop`, `Demp`) and
`TrimmedMMD/Concentration` (`region`, `empirical`) statements; not copied.

Covered (targets; label map):
* `thm:boundary`, proof Step 1 — `boundary_dual`: `D = max_Θ Γ_{P,Q}`, `D̂ = max_Θ Γ_{P_n,Q_m}`, `Θ = 𝔹_r × [−κ,κ]²`.
* `thm:boundary`, proof Step 2 — `boundary_donsker`: the two-sample functional CLT in `C(𝔹_r × [−κ,κ])²` (as
  `C(Idx2)`): existence of the limit Gaussian process with continuous paths, uniqueness of its law, convergence.
* `thm:boundary`, setting — `boundary_quantile`: `q_P(f)` is a nonempty compact interval, `= ` the `α`-quantile set
  for `α > 0`.
* `thm:boundary`, setting — `boundary_rates`: the printed `N = n ∧ m`, `n/m → ρ` gives the scaling hypothesis.
* `thm:boundary` (i) — `boundary_every`: `√N(D̂ − D) ⇒ sup_{g ∈ G*} {−c_P H_P(−g) − c_Q H_Q(g)}` at every `α`;
  `G* ≠ ∅`; `G* = {(a* − b*)/‖a* − b*‖}` when `D > 0`.
* `thm:boundary` (ii) — `boundary_contact`: if `A ∩ B ≠ ∅`: `K = cl(T_Q(z) − T_P(z))` at every contact point,
  `G* = K° ∩ 𝔹_r`, `√N D̂ ⇒ sup_{K° ∩ 𝔹_r} {−c_P H_P(−g) − c_Q H_Q(g)}`.
* `cor:boundary-linear` (main) — `boundary_linear`: linear `H` on the polar directions ⇒
  `√N D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`, and `‖Π_{K°} x‖ = dist(x, K)`.
* `cor:boundary-linear` (a) — `boundary_ray`: `K° = ℝ₊ν` ⇒ limit `(−c_P H_P(−ν) − c_Q H_Q(ν))_+`; unique quantiles ⇒
  `Z_+`, `Z ∼ N(0, σ²)`, atom `1/2` at `0` when `σ > 0`.
* `cor:boundary-linear` (b) — `boundary_vertex`: discrete vertex contact ⇒ the corollary's hypothesis holds, with the
  stated Gaussian law of `G_P, G_Q` on the relevant directions, and the projected-norm limit.

Not covered (declared): attainment of
the `max` in (i)/(ii) (stated as a genuine `sSup` of a bounded nonempty set: `G*` nonempty, `|H| ≤ β‖𝔾‖_∞`) and the
compactness of `G*`; existence of a nearest pair (the `D > 0` description of `G*` is stated for every nearest pair);
the specialisation "in particular at `α = α*_r`" of (ii) (that the regions meet at `α*_r`, Step 5) — (ii) assumes
`A ∩ B ≠ ∅` directly; the sentences after the theorem (the limit in (ii) is `≥ 0`, degenerate when `K° = {0}`);
`lem:supdir` and `lem:Hprops` are used in the routes (Wave 30v `boundary_sup_hadamard`; `Hfun_smul`, `linCons_zero_*`)
but are not stated as claims; `rem:boundary-reading` (`H_P` as the limit of the support-function process); in (a), the
existence of the vectors `G_P, G_Q` (the corollary's hypothesis) is not stated — the limit is stated directly in the
printed explicit form; in (b), that `G_P` is a function of `𝔾_P` (only its law on the relevant directions, jointly
with `G_Q`, is stated; the independence of `G_P` and `G_Q` there follows from the additive variance); the
chi-bar-square description of the squared limit in (a) and the half-normal shape on `(0, ∞)` (only the atom `1/2` is
formalised); the full vector identity `G_P = β 𝔾_P ψ_P` in (b) (the limit process is indexed by the hinge class only,
so `G_P` is pinned on the directions `−K°` that enter the limit — the orthogonal part is irrelevant to the limit);
`α*_r ≤ TV`, the examples and the bootstrap remarks.

Encodings (to be checked by the critic):
* `ℝ^r`: any finite-dimensional real inner product space `E`; `φ` strongly measurable with `‖φ‖ ≤ κ` (the frozen
  setting of `lem:cvar`); `𝒳` any measurable space.
* `Θ = Ball E × [−κ,κ] × [−κ,κ]` (`Theta`); the one-sample index `𝔹_r × [−κ,κ]` (`Idx1`); the JOINT index
  `Idx1 ⊕ Idx1` (`Idx2`; left copy = `P`, right copy = `Q`), so `C(Idx2, ℝ) ≅ C(Idx1, ℝ) × C(Idx1, ℝ)` carries the
  pair `(𝔾_P ℓ, 𝔾_Q ℓ)`. `C(·, ℝ)` with Mathlib's Borel σ-algebra (`ContinuousMap.measurableSpace`, which equals the
  product σ-algebra of the evaluations).
* Sampling (van der Vaart–Wellner, one probability space; `SampleModel`): `ξ, η : ℕ → Ω → 𝒳`, each i.i.d.
  (`iIndepFun`, measurable, `μ.map (ξ i) = P`, `μ.map (η j) = Q`), the two sequences independent; `P_n` is the
  frozen `empirical` of the first `n ≥ 1` points. Scaling (`Scaling`, a GENERALISATION of the printed one): sizes
  `n_k, m_k ≥ 1`, `→ ∞`, a rate `r_k > 0`, `r_k → ∞`, with `r_k/√n_k → c_P`, `r_k/√m_k → c_Q`; the printed
  `r = √(n ∧ m)`, `n/m → ρ ∈ (0,∞)`, `c_P = 1 ∧ ρ^{-1/2}`, `c_Q = 1 ∧ ρ^{1/2}` is an instance (`boundary_rates`).
* The limit (`IsLimitGP φ P Q c_P c_Q κ μ' 𝕍`): `𝕍 : Ω' → C(Idx2, ℝ)` a.e.-measurable, every finite linear
  combination `Σ u_i 𝕍(z_i)` is `N(0, c_P² Var_P[Σ u_i ℓ^P_{z_i}] + c_Q² Var_Q[Σ u_i ℓ^Q_{z_i}])` (`gpVar`; `ℓ^P` =
  `ℓ` on the left copy and `0` on the right, `ℓ^Q` symmetrically) — the Cramér–Wold form of "the centred Gaussian
  process with covariance `c_P² Cov_P` on the left, `c_Q² Cov_Q` on the right, independent copies". The paper's
  pair of independent Brownian bridges `(𝔾_P ℓ, 𝔾_Q ℓ)` (continuous versions) is `IsLimitGP … 1 1`; it EXISTS and
  its law is UNIQUE (`boundary_donsker`, existence stated under a sampling model with a scaling; both always exist —
  `μ = (⊗_ℕ P) ⊗ (⊗_ℕ Q)` on `(ℕ → 𝒳) × (ℕ → 𝒳)` with the coordinate maps, `n_k = m_k = k + 1`, `r_k = √(k+1)`,
  `c_P = c_Q = 1` — checked in Lean by the critic), so hypotheses `IsLimitGP … 𝔾` are never vacuous and pin the law
  of `𝔾` on the Borel σ-algebra of `C(Idx2, ℝ)`.
* Convergence in distribution is Mathlib's `TendstoInDistribution`, a structure that INCLUDES a.e.-measurability of
  every `ω ↦ r_k(D̂ − D)` and of the limit (proved, via `D̂ = sup_Θ Γ_{P_n,Q_m}` and the measurability of the
  empirical process in `C(Idx2, ℝ)`), so no outer-probability convention is involved; the samples live on one
  probability space `(Ω, μ)`, the limit on any `(Ω', μ')`.
* `H_P(f) = β min_{t ∈ q_P(f)} 𝔾_P ℓ_{f,t}` is `Hfun … Sum.inl 𝔾 f` (`β · sInf` over the argmin set
  `q_P(f) = argminSet` of `t ↦ t + β P ℓ_{f,t}` on `[−κ,κ]`, nonempty compact: genuine); `G*` is `Gstar` (maximisers
  over the unit ball of `g ↦ −h_A(−g) − h_B(g)`, an `IsMaxOn`-style set); the limit functional is `boundaryLim`.
* Variances: Mathlib `variance` of bounded measurable functions (genuine); in (b) the covariance of `ψ_P` is written
  through the atoms (`discVar`, `vertexVec`; `P = Σ_j p_j δ_{x_j}`), so no measurability of `ψ_P` is needed.
* `Π_{K°}`: `metricProj C x` = a nearest point of `C` to `x` when one exists (closed convex nonempty `C` in
  finite dimension: always; it is then unique), `x` otherwise (never used).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30z

open StatFormal.TrimmedMMD.Concentration (region empirical)
open StatFormal.TrimmedMMD.Unconditional (setDist Dpop Demp)
open StatFormal.Wave30v (supFun supportFn Ball ballNeg polarSet coneHull tanCone)

section Defs
variable {𝒳 E : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hinge `ℓ_{f,t}(x) = (⟨f, φ(x)⟩ − t)_+`. -/
def hinge (φ : 𝒳 → E) (f : E) (t : ℝ) (x : 𝒳) : ℝ := max (⟪f, φ x⟫ - t) 0

/-- The index set `Θ = B₁ × [−κ, κ] × [−κ, κ]` of the dual representation (points `(g, t, s)`). -/
abbrev Theta (E : Type*) [NormedAddCommGroup E] (κ : ℝ) := Ball E × Icc (-κ) κ × Icc (-κ) κ

/-- The one-sample index set `B₁ × [−κ, κ]` (points `(f, t)`, the function `ℓ_{f,t}`). -/
abbrev Idx1 (E : Type*) [NormedAddCommGroup E] (κ : ℝ) := Ball E × Icc (-κ) κ

/-- The joint index set `Idx1 ⊕ Idx1` (left copy: the `P`-process; right copy: the `Q`-process). -/
abbrev Idx2 (E : Type*) [NormedAddCommGroup E] (κ : ℝ) := Idx1 E κ ⊕ Idx1 E κ

/-- The dual objective `Γ_{μ,ν}(g, t, s) = −t − β μ ℓ_{−g,t} − s − β ν ℓ_{g,s}`, `β = 1/(1−α)`. -/
def dualTrim (φ : 𝒳 → E) (α : ℝ) (μ ν : Measure 𝒳) {κ : ℝ} (θ : Theta E κ) : ℝ :=
  -(θ.2.1 : ℝ) - 1 / (1 - α) * ∫ x, hinge φ (-(θ.1 : E)) θ.2.1 x ∂μ
    - (θ.2.2 : ℝ) - 1 / (1 - α) * ∫ x, hinge φ (θ.1 : E) θ.2.2 x ∂ν

/-- The `P`-side functions on the joint index: `ℓ_{f,t}` on the left copy, `0` on the right copy. -/
def hingeP (φ : 𝒳 → E) {κ : ℝ} : Idx2 E κ → 𝒳 → ℝ :=
  Sum.elim (fun z x => hinge φ (z.1 : E) z.2 x) (fun _ _ => 0)

/-- The `Q`-side functions on the joint index: `0` on the left copy, `ℓ_{f,s}` on the right copy. -/
def hingeQ (φ : 𝒳 → E) {κ : ℝ} : Idx2 E κ → 𝒳 → ℝ :=
  Sum.elim (fun _ _ => 0) (fun z x => hinge φ (z.1 : E) z.2 x)

/-- The two-sample empirical process on the joint index: `r ((P_n − P) ℓ_{f,t})` on the left copy and
`r ((Q_m − Q) ℓ_{f,s})` on the right copy, `P_n = n⁻¹ Σ_{i<n} δ_{x_i}`, `Q_m = m⁻¹ Σ_{j<m} δ_{y_j}`. -/
def empProc (φ : 𝒳 → E) (P Q : Measure 𝒳) (n m : ℕ) (r : ℝ) (x y : ℕ → 𝒳) {κ : ℝ} (z : Idx2 E κ) : ℝ :=
  r * ((∑ i ∈ Finset.range n, hingeP φ z (x i)) / n - ∫ w, hingeP φ z w ∂P)
    + r * ((∑ j ∈ Finset.range m, hingeQ φ z (y j)) / m - ∫ w, hingeQ φ z w ∂Q)

/-- The variance of `Σ_i u_i 𝕍(z_i)` for the limit process: `c_P² Var_P[Σ u_i ℓ^P_{z_i}] + c_Q² Var_Q[Σ u_i ℓ^Q_{z_i}]`. -/
def gpVar (φ : 𝒳 → E) (P Q : Measure 𝒳) (cP cQ : ℝ) {κ : ℝ} {p : ℕ} (z : Fin p → Idx2 E κ) (u : Fin p → ℝ) : ℝ :=
  cP ^ 2 * Var[fun w => ∑ i, u i * hingeP φ (z i) w; P] + cQ ^ 2 * Var[fun w => ∑ i, u i * hingeQ φ (z i) w; Q]

/-- `𝕍` is the limit Gaussian process `(c_P 𝔾_P ℓ, c_Q 𝔾_Q ℓ)` (with continuous paths, on the joint index): it is
a.e.-measurable and every finite linear combination of its evaluations is centred Gaussian with variance `gpVar`. -/
def IsLimitGP (φ : 𝒳 → E) (P Q : Measure 𝒳) (cP cQ κ : ℝ) {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    (𝕍 : Ω' → C(Idx2 E κ, ℝ)) : Prop :=
  AEMeasurable 𝕍 μ' ∧ ∀ (p : ℕ) (z : Fin p → Idx2 E κ) (u : Fin p → ℝ),
    μ'.map (fun ω => ∑ i, u i * 𝕍 ω (z i)) = gaussianReal 0 (gpVar φ P Q cP cQ z u).toNNReal

/-- The set of minimisers of `t ↦ t + β μ ℓ_{f,t}` over `[−κ, κ]` (the CVaR minimisers: the `α`-quantile set of
`⟨f, φ⟩` intersected with `[−κ, κ]`). -/
def argminSet (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (f : E) : Set (Icc (-κ) κ) :=
  {t | ∀ t' : Icc (-κ) κ, (t : ℝ) + 1 / (1 - α) * ∫ x, hinge φ f t x ∂μ ≤ (t' : ℝ) + 1 / (1 - α) * ∫ x, hinge φ f t' x ∂μ}

/-- `H(f) = β min_{t ∈ q(f)} 𝔾(f, t)` on one copy of the joint index (`side = Sum.inl`: `H_P`, from `𝔾_P`;
`side = Sum.inr`: `H_Q`, from `𝔾_Q`), `eq:Hdef`. -/
def Hfun (φ : 𝒳 → E) (α : ℝ) (μ : Measure 𝒳) (κ : ℝ) (side : Idx1 E κ → Idx2 E κ) (v : C(Idx2 E κ, ℝ))
    (f : Ball E) : ℝ :=
  1 / (1 - α) * sInf ((fun t => v (side (f, t))) '' argminSet φ α μ κ (f : E))

/-- `G* ⊆ 𝔹_r`: the maximisers over the unit ball of `g ↦ −h_A(−g) − h_B(g)`, `A = 𝒞_α(P)`, `B = 𝒞_α(Q)`. -/
def Gstar (φ : 𝒳 → E) (α : ℝ) (P Q : Measure 𝒳) : Set (Ball E) :=
  {g | ∀ g' : Ball E, -supportFn (region φ α P) (-(g' : E)) - supportFn (region φ α Q) (g' : E) ≤
    -supportFn (region φ α P) (-(g : E)) - supportFn (region φ α Q) (g : E)}

/-- The limit functional of `thm:boundary`: `g ↦ −c_P H_P(−g) − c_Q H_Q(g)`. -/
def boundaryLim (φ : 𝒳 → E) (α : ℝ) (P Q : Measure 𝒳) (κ cP cQ : ℝ) (v : C(Idx2 E κ, ℝ)) (g : Ball E) : ℝ :=
  -cP * Hfun φ α P κ Sum.inl v (ballNeg g) - cQ * Hfun φ α Q κ Sum.inr v g

/-- The sampling model: `ξ` i.i.d. `P`, `η` i.i.d. `Q`, measurable, the two sequences independent. -/
def SampleModel {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure 𝒳) (μ : Measure Ω) (ξ η : ℕ → Ω → 𝒳) : Prop :=
  (∀ i, Measurable (ξ i)) ∧ (∀ j, Measurable (η j)) ∧ iIndepFun ξ μ ∧ iIndepFun η μ ∧
    (∀ i, μ.map (ξ i) = P) ∧ (∀ j, μ.map (η j) = Q) ∧ IndepFun (fun ω i => ξ i ω) (fun ω j => η j ω) μ

end Defs

/-- The variance of the discrete law `Σ_j p_j δ_{a_j}` (`Σ_j p_j = 1`): `Σ_j p_j a_j² − (Σ_j p_j a_j)²`. -/
def discVar {J : ℕ} (ps : Fin J → ℝ) (a : Fin J → ℝ) : ℝ := ∑ j, ps j * a j ^ 2 - (∑ j, ps j * a j) ^ 2

/-- The scaling: sizes `n_k, m_k ≥ 1` tending to infinity, a rate `r_k > 0`, `r_k → ∞`, with `r_k/√n_k → c_P`,
`r_k/√m_k → c_Q` (the printed `r = √(n ∧ m)`, `n/m → ρ` is `boundary_rates`). -/
def Scaling (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ) : Prop :=
  (∀ k, 1 ≤ n k) ∧ (∀ k, 1 ≤ m k) ∧ Tendsto n atTop atTop ∧ Tendsto m atTop atTop ∧ (∀ k, 0 < r k) ∧
    Tendsto r atTop atTop ∧ Tendsto (fun k => r k / √(n k : ℝ)) atTop (𝓝 cP) ∧
    Tendsto (fun k => r k / √(m k : ℝ)) atTop (𝓝 cQ)

section Defs2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vertex feature of `cor:boundary-linear` (b) at the atoms: `ψ(x_j) = (φ(x_j) − φ(x_{j₀})) 𝟙{j ∈ U}`. -/
def vertexVec {𝒳 : Type*} {J : ℕ} (φ : 𝒳 → E) (xs : Fin J → 𝒳) (j0 : Fin J) (U : Finset (Fin J)) (j : Fin J) : E :=
  if j ∈ U then φ (xs j) - φ (xs j0) else 0

open Classical in
/-- A nearest point of `C` to `x` (the metric projection `Π_C x` when `C` is closed, convex, nonempty), `x` if
none exists. -/
def metricProj (C : Set E) (x : E) : E :=
  if h : ∃ p ∈ C, ∀ q ∈ C, ‖x - p‖ ≤ ‖x - q‖ then h.choose else x

end Defs2

namespace Claims

/-- `thm:boundary`, proof Step 1 (the dual representation, `lem:cvar` + the separation duality): for probability
measures `P, Q`, `D = dist(𝒞_α(P), 𝒞_α(Q)) = max_{(g,t,s) ∈ Θ} Γ_{P,Q}(g,t,s)` (attained), `Θ = 𝔹_r × [−κ,κ]²`;
and the same for the empirical laws: `D̂ = max_Θ Γ_{P_n,Q_m}`. -/
def boundary_dual : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
      (∀ (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
        IsGreatest (range (dualTrim φ α P Q (κ := κ))) (Dpop φ P Q α)) ∧
      (∀ (n m : ℕ) (x : Fin n → 𝒳) (y : Fin m → 𝒳), 1 ≤ n → 1 ≤ m →
        IsGreatest (range (dualTrim φ α (empirical x) (empirical y) (κ := κ))) (Demp φ x y α))

/-- `thm:boundary`, proof Step 2 (the two-sample functional CLT): the empirical processes `r_k (P_{n_k} − P) ℓ_{f,t}`
and `r_k (Q_{m_k} − Q) ℓ_{f,s}`, `(f, t) ∈ 𝔹_r × [−κ, κ]`, jointly (one element of `C(Idx2, ℝ)`) converge in
distribution to `(c_P 𝔾_P ℓ, c_Q 𝔾_Q ℓ)` with independent Brownian bridges `𝔾_P, 𝔾_Q` (continuous versions); such a
process exists, its law is unique, and the convergence holds to every version of it. -/
def boundary_donsker : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ) (V : ℕ → Ω → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    (∀ k ω z, V k ω z = empProc φ P Q (n k) (m k) (r k) (fun i => ξ i ω) (fun j => η j ω) z) →
      (∃ 𝕍 : ProbabilityMeasure C(Idx2 E κ, ℝ), IsLimitGP φ P Q cP cQ κ (𝕍 : Measure C(Idx2 E κ, ℝ)) id) ∧
      (∀ 𝕍₁ 𝕍₂ : ProbabilityMeasure C(Idx2 E κ, ℝ), IsLimitGP φ P Q cP cQ κ (𝕍₁ : Measure C(Idx2 E κ, ℝ)) id →
        IsLimitGP φ P Q cP cQ κ (𝕍₂ : Measure C(Idx2 E κ, ℝ)) id → 𝕍₁ = 𝕍₂) ∧
      (∀ (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝕍 : Ω' → C(Idx2 E κ, ℝ)),
        IsLimitGP φ P Q cP cQ κ μ' 𝕍 → TendstoInDistribution V atTop 𝕍 (fun _ => μ) μ')

/-- The printed scaling: `n, m → ∞`, `n/m → ρ ∈ (0, ∞)`, `N = n ∧ m`: then `√N/√n → c_P = 1 ∧ ρ^{-1/2}` and
`√N/√m → c_Q = 1 ∧ ρ^{1/2}` (so `Scaling n m √N c_P c_Q`). -/
def boundary_rates : Prop :=
  ∀ (n m : ℕ → ℕ) (ρ : ℝ), 0 < ρ → (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    Tendsto (fun k => (n k : ℝ) / m k) atTop (𝓝 ρ) →
      Scaling n m (fun k => √(min (n k) (m k) : ℝ)) (min 1 (ρ ^ (-(1 / 2 : ℝ)))) (min 1 (ρ ^ (1 / 2 : ℝ)))

/-- `thm:boundary`, setting (`supp:boundarystate`, "By Step 1 of the proof"): for `‖f‖ ≤ 1`, `q_P(f)` is a nonempty
compact interval, and for `α > 0` it is exactly the set of `α`-quantiles of `⟨f, φ(X)⟩`, `X ∼ P`:
`t ∈ q_P(f) ⟺ P(⟨f, φ⟩ < t) ≤ α ≤ P(⟨f, φ⟩ ≤ t)` (for `t ∈ [−κ, κ]`; every `α`-quantile lies there). -/
def boundary_quantile : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P : Measure 𝒳) [IsProbabilityMeasure P],
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → ∀ f : E, ‖f‖ ≤ 1 →
      (argminSet φ α P κ f).Nonempty ∧ (∃ a b : ℝ, Subtype.val '' argminSet φ α P κ f = Icc a b) ∧
      (0 < α → (∀ t : ℝ, P.real {x | ⟪f, φ x⟫ < t} ≤ α → α ≤ P.real {x | ⟪f, φ x⟫ ≤ t} → t ∈ Icc (-κ) κ) ∧
        ∀ t : Icc (-κ) κ, t ∈ argminSet φ α P κ f ↔
          (P.real {x | ⟪f, φ x⟫ < t} ≤ α ∧ α ≤ P.real {x | ⟪f, φ x⟫ ≤ t}))

/-- `thm:boundary` (i): at EVERY `α ∈ [0, 1)`, `r_k (D̂ − D) ⇒ sup_{g ∈ G*} {−c_P H_P(−g) − c_Q H_Q(g)}` for every
version `𝔾 = (𝔾_P ℓ, 𝔾_Q ℓ)` of the limit process (`IsLimitGP` with `c = 1`; one exists, `boundary_donsker`);
`G*` (the maximisers of `g ↦ −h_A(−g) − h_B(g)` over `𝔹_r`) is nonempty, and when `D > 0` it is the single point
`(a* − b*)/‖a* − b*‖` for any nearest pair. -/
def boundary_every : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 →
      (Gstar φ α P Q).Nonempty ∧
      (0 < Dpop φ P Q α → ∀ a ∈ region φ α P, ∀ b ∈ region φ α Q, ‖a - b‖ = Dpop φ P Q α →
        ∀ g : Ball E, g ∈ Gstar φ α P Q ↔ (g : E) = ‖a - b‖⁻¹ • (a - b)) ∧
      TendstoInDistribution
        (fun k ω => r k * (Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α - Dpop φ P Q α))
        atTop (fun ω' => sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') '' Gstar φ α P Q)) (fun _ => μ) μ'

/-- `thm:boundary` (ii): if `A ∩ B ≠ ∅`, with `K = cl{λ(b − a)} = cl cone(B − A)`: `K = cl(T_Q(z) − T_P(z))` at every
contact point `z`, `G* = K° ∩ 𝔹_r`, and `r_k D̂ ⇒ sup_{g ∈ K°, ‖g‖ ≤ 1} {−c_P H_P(−g) − c_Q H_Q(g)}`. -/
def boundary_contact : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ)),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
      (∀ z ∈ region φ α P ∩ region φ α Q, closure (coneHull (region φ α Q - region φ α P)) =
        closure (tanCone (region φ α Q) z - tanCone (region φ α P) z)) ∧
      (∀ g : Ball E, g ∈ Gstar φ α P Q ↔ (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))) ∧
      TendstoInDistribution
        (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
        atTop (fun ω' => sSup (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ''
          {g | (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))})) (fun _ => μ) μ'

/-- `cor:boundary-linear` (main statement): in the setting of `thm:boundary` (ii), if almost surely
`H_P(f) = ⟨f, G_P⟩` for `f ∈ −K°`, `‖f‖ ≤ 1`, and `H_Q(g) = ⟨g, G_Q⟩` for `g ∈ K°`, `‖g‖ ≤ 1`, then
`r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`; and `‖Π_{K°} x‖ = dist(x, K)` for every `x` (Moreau). -/
def boundary_linear : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (GP GQ : Ω' → E),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
    (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫) →
      TendstoInDistribution
        (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
        atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
          (cP • GP ω' - cQ • GQ ω')‖) (fun _ => μ) μ' ∧
      ∀ x : E, ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P)))) x‖ =
        infDist x (closure (coneHull (region φ α Q - region φ α P)))

/-- `cor:boundary-linear` (a), a unique separating direction: in the setting of `thm:boundary` (ii), if
`K° = {λν : λ ≥ 0}` for a unit vector `ν`, then `r_k D̂ ⇒ (−c_P H_P(−ν) − c_Q H_Q(ν))_+`; if moreover
`q_P(−ν) = {t_P}` and `q_Q(ν) = {s_Q}`, the limit is `Z_+`, `Z ∼ N(0, σ²)`,
`σ² = β²{c_P² Var_P(ℓ_{−ν,t_P}) + c_Q² Var_Q(ℓ_{ν,s_Q})}`, which has an atom of mass `1/2` at `0` when `σ > 0`. -/
def boundary_ray : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (ν : Ball E),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty → ‖(ν : E)‖ = 1 →
    polarSet (closure (coneHull (region φ α Q - region φ α P))) = {x | ∃ c : ℝ, 0 ≤ c ∧ x = c • (ν : E)} →
      TendstoInDistribution
        (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
        atTop (fun ω' => max (boundaryLim φ α P Q κ cP cQ (𝔾 ω') ν) 0) (fun _ => μ) μ' ∧
      ∀ (tP sQ : Icc (-κ) κ), argminSet φ α P κ (-(ν : E)) = {tP} → argminSet φ α Q κ (ν : E) = {sQ} →
        let σ2 := (1 / (1 - α)) ^ 2 * (cP ^ 2 * Var[hinge φ (-(ν : E)) tP; P] + cQ ^ 2 * Var[hinge φ (ν : E) sQ; Q])
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun x : ℝ => max x 0) (fun _ => μ) (gaussianReal 0 σ2.toNNReal) ∧
        (0 < σ2 → (gaussianReal 0 σ2.toNNReal).map (fun x : ℝ => max x 0) {0} = 1 / 2)

/-- `cor:boundary-linear` (b), a nondegenerate vertex contact of discrete laws: in the setting of `thm:boundary`
(ii), if `P = Σ_j p_j δ_{x_j}` with `Σ_{j ∈ U} p_j < 1 − α < Σ_{j ∈ U} p_j + p_{j₀}` and every `f ∈ −K° \ {0}` has
`⟨f, φ(x_j)⟩ > ⟨f, φ(x_{j₀})⟩` for `j ∈ U` and `<` for `j ∉ U ∪ {j₀}`, and `Q` likewise with `K°` in place of
`−K°`, then the hypothesis of the corollary holds with random vectors `G_P, G_Q` whose evaluations on the relevant
directions are those of `β 𝔾_P ψ_P`, `β 𝔾_Q ψ_Q` (jointly centred Gaussian, covariance
`β² Cov_P(ψ_P) ⊕ β² Cov_Q(ψ_Q)` there, written through the atoms: `discVar`, `vertexVec`), and hence `r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`. -/
def boundary_vertex : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (J : ℕ) (xs : Fin J → 𝒳) (ps : Fin J → ℝ) (j0 : Fin J) (U : Finset (Fin J))
    (J' : ℕ) (ys : Fin J' → 𝒳) (qs : Fin J' → ℝ) (j0' : Fin J') (U' : Finset (Fin J')),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
    (∀ j, 0 ≤ ps j) → P = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j) → j0 ∉ U →
    ∑ j ∈ U, ps j < 1 - α → 1 - α < ∑ j ∈ U, ps j + ps j0 →
    (∀ g ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))), g ≠ 0 →
      (∀ j ∈ U, ⟪-g, φ (xs j0)⟫ < ⟪-g, φ (xs j)⟫) ∧ (∀ j, j ∉ U → j ≠ j0 → ⟪-g, φ (xs j)⟫ < ⟪-g, φ (xs j0)⟫)) →
    (∀ j, 0 ≤ qs j) → Q = ∑ j, ENNReal.ofReal (qs j) • Measure.dirac (ys j) → j0' ∉ U' →
    ∑ j ∈ U', qs j < 1 - α → 1 - α < ∑ j ∈ U', qs j + qs j0' →
    (∀ g ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))), g ≠ 0 →
      (∀ j ∈ U', ⟪g, φ (ys j0')⟫ < ⟪g, φ (ys j)⟫) ∧ (∀ j, j ∉ U' → j ≠ j0' → ⟪g, φ (ys j)⟫ < ⟪g, φ (ys j0')⟫)) →
      ∃ GP GQ : Ω' → E,
        (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
          Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫) ∧
        (∀ (p : ℕ) (f g : Fin p → E) (u w : Fin p → ℝ),
          (∀ i, f i ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))) →
          (∀ i, g i ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))) →
          μ'.map (fun ω' => ∑ i, u i * ⟪-f i, GP ω'⟫ + ∑ i, w i * ⟪g i, GQ ω'⟫) =
            gaussianReal 0 ((1 / (1 - α)) ^ 2 * (discVar ps (fun j => ∑ i, u i * ⟪-f i, vertexVec φ xs j0 U j⟫) +
              discVar qs (fun j => ∑ i, w i * ⟪g i, vertexVec φ ys j0' U' j⟫))).toNNReal) ∧
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
            (cP • GP ω' - cQ • GQ ω')‖) (fun _ => μ) μ'

end Claims

end StatFormal.Wave30z
