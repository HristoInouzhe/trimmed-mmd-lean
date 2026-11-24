import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements

/-!
# FROZEN STATEMENTS (DRAFT) — wave 30v: trimmed-mmd `conj:boundary`, the limiting law of `D̂_{α*}` at the
# contact level at fixed feature dimension (directional delta method)

Source (read 2026-10-20): `trimmed-mmd/supplement.tex:2239-2324` (`supp:boundary`, `conj:boundary` and the remark
"Reading the statement"); definitions `paper.tex:183-230` (`eq:trimMMDpop`, `𝒞_{α,k}`, `lem:cvar`), `:628-720`
(`eq:region`, `prop:georep`, `lem:attainment`), `:1081-1094` (`lem:separation`), `:1686-1696` (random features:
`𝒞^{(r)}` is `𝒞_{α,k}` for the feature map `z_r : 𝒳 → ℝ^r`, a fixed bounded map once drawn).
Imports the frozen `TrimmedMMD/Unconditional` statements (`setDist`), not copied. Mathlib's `TendstoInDistribution`,
`TendstoInMeasure`, `Metric.infDist`, `ContinuousMap` (sup norm on `C(Θ, ℝ)` for compact `Θ`) otherwise.
New definitions: `HasHadamardDirDeriv` (Shapiro 1990, sequential form, real-valued, NON-tangential), `supFun`
(the sup functional), `supportFn`, `polarSet`, `coneHull`, `tanCone`, `Ball`, `ballNeg`, `dualObj`, `valueFn`,
`valueDeriv`, `linDir`. (Critic 2026-10-20: `argmaxSet`, `supDeriv` and the library claims `boundary_sup_hadamard`,
`boundary_contact_argmax`, `boundary_polar_infDist`, `boundary_delta_method`, `boundary_sup_limit` moved to the
route files `RouteSup`, `RouteGeom`, `RouteDelta` — general facts, no printed label.)

What `conj:boundary` says. Fix `r`. (B1) `𝒞^{(r)}_{α*}(P) ∩ 𝒞^{(r)}_{α*}(Q) = {z*}` with tangent cones `T_P, T_Q`;
(B2) the points `û_n, v̂_m` of the empirical regions exposed by `ν, −ν` satisfy `√n(û_n − z*) ⇒ G_P`,
`√m(v̂_m − z*) ⇒ G_Q`, independent centred Gaussians; (B3) `D̂^{(r)}_{α*} = dist(û_n − v̂_m, T_Q − T_P) +
o_P(min(n,m)^{-1/2})`. Then along `n/m → ρ`, `√min(n,m) D̂ ⇒ ‖Π_{K°}((1/√ρ ∧ 1)G_P − (√ρ ∧ 1)G_Q)‖`,
`K = cl(T_Q − T_P)`, and "the squared limit is then a chi-bar-square variable".

Covered (targets):
* `conj:boundary`, the conjecture's implication, literally (`boundary_conditional`): (B2) in joint form + (B3) ⇒ the
  printed limit, in the distance form `dist(X, K)`, with `dist(X, K) = sup_{g ∈ K° , ‖g‖ ≤ 1} ⟨g, X⟩` for convex `T`
  (the further Moreau step `= ‖Π_{K°}X‖` is textbook and NOT formalised: Lean has no projection onto `K°` here).
  (B1) is not needed beyond `T` being a cone. This is a continuous-mapping + Slutsky argument: the content of the
  conjecture is in (B2), (B3).
* `lem:separation`, finite-dimensional equality form (`boundary_dist_dual`): `dist(A, B) = sup_{‖g‖ ≤ 1}
  (−h_A(−g) − h_B(g))` for nonempty compact convex `A, B ⊆ ℝ^r` (overlaps the certified Wave17a `separation`,
  `separation_attained`; here also the `dist = 0` case and in support-function form).
* `supp:boundary`'s "the value function [is] directionally, not fully, differentiable": the value function is
  Hadamard directionally differentiable at a contact pair (`A ∩ B ≠ ∅`) with the EXPLICIT derivative
  `(H_A, H_B) ↦ sup {−H_A(−g) − H_B(g) : ‖g‖ ≤ 1, g ∈ (B − A)°}` (`boundary_value_hadamard`).
* the conjecture's limit functional is this derivative in translation directions (`boundary_translation`):
  at `H_A = ⟨·, x_A⟩`, `H_B = ⟨·, x_B⟩` it equals `dist(x_A − x_B, cl cone(B − A))`, and
  `cl cone(B − A) = cl(T_B(z) − T_A(z))` for every `z ∈ A ∩ B` (`boundary_tangent_cone`: the printed `K`).
* NOT printed (an upgrade of `conj:boundary`): the limit law at the contact level, CONDITIONAL on a CLT for the
  support-function processes in `C(Ball) × C(Ball)` (on the WHOLE unit ball — stronger than the paper's
  "in a neighbourhood of `ν`" reading of (B2)), with no (B3) and no exposed-point CLT (`boundary_limit`):
  `r_k dist(A_k, B_k) ⇒ sup {−H_A(−g) − H_B(g) : ‖g‖ ≤ 1, g ∈ (B − A)°}`; and the printed limit
  `dist(G_A − G_B, K)` when the limit processes are a.s. translations on the whole ball (`boundary_limit_linear`).
Route-only (critic: general library facts, no printed label): the sup-functional derivative (Danskin/Römisch),
the contact argmax, the Moreau-type identity, the delta method for Hadamard directionally differentiable maps, and
the abstract lifted limit law `r_k(sup Γ_k − sup Γ) ⇒ sup_{argmax Γ} 𝕃` for processes converging in `C(Θ, ℝ)`.

Not covered (declared): the UNCONDITIONAL limit law ("Theorem A" of the wave-30v report) — it needs the `lem:cvar`
lift `D̂ = sup_Θ Γ_{P_n,Q_m}`, `Θ = Ball × [−κ, κ]²`, and the Donsker CLT for `{(⟨g, φ⟩ − t)_+}` in `C(Θ)`; neither is
formalised, so Theorem A is a report/paper-side argument, NOT certified here; the CLT for the support-function
process of the trimmed regions (limit `H(f) = min_{t ∈ q_α(f)} β 𝔾((⟨f, φ⟩ − t)_+)`); the counterexamples to (B2)
at the contact level `α* = TV` (two-atom and gapped-support laws, Stigler 1973; limit atom `1/4`, not `1/2`) and to
"chi-bar-square" (anisotropic covariance) — numerical (`~/.cache/w30v/`) and by hand.

Encodings (to be checked by the critic):
* `ℝ^r`: any finite-dimensional real inner product space `E`; the closed unit ball `Ball E` as a compact subtype;
  directions `C(Ball E, ℝ)` with the sup norm; pairs with the max norm.
* Support function `h_S(g) = sSup ⟨g, S⟩` (genuine for nonempty bounded `S`, which every claim assumes);
  `dist(A, B)` is the frozen `setDist`; the polar of a set `S°  = {g | ∀ x ∈ S, ⟨g, x⟩ ≤ 0}`; `B − A` the pointwise
  (Minkowski) difference; `T_S(z) = cl{c(s − z) : c ≥ 0, s ∈ S}` (tangent cone of a convex set).
* `HasHadamardDirDeriv Φ x Φ'`: for all `h`, `t_n > 0`, `t_n → 0`, `h_n → h`, `(Φ(x + t_n h_n) − Φ x)/t_n →
  Φ'(h)` — the full (non-tangential) Hadamard directional derivative, i.e. stronger than the tangential form of
  Fang–Santos 2019 (no restriction of `h` to a tangent set). The derivative at a contact pair is a `sSup` over the nonempty compact set `{g ∈ Ball | g ∈ (B − A)°}`
  (contains `0`) of a continuous function: genuine.
* Weak convergence: Mathlib `TendstoInDistribution` on ONE probability space `(Ω, μ)` (all samples defined there,
  as in van der Vaart–Wellner; specialisation of the paper's varying sample spaces). `o_P(s_k⁻¹)`:
  `TendstoInMeasure μ (s_k · (…)) atTop 0`. Scaling `s_k = √min(n_k, m_k)`: any `s_k > 0` (with `s_k → ∞` where the
  delta method needs it). (B2) is used in the joint form `s_k(û_k − v̂_k) ⇒ X` (it follows from the printed
  marginal form + independence of the two samples + `n/m → ρ`, with `X = c_P G_P − c_Q G_Q`; that step is not
  formalised). The joint hypothesis is WEAKER than the printed (B2) (only the difference must converge, to any
  limit, Gaussian or not), so `boundary_conditional` is more general than the printed implication, never less.
* Random sets `A_k ω, B_k ω` (nonempty, compact, convex — true for `𝒞_{α}(P_n)` by `prop:georep`, polytopes),
  with support-function processes `hA_k ω, hB_k ω ∈ C(Ball E, ℝ)`; a Borel σ-algebra on the pair space is a
  hypothesis (instance argument), as is joint weak convergence.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30v

open StatFormal.TrimmedMMD.Unconditional (setDist)

/-- Hadamard directional differentiability (Shapiro 1990) of `Φ : V → ℝ` at `x` with derivative `Φ'`: for every
direction `h`, every sequence `t_n > 0` with `t_n → 0` and every `h_n → h`,
`(Φ(x + t_n h_n) − Φ(x)) / t_n → Φ'(h)`. -/
def HasHadamardDirDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : V → ℝ) (x : V)
    (Φ' : V → ℝ) : Prop :=
  ∀ (h : V) (t : ℕ → ℝ) (k : ℕ → V), (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) → Tendsto k atTop (𝓝 h) →
    Tendsto (fun n => (Φ (x + t n • k n) - Φ x) / t n) atTop (𝓝 (Φ' h))

section SupFunctional
variable {Θ : Type*} [TopologicalSpace Θ]

/-- The sup functional `z ↦ sup_Θ z` on `C(Θ, ℝ)`. -/
def supFun (z : C(Θ, ℝ)) : ℝ := sSup (Set.range z)

end SupFunctional

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function `h_S(g) = sup_{s ∈ S} ⟨g, s⟩`. -/
def supportFn (S : Set E) (g : E) : ℝ := sSup ((fun s => ⟪g, s⟫) '' S)

/-- The (negative) polar of a set, `S° = {g | ∀ x ∈ S, ⟨g, x⟩ ≤ 0}`. -/
def polarSet (S : Set E) : Set E := {g | ∀ x ∈ S, ⟪g, x⟫ ≤ 0}

/-- The conic hull `{c s : c ≥ 0, s ∈ S}`. -/
def coneHull (S : Set E) : Set E := {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ S, v = c • s}

/-- The tangent cone of a convex set `S` at `z`: `T_S(z) = cl{c (s − z) : c ≥ 0, s ∈ S}`. -/
def tanCone (S : Set E) (z : E) : Set E := closure {v | ∃ c : ℝ, 0 ≤ c ∧ ∃ s ∈ S, v = c • (s - z)}

/-- The closed unit ball of `E`, as a type (the index set of the support-function processes). -/
abbrev Ball (E : Type*) [NormedAddCommGroup E] := ↥(closedBall (0 : E) 1)

/-- `g ↦ −g` on the unit ball. -/
def ballNeg (g : Ball E) : Ball E :=
  ⟨-(g : E), by have h := g.2; rw [mem_closedBall_zero_iff] at h ⊢; rwa [norm_neg]⟩

omit [InnerProductSpace ℝ E] in
lemma continuous_ballNeg : Continuous (ballNeg (E := E)) :=
  (continuous_subtype_val.neg).subtype_mk _

/-- The dual objective `g ↦ −H_A(−g) − H_B(g)` of the distance between two sets, as a continuous function on the
unit ball (`lem:separation`: `dist(A, B) ≥ inf_A ⟨g, ·⟩ − sup_B ⟨g, ·⟩ = −h_A(−g) − h_B(g)`). -/
def dualObj (H₁ H₂ : C(Ball E, ℝ)) : C(Ball E, ℝ) :=
  ⟨fun g => -H₁ (ballNeg g) - H₂ g, ((H₁.continuous.comp continuous_ballNeg).neg).sub H₂.continuous⟩

/-- The value function `(H_A, H_B) ↦ sup_{‖g‖ ≤ 1} (−H_A(−g) − H_B(g))`; at the support functions of nonempty
compact convex `A, B` it is `dist(A, B)` (`boundary_dist_dual`). -/
def valueFn (H : C(Ball E, ℝ) × C(Ball E, ℝ)) : ℝ := supFun (dualObj H.1 H.2)

/-- The explicit Hadamard directional derivative of `valueFn` at a contact pair `(h_A, h_B)` (`A ∩ B ≠ ∅`):
`(H_A, H_B) ↦ sup {−H_A(−g) − H_B(g) : ‖g‖ ≤ 1, g ∈ (B − A)°}`. -/
def valueDeriv (A B : Set E) (H : C(Ball E, ℝ) × C(Ball E, ℝ)) : ℝ :=
  sSup ((fun g : Ball E => -H.1 (ballNeg g) - H.2 g) '' {g : Ball E | (g : E) ∈ polarSet (B - A)})

/-- The translation direction `g ↦ ⟨g, x⟩` (the support-function perturbation of `S ↦ S + t x`). -/
def linDir (x : E) : C(Ball E, ℝ) := ⟨fun g => ⟪(g : E), x⟫, continuous_subtype_val.inner continuous_const⟩

end Geometry

namespace Claims

/-! ### The deterministic core -/

/-- `lem:separation`, equality form (the representation of `D̂` as a value function): for nonempty compact convex
`A, B ⊆ ℝ^r`, `dist(A, B) = sup_{‖g‖ ≤ 1} (−h_A(−g) − h_B(g))`. -/
def boundary_dist_dual : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : Set E) (hA hB : C(Ball E, ℝ)), A.Nonempty → B.Nonempty → IsCompact A → IsCompact B →
    Convex ℝ A → Convex ℝ B → (∀ g, hA g = supportFn A g) → (∀ g, hB g = supportFn B g) →
      setDist A B = valueFn (hA, hB)

/-- `supp:boundary` ("the value function [is] directionally, not fully, differentiable"), the deterministic part of
`conj:boundary`: at a contact pair (`A ∩ B ≠ ∅`, `A, B` nonempty bounded), the value
function is `0` and is Hadamard directionally differentiable at `(h_A, h_B)` with the explicit derivative
`(H_A, H_B) ↦ sup {−H_A(−g) − H_B(g) : ‖g‖ ≤ 1, g ∈ (B − A)°}`. -/
def boundary_value_hadamard : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : Set E) (hA hB : C(Ball E, ℝ)), A.Nonempty → B.Nonempty →
    Bornology.IsBounded A → Bornology.IsBounded B → (A ∩ B).Nonempty →
    (∀ g, hA g = supportFn A g) → (∀ g, hB g = supportFn B g) →
      valueFn (hA, hB) = 0 ∧ HasHadamardDirDeriv valueFn (hA, hB) (valueDeriv A B)

/-- The conjecture's cone: for convex `A, B` and any `z ∈ A ∩ B`, `cl(T_B(z) − T_A(z)) = cl cone(B − A)` (so the
cone `K = cl(T_Q − T_P)` of `conj:boundary` does not depend on the contact point and is the tangent cone of
`B − A` at `0`). -/
def boundary_tangent_cone : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : Set E) (z : E),
    Convex ℝ A → Convex ℝ B → z ∈ A → z ∈ B →
      closure (tanCone B z - tanCone A z) = closure (coneHull (B - A))

/-- The conjecture's limit functional is the derivative in translation directions: at a contact pair of nonempty
convex `A, B` (no boundedness needed: `valueDeriv` does not involve support functions), `valueDeriv A B (⟨·, x_A⟩, ⟨·, x_B⟩) = dist(x_A − x_B, cl cone(B − A))`. -/
def boundary_translation : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (A B : Set E),
    A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B → (A ∩ B).Nonempty → ∀ xA xB : E,
      valueDeriv A B (linDir xA, linDir xB) = infDist (xA - xB) (closure (coneHull (B - A)))

/-! ### Delta method and the limit law -/

/-- `conj:boundary`, the limit law at the contact level, conditional only on the support-function CLT: let
`A, B ⊆ ℝ^r` be nonempty compact convex with `A ∩ B ≠ ∅`, `A_k, B_k` random nonempty compact convex sets
(e.g. `𝒞^{(r)}_{α*}(P_n), 𝒞^{(r)}_{α*}(Q_m)`) with support functions `hA_k, hB_k` on the unit ball, and suppose
`r_k (hA_k − h_A, hB_k − h_B) ⇒ (H_A, H_B)` in `C(Ball) × C(Ball)`, `r_k → ∞`. Then
`r_k dist(A_k, B_k) ⇒ sup {−H_A(−g) − H_B(g) : ‖g‖ ≤ 1, g ∈ (B − A)°}`. No exposed-point CLT (B2) and no
expansion (B3) are assumed; the support-function CLT on the WHOLE unit ball is assumed (stronger than the printed local
"neighbourhood of `ν`" form, and it can fail for the trimmed regions when the quantile set of `⟨g, φ⟩` jumps with
`g`; the trimmed-region CLT is not formalised). Not a printed result: an upgrade of `conj:boundary`. -/
def boundary_limit : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (C(Ball E, ℝ) × C(Ball E, ℝ))] [BorelSpace (C(Ball E, ℝ) × C(Ball E, ℝ))]
    (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (A B : Set E) (hA hB : C(Ball E, ℝ))
    (Ak Bk : ℕ → Ω → Set E) (hAk hBk : ℕ → Ω → C(Ball E, ℝ)) (H : Ω' → C(Ball E, ℝ) × C(Ball E, ℝ)) (r : ℕ → ℝ),
    A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B → (A ∩ B).Nonempty →
    (∀ g, hA g = supportFn A g) → (∀ g, hB g = supportFn B g) →
    (∀ k ω, (Ak k ω).Nonempty ∧ (Bk k ω).Nonempty ∧ IsCompact (Ak k ω) ∧ IsCompact (Bk k ω) ∧
      Convex ℝ (Ak k ω) ∧ Convex ℝ (Bk k ω)) →
    (∀ k ω g, hAk k ω g = supportFn (Ak k ω) g) → (∀ k ω g, hBk k ω g = supportFn (Bk k ω) g) →
    (∀ k, 0 < r k) → Tendsto r atTop atTop →
    TendstoInDistribution (fun k ω => r k • ((hAk k ω, hBk k ω) - (hA, hB))) atTop H (fun _ => μ) μ' →
      TendstoInDistribution (fun k ω => r k * setDist (Ak k ω) (Bk k ω)) atTop (fun ω => valueDeriv A B (H ω))
        (fun _ => μ) μ'

/-- `conj:boundary`'s printed limit, WITHOUT (B3) and without an exposed-point CLT: in the setting of
`boundary_limit`, if the limit processes are a.s. translations ON THE WHOLE UNIT BALL, `H_A = ⟨·, G_A⟩`,
`H_B = ⟨·, G_B⟩`, then `r_k dist(A_k, B_k) ⇒ dist(G_A − G_B, cl cone(B − A))` (`= ‖Π_{K°}(G_A − G_B)‖` by Moreau,
not formalised). Global linearity is stronger than what the limit uses (linearity of `H_A` on `−K°` and of `H_B`
on `K°`): for discrete laws the support-function limit is only piecewise linear (one Gaussian per vertex), so this
corollary covers translation-type limits only; the polar-cone version follows from `boundary_limit` but is not
stated here. -/
def boundary_limit_linear : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (C(Ball E, ℝ) × C(Ball E, ℝ))] [BorelSpace (C(Ball E, ℝ) × C(Ball E, ℝ))]
    (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (A B : Set E) (hA hB : C(Ball E, ℝ))
    (Ak Bk : ℕ → Ω → Set E) (hAk hBk : ℕ → Ω → C(Ball E, ℝ)) (GA GB : Ω' → E) (r : ℕ → ℝ),
    A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B → (A ∩ B).Nonempty →
    (∀ g, hA g = supportFn A g) → (∀ g, hB g = supportFn B g) →
    (∀ k ω, (Ak k ω).Nonempty ∧ (Bk k ω).Nonempty ∧ IsCompact (Ak k ω) ∧ IsCompact (Bk k ω) ∧
      Convex ℝ (Ak k ω) ∧ Convex ℝ (Bk k ω)) →
    (∀ k ω g, hAk k ω g = supportFn (Ak k ω) g) → (∀ k ω g, hBk k ω g = supportFn (Bk k ω) g) →
    (∀ k, 0 < r k) → Tendsto r atTop atTop →
    TendstoInDistribution (fun k ω => r k • ((hAk k ω, hBk k ω) - (hA, hB))) atTop
      (fun ω => (linDir (GA ω), linDir (GB ω))) (fun _ => μ) μ' →
      TendstoInDistribution (fun k ω => r k * setDist (Ak k ω) (Bk k ω)) atTop
        (fun ω => infDist (GA ω - GB ω) (closure (coneHull (B - A)))) (fun _ => μ) μ'

/-- `conj:boundary` as printed, its implication: if `s_k(û_k − v̂_k) ⇒ X` ((B2), joint form) and
`D̂_k = dist(û_k − v̂_k, T) + o_P(s_k⁻¹)` ((B3)) for a cone `T`, then `s_k D̂_k ⇒ dist(X, T) = dist(X, cl T)`;
if `T` is moreover convex, `dist(X, cl T) = sup {⟨g, X⟩ : g ∈ T°, ‖g‖ ≤ 1}` (`= ‖Π_{K°} X‖`, `K = cl T`, by Moreau —
that last step is not formalised). Instantiation: `T = T_Q − T_P` (convex), `s_k = √min(n_k, m_k)`,
`X = (1 ∧ ρ^{-1/2}) G_P − (1 ∧ ρ^{1/2}) G_Q`; the printed (B2) (marginal CLTs, independent samples, `n/m → ρ`)
implies the joint hypothesis, which is weaker, so this claim is at least as general as the printed implication.
(B1) is not used. -/
def boundary_conditional : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (T : Set E) (u v : ℕ → Ω → E) (D : ℕ → Ω → ℝ)
    (X : Ω' → E) (s : ℕ → ℝ),
    T.Nonempty → (∀ c : ℝ, 0 < c → ∀ w ∈ T, c • w ∈ T) → (∀ k, 0 < s k) → (∀ k, AEMeasurable (D k) μ) →
    TendstoInDistribution (fun k ω => s k • (u k ω - v k ω)) atTop X (fun _ => μ) μ' →
    TendstoInMeasure μ (fun k ω => s k * (D k ω - infDist (u k ω - v k ω) T)) atTop 0 →
      TendstoInDistribution (fun k ω => s k * D k ω) atTop (fun ω => infDist (X ω) (closure T)) (fun _ => μ) μ' ∧
      (Convex ℝ T → ∀ x : E, infDist x (closure T) = sSup ((fun g => ⟪g, x⟫) '' (polarSet T ∩ closedBall 0 1)))

end Claims

end StatFormal.Wave30v
