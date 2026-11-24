import StatFormal.Archive.OTFD.Wave6b.Statements
import TauCeti.Data.Matrix.EntropicTransport
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FROZEN STATEMENTS — otfd wave 8b: A `thm:naive-degenerate`, A `prop:emp-bijective-weak`,
# A `cor:app-entropic-weak`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of 2026-10-14, paths below
are under `otfd/papers/`):
* A `thm:naive-degenerate` (`A_sieves/main.tex:529-550`), with the naive spherical law, `Π_K`, `ι_K`, `‖·‖_{M_K}`,
  `B_{K,M_K}(τ)` of `subsec:geometry` (`main.tex:388-440`) and `eq:iota-isometry` (`main.tex:589-598`); proof
  `A_sieves/supplement.tex:851-895`.
* A `prop:emp-bijective-weak` (`A_sieves/supplement.tex:2518-2536`), with `ass:app-weak-conditioning`
  (`supplement.tex:2483-2498`); proof `supplement.tex:3231-3271` (Step 1 of the proof of `prop:emp-bijective`, the
  fixed-marginal expansion, is restated there).
* A `cor:app-entropic-weak` (`A_sieves/supplement.tex:2587-2609`), with the entropic program
  `eq:app-entropic-program` and the barycentric rank `eq:app-entropic-barycenter` (`supplement.tex:3280-3296`); proof
  `supplement.tex:3392-3409`, which reuses `eq:app-entropic-cost-gap`, `eq:app-entropic-kl-bound` and the coupling
  expansion of the proof of `prop:app-entropic` (`supplement.tex:3322-3390`).
Reuses the frozen `OTFD/Wave6b/Statements.lean` (`empMeasure`), imported, not copied; Tau Ceti's `wassersteinEDist`
(`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean:173`), `Matrix.transportPolytope`,
`Matrix.entropicTransportObjective` (`TauCeti/Data/Matrix/EntropicTransport.lean:105,115`) and `Matrix.relEntropy`
(`TauCeti/Data/Matrix/Scaling.lean:195`); Mathlib's `Measure.toSphere`.

Covered:
* `thm:naive-degenerate`: `naive_law_indep` (the law does not depend on the choice of `L_K`, `subsec:geometry`);
  `naive_radial` (`‖U‖_{M_K}` has law `Unif(0,1)`, and `μ°_K(B_{K,M_K}(τ)) = τ` for `τ ∈ [0,1]`); `naive_identity_I`
  (`M_K = I`: the law is that of `Rθ`, and the second moment is exactly `‖Π_K h‖²/(3K)`); `naive_second_moment`
  (the exact identity `E⟨ι_K U, h⟩² = ‖L_K^{-⊤}Π_K h‖²/(3K)`, with integrability); `naive_second_moment_le` (`≤
  ‖Π_K h‖²/(3cK)`, and Bessel `‖Π_K h‖ ≤ ‖h‖`); `naive_second_moment_tendsto` (`→ 0`); `naive_weak_tendsto` (the
  embedded laws converge to `δ₀` for the weak topology of `H`); `naive_norm_mass` (with `λ_max ≤ C`:
  `inf_K P(‖ι_K U‖ > a/√C) ≥ P(R > a)`), `naive_norm_no_weak` (with `λ_max ≤ C`: no weak convergence to `δ₀` for the
  norm topology); `naive_KI_norm` (`M_K = KI_K`: `‖ι_K U‖ = R/√K`), `naive_KI_converges` (`M_K = KI_K` satisfies the
  lower bound with `c = 1`, and the embedded laws converge to `δ₀` for the norm topology).
* `prop:emp-bijective-weak`: `bregman_assign` (Step 1: `σ̂` minimises the squared assignment cost iff it minimises
  `σ ↦ Σ_i D(u_{σ(i)}, r_i)`); `bregman_plan` (the same expansion for any two plans with equal marginals, used by
  both items); `bijective_core` (Steps 1–2 for one realisation: `(α/2)·n⁻¹Σ‖u_{σ̂(i)} − r_i‖² ≤
  (2 m⁻¹Σ‖s_j‖² + 2n⁻¹Σ‖x_i‖²)^{1/2} W₂(ν̂_n, μ_{K,n})`); `emp_bijective_weak` (the displayed bound).
* `cor:app-entropic-weak`: `kl_le_log_min` (`eq:app-entropic-kl-bound`: `KL(π‖a⊗b) ≤ log min(n,m)` for every plan
  with uniform marginals); `entropic_core` (the bound for one realisation); `app_entropic_weak` (the displayed bound,
  every `n, m ≥ 1` and `ε > 0`).

Not covered (declared):
* `thm:naive-degenerate`: "Without the lower spectral condition `L_K^{-1}` need not be uniformly bounded and the
  displayed bound breaks down; we do not pursue sharpness" (interpretive, no claim). The orthonormality example after
  the lemma (outside the environment).
* `prop:emp-bijective-weak`: the Brenier layer. `φ_{K_n}`, its conjugate and Step 0 of the proof (`x_i ∈
  ∂φ*(r_i)` from `r_i = ∇φ(x_i)`, hence `x_i = ∇φ*(r_i)` where `φ*` is differentiable) are not formalised; their
  consequences enter as hypotheses at the points used: `SubgradAt` (`s_j ∈ ∂φ*(u_j)`, tested at the ranks) and
  `OneSidedAt` (`ass:app-weak-conditioning`(i) at the pairs `(u_j, r_i)`, with `x_i` in the role of `∇φ*(r_i)`), both
  almost surely. The last sentence ("Consequently `Δ^{emp,(n)}_n` is bounded by …") is Minkowski against the
  finite-grid population map `F_{+,K_n,m_n}`, which is not formalised. That the `r_i` are iid `μ_{K_n}` is not used.
* `cor:app-entropic-weak`: the sentence "After taking square roots and inserting `ι_K F_{+,K_n}(x_i)`, Minkowski …"
  (needs `𝔽_P`, `Δ^{sieve,L²}` and `prop:integrated-sieve-strong`), and "This route does not use …" (interpretive).
  The Brenier layer, as above.

Encodings (see card):
* Naive law: `ℝ^K = EuclideanSpace ℝ (Fin K)`. `θ ~ Unif(S^{K−1})` is Mathlib's `volume.toSphere` pushed to `ℝ^K`
  and normalised (`sphereUnif`; a probability measure for `K ≥ 1`); `R ~ Unif(0,1)` is `volume` on `(0,1]`
  (`unifRadius`); independence is the product measure, and `μ°_K = (Unif(0,1) ⊗ Unif(S^{K−1})).map((r,θ) ↦
  L_K^{-1}(rθ))` (`naiveLaw`). `L_K` is an invertible linear map `ℝ^K ≃L ℝ^K` (a `K×K` invertible matrix), and
  `M_K = L_K^⊤L_K` enters through its quadratic form `u^⊤M_Ku = ‖L_Ku‖²`; so `‖u‖_{M_K} = ‖L_Ku‖`,
  "`L^⊤L = L'^⊤L'`" is `∀ v, ‖Lv‖ = ‖L'v‖` (polarisation), `λ_min(M_K) ≥ c` is `c‖v‖² ≤ ‖L_Kv‖²` for all `v`, and
  `λ_max(M_K) ≤ C` is `‖L_Kv‖² ≤ C‖v‖²`. `L_K^{-⊤} = (L_K^{-1})^*` (Hilbert adjoint). `M_K = I` is `L_K = id`;
  `M_K = KI_K` is `L_K v = √K v`. `(e_k)` is `e : ℕ → H`, `Orthonormal ℝ e` (index shift `e_{k+1} ↦ e k`);
  `ι_K z = Σ_{k<K} z_k e_k` (`embed`), `Π_K h = (⟨e_k,h⟩)_{k<K}` (`proj`). `H` is a real inner-product space, complete
  where the weak topology is used (no separability: generalisation). The embedded law is `μ°_K.map ι_K` on the Borel
  `σ`-algebra of the norm (`embLaw`). "Converge to `δ₀` weakly as measures on `H` with its weak topology": for every
  bounded `f : H → ℝ` that is continuous for the weak topology (`f ∘ (toWeakSpace ℝ H).symm` continuous on
  `WeakSpace ℝ H`), `∫ f dμ_K → f(0)`; such `f` are norm-continuous, so Borel (no junk integral). For the norm
  topology the test functions are bounded norm-continuous `f`. `E⟨ι_K U,h⟩²` is a Bochner integral, stated together
  with integrability. Sequences are indexed by every `K ∈ ℕ` (`K = 0` gives the zero measure, irrelevant for `atTop`);
  pointwise claims take `K ≥ 1`.
* Bijective/entropic: `n, m ≥ 1`; `x_i ∈ ℝ^K` the projected data `Π_K X_i`, `r_i = F(x_i)` with `F : ℝ^K → ℝ^K`
  arbitrary (the population rank map `F_{+,K_n}`), grid `u : Fin m → ℝ^K`, subgradients `s : Fin m → ℝ^K`. `φ*_{K_n}`
  is a real function `f` that is only evaluated at grid points and at ranks (where the paper shows it is finite), so the
  extended-real conjugate is never needed: `SubgradAt` is the subgradient inequality of `s_j ∈ ∂φ*(u_j)` at the
  ranks, `bregD f x r u = f(u) − f(r) − ⟨x, u − r⟩` is `D(u,r)` with `x = ∇φ*(r)`, and `OneSidedAt` is
  `ass:app-weak-conditioning`(i) at the pairs `(u_j, r_i)`. `ass:app-weak-conditioning`(ii) is `m⁻¹Σ‖s_j‖² ≤ β²`.
  The hard assignment is any `σ̂` minimising `Σ_i ‖x_i − u_{σ(i)}‖²` (`IsOptAssign`, for every realisation; no
  measurability, no uniqueness); `F̂^{(n)}_{+,K,n}(x_i) = u_{σ̂(i)}`. The entropic plan is any minimiser over Tau Ceti's
  `transportPolytope (1/n) (1/m)` of `entropicTransportObjective` with cost `‖x_i − u_j‖²` (`IsEntPlan`; its
  `relEntropy` against `a ⊗ b` is `KL(π‖a⊗b)` for probability vectors), `F̂^{bar}(x_i) = n Σ_j π_ij u_j` (`entBary`).
  `ν̂_n = n⁻¹Σδ_{r_i}` and `μ_{K,m} = m⁻¹Σδ_{u_j}` are the frozen `empMeasure`; `W₂` is Tau Ceti's
  `wassersteinEDist 2` (`ℝ≥0∞`, infimum over couplings, no attainment assumed). Data: `x i : Ω → ℝ^K` measurable,
  each with law `P_K` (`P.map (x i) = P_K`; independence is not needed), finite second moment, `σ²_{K} =
  ∫‖z‖² dP_K`; `μ` is any probability measure (the reference `μ_{K_n}`). Expectations are lower Lebesgue integrals
  `∫⁻` (as in the frozen `lem:app-empirical-wass`), the bounds are in `ℝ≥0∞` with `ENNReal.ofReal` of nonnegative
  reals (so a `W₂ = ∞` is never truncated to `0`), and `{·}^{1/2}` is `rpow (1/2)`. `log min(n,m)` is
  `Real.log (min n m)` (`n, m ≥ 1`).

Critic notes:
* `thm:naive-degenerate`: the identity holds for every system `(e_k)` (orthonormality is used only for Bessel and for
  `‖ι_K z‖ = ‖z‖`); the weak-topology convergence needs neither separability nor weak compactness (route: a
  weak neighbourhood of `0` contains `{|⟨·,h_ℓ⟩| < δ, ℓ ≤ p}`, then Chebyshev with the second-moment bound). The
  norm-negative clause does not need the lower spectral bound.
* `prop:emp-bijective-weak`/`cor:app-entropic-weak`: the constants `4/α` and `ε/α` are recovered exactly; the
  deterministic cores hold with the actual grid mean `m⁻¹Σ‖s_j‖²` in place of `β²`. The proof's `π₀` (unregularised
  optimum) is not needed: comparing the entropic plan directly with any Euclidean plan `π_E` gives the same bound.
  Uniform marginals with repeated points are handled (a coupling of `ν̂_n` and `μ_{K,m}` is split evenly over equal
  atoms, `RouteBregman.exists_plan_of_coupling`). The expectation step never needs measurability of
  `ω ↦ W₂(ν̂_n(ω), ·)`: Cauchy–Schwarz is done by Young's inequality with one measurable factor
  (`RouteBregman.lintegral_mul_le_sqrt`).
* Routes: all 18 claims are proved in `Wave8b/RouteNaive.lean` (11) and `Wave8b/RouteBregman.lean` (7), axioms
  `propext, Classical.choice, Quot.sound` only. No paper defect found; the printed constants are exact.
* Critic (2026-10-14): ACCEPT-WITH-NOTE. The weak-topology encoding is the paper's notion (weak convergence of measures
  on `(H, weak)`), not weak convergence in `H`; `naive_KI_converges` with `f ≡ 1` forces mass 1, so the law is not `0`
  and `naive_norm_no_weak` is not vacuous. `SubgradAt`/`OneSidedAt` are derivable from ass:app-weak-conditioning plus
  Step 0 (supplement 3232–3239) and are non-trivialising (`K = 1`, `f = u²/2`, `F = id`). `∫⁻` covers the paper's
  case (Borel `F`, measurable argmin selection) exactly. The Minkowski "consequently" sentences remain declared.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave8b

open StatFormal.OTFD.Wave6b (empMeasure)
open TauCeti (wassersteinEDist)

/-! ### A `thm:naive-degenerate` -/

section Naive

/-- `Unif(S^{K−1})`: Mathlib's sphere measure `volume.toSphere`, pushed to `ℝ^K` and normalised. -/
def sphereUnif (K : ℕ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere univ)⁻¹ •
    ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere.map Subtype.val)

/-- `Unif(0,1)` for the radius. -/
def unifRadius : Measure ℝ := volume.restrict (Ioc 0 1)

/-- The naive spherical law `μ°_K = L(L_K^{-1}(Rθ))`, `R ~ Unif(0,1)` independent of `θ ~ Unif(S^{K−1})`. -/
def naiveLaw {K : ℕ} (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) :
    Measure (EuclideanSpace ℝ (Fin K)) :=
  (unifRadius.prod (sphereUnif K)).map fun p => L.symm (p.1 • p.2)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ι_K z = Σ_{k<K} z_k e_k`. -/
def embed (e : ℕ → H) (K : ℕ) (z : EuclideanSpace ℝ (Fin K)) : H := ∑ k : Fin K, z k • e k

/-- `Π_K h = (⟨e_k, h⟩)_{k<K}`. -/
def proj (e : ℕ → H) (K : ℕ) (h : H) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k : Fin K => ⟪e k, h⟫_ℝ

/-- The embedded law `ι_K # μ°_K` on `H`. -/
def embLaw [MeasurableSpace H] (e : ℕ → H) {K : ℕ}
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) : Measure H :=
  (naiveLaw L).map (embed e K)

end Naive

/-! ### A `prop:emp-bijective-weak`, `cor:app-entropic-weak` -/

section Bregman
variable {K n m : ℕ}

/-- `D(u,r) = φ*(u) − φ*(r) − ⟨x, u − r⟩`, with `x` in the role of `∇φ*(r)`. -/
def bregD (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  f u - f r - ⟪x, u - r⟫_ℝ

/-- `s_j ∈ ∂φ*(u_j)`, tested at the ranks: `φ*(u_j) + ⟨s_j, r_i − u_j⟩ ≤ φ*(r_i)`. -/
def SubgradAt (f : EuclideanSpace ℝ (Fin K) → ℝ) (u s : Fin m → EuclideanSpace ℝ (Fin K))
    (r : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ i j, f (u j) + ⟪s j, r i - u j⟫_ℝ ≤ f (r i)

/-- `ass:app-weak-conditioning`(i) at the pairs `(u_j, r_i)`, with `∇φ*(r_i) = x_i`. -/
def OneSidedAt (α : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (x r : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ i j, α / 2 * ‖u j - r i‖ ^ 2 ≤ bregD f (x i) (r i) (u j)

/-- `σ` is a hard assignment: it minimises `Σ_i ‖x_i − u_{σ(i)}‖²`. -/
def IsOptAssign (x u : Fin n → EuclideanSpace ℝ (Fin K)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), ∑ i, ‖x i - u (σ i)‖ ^ 2 ≤ ∑ i, ‖x i - u (τ i)‖ ^ 2

/-- Uniform weights `1/n`. -/
def unifW (n : ℕ) : Fin n → ℝ := fun _ => 1 / n

/-- Squared-distance cost matrix `C_ij = ‖x_i − u_j‖²`. -/
def sqCost (x : Fin n → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K)) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => ‖x i - u j‖ ^ 2

/-- `π` solves `eq:app-entropic-program`: a feasible minimiser of `Σ π_ij‖x_i − u_j‖² + ε KL(π‖a⊗b)`. -/
def IsEntPlan (ε : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (π : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  π ∈ Matrix.transportPolytope (unifW n) (unifW m) ∧
    IsMinOn ((sqCost x u).entropicTransportObjective ε (unifW n) (unifW m))
      (Matrix.transportPolytope (unifW n) (unifW m)) π

/-- The entropic barycentric rank `n Σ_j π_ij u_j` (`eq:app-entropic-barycenter`). -/
def entBary (π : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → EuclideanSpace ℝ (Fin K)) (i : Fin n) :
    EuclideanSpace ℝ (Fin K) :=
  (n : ℝ) • ∑ j, π i j • u j

end Bregman

namespace Claims

/-! ### A `thm:naive-degenerate` -/

/-- The naive law depends on `L_K` only through `M_K = L_K^⊤L_K`. -/
def naive_law_indep : Prop :=
  ∀ (K : ℕ) (L L' : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)),
    (∀ v, ‖L v‖ = ‖L' v‖) → naiveLaw L = naiveLaw L'

/-- `‖U‖_{M_K} = ‖L_K U‖` has law `Unif(0,1)`; hence `μ°_K(B_{K,M_K}(τ)) = τ` for `τ ∈ [0,1]`. -/
def naive_radial : Prop :=
  ∀ (K : ℕ) (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)), 1 ≤ K →
    (naiveLaw L).map (fun u => ‖L u‖) = unifRadius ∧
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → naiveLaw L {u | ‖L u‖ ≤ τ} = ENNReal.ofReal τ

/-- `M_K = I`: the law is that of `Rθ`, and `E⟨ι_K U,h⟩² = ‖Π_K h‖²/(3K)`. -/
def naive_identity_I : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ) (h : H), 1 ≤ K →
    naiveLaw (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin K))) =
        (unifRadius.prod (sphereUnif K)).map (fun p => p.1 • p.2) ∧
      Integrable (fun u => ⟪embed e K u, h⟫_ℝ ^ 2)
        (naiveLaw (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin K)))) ∧
      ∫ u, ⟪embed e K u, h⟫_ℝ ^ 2 ∂(naiveLaw (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin K)))) =
        ‖proj e K h‖ ^ 2 / (3 * K)

/-- The exact identity `E⟨ι_K U,h⟩² = ‖L_K^{-⊤}Π_K h‖²/(3K)`. -/
def naive_second_moment : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (h : H), 1 ≤ K →
    Integrable (fun u => ⟪embed e K u, h⟫_ℝ ^ 2) (naiveLaw L) ∧
      ∫ u, ⟪embed e K u, h⟫_ℝ ^ 2 ∂(naiveLaw L) =
        ‖ContinuousLinearMap.adjoint (L.symm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
            (proj e K h)‖ ^ 2 / (3 * K)

/-- Under `λ_min(M_K) ≥ c > 0`: `E⟨ι_K U,h⟩² ≤ ‖Π_K h‖²/(3cK)`, and `‖Π_K h‖ ≤ ‖h‖` (Bessel). -/
def naive_second_moment_le : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (c : ℝ) (h : H),
    1 ≤ K → Orthonormal ℝ e → 0 < c → (∀ v, c * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2) →
      ∫ u, ⟪embed e K u, h⟫_ℝ ^ 2 ∂(naiveLaw L) ≤ ‖proj e K h‖ ^ 2 / (3 * c * K) ∧
        ‖proj e K h‖ ≤ ‖h‖

/-- Under `inf_K λ_min(M_K) ≥ c > 0`: `E⟨ι_K U^{(K)},h⟩² → 0`. -/
def naive_second_moment_tendsto : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H)
    (L : ∀ K : ℕ, EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (c : ℝ) (h : H),
    Orthonormal ℝ e → 0 < c → (∀ K v, c * ‖v‖ ^ 2 ≤ ‖L K v‖ ^ 2) →
      Tendsto (fun K => ∫ u, ⟪embed e K u, h⟫_ℝ ^ 2 ∂(naiveLaw (L K))) atTop (𝓝 0)

/-- Under `inf_K λ_min(M_K) ≥ c > 0`, the embedded laws converge to `δ₀` for the weak topology of `H`. -/
def naive_weak_tendsto : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (e : ℕ → H) (L : ∀ K : ℕ, EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K))
    (c : ℝ), Orthonormal ℝ e → 0 < c → (∀ K v, c * ‖v‖ ^ 2 ≤ ‖L K v‖ ^ 2) →
      ∀ f : H → ℝ, Continuous (fun y : WeakSpace ℝ H => f ((toWeakSpace ℝ H).symm y)) →
        (∃ B, ∀ x, |f x| ≤ B) →
          Tendsto (fun K => ∫ x, f x ∂(embLaw e (L K))) atTop (𝓝 (f 0))

/-- Under `sup_K λ_max(M_K) ≤ C`: `P(‖ι_K U^{(K)}‖ > a/√C) ≥ P(R > a) = 1 − a` for every `K ≥ 1`. -/
def naive_norm_mass : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (K : ℕ) (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (C a : ℝ),
    1 ≤ K → Orthonormal ℝ e → 0 < C → (∀ v, ‖L v‖ ^ 2 ≤ C * ‖v‖ ^ 2) → 0 < a → a < 1 →
      ENNReal.ofReal (1 - a) ≤ embLaw e L {x | a / Real.sqrt C < ‖x‖}

/-- Under `sup_K λ_max(M_K) ≤ C`, the embedded laws do not converge weakly to `δ₀` for the norm topology. -/
def naive_norm_no_weak : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (L : ∀ K : ℕ, EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (C : ℝ),
    Orthonormal ℝ e → 0 < C → (∀ K v, ‖L K v‖ ^ 2 ≤ C * ‖v‖ ^ 2) →
      ¬ ∀ f : H → ℝ, Continuous f → (∃ B, ∀ x, |f x| ≤ B) →
          Tendsto (fun K => ∫ x, f x ∂(embLaw e (L K))) atTop (𝓝 (f 0))

/-- `M_K = KI_K` (`L_K = √K I`): `‖ι_K U‖ = R/√K`. -/
def naive_KI_norm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : ℕ → H) (K : ℕ)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)),
    1 ≤ K → Orthonormal ℝ e → (∀ v, L v = Real.sqrt K • v) →
      ∀ (r : ℝ) (θ : EuclideanSpace ℝ (Fin K)), ‖θ‖ = 1 → ‖embed e K (L.symm (r • θ))‖ = |r| / Real.sqrt K

/-- `M_K = KI_K` satisfies `λ_min ≥ 1`, and the embedded laws converge to `δ₀` for the norm topology. -/
def naive_KI_converges : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (L : ∀ K : ℕ, EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)),
    Orthonormal ℝ e → (∀ K v, L K v = Real.sqrt K • v) →
      (∀ K, 1 ≤ K → ∀ v, 1 * ‖v‖ ^ 2 ≤ ‖L K v‖ ^ 2) ∧
      ∀ f : H → ℝ, Continuous f → (∃ B, ∀ x, |f x| ≤ B) →
        Tendsto (fun K => ∫ x, f x ∂(embLaw e (L K))) atTop (𝓝 (f 0))

/-! ### A `prop:emp-bijective-weak` -/

/-- Step 1: `σ̂` minimises the squared assignment cost iff it minimises `σ ↦ Σ_i D(u_{σ(i)}, r_i)`. -/
def bregman_assign : Prop :=
  ∀ (K n : ℕ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r u : Fin n → EuclideanSpace ℝ (Fin K))
    (σ : Equiv.Perm (Fin n)),
    IsOptAssign x u σ ↔
      ∀ τ : Equiv.Perm (Fin n), ∑ i, bregD f (x i) (r i) (u (σ i)) ≤ ∑ i, bregD f (x i) (r i) (u (τ i))

/-- The fixed-marginal expansion: for plans with equal marginals the `D`-cost and half the squared cost differ by
the same constant. -/
def bregman_plan : Prop :=
  ∀ (K n m : ℕ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) (a : Fin n → ℝ) (b : Fin m → ℝ) (π π' : Matrix (Fin n) (Fin m) ℝ),
    Matrix.HasMarginals π a b → Matrix.HasMarginals π' a b →
      ∑ i, ∑ j, π i j * bregD f (x i) (r i) (u j) - ∑ i, ∑ j, π' i j * bregD f (x i) (r i) (u j) =
        (∑ i, ∑ j, π i j * ‖x i - u j‖ ^ 2 - ∑ i, ∑ j, π' i j * ‖x i - u j‖ ^ 2) / 2

/-- Steps 1–2 for one realisation: `(α/2)·n⁻¹Σ‖u_{σ̂(i)} − r_i‖² ≤ (2n⁻¹Σ‖s_j‖² + 2n⁻¹Σ‖x_i‖²)^{1/2} W₂(ν̂_n, μ_{K,n})`,
written divided by `α/2`. -/
def bijective_core : Prop :=
  ∀ (K n : ℕ) (α : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r u s : Fin n → EuclideanSpace ℝ (Fin K))
    (σ : Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → SubgradAt f u s r → OneSidedAt α f u x r → IsOptAssign x u σ →
      ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) ≤
        ENNReal.ofReal (2 / α * Real.sqrt (2 * ((1 / n : ℝ) * ∑ j, ‖s j‖ ^ 2) +
            2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2))) *
          wassersteinEDist 2 (empMeasure r) (empMeasure u)

/-- `prop:emp-bijective-weak`: `E[n⁻¹Σ‖F̂(x_i) − F(x_i)‖²] ≤ (4/α)(β² + σ²)^{1/2}{E W₂²(ν̂_n, μ) + W₂²(μ_{K,n}, μ)}^{1/2}`. -/
def emp_bijective_weak : Prop :=
  ∀ (K n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K)) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (u s : Fin n → EuclideanSpace ℝ (Fin K)) (f : EuclideanSpace ℝ (Fin K) → ℝ) (α β : ℝ)
    (σ : Ω → Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → (∀ i, Measurable (x i)) → (∀ i, P.map (x i) = PK) →
    Integrable (fun z => ‖z‖ ^ 2) PK → (1 / n : ℝ) * ∑ j, ‖s j‖ ^ 2 ≤ β ^ 2 →
    (∀ᵐ ω ∂P, SubgradAt f u s (fun i => F (x i ω)) ∧
      OneSidedAt α f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsOptAssign (fun i => x i ω) u (σ ω)) →
      ∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖u (σ ω i) - F (x i ω)‖ ^ 2) ∂P ≤
        ENNReal.ofReal (4 / α * Real.sqrt (β ^ 2 + ∫ z, ‖z‖ ^ 2 ∂PK)) *
          (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
              wassersteinEDist 2 (empMeasure u) μ ^ 2) ^ (1 / 2 : ℝ)

/-! ### A `cor:app-entropic-weak` -/

/-- `eq:app-entropic-kl-bound`: every plan with uniform marginals has `KL(π‖a⊗b) ≤ log min(n,m)`. -/
def kl_le_log_min : Prop :=
  ∀ (n m : ℕ) (π : Matrix (Fin n) (Fin m) ℝ), 1 ≤ n → 1 ≤ m →
    π ∈ Matrix.transportPolytope (unifW n) (unifW m) →
      Matrix.relEntropy π (Matrix.vecMulVec (unifW n) (unifW m)) ≤ Real.log (min n m)

/-- The entropic bound for one realisation. -/
def entropic_core : Prop :=
  ∀ (K n m : ℕ) (α ε : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r : Fin n → EuclideanSpace ℝ (Fin K))
    (u s : Fin m → EuclideanSpace ℝ (Fin K)) (π : Matrix (Fin n) (Fin m) ℝ),
    1 ≤ n → 1 ≤ m → 0 < α → 0 < ε → SubgradAt f u s r → OneSidedAt α f u x r → IsEntPlan ε x u π →
      ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖entBary π u i - r i‖ ^ 2) ≤
        ENNReal.ofReal (2 / α * Real.sqrt (2 * ((1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2) +
            2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2))) *
          wassersteinEDist 2 (empMeasure r) (empMeasure u) +
        ENNReal.ofReal (ε / α * Real.log (min n m))

/-- `cor:app-entropic-weak`: `E[n⁻¹Σ‖F̂^{bar}(x_i) − F(x_i)‖²] ≤ (4/α)(β² + σ²)^{1/2}{E W₂²(ν̂_n, μ) +
W₂²(μ_{K,m}, μ)}^{1/2} + (ε/α) log min(n,m)`, every `n, m ≥ 1`, `ε > 0`. -/
def app_entropic_weak : Prop :=
  ∀ (K n m : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K)) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (u s : Fin m → EuclideanSpace ℝ (Fin K)) (f : EuclideanSpace ℝ (Fin K) → ℝ) (α β ε : ℝ)
    (π : Ω → Matrix (Fin n) (Fin m) ℝ),
    1 ≤ n → 1 ≤ m → 0 < α → 0 < ε → (∀ i, Measurable (x i)) → (∀ i, P.map (x i) = PK) →
    Integrable (fun z => ‖z‖ ^ 2) PK → (1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2 ≤ β ^ 2 →
    (∀ᵐ ω ∂P, SubgradAt f u s (fun i => F (x i ω)) ∧
      OneSidedAt α f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsEntPlan ε (fun i => x i ω) u (π ω)) →
      ∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖entBary (π ω) u i - F (x i ω)‖ ^ 2) ∂P ≤
        ENNReal.ofReal (4 / α * Real.sqrt (β ^ 2 + ∫ z, ‖z‖ ^ 2 ∂PK)) *
          (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
              wassersteinEDist 2 (empMeasure u) μ ^ 2) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (ε / α * Real.log (min n m))

end Claims

end StatFormal.OTFD.Wave8b
