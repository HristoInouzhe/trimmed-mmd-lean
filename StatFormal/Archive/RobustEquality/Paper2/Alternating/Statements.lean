import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.LocalExtr
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements

/-!
# FROZEN STATEMENTS — robust equality, companion paper (`paper2/`): `lem:delta-inf` and `thm:alternating`

**Draft** for critic review; on approval the human renames it `Statements.lean` and freezes it.

Sources (verbatim in `inventory/extracted/robust-equality-paper2.md`): `lem:delta-inf`
(`paper2/main.tex:296`, proof `app_proofs.tex:34`) and `thm:alternating` (`paper2/main.tex:478`, with
Algorithm `alg:alternating` and the definition of `J(w, γ)` just before it, proof `app_proofs.tex:153`).
`Deltafin` is imported from the frozen `Paper2/Seminorm/Statements.lean`, where it *defines* `Δ` by its
coupling form; `delta_inf_W2`/`delta_inf_linear` are the bridge to the Wasserstein distance (Tau Ceti's
`wassersteinEDist`) that the frozen seminorm statements left to this target.

Covered:
* `delta_inf_W2` — `lem:delta-inf`, first sentence, for finitely supported laws on any measurable space
  `K` and any measurable `h : K → ℝ`: the minimum of `E_γ{h(X) − h(Y)}²` over the transport polytope
  exists and `W₂(h#μ₀, h#μ₁) = √min`;
* `delta_inf_vertex` — the polytope has finitely many vertices (extreme points); a quantile coupling of
  any projections exists; every quantile coupling is a vertex and attains the minimum;
* `delta_inf_linear` — linear rules: `W₂(⟪w,·⟫#P̂₀, ⟪w,·⟫#P̂₁) = Δ(w)` (`Deltafin`), and every quantile
  coupling `γ` of the projections attains `min_γ wᵀM_γw = Δ(w)²`;
* `alternating` — `thm:alternating`, **corrected** (DEFECTS #16): attainment of the convex step is a
  hypothesis. For any exact minimisation oracle `step` of `J(·, γ)` and any quantile-coupling oracle `q`:
  `J = min over vertices of J(·, γ)`; the certificate is exact by sorting (`Δ(w) = |M_{q(w)}^{1/2}w|`);
  `J(w_k)` is nonincreasing; the algorithm stops at some `K` with `K + 1 ≤ #vertices`, the couplings
  `γ₀, …, γ_K` are distinct vertices; the returned pair `(w*, γ*) = (step γ_K, γ_K)` is a fixed point of
  the iteration; `w*` minimises the majorant `J(·, γ*)`, which lies above `J` everywhere and touches it
  at `w*`; the majorant is convex when `𝓡` is; and `w*` is a local minimiser of `J` when the projections
  `⟪w*, x⟫` are pairwise distinct on the support of each centre;
* `alternating_counterexample` — the literal hypotheses ("`𝓡` strictly convex and continuous, `η > 0`,
  finitely supported centres") do not give attainment: `𝓡 = exp` on `ℝ` (strictly convex, continuous,
  even `≥ 0`), `P̂₀ = P̂₁ = δ₀`, Wasserstein-ball seminorms at budget `r_s = 0` (`N_s = √r_s |·| = 0`,
  `thm:seminorm` (iv)(a); the floor of these sets is `0`, so the sets `{P̂_s}` are non-empty): for every
  `η > 0` and every coupling, `J(·, γ)` has no minimiser, so no pair `(w*, γ*)` as in the theorem exists
  and line 3 of the algorithm is undefined at `k = 0`;
* `alternating_attainment` — the repair on `ℝ^d` (finite dimension): attainment holds for every coupling
  if `𝓡` is continuous and coercive, or if `𝓡` is convex and continuous and `N₀ + N₁ ≥ c‖·‖`, `c > 0`
  (any Wasserstein/anisotropic model with positive budgets); seminorms bounded by `C‖·‖`
  (`thm:seminorm` (ii) gives `C = √r_s`).

Not covered (declared):
* `lem:delta-inf` for non-finitely supported laws (`μ₀, μ₁` arbitrary on `K`: needs disintegration);
* the paper's specific initialisation "`w₀` = the unpenalised rule": `w₀` is arbitrary here (the
  unpenalised minimiser of a strictly convex `𝓡` need not exist either — same gap, e.g. `exp`);
* uniqueness of the argmin (strict convexity): any exact minimiser is allowed, so strict convexity is
  not assumed in `alternating` (generalisation); continuity of `𝓡` is not needed there either;
* the connection `J = R + η inf_λ F̄` (`thm:seminorm` (iii), already certified, `seminorm_G`): `Jobj` is
  stated with arbitrary seminorms `N₀, N₁`; the reading "`N_s` comes from a model of the shift" is a
  specialisation of it;
* the empirical-sample reading of "the projections are pairwise distinct on the support": stated for the
  weighted representation, indices with positive weight (duplicate sample points must be merged into one
  weighted atom — WLOG, the centre is the same measure);
* the remark after the theorem (numerical experiments) and `(C_δ)`.

Encodings (see card):
* covariates in a real inner-product space `E` (generalises `ℝ^d`; finite dimension only in
  `alternating_attainment`); `h_w = ⟪w, ·⟫`;
* centres `P̂_s = Σ_i a^s_i δ_{x^s_i}` (`centre`), `a ≥ 0`, `Σ a = 1` (generalises empirical);
* the transport polytope `Π(P̂₀, P̂₁)` is `Plans` (same set as in `Deltafin`); its vertices are
  `Set.extremePoints ℝ (Plans a₀ a₁)`; "as many iterations as vertices" is `K + 1 ≤ ncard`, made
  non-junk by the `Finite` conjunct of `delta_inf_vertex`;
* `M_γ` is never formed: `wᵀM_γw = quad x₀ x₁ w γ = Σ γ_ij ⟪w, x⁰_i − x¹_j⟫²`, `|M_γ^{1/2}w| = √quad`;
* the quantile coupling "of the projections lifted to the covariates, ties broken arbitrarily" is
  `IsQuantileCoupling`: a plan which, in some ordering of the atoms by their projections, has no crossing
  pair of positive entries — this is the north-west-corner plan of that ordering (unique given the
  ordering, Tau Ceti `existsUnique_isMonotone`), i.e. `(F₀⁻¹(U), F₁⁻¹(U))` lifted;
* Algorithm `alg:alternating` is `run k = next^[k] (w₀, q w₀)` with oracles `step` (line 3,
  `argmin_w J(w, γ_k)`, specified by `IsMinOn`) and `q` (lines 1, 4); `next` is one pass of lines 3–5;
  `Stops k` is the failure of the test of line 5 at iteration `k`; after a stop `next` fixes the
  state, so the returned pair is `run (K + 1)`; `K + 1 ≤ ncard` itself forces `ncard > 0` (no
  `ncard = 0` junk for an infinite set);
* `J(w)` is `Jobj = 𝓡 + η (Δ + N₀ + N₁)²` (the objective of `(P_η)` for linear rules); the paper's
  definition `J = min_γ J(·, γ)` is the first conjunct of `alternating`;
* `W₂` is Tau Ceti's `wassersteinEDist 2` (`ℝ≥0∞`-valued; equality with `ENNReal.ofReal √min`, which
  is finite and non-junk since `min ≥ 0` is attained); `Measure.map h` with `h` measurable (no junk 0);
* every `min` is an `IsLeast`; `Deltafin` is non-junk (nonempty polytope, nonnegative summands).
Critic notes: DEFECTS #16 is real but narrow: it needs a degenerate penalty (some direction with
`N₀ + N₁ = 0` and `M_γ w = 0`, e.g. budgets at the floor) together with a non-coercive risk; least
squares with `Σ ≻ 0` (the paper's experiments, `prop:direction`) is coercive. The proof
(`app_proofs.tex:155-156`) already says "for a general strictly convex risk we assume the minimum is
attained"; the theorem statement omits it.
Critic note: DEFECTS #16 is an omission in the theorem statement (the proof, app_proofs.tex:155-156, assumes attainment
of the convex step; the statement drops it); the witness uses the legitimate floor budget `r_s = 0` and a non-coercive risk
(logistic risk on separable 1-D data fails the same way). `alternating` is the corrected theorem; `alternating_attainment`
gives sufficient conditions (coercive risk, or convex risk with `N₀ + N₁ ≥ c‖·‖`). `lem:delta-inf` justifies the coupling
form `Deltafin` of the frozen `Paper2/Seminorm` statements.
-/

noncomputable section
open Finset MeasureTheory TauCeti Filter
open scoped ENNReal

namespace StatFormal.RobustEquality.Paper2.Alternating

open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin)

/-! ### Definitions (verbatim copies of the route definitions, namespace `…Alternating.Route`) -/

section Defs

variable {n₀ n₁ : ℕ}

/-- The transport polytope `Π(P̂₀, P̂₁)` of two finitely supported centres with weights `a₀, a₁`. -/
def Plans (a₀ : Fin n₀ → ℝ) (a₁ : Fin n₁ → ℝ) : Set (Fin n₀ → Fin n₁ → ℝ) :=
  {γ | (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j}

/-- `E_γ {h(X) − h(Y)}²` for the projections `u_i = h(x⁰_i)`, `v_j = h(x¹_j)`. -/
def pcost (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  ∑ i, ∑ j, γ i j * (u i - v j) ^ 2

/-- In the order `σ₀, σ₁` of the atoms, the positive entries of `γ` do not cross. -/
def NoCross (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) (γ : Fin n₀ → Fin n₁ → ℝ) :
    Prop :=
  ∀ ⦃k₁ k₂ : Fin n₀⦄ ⦃l₁ l₂ : Fin n₁⦄, k₁ < k₂ → γ (σ₀ k₁) (σ₁ l₁) ≠ 0 →
    γ (σ₀ k₂) (σ₁ l₂) ≠ 0 → l₁ ≤ l₂

/-- `γ` is a quantile coupling of the projections `u, v` lifted to the atoms: a plan which, for some
ordering of the atoms by their projections (ties broken arbitrarily), is the north-west-corner
(non-crossing) plan of that order. -/
def IsQuantileCoupling (a₀ : Fin n₀ → ℝ) (a₁ : Fin n₁ → ℝ) (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ)
    (γ : Fin n₀ → Fin n₁ → ℝ) : Prop :=
  γ ∈ Plans a₀ a₁ ∧ ∃ (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)),
    Monotone (u ∘ σ₀) ∧ Monotone (v ∘ σ₁) ∧ NoCross σ₀ σ₁ γ

/-- The finitely supported law `Σ_i a_i δ_{x_i}`. -/
def centre {K : Type*} [MeasurableSpace K] {n : ℕ} (a : Fin n → ℝ) (x : Fin n → K) : Measure K :=
  ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Projections `⟪w, x_i⟫` of the atoms. -/
def proj {n : ℕ} (x : Fin n → E) (w : E) : Fin n → ℝ := fun i => inner ℝ w (x i)

/-- `wᵀ M_γ w = Σ γ_ij ⟪w, x⁰_i − x¹_j⟫²`. -/
def quad (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  ∑ i, ∑ j, γ i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2

/-- The convex majorant `J(w, γ) = 𝓡(w) + η (|M_γ^{1/2} w| + N₀(w) + N₁(w))²`. -/
def Jcpl (R : E → ℝ) (η : ℝ) (N₀ N₁ : Seminorm ℝ E) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E)
    (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  R w + η * (√(quad x₀ x₁ w γ) + N₀ w + N₁ w) ^ 2

/-- The objective of `(P_η)` for a linear rule, `J(w) = 𝓡(w) + η G(w)²`, `G = Δ + N₀ + N₁`. -/
def Jobj (R : E → ℝ) (η : ℝ) (N₀ N₁ : Seminorm ℝ E) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E) : ℝ :=
  R w + η * (Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w) ^ 2

/-- One pass of the loop of `alg:alternating` (lines 3–5) on the state `s = (w_k, γ_k)`:
`w_{k+1} = step γ_k`, `γ' = q(w_{k+1})`, and `γ_{k+1} = γ'` if `w_{k+1}ᵀM_{γ'}w_{k+1} <
w_{k+1}ᵀM_{γ_k}w_{k+1}`, else `γ_k` (the algorithm returns; the state is then a fixed point). -/
def next (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (step : (Fin n₀ → Fin n₁ → ℝ) → E)
    (q : E → Fin n₀ → Fin n₁ → ℝ) (s : E × (Fin n₀ → Fin n₁ → ℝ)) : E × (Fin n₀ → Fin n₁ → ℝ) :=
  (step s.2, if quad x₀ x₁ (step s.2) (q (step s.2)) < quad x₀ x₁ (step s.2) s.2
    then q (step s.2) else s.2)

/-- Algorithm `alg:alternating`, run with a minimisation oracle `step` for the convex step and a
coupling oracle `q`, from `(w₀, q w₀)`; `run k = (w_k, γ_k)`. -/
def run (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (step : (Fin n₀ → Fin n₁ → ℝ) → E)
    (q : E → Fin n₀ → Fin n₁ → ℝ) (w₀ : E) (k : ℕ) : E × (Fin n₀ → Fin n₁ → ℝ) :=
  (next x₀ x₁ step q)^[k] (w₀, q w₀)

/-- The test of `alg:alternating` fails at iteration `k`: the algorithm returns
`(w_{k+1}, γ_k) = (step γ_k, γ_k)`. -/
def Stops (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (step : (Fin n₀ → Fin n₁ → ℝ) → E)
    (q : E → Fin n₀ → Fin n₁ → ℝ) (w₀ : E) (k : ℕ) : Prop :=
  ¬ quad x₀ x₁ (step (run x₀ x₁ step q w₀ k).2) (q (step (run x₀ x₁ step q w₀ k).2)) <
      quad x₀ x₁ (step (run x₀ x₁ step q w₀ k).2) (run x₀ x₁ step q w₀ k).2

end Defs

namespace Claims

/-- `lem:delta-inf`, first sentence, finitely supported centres, any measurable rule. -/
def delta_inf_W2 : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → K) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → K) (h : K → ℝ),
    Measurable h → (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      (∃ c, IsLeast (pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) '' Plans a₀ a₁) c) ∧
      ∀ c, IsLeast (pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) '' Plans a₀ a₁) c →
        wassersteinEDist 2 ((centre a₀ x₀).map h) ((centre a₁ x₁).map h) =
          ENNReal.ofReal (√c)

/-- `lem:delta-inf`, vertex part: finitely many vertices; quantile couplings exist, are vertices and
are optimal. -/
def delta_inf_vertex : Prop :=
  ∀ (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (a₁ : Fin n₁ → ℝ) (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      (Set.extremePoints ℝ (Plans a₀ a₁)).Finite ∧
      (∃ γ, IsQuantileCoupling a₀ a₁ u v γ) ∧
      ∀ γ, IsQuantileCoupling a₀ a₁ u v γ →
        γ ∈ Set.extremePoints ℝ (Plans a₀ a₁) ∧ IsLeast (pcost u v '' Plans a₀ a₁) (pcost u v γ)

/-- `lem:delta-inf` for linear rules: `W₂(⟪w,·⟫#P̂₀, ⟪w,·⟫#P̂₁) = Δ(w)`, and `Δ(w)² = min_γ wᵀM_γw`
is attained at every quantile coupling of the projections. -/
def delta_inf_linear : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      wassersteinEDist 2 ((centre a₀ x₀).map (fun x => inner ℝ w x))
          ((centre a₁ x₁).map (fun x => inner ℝ w x)) =
        ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) ∧
      ∀ γ, IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) γ →
        IsLeast ((fun g => quad x₀ x₁ w g) '' Plans a₀ a₁) (quad x₀ x₁ w γ) ∧
        Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w γ)

/-- `thm:alternating`, corrected: attainment of the convex step is a hypothesis (an exact
minimisation oracle `step`); the coupling oracle `q` returns a quantile coupling of the projections. -/
def alternating : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (R : E → ℝ) (η : ℝ) (N₀ N₁ : Seminorm ℝ E) (w₀ : E)
    (step : (Fin n₀ → Fin n₁ → ℝ) → E) (q : E → Fin n₀ → Fin n₁ → ℝ),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 → 0 < η →
    (∀ γ ∈ Plans a₀ a₁, IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) Set.univ (step γ)) →
    (∀ w, IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) (q w)) →
      (∀ w, IsLeast ((fun γ => Jcpl R η N₀ N₁ x₀ x₁ w γ) '' Set.extremePoints ℝ (Plans a₀ a₁))
        (Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w)) ∧
      (∀ w, Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w (q w))) ∧
      Antitone (fun k => Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (run x₀ x₁ step q w₀ k).1) ∧
      ∃ K : ℕ, K + 1 ≤ (Set.extremePoints ℝ (Plans a₀ a₁)).ncard ∧
        Stops x₀ x₁ step q w₀ K ∧ (∀ k < K, ¬ Stops x₀ x₁ step q w₀ k) ∧
        Set.InjOn (fun k => (run x₀ x₁ step q w₀ k).2) (Set.Iic K) ∧
        (∀ k ≤ K, (run x₀ x₁ step q w₀ k).2 ∈ Set.extremePoints ℝ (Plans a₀ a₁)) ∧
        run x₀ x₁ step q w₀ (K + 1) =
          (step (run x₀ x₁ step q w₀ K).2, (run x₀ x₁ step q w₀ K).2) ∧
        IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w (run x₀ x₁ step q w₀ K).2) Set.univ
          (step (run x₀ x₁ step q w₀ K).2) ∧
        (∀ w, Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w ≤ Jcpl R η N₀ N₁ x₀ x₁ w (run x₀ x₁ step q w₀ K).2) ∧
        Jcpl R η N₀ N₁ x₀ x₁ (step (run x₀ x₁ step q w₀ K).2) (run x₀ x₁ step q w₀ K).2 =
          Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (run x₀ x₁ step q w₀ K).2) ∧
        (ConvexOn ℝ Set.univ R →
          ConvexOn ℝ Set.univ (fun w => Jcpl R η N₀ N₁ x₀ x₁ w (run x₀ x₁ step q w₀ K).2)) ∧
        ((∀ i k, i ≠ k → 0 < a₀ i → 0 < a₀ k →
            inner ℝ (step (run x₀ x₁ step q w₀ K).2) (x₀ i) ≠
              inner ℝ (step (run x₀ x₁ step q w₀ K).2) (x₀ k)) →
          (∀ j l, j ≠ l → 0 < a₁ j → 0 < a₁ l →
            inner ℝ (step (run x₀ x₁ step q w₀ K).2) (x₁ j) ≠
              inner ℝ (step (run x₀ x₁ step q w₀ K).2) (x₁ l)) →
          IsLocalMin (Jobj R η N₀ N₁ a₀ x₀ a₁ x₁) (step (run x₀ x₁ step q w₀ K).2))

/-- DEFECTS #16: under the paper's hypotheses the convex step need not have a minimiser
(`𝓡 = exp`, `P̂₀ = P̂₁ = δ₀` on `ℝ`, `N₀ = N₁ = 0`, i.e. Wasserstein balls at budget `0`). -/
def alternating_counterexample : Prop :=
  ∃ R : ℝ → ℝ, StrictConvexOn ℝ Set.univ R ∧ Continuous R ∧ (∀ w, 0 ≤ R w) ∧
    ∀ η : ℝ, 0 < η →
      ∀ γ ∈ Plans (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)),
        ¬ ∃ w : ℝ, IsMinOn (fun w => Jcpl R η 0 0 (fun _ : Fin 1 => (0 : ℝ))
          (fun _ : Fin 1 => (0 : ℝ)) w γ) Set.univ w

/-- The repair: sufficient conditions for the attainment hypothesis of `alternating` in finite
dimension (coercive continuous risk, or convex continuous risk with `N₀ + N₁ ≥ c‖·‖`, `c > 0`). -/
def alternating_attainment : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (R : E → ℝ) (η C : ℝ) (N₀ N₁ : Seminorm ℝ E),
    Continuous R → 0 < η → (∀ w, N₀ w ≤ C * ‖w‖) → (∀ w, N₁ w ≤ C * ‖w‖) →
    (Tendsto R (cocompact E) atTop ∨
      (ConvexOn ℝ Set.univ R ∧ ∃ c > 0, ∀ w, c * ‖w‖ ≤ N₀ w + N₁ w)) →
      ∀ γ ∈ Plans a₀ a₁, ∃ w, IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) Set.univ w

end Claims
end StatFormal.RobustEquality.Paper2.Alternating
