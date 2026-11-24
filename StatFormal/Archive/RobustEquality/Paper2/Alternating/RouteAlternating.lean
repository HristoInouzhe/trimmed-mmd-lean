import StatFormal.Archive.RobustEquality.Paper2.Alternating.RouteW2
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Order.Compact

/-!
# Route: paper 2 `thm:alternating` (finite termination at a local minimiser) and `lem:delta-inf`
for linear rules

* `delta_inf_W2`, `delta_inf_vertex`, `delta_inf_linear` — `lem:delta-inf` for finitely supported
  centres (any measurable rule; vertices and the quantile coupling; linear rules and `Deltafin`);
* `alternating` — the corrected `thm:alternating`: for *any* exact minimisation oracle of the convex
  step (attainment is a hypothesis) and the quantile coupling oracle, the alternation has
  nonincreasing objective, never revisits a coupling, stops within `#vertices` iterations at a pair
  whose convex majorant touches `J` and is minimised there, and the stopping point is a local
  minimiser of `J` when the projections are distinct on the supports;
* `alternating_counterexample` — DEFECTS #16: with `𝓡 = exp` (strictly convex, continuous, `≥ 0`),
  `η > 0`, `P̂₀ = P̂₁ = δ₀` on `ℝ` and the Wasserstein-ball seminorms at budget `r_s = 0`
  (`N_s = √r_s |·| = 0`), no coupling has a minimiser of the convex step;
* `alternating_attainment` — sufficient conditions for the attainment hypothesis on `ℝ^d`
  (finite dimension): a coercive continuous risk, or a convex continuous risk with
  `N₀ + N₁ ≥ c‖·‖`, `c > 0`.
-/

noncomputable section
open Finset MeasureTheory TauCeti Filter Topology
open scoped ENNReal

namespace StatFormal.RobustEquality.Paper2.Alternating.Route

open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin)

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}

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

/-! ### Basic facts -/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}
variable {a₀ : Fin n₀ → ℝ} {x₀ : Fin n₀ → E} {a₁ : Fin n₁ → ℝ} {x₁ : Fin n₁ → E}

lemma quad_eq_pcost (w : E) (γ : Fin n₀ → Fin n₁ → ℝ) :
    quad x₀ x₁ w γ = pcost (proj x₀ w) (proj x₁ w) γ := by
  simp [quad, pcost, proj, inner_sub_right]

lemma quad_nonneg (w : E) {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : ∀ i j, 0 ≤ γ i j) :
    0 ≤ quad x₀ x₁ w γ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hγ i j) (sq_nonneg _)

lemma continuous_quad (γ : Fin n₀ → Fin n₁ → ℝ) : Continuous fun w : E => quad x₀ x₁ w γ := by
  unfold quad
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_id.inner continuous_const).pow 2)

lemma Deltafin_le (w : E) {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) :
    Deltafin a₀ x₀ a₁ x₁ w ≤ √(quad x₀ x₁ w γ) := by
  unfold Deltafin
  refine Real.sqrt_le_sqrt ?_
  refine ciInf_le ⟨0, ?_⟩ (⟨γ, hγ⟩ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧
      (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j})
  rintro _ ⟨g, rfl⟩
  exact quad_nonneg (x₀ := x₀) (x₁ := x₁) w g.2.1

lemma Deltafin_eq (w : E) {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁)
    (hopt : ∀ g ∈ Plans a₀ a₁, quad x₀ x₁ w γ ≤ quad x₀ x₁ w g) :
    Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w γ) := by
  refine le_antisymm (Deltafin_le w hγ) ?_
  unfold Deltafin
  refine Real.sqrt_le_sqrt ?_
  haveI : Nonempty {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧
      (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j} := ⟨⟨γ, hγ⟩⟩
  exact le_ciInf fun g => hopt g.1 g.2

variable {R : E → ℝ} {η : ℝ} {N₀ N₁ : Seminorm ℝ E}

lemma Jobj_le_Jcpl (hη : 0 ≤ η) (w : E) {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) :
    Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w ≤ Jcpl R η N₀ N₁ x₀ x₁ w γ := by
  unfold Jobj Jcpl
  have h0 : 0 ≤ Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w := by
    have := Real.sqrt_nonneg (⨅ γ : {γ : Fin n₀ → Fin n₁ → ℝ | (∀ i j, 0 ≤ γ i j) ∧
      (∀ i, ∑ j, γ i j = a₀ i) ∧ ∀ j, ∑ i, γ i j = a₁ j},
      ∑ i, ∑ j, (γ : Fin n₀ → Fin n₁ → ℝ) i j * (inner ℝ w (x₀ i - x₁ j)) ^ 2)
    have h1 := apply_nonneg N₀ w
    have h2 := apply_nonneg N₁ w
    unfold Deltafin; linarith
  have := pow_le_pow_left₀ h0 (by linarith [Deltafin_le (x₀ := x₀) (x₁ := x₁) w hγ] :
    Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w ≤ √(quad x₀ x₁ w γ) + N₀ w + N₁ w) 2
  nlinarith

lemma Jcpl_lt (hη : 0 < η) (w : E) {γ γ' : Fin n₀ → Fin n₁ → ℝ} (hγ' : ∀ i j, 0 ≤ γ' i j)
    (hlt : quad x₀ x₁ w γ' < quad x₀ x₁ w γ) :
    Jcpl R η N₀ N₁ x₀ x₁ w γ' < Jcpl R η N₀ N₁ x₀ x₁ w γ := by
  unfold Jcpl
  have hs := Real.sqrt_lt_sqrt (quad_nonneg w hγ') hlt
  have h0 : 0 ≤ √(quad x₀ x₁ w γ') + N₀ w + N₁ w := by
    have := Real.sqrt_nonneg (quad x₀ x₁ w γ')
    linarith [apply_nonneg N₀ w, apply_nonneg N₁ w]
  have := pow_lt_pow_left₀ (by linarith : √(quad x₀ x₁ w γ') + N₀ w + N₁ w <
    √(quad x₀ x₁ w γ) + N₀ w + N₁ w) h0 (two_ne_zero)
  nlinarith

/-- The convex majorant is convex when `𝓡` is. -/
lemma Jcpl_convex (hη : 0 ≤ η) (hR : ConvexOn ℝ Set.univ R) {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : ∀ i j, 0 ≤ γ i j) : ConvexOn ℝ Set.univ (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) := by
  let V : E → EuclideanSpace ℝ (Fin n₀ × Fin n₁) := fun w =>
    WithLp.toLp 2 (fun q : Fin n₀ × Fin n₁ => √(γ q.1 q.2) * inner ℝ w (x₀ q.1 - x₁ q.2))
  have hV : ∀ w, √(quad x₀ x₁ w γ) = ‖V w‖ := by
    intro w
    rw [EuclideanSpace.norm_eq, quad, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [V, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (hγ i j)]
  have hg : ConvexOn ℝ Set.univ (fun w => √(quad x₀ x₁ w γ)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    simp only [hV, smul_eq_mul]
    have hlin : V (a • x + b • y) = a • V x + b • V y := by
      ext q
      simp only [V, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        inner_add_left, inner_smul_left, RCLike.conj_to_real]
      ring
    rw [hlin]
    calc ‖a • V x + b • V y‖ ≤ ‖a • V x‖ + ‖b • V y‖ := norm_add_le _ _
      _ = a * ‖V x‖ + b * ‖V y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hsum : ConvexOn ℝ Set.univ (fun w => √(quad x₀ x₁ w γ) + N₀ w + N₁ w) :=
    (hg.add (N₀.convexOn)).add N₁.convexOn
  have hsq := hsum.pow (fun w _ => by
    have := Real.sqrt_nonneg (quad x₀ x₁ w γ)
    linarith [apply_nonneg N₀ w, apply_nonneg N₁ w]) 2
  exact hR.add (hsq.smul hη)

end Basic

/-! ### `lem:delta-inf` for linear rules -/

section DeltaLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}
variable {a₀ : Fin n₀ → ℝ} {x₀ : Fin n₀ → E} {a₁ : Fin n₁ → ℝ} {x₁ : Fin n₁ → E}
variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

include h00 h01 h10 h11 in
lemma quantile_quad_optimal {w : E} {γ : Fin n₀ → Fin n₁ → ℝ}
    (hq : IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) γ) :
    ∀ g ∈ Plans a₀ a₁, quad x₀ x₁ w γ ≤ quad x₀ x₁ w g := by
  intro g hg
  rw [quad_eq_pcost, quad_eq_pcost]
  exact quantile_optimal h00 h01 h10 h11 hq g hg

include h00 h01 h10 h11 in
lemma Deltafin_quantile {w : E} {γ : Fin n₀ → Fin n₁ → ℝ}
    (hq : IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) γ) :
    Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w γ) :=
  Deltafin_eq w hq.1 (quantile_quad_optimal h00 h01 h10 h11 hq)

end DeltaLinear

/-! ### The alternation -/

section Alt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}
variable {a₀ : Fin n₀ → ℝ} {x₀ : Fin n₀ → E} {a₁ : Fin n₁ → ℝ} {x₁ : Fin n₁ → E}
variable {R : E → ℝ} {η : ℝ} {N₀ N₁ : Seminorm ℝ E} {w₀ : E}
  {step : (Fin n₀ → Fin n₁ → ℝ) → E} {q : E → Fin n₀ → Fin n₁ → ℝ}

lemma run_succ (k : ℕ) :
    run x₀ x₁ step q w₀ (k + 1) = next x₀ x₁ step q (run x₀ x₁ step q w₀ k) :=
  Function.iterate_succ_apply' _ _ _

lemma run_fst_succ (k : ℕ) :
    (run x₀ x₁ step q w₀ (k + 1)).1 = step (run x₀ x₁ step q w₀ k).2 := by
  rw [run_succ]; rfl

lemma run_stop {k : ℕ} (h : Stops x₀ x₁ step q w₀ k) :
    (run x₀ x₁ step q w₀ (k + 1)).2 = (run x₀ x₁ step q w₀ k).2 := by
  rw [run_succ]; exact if_neg h

lemma run_go {k : ℕ} (h : ¬ Stops x₀ x₁ step q w₀ k) :
    (run x₀ x₁ step q w₀ (k + 1)).2 = q (step (run x₀ x₁ step q w₀ k).2) := by
  rw [run_succ]; exact if_pos (not_not.1 h)

lemma run_range (k : ℕ) : ∃ w, (run x₀ x₁ step q w₀ k).2 = q w := by
  induction k with
  | zero => exact ⟨w₀, rfl⟩
  | succ k ih =>
    by_cases h : Stops x₀ x₁ step q w₀ k
    · rw [run_stop h]; exact ih
    · rw [run_go h]; exact ⟨_, rfl⟩

variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

include h00 h01 h10 h11 in
theorem alternating_main (hη : 0 < η)
    (hstep : ∀ γ ∈ Plans a₀ a₁, IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) Set.univ (step γ))
    (hq : ∀ w, IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) (q w)) :
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
        IsLocalMin (Jobj R η N₀ N₁ a₀ x₀ a₁ x₁) (step (run x₀ x₁ step q w₀ K).2)) := by
  classical
  set γs : ℕ → Fin n₀ → Fin n₁ → ℝ := fun k => (run x₀ x₁ step q w₀ k).2 with hγs
  set Ext := Set.extremePoints ℝ (Plans a₀ a₁) with hExt
  have hopt : ∀ w, ∀ g ∈ Plans a₀ a₁, quad x₀ x₁ w (q w) ≤ quad x₀ x₁ w g := fun w =>
    quantile_quad_optimal h00 h01 h10 h11 (hq w)
  have hD : ∀ w, Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w (q w)) := fun w =>
    Deltafin_quantile h00 h01 h10 h11 (hq w)
  have hJq : ∀ w, Jcpl R η N₀ N₁ x₀ x₁ w (q w) = Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w := by
    intro w; unfold Jcpl Jobj; rw [hD w]
  have hle : ∀ w, ∀ g ∈ Plans a₀ a₁,
      Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w ≤ Jcpl R η N₀ N₁ x₀ x₁ w g := fun w g hg =>
    Jobj_le_Jcpl hη.le w hg
  have hqext : ∀ w, q w ∈ Ext := fun w => quantile_extreme h00 h01 h10 h11 (hq w)
  have hext : ∀ k, γs k ∈ Ext := by
    intro k; obtain ⟨w, hw⟩ := run_range (x₀ := x₀) (x₁ := x₁) (step := step) (w₀ := w₀) k
    simp only [hγs]; rw [hw]; exact hqext w
  have hPl : ∀ k, γs k ∈ Plans a₀ a₁ := fun k => (hext k).1
  have hmin : ∀ g ∈ Plans a₀ a₁, ∀ w,
      Jcpl R η N₀ N₁ x₀ x₁ (step g) g ≤ Jcpl R η N₀ N₁ x₀ x₁ w g := fun g hg w =>
    isMinOn_iff.1 (hstep g hg) w (Set.mem_univ w)
  -- the value of a coupling
  set v : (Fin n₀ → Fin n₁ → ℝ) → ℝ := fun g => Jcpl R η N₀ N₁ x₀ x₁ (step g) g with hv
  have hdec : ∀ k, ¬ Stops x₀ x₁ step q w₀ k → v (γs (k + 1)) < v (γs k) := by
    intro k hk
    have hgo := run_go hk
    simp only [hv]
    rw [show γs (k + 1) = q (step (γs k)) from hgo]
    calc Jcpl R η N₀ N₁ x₀ x₁ (step (q (step (γs k)))) (q (step (γs k)))
        ≤ Jcpl R η N₀ N₁ x₀ x₁ (step (γs k)) (q (step (γs k))) :=
          hmin _ (hqext _).1 _
      _ < Jcpl R η N₀ N₁ x₀ x₁ (step (γs k)) (γs k) :=
          Jcpl_lt hη _ (hqext _).1.1 (not_not.1 hk)
  have hchain : ∀ M, (∀ k < M, ¬ Stops x₀ x₁ step q w₀ k) →
      ∀ d i, i + d + 1 ≤ M → v (γs (i + d + 1)) < v (γs i) := by
    intro M hM d
    induction d with
    | zero => intro i hi; exact hdec i (hM i (by omega))
    | succ d ih =>
      intro i hi
      have h1 := hdec (i + d + 1) (hM _ (by omega))
      have h2 := ih i (by omega)
      have : i + (d + 1) + 1 = i + d + 1 + 1 := by omega
      rw [this]; linarith
  have hinj : ∀ M, (∀ k < M, ¬ Stops x₀ x₁ step q w₀ k) → Set.InjOn γs (Set.Iic M) := by
    intro M hM i hi j hj hij
    simp only [Set.mem_Iic] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · have := hchain M hM (j - i - 1) i (by omega)
      rw [show i + (j - i - 1) + 1 = j by omega, hij] at this
      exact absurd this (lt_irrefl _)
    · exact h
    · have := hchain M hM (i - j - 1) j (by omega)
      rw [show j + (i - j - 1) + 1 = i by omega, hij] at this
      exact absurd this (lt_irrefl _)
  have hfin : Ext.Finite := extreme_finite
  have hcard : ∀ M, (∀ k < M, ¬ Stops x₀ x₁ step q w₀ k) → M + 1 ≤ Ext.ncard := by
    intro M hM
    have := Set.ncard_le_ncard_of_injOn γs (fun k _ => hext k) (hinj M hM) hfin
    rwa [Set.ncard_Iic_nat] at this
  have hex : ∃ k, Stops x₀ x₁ step q w₀ k := by
    by_contra hno
    push_neg at hno
    have := hcard Ext.ncard (fun k _ => hno k)
    omega
  set K := Nat.find hex with hK
  have hKs : Stops x₀ x₁ step q w₀ K := Nat.find_spec hex
  have hKmin : ∀ k < K, ¬ Stops x₀ x₁ step q w₀ k := fun k hk => Nat.find_min hex hk
  set ws := step (γs K) with hws
  have hstopK := run_stop hKs
  -- the majorant touches `J` at the stopping point
  have htouchq : quad x₀ x₁ ws (γs K) = quad x₀ x₁ ws (q ws) :=
    le_antisymm (not_lt.1 hKs) (hopt ws _ (hPl K))
  have htouch : Jcpl R η N₀ N₁ x₀ x₁ ws (γs K) = Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ ws := by
    rw [← hJq ws]; unfold Jcpl; rw [htouchq]
  refine ⟨?_, hD, ?_, K, hcard K hKmin, hKs, hKmin, hinj K hKmin, fun k _ => hext k, ?_,
    hstep _ (hPl K), fun w => hle w _ (hPl K), htouch,
    fun hR => Jcpl_convex hη.le hR (hPl K).1, ?_⟩
  · -- `J(w) = min over vertices of J(w, γ)`
    intro w
    refine ⟨⟨q w, hqext w, hJq w⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hle w g hg.1
  · -- nonincreasing objective
    refine antitone_nat_of_succ_le fun k => ?_
    rw [run_fst_succ]
    cases k with
    | zero =>
      calc Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (γs 0))
          ≤ Jcpl R η N₀ N₁ x₀ x₁ (step (γs 0)) (γs 0) := hle _ _ (hPl 0)
        _ ≤ Jcpl R η N₀ N₁ x₀ x₁ w₀ (γs 0) := hmin _ (hPl 0) w₀
        _ = Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w₀ := hJq w₀
    | succ k =>
      rw [run_fst_succ]
      show Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (γs (k + 1))) ≤
        Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (γs k))
      by_cases hk : Stops x₀ x₁ step q w₀ k
      · have : γs (k + 1) = γs k := run_stop hk
        rw [this]
      · have hgo : γs (k + 1) = q (step (γs k)) := run_go hk
        calc Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (γs (k + 1)))
            ≤ Jcpl R η N₀ N₁ x₀ x₁ (step (γs (k + 1))) (γs (k + 1)) := hle _ _ (hPl _)
          _ ≤ Jcpl R η N₀ N₁ x₀ x₁ (step (γs k)) (γs (k + 1)) := hmin _ (hPl _) _
          _ = Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ (step (γs k)) := by rw [hgo]; exact hJq _
  · -- the returned pair is a fixed point
    exact Prod.ext (run_fst_succ K) hstopK
  · -- local minimality under distinct projections
    intro hu hv'
    have hgs_opt : ∀ g ∈ Plans a₀ a₁, quad x₀ x₁ ws (γs K) ≤ quad x₀ x₁ ws g := by
      intro g hg; rw [htouchq]; exact hopt ws g hg
    have huniq : ∀ g ∈ Plans a₀ a₁, quad x₀ x₁ ws g = quad x₀ x₁ ws (γs K) → g = γs K := by
      intro g hg heq
      refine optimal_unique h00 h01 h10 h11 (u := proj x₀ ws) (v := proj x₁ ws) hg ?_ (hPl K) ?_
        hu hv'
      · intro g' hg'; rw [← quad_eq_pcost, ← quad_eq_pcost, heq]; exact hgs_opt g' hg'
      · intro g' hg'; rw [← quad_eq_pcost, ← quad_eq_pcost]; exact hgs_opt g' hg'
    have hstrict : ∀ g ∈ Ext \ {γs K}, ∀ᶠ w in 𝓝 ws, quad x₀ x₁ w (γs K) < quad x₀ x₁ w g := by
      rintro g ⟨hge, hne⟩
      have hgt : quad x₀ x₁ ws (γs K) < quad x₀ x₁ ws g := by
        refine lt_of_le_of_ne (hgs_opt g hge.1) ?_
        intro heq; exact hne (huniq g hge.1 heq.symm)
      exact (continuous_quad _).continuousAt.eventually_lt (continuous_quad _).continuousAt hgt
    have hall := (Filter.eventually_all_finite (hfin.sdiff)).2 hstrict
    filter_upwards [hall] with w hw
    have hqw : q w = γs K := by
      by_contra hne
      have h1 := hw (q w) ⟨hqext w, hne⟩
      have h2 := hopt w (γs K) (hPl K)
      linarith
    calc Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ ws = Jcpl R η N₀ N₁ x₀ x₁ ws (γs K) := htouch.symm
      _ ≤ Jcpl R η N₀ N₁ x₀ x₁ w (γs K) := hmin _ (hPl K) w
      _ = Jcpl R η N₀ N₁ x₀ x₁ w (q w) := by rw [hqw]
      _ = Jobj R η N₀ N₁ a₀ x₀ a₁ x₁ w := hJq w

end Alt

/-! ### Attainment of the convex step -/

section Attain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n₀ n₁ : ℕ}
variable {x₀ : Fin n₀ → E} {x₁ : Fin n₁ → E}

lemma seminorm_continuous_of_le (N : Seminorm ℝ E) {C : ℝ} (hC : ∀ w, N w ≤ C * ‖w‖) :
    Continuous N := by
  refine (LipschitzWith.of_dist_le_mul (K := C.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  calc |N x - N y| ≤ N (x - y) := abs_sub_map_le_sub N x y
    _ ≤ C * ‖x - y‖ := hC _
    _ ≤ (C.toNNReal : ℝ) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

theorem attainment_main [FiniteDimensional ℝ E] {R : E → ℝ} {η C : ℝ} {N₀ N₁ : Seminorm ℝ E}
    (hRc : Continuous R) (hη : 0 < η) (hC₀ : ∀ w, N₀ w ≤ C * ‖w‖) (hC₁ : ∀ w, N₁ w ≤ C * ‖w‖)
    (hcase : Tendsto R (cocompact E) atTop ∨
      (ConvexOn ℝ Set.univ R ∧ ∃ c > 0, ∀ w, c * ‖w‖ ≤ N₀ w + N₁ w))
    (γ : Fin n₀ → Fin n₁ → ℝ) :
    ∃ w, IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) Set.univ w := by
  set f : E → ℝ := fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ with hf
  have hN₀ := seminorm_continuous_of_le N₀ hC₀
  have hN₁ := seminorm_continuous_of_le N₁ hC₁
  have hcont : Continuous f := by
    simp only [hf, Jcpl]
    exact hRc.add (continuous_const.mul
      ((((Real.continuous_sqrt.comp (continuous_quad γ)).add hN₀).add hN₁).pow 2))
  have hpen : ∀ w, 0 ≤ √(quad x₀ x₁ w γ) + N₀ w + N₁ w := fun w => by
    have := Real.sqrt_nonneg (quad x₀ x₁ w γ)
    linarith [apply_nonneg N₀ w, apply_nonneg N₁ w]
  have hRf : ∀ w, R w ≤ f w := fun w => by
    simp only [hf, Jcpl]
    have := mul_nonneg hη.le (sq_nonneg (√(quad x₀ x₁ w γ) + N₀ w + N₁ w))
    linarith
  have htend : Tendsto f (cocompact E) atTop := by
    rcases hcase with hcoer | ⟨hconv, c, hc, hcN⟩
    · exact tendsto_atTop_mono hRf hcoer
    · obtain ⟨m, hm⟩ := ((isCompact_sphere (0 : E) 1).image_of_continuousOn
        hRc.continuousOn).bddBelow
      set Kc := max 0 (R 0 - m) with hKc
      have hlow : ∀ w : E, 1 ≤ ‖w‖ → R 0 - Kc * ‖w‖ ≤ R w := by
        intro w hw
        set t := ‖w‖ with ht
        have htpos : 0 < t := by linarith
        have hu : t⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ htpos.ne']
        have hmu : m ≤ R (t⁻¹ • w) := hm ⟨_, hu, rfl⟩
        have ha : (0 : ℝ) ≤ 1 - t⁻¹ := by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hw
        have hconv' := hconv.2 (Set.mem_univ (0 : E)) (Set.mem_univ w) ha
          (inv_nonneg.2 htpos.le) (by ring)
        rw [smul_zero, zero_add, smul_eq_mul, smul_eq_mul] at hconv'
        have h1 : t * R (t⁻¹ • w) ≤ (t - 1) * R 0 + R w := by
          have := mul_le_mul_of_nonneg_left hconv' htpos.le
          have e : t * ((1 - t⁻¹) * R 0 + t⁻¹ * R w) = (t - 1) * R 0 + R w := by
            field_simp
          linarith
        have hK1 : 0 ≤ Kc := le_max_left _ _
        have hK2 : R 0 - m ≤ Kc := le_max_right _ _
        nlinarith
      have hfge : ∀ w : E, 1 ≤ ‖w‖ → R 0 - Kc * ‖w‖ + η * c ^ 2 * ‖w‖ ^ 2 ≤ f w := by
        intro w hw
        have h1 := hlow w hw
        have h2 : c * ‖w‖ ≤ √(quad x₀ x₁ w γ) + N₀ w + N₁ w := by
          have := Real.sqrt_nonneg (quad x₀ x₁ w γ)
          linarith [hcN w]
        have h3 : (c * ‖w‖) ^ 2 ≤ (√(quad x₀ x₁ w γ) + N₀ w + N₁ w) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
        simp only [hf, Jcpl]
        nlinarith
      rw [tendsto_atTop]
      intro M
      set A := η * c ^ 2 with hA
      have hApos : 0 < A := by positivity
      set r0 := max 1 ((|M| + |R 0| + Kc) / A) with hr0
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop r0] with w hw
      have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_left _ _) hw
      have hw2 : (|M| + |R 0| + Kc) / A ≤ ‖w‖ := le_trans (le_max_right _ _) hw
      have hw3 : |M| + |R 0| + Kc ≤ A * ‖w‖ := by
        rw [div_le_iff₀ hApos] at hw2; linarith
      have hK1 : 0 ≤ Kc := le_max_left _ _
      have hfw := hfge w hw1
      have e1 : A * ‖w‖ ^ 2 ≥ (|M| + |R 0| + Kc) * ‖w‖ := by nlinarith
      have e2 : (|M| + |R 0|) * ‖w‖ ≥ |M| + |R 0| := by
        nlinarith [abs_nonneg M, abs_nonneg (R 0)]
      have e3 : M ≤ |M| := le_abs_self M
      have e4 : -|R 0| ≤ R 0 := neg_abs_le (R 0)
      nlinarith
  obtain ⟨w, hw⟩ := hcont.exists_forall_le htend
  exact ⟨w, isMinOn_iff.2 fun y _ => hw y⟩

end Attain

/-! ### Claims -/

/-- `lem:delta-inf`, first sentence, finitely supported centres, any measurable rule. -/
theorem delta_inf_W2 : ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → K) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → K) (h : K → ℝ),
    Measurable h → (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      (∃ c, IsLeast (pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) '' Plans a₀ a₁) c) ∧
      ∀ c, IsLeast (pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) '' Plans a₀ a₁) c →
        wassersteinEDist 2 ((centre a₀ x₀).map h) ((centre a₁ x₁).map h) =
          ENNReal.ofReal (√c) := by
  intro K _ n₀ n₁ a₀ x₀ a₁ x₁ h hh h00 h01 h10 h11
  refine ⟨pcost_isLeast_exists h00 h01 h10 h11 _ _, fun c hc => ?_⟩
  rw [map_centre _ _ hh, map_centre _ _ hh]
  exact W2_projected h00 h01 h10 h11 _ _ hc

/-- `lem:delta-inf`, vertex part. -/
theorem delta_inf_vertex : ∀ (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (a₁ : Fin n₁ → ℝ)
    (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      (Set.extremePoints ℝ (Plans a₀ a₁)).Finite ∧
      (∃ γ, IsQuantileCoupling a₀ a₁ u v γ) ∧
      ∀ γ, IsQuantileCoupling a₀ a₁ u v γ →
        γ ∈ Set.extremePoints ℝ (Plans a₀ a₁) ∧ IsLeast (pcost u v '' Plans a₀ a₁) (pcost u v γ) := by
  intro n₀ n₁ a₀ a₁ u v h00 h01 h10 h11
  refine ⟨extreme_finite, quantile_exists h00 h01 h10 h11 u v, fun γ hq => ?_⟩
  refine ⟨quantile_extreme h00 h01 h10 h11 hq, ⟨γ, hq.1, rfl⟩, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  exact quantile_optimal h00 h01 h10 h11 hq g hg

/-- `lem:delta-inf` for linear rules: `W₂(⟪w,·⟫#P̂₀, ⟪w,·⟫#P̂₁) = Δ(w)` and `Δ(w)² = min_γ wᵀM_γw`,
attained at every quantile coupling of the projections. -/
theorem delta_inf_linear : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E),
    (∀ i, 0 ≤ a₀ i) → ∑ i, a₀ i = 1 → (∀ j, 0 ≤ a₁ j) → ∑ j, a₁ j = 1 →
      wassersteinEDist 2 ((centre a₀ x₀).map (fun x => inner ℝ w x))
          ((centre a₁ x₁).map (fun x => inner ℝ w x)) =
        ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) ∧
      ∀ γ, IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) γ →
        IsLeast ((fun g => quad x₀ x₁ w g) '' Plans a₀ a₁) (quad x₀ x₁ w γ) ∧
        Deltafin a₀ x₀ a₁ x₁ w = √(quad x₀ x₁ w γ) := by
  intro E _ _ _ _ n₀ n₁ a₀ x₀ a₁ x₁ w h00 h01 h10 h11
  have hmeas : Measurable (fun x : E => inner ℝ w x) :=
    (continuous_const.inner continuous_id).measurable
  obtain ⟨γ, hq⟩ := quantile_exists h00 h01 h10 h11 (proj x₀ w) (proj x₁ w)
  have hleast : ∀ γ, IsQuantileCoupling a₀ a₁ (proj x₀ w) (proj x₁ w) γ →
      IsLeast ((fun g => quad x₀ x₁ w g) '' Plans a₀ a₁) (quad x₀ x₁ w γ) := by
    intro γ hq
    refine ⟨⟨γ, hq.1, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact quantile_quad_optimal h00 h01 h10 h11 hq g hg
  refine ⟨?_, fun γ hq => ⟨hleast γ hq, Deltafin_quantile h00 h01 h10 h11 hq⟩⟩
  rw [map_centre _ _ hmeas, map_centre _ _ hmeas, Deltafin_quantile h00 h01 h10 h11 hq]
  refine W2_projected h00 h01 h10 h11 _ _ ?_
  have := hleast γ hq
  simp only [quad_eq_pcost] at this
  rw [quad_eq_pcost]
  exact this

/-- `thm:alternating`, corrected: attainment of the convex step is a hypothesis (an exact
minimisation oracle `step`); the coupling oracle `q` returns a quantile coupling of the projections. -/
theorem alternating : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
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
          IsLocalMin (Jobj R η N₀ N₁ a₀ x₀ a₁ x₁) (step (run x₀ x₁ step q w₀ K).2)) := by
  intro E _ _ n₀ n₁ a₀ x₀ a₁ x₁ R η N₀ N₁ w₀ step q h00 h01 h10 h11 hη hstep hq
  exact alternating_main h00 h01 h10 h11 hη hstep hq

/-- DEFECTS #16: the paper's hypotheses do not give attainment of the convex step. -/
theorem alternating_counterexample : ∃ R : ℝ → ℝ, StrictConvexOn ℝ Set.univ R ∧ Continuous R ∧
    (∀ w, 0 ≤ R w) ∧ ∀ η : ℝ, 0 < η →
      ∀ γ ∈ Plans (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)),
        ¬ ∃ w : ℝ, IsMinOn (fun w => Jcpl R η 0 0 (fun _ : Fin 1 => (0 : ℝ))
          (fun _ : Fin 1 => (0 : ℝ)) w γ) Set.univ w := by
  refine ⟨Real.exp, strictConvexOn_exp, Real.continuous_exp, fun w => (Real.exp_pos w).le, ?_⟩
  rintro η - γ - ⟨w, hw⟩
  have h := isMinOn_iff.1 hw (w - 1) (Set.mem_univ _)
  simp only [Jcpl, quad, sub_self, inner_zero_right, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, Real.sqrt_zero,
    FunLike.coe_zero, Pi.zero_apply, add_zero] at h
  have := Real.exp_lt_exp.2 (by linarith : w - 1 < w)
  linarith

/-- Sufficient conditions for the attainment hypothesis of `alternating` on a finite-dimensional
space: a coercive continuous risk, or a convex continuous risk and penalties with
`N₀ + N₁ ≥ c‖·‖`, `c > 0` (seminorms bounded by `C‖·‖`, as in `thm:seminorm` (ii)). -/
theorem alternating_attainment : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (R : E → ℝ) (η C : ℝ) (N₀ N₁ : Seminorm ℝ E),
    Continuous R → 0 < η → (∀ w, N₀ w ≤ C * ‖w‖) → (∀ w, N₁ w ≤ C * ‖w‖) →
    (Tendsto R (cocompact E) atTop ∨
      (ConvexOn ℝ Set.univ R ∧ ∃ c > 0, ∀ w, c * ‖w‖ ≤ N₀ w + N₁ w)) →
      ∀ γ ∈ Plans a₀ a₁, ∃ w, IsMinOn (fun w => Jcpl R η N₀ N₁ x₀ x₁ w γ) Set.univ w := by
  intro E _ _ _ n₀ n₁ a₀ x₀ a₁ x₁ R η C N₀ N₁ hRc hη hC₀ hC₁ hcase γ hγ
  exact attainment_main hRc hη hC₀ hC₁ hcase γ

end StatFormal.RobustEquality.Paper2.Alternating.Route
