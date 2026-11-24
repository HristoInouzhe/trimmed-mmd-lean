import StatFormal.Archive.OTFD.Wave8b.Statements
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Route: A `prop:emp-bijective-weak`, `cor:app-entropic-weak` (deterministic algebra)

1. `bregD_split`: `D(u,r) = ½‖x − u‖² + g(r,x) + h(u)`, so for plans with fixed marginals the `D`-cost and half the
   squared cost differ by a constant (`bregman_plan`, `bregman_assign`).
2. `core_real`: for two plans `π, P` with uniform marginals and `Σπ C ≤ Σ P C + δ`, the one-sided bound, the
   subgradient inequality and a weighted Cauchy–Schwarz give
   `Σ π_ij‖u_j − r_i‖² ≤ (2/α)(2m⁻¹Σ‖s_j‖² + 2n⁻¹Σ‖x_i‖²)^{1/2}(Σ P_ij‖r_i − u_j‖²)^{1/2} + δ/α`.
3. `perm_le_plan` (Birkhoff): an optimal permutation is optimal among all plans with marginals `1/n`.
4. `kl_le_log_min`: `π_ij ≤ min(1/n, 1/m)` bounds each relative-entropy term.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave8b

open StatFormal.OTFD.Wave6b (empMeasure)
open TauCeti (wassersteinEDist)

variable {K n m : ℕ}

lemma bregD_split (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r u : EuclideanSpace ℝ (Fin K)) :
    bregD f x r u = ‖x - u‖ ^ 2 / 2 + (-f r + ⟪x, r⟫_ℝ - ‖x‖ ^ 2 / 2) + (f u - ‖u‖ ^ 2 / 2) := by
  unfold bregD
  rw [norm_sub_sq_real, inner_sub_right]
  ring

lemma plan_sum_split (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (π : Matrix (Fin n) (Fin m) ℝ) (hπ : Matrix.HasMarginals π a b) :
    ∑ i, ∑ j, π i j * bregD f (x i) (r i) (u j) =
      (∑ i, ∑ j, π i j * ‖x i - u j‖ ^ 2) / 2 +
        ∑ i, a i * (-f (r i) + ⟪x i, r i⟫_ℝ - ‖x i‖ ^ 2 / 2) +
        ∑ j, b j * (f (u j) - ‖u j‖ ^ 2 / 2) := by
  have h1 : ∑ i, ∑ j, π i j * (-f (r i) + ⟪x i, r i⟫_ℝ - ‖x i‖ ^ 2 / 2) =
      ∑ i, a i * (-f (r i) + ⟪x i, r i⟫_ℝ - ‖x i‖ ^ 2 / 2) := by
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_mul, hπ.1 i]
  have h2 : ∑ i, ∑ j, π i j * (f (u j) - ‖u j‖ ^ 2 / 2) = ∑ j, b j * (f (u j) - ‖u j‖ ^ 2 / 2) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_mul, hπ.2 j]
  simp_rw [bregD_split, mul_add, sum_add_distrib]
  rw [h1, h2, sum_div]
  congr 2
  refine sum_congr rfl fun i _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem bregman_plan : Claims.bregman_plan := by
  intro K n m f x r u a b π π' hπ hπ'
  rw [plan_sum_split f x r u a b π hπ, plan_sum_split f x r u a b π' hπ']
  ring

theorem bregman_assign : Claims.bregman_assign := by
  intro K n f x r u σ
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ i, bregD f (x i) (r i) (u (τ i)) =
      (∑ i, ‖x i - u (τ i)‖ ^ 2) / 2 + ∑ i, (-f (r i) + ⟪x i, r i⟫_ℝ - ‖x i‖ ^ 2 / 2) +
        ∑ j, (f (u j) - ‖u j‖ ^ 2 / 2) := by
    intro τ
    simp_rw [bregD_split, sum_add_distrib, sum_div]
    congr 1
    exact Equiv.sum_comp τ (fun j => f (u j) - ‖u j‖ ^ 2 / 2)
  constructor
  · intro h τ
    rw [key σ, key τ]
    have := h τ
    linarith
  · intro h τ
    have := h τ
    rw [key σ, key τ] at this
    linarith

/-! ### Weighted Cauchy–Schwarz and the core inequality -/

lemma weighted_cs {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∑ k, w k * a k * b k ≤ √(∑ k, w k * a k ^ 2) * √(∑ k, w k * b k ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun k => √(w k) * a k) (fun k => √(w k) * b k)
  have e1 : ∀ k, √(w k) * a k * (√(w k) * b k) = w k * a k * b k := fun k => by
    have := Real.mul_self_sqrt (hw k)
    calc √(w k) * a k * (√(w k) * b k) = (√(w k) * √(w k)) * a k * b k := by ring
      _ = _ := by rw [this]
  have e2 : ∀ (c : ι → ℝ) k, (√(w k) * c k) ^ 2 = w k * c k ^ 2 := fun c k => by
    rw [mul_pow, Real.sq_sqrt (hw k)]
  simp only [e1, e2] at h
  exact h

lemma polytope_nonneg {π : Matrix (Fin n) (Fin m) ℝ}
    (h : π ∈ Matrix.transportPolytope (unifW n) (unifW m)) (i j) : 0 ≤ π i j := h.1 i j

lemma polytope_row {π : Matrix (Fin n) (Fin m) ℝ}
    (h : π ∈ Matrix.transportPolytope (unifW n) (unifW m)) (i) : ∑ j, π i j = 1 / n := h.2.1 i

lemma polytope_col {π : Matrix (Fin n) (Fin m) ℝ}
    (h : π ∈ Matrix.transportPolytope (unifW n) (unifW m)) (j) : ∑ i, π i j = 1 / m := h.2.2 j

/-- The core inequality shared by both items. -/
lemma core_real {α δ : ℝ} (hα : 0 < α) {f : EuclideanSpace ℝ (Fin K) → ℝ}
    {x r : Fin n → EuclideanSpace ℝ (Fin K)} {u s : Fin m → EuclideanSpace ℝ (Fin K)}
    (hsub : SubgradAt f u s r) (hone : OneSidedAt α f u x r) {π P : Matrix (Fin n) (Fin m) ℝ}
    (hπ : π ∈ Matrix.transportPolytope (unifW n) (unifW m))
    (hP : P ∈ Matrix.transportPolytope (unifW n) (unifW m))
    (hgap : ∑ i, ∑ j, π i j * ‖x i - u j‖ ^ 2 ≤ ∑ i, ∑ j, P i j * ‖x i - u j‖ ^ 2 + δ) :
    ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤
      2 / α * √(2 * ((1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2) + 2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2)) *
        √(∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) + δ / α := by
  set D : Fin n → Fin m → ℝ := fun i j => bregD f (x i) (r i) (u j) with hD
  -- (1) one-sided conditioning under `π`
  have h1 : α / 2 * ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤ ∑ i, ∑ j, π i j * D i j := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_left (hone i j) (polytope_nonneg hπ i j)
    simp only [hD]
    nlinarith
  -- (2) fixed-marginal expansion
  have h2 := bregman_plan K n m f x r u (unifW n) (unifW m) π P hπ.2 hP.2
  -- (3) convexity: `D_ij ≤ (‖s_j‖ + ‖x_i‖)‖u_j − r_i‖`
  have h3 : ∀ i j, D i j ≤ (‖s j‖ + ‖x i‖) * ‖r i - u j‖ := by
    intro i j
    have hs := hsub i j
    have e : D i j ≤ ⟪s j - x i, u j - r i⟫_ℝ := by
      simp only [hD, bregD, inner_sub_left]
      have : ⟪s j, r i - u j⟫_ℝ = -⟪s j, u j - r i⟫_ℝ := by
        rw [← inner_neg_right, neg_sub]
      linarith
    refine e.trans ((real_inner_le_norm _ _).trans ?_)
    rw [norm_sub_rev (u j) (r i)]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
  have h4 : ∑ i, ∑ j, P i j * D i j ≤
      ∑ i, ∑ j, P i j * (‖s j‖ + ‖x i‖) * ‖r i - u j‖ := by
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h3 i j) (polytope_nonneg hP i j)
  -- (4) weighted Cauchy–Schwarz over `Fin n × Fin m`
  have h5 := weighted_cs (fun q : Fin n × Fin m => P q.1 q.2) (fun q => ‖s q.2‖ + ‖x q.1‖)
    (fun q => ‖r q.1 - u q.2‖) (fun q => polytope_nonneg hP q.1 q.2)
  simp only [Fintype.sum_prod_type] at h5
  have h6 : ∑ i, ∑ j, P i j * (‖s j‖ + ‖x i‖) ^ 2 ≤
      2 * ((1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2) + 2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2) := by
    have hle : ∑ i, ∑ j, P i j * (‖s j‖ + ‖x i‖) ^ 2 ≤
        ∑ i, ∑ j, (2 * (P i j * ‖s j‖ ^ 2) + 2 * (P i j * ‖x i‖ ^ 2)) := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      have := polytope_nonneg hP i j
      nlinarith [sq_nonneg (‖s j‖ - ‖x i‖)]
    refine hle.trans (le_of_eq ?_)
    simp_rw [sum_add_distrib, ← mul_sum]
    have ea : ∑ i, ∑ j, P i j * ‖s j‖ ^ 2 = (1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2 := by
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_mul, polytope_col hP j]
    have eb : ∑ i, ∑ j, P i j * ‖x i‖ ^ 2 = (1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_mul, polytope_row hP i]
    rw [ea, eb]
  set A := √(2 * ((1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2) + 2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2)) with hA
  set Q := √(∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) with hQ
  have h7 : ∑ i, ∑ j, P i j * D i j ≤ A * Q := by
    refine h4.trans (h5.trans ?_)
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h6) (Real.sqrt_nonneg _)
  have hmain : α / 2 * ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤ A * Q + δ / 2 := by
    have : ∑ i, ∑ j, π i j * D i j ≤ ∑ i, ∑ j, P i j * D i j + δ / 2 := by
      simp only [hD]
      linarith
    linarith
  have hα2 : 0 < α / 2 := by linarith
  have := (le_div_iff₀' hα2).2 hmain
  calc ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 ≤ (A * Q + δ / 2) / (α / 2) := this
    _ = 2 / α * A * Q + δ / α := by field_simp

/-! ### Birkhoff: an optimal permutation is optimal among plans -/

lemma permMatrix_apply_eq' (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix ℝ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

lemma perm_le_plan (hn : 1 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ τ : Equiv.Perm (Fin n), ∑ i, C i (σ i) ≤ ∑ i, C i (τ i))
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ Matrix.transportPolytope (unifW n) (unifW n)) :
    (1 / n : ℝ) * ∑ i, C i (σ i) ≤ ∑ i, ∑ j, P i j * C i j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ℓ : Matrix (Fin n) (Fin n) ℝ → ℝ := fun A => ∑ i, ∑ j, A i j * C i j with hℓ
  have hlin : IsLinearMap ℝ ℓ := by
    constructor
    · intro A B; simp only [hℓ, Matrix.add_apply, add_mul, sum_add_distrib]
    · intro c A; simp only [hℓ, Matrix.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hconv := convex_halfSpace_ge hlin (∑ i, C i (σ i))
  have hperm : ∀ τ : Equiv.Perm (Fin n), ℓ (τ.permMatrix ℝ) = ∑ i, C i (τ i) := by
    intro τ
    simp only [hℓ, permMatrix_apply_eq', ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  have hsub : {M | ∃ τ : Equiv.Perm (Fin n), τ.permMatrix ℝ = M} ⊆
      {A | ∑ i, C i (σ i) ≤ ℓ A} := by
    rintro _ ⟨τ, rfl⟩
    simp only [Set.mem_setOf_eq, hperm]
    exact hσ τ
  have hQ : (n : ℝ) • P ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hn'.le (polytope_nonneg hP i j)
    · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, polytope_row hP i]; field_simp
    · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, polytope_col hP j]; field_simp
  have hQ' : (n : ℝ) • P ∈ convexHull ℝ {M | ∃ τ : Equiv.Perm (Fin n), τ.permMatrix ℝ = M} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hQ
  have := convexHull_min hsub hconv hQ'
  simp only [Set.mem_setOf_eq, hℓ, Matrix.smul_apply, smul_eq_mul] at this
  have e : ∑ i, ∑ j, (n : ℝ) * P i j * C i j = n * ∑ i, ∑ j, P i j * C i j := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [mul_sum]
    refine sum_congr rfl fun j _ => by ring
  rw [e] at this
  rw [one_div, inv_mul_le_iff₀ hn']
  exact this

/-- The permutation plan `π_ij = 1/n` if `σ(i) = j`. -/
def permPlan (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if σ i = j then (1 / n : ℝ) else 0

lemma permPlan_mem (σ : Equiv.Perm (Fin n)) :
    permPlan σ ∈ Matrix.transportPolytope (unifW n) (unifW n) := by
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · simp only [permPlan]; split_ifs <;> positivity
  · simp [permPlan, unifW]
  · simp only [permPlan, unifW]
    rw [Equiv.sum_comp σ (fun k => if k = j then (1 / n : ℝ) else 0)]
    simp

lemma permPlan_sum (σ : Equiv.Perm (Fin n)) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, permPlan σ i j * g i j = (1 / n : ℝ) * ∑ i, g i (σ i) := by
  simp [permPlan, ite_mul, mul_sum]

/-! ### `eq:app-entropic-kl-bound` -/

theorem kl_le_log_min : Claims.kl_le_log_min := by
  intro n m π hn hm hπ
  have hle_row : ∀ i j, π i j ≤ 1 / n := fun i j => by
    rw [← polytope_row hπ i]
    exact single_le_sum (fun j _ => polytope_nonneg hπ i j) (mem_univ j)
  have hle_col : ∀ i j, π i j ≤ 1 / m := fun i j => by
    rw [← polytope_col hπ j]
    exact single_le_sum (fun i _ => polytope_nonneg hπ i j) (mem_univ i)
  have hterm : ∀ i j, π i j * Real.log (π i j) - π i j * Real.log (unifW n i * unifW m j) =
      π i j * Real.log (π i j) + π i j * Real.log n + π i j * Real.log m := by
    intro i j
    simp only [unifW]
    rw [Real.log_mul (by positivity) (by positivity), one_div, one_div, Real.log_inv, Real.log_inv]
    ring
  have hsum : ∀ L : ℝ, ∑ i, ∑ j, π i j * L = L := by
    intro L
    simp_rw [← sum_mul, polytope_row hπ]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have bound : ∀ (c d : ℕ), 0 < c → (∀ i j, π i j ≤ 1 / c) →
      Real.log n + Real.log m = Real.log c + Real.log d →
      Matrix.relEntropy π (Matrix.vecMulVec (unifW n) (unifW m)) ≤ Real.log d := by
    intro c d hc hcle hcd
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    rw [Matrix.relEntropy_def]
    have hij : ∀ i j, π i j * Real.log (π i j) -
        π i j * Real.log (Matrix.vecMulVec (unifW n) (unifW m) i j) ≤ π i j * Real.log d := by
      intro i j
      rw [Matrix.vecMulVec_apply, hterm]
      have hp := polytope_nonneg hπ i j
      have hlog : π i j * Real.log (π i j) + π i j * Real.log c ≤ 0 := by
        rcases hp.eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · have : Real.log (π i j) ≤ Real.log (1 / c) := Real.log_le_log hpos (hcle i j)
          rw [one_div, Real.log_inv] at this
          nlinarith
      have : π i j * Real.log n + π i j * Real.log m = π i j * Real.log c + π i j * Real.log d := by
        rw [← mul_add, ← mul_add, hcd]
      linarith
    calc ∑ i, ∑ j, (π i j * Real.log (π i j) -
          π i j * Real.log (Matrix.vecMulVec (unifW n) (unifW m) i j))
        ≤ ∑ i, ∑ j, π i j * Real.log d := sum_le_sum fun i _ => sum_le_sum fun j _ => hij i j
      _ = Real.log d := hsum _
  rcases le_total n m with h | h
  · rw [min_eq_left (by exact_mod_cast h)]
    exact bound m n hm hle_col (by ring)
  · rw [min_eq_right (by exact_mod_cast h)]
    exact bound n m hn hle_row (by ring)

/-! ### Couplings of two empirical measures are plans -/

section Coupling

lemma sum_div_card_fiber {X : Type*} [DecidableEq X] {N : ℕ} (x : Fin N → X) (g : X → ℝ) :
    ∑ i, g (x i) / ((univ.filter fun k => x k = x i).card : ℝ) = ∑ a ∈ univ.image x, g a := by
  symm
  refine Finset.sum_image' (fun i => g (x i) / ((univ.filter fun k => x k = x i).card : ℝ)) ?_
  intro i _
  have hcard : 0 < (univ.filter fun k => x k = x i).card :=
    Finset.card_pos.2 ⟨i, by simp⟩
  have : ∑ j ∈ univ with x j = x i, g (x j) / ((univ.filter fun k => x k = x j).card : ℝ) =
      ∑ j ∈ univ with x j = x i, g (x i) / ((univ.filter fun k => x k = x i).card : ℝ) := by
    refine sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [this, sum_const, nsmul_eq_mul]
  have : ((univ.filter fun k => x k = x i).card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  field_simp

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

lemma empMeasure_apply {N : ℕ} (x : Fin N → X) {A : Set X} (hA : MeasurableSet A) :
    empMeasure x A = (N : ℝ≥0∞)⁻¹ * ∑ k, A.indicator 1 (x k) := by
  simp only [empMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
    Finset.sum_apply, Measure.dirac_apply' _ hA]

lemma empMeasure_singleton [DecidableEq X] {N : ℕ} (x : Fin N → X) (a : X) :
    empMeasure x {a} = (N : ℝ≥0∞)⁻¹ * ((univ.filter fun k => x k = a).card : ℝ≥0∞) := by
  rw [empMeasure_apply x (measurableSet_singleton a)]
  congr 1
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [Finset.sum_boole]

lemma empMeasure_univ {N : ℕ} (hN : 1 ≤ N) (x : Fin N → X) : empMeasure x Set.univ = 1 := by
  rw [empMeasure_apply x MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega)) (ENNReal.natCast_ne_top N)

instance empMeasure_isProb {N : ℕ} [NeZero N] (x : Fin N → X) : IsProbabilityMeasure (empMeasure x) :=
  ⟨empMeasure_univ (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) x⟩

lemma empMeasure_compl_image [DecidableEq X] {N : ℕ} (x : Fin N → X) :
    empMeasure x (↑(univ.image x) : Set X)ᶜ = 0 := by
  rw [empMeasure_apply x (Finset.measurableSet _).compl]
  simp [Set.indicator_apply]

lemma empMeasure_real_singleton [DecidableEq X] {N : ℕ} (x : Fin N → X) (i : Fin N) :
    (empMeasure x).real {x i} = ((univ.filter fun k => x k = x i).card : ℝ) / N := by
  rw [measureReal_def, empMeasure_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_inv_mul]

end Coupling

/-- Every coupling of `ν̂_n = n⁻¹Σδ_{r_i}` and `μ_{K,m} = m⁻¹Σδ_{u_j}` is (the image of) a plan with uniform
marginals, with the same quadratic cost. -/
lemma exists_plan_of_coupling (hn : 1 ≤ n) (hm : 1 ≤ m) (r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) {γ : Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K))}
    (hγ : TauCeti.IsCoupling γ (empMeasure r) (empMeasure u)) :
    ∃ P ∈ Matrix.transportPolytope (unifW n) (unifW m),
      ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ = ENNReal.ofReal (∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) := by
  classical
  have : NeZero n := ⟨by omega⟩
  have : NeZero m := ⟨by omega⟩
  have : IsProbabilityMeasure γ := hγ.isProbabilityMeasure
  set R := univ.image r with hR
  set U := univ.image u with hU
  set S := R ×ˢ U with hS
  set cr : Fin n → ℝ := fun i => ((univ.filter fun k => r k = r i).card : ℝ) with hcr
  set cu : Fin m → ℝ := fun j => ((univ.filter fun k => u k = u j).card : ℝ) with hcu
  have hcr_pos : ∀ i, 0 < cr i := fun i => by
    simp only [hcr]; exact_mod_cast Finset.card_pos.2 ⟨i, by simp⟩
  have hcu_pos : ∀ j, 0 < cu j := fun j => by
    simp only [hcu]; exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩
  -- `γ` is carried by `R × U`
  have hfst : ∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A →
      γ (Prod.fst ⁻¹' A) = empMeasure r A := fun A hA => by
    rw [← Measure.fst_apply hA, hγ.fst_eq]
  have hsnd : ∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A →
      γ (Prod.snd ⁻¹' A) = empMeasure u A := fun A hA => by
    rw [← Measure.snd_apply hA, hγ.snd_eq]
  have hSc : γ (↑S : Set _)ᶜ = 0 := by
    have hsub : (↑S : Set (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)))ᶜ ⊆
        Prod.fst ⁻¹' (↑R : Set _)ᶜ ∪ Prod.snd ⁻¹' (↑U : Set _)ᶜ := by
      intro z hz
      simp only [hS, Finset.coe_product, Set.mem_compl_iff, Set.mem_prod, not_and_or] at hz
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [hfst _ (Finset.measurableSet _).compl, hsnd _ (Finset.measurableSet _).compl,
      empMeasure_compl_image, empMeasure_compl_image, add_zero]
  -- row and column masses
  have hrow_mass : ∀ i, ∑ b ∈ U, γ.real {(r i, b)} = cr i / n := by
    intro i
    have himg : ∑ b ∈ U, γ.real {(r i, b)} = ∑ z ∈ U.image (Prod.mk (r i)), γ.real {z} :=
      (Finset.sum_image (f := fun z => γ.real {z}) (s := U) (g := Prod.mk (r i))
        (by intro a _ b _ h; exact (Prod.mk.inj h).2)).symm
    rw [himg, sum_measureReal_singleton]
    have hset : (↑(U.image (Prod.mk (r i))) : Set (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K))) =
        Prod.fst ⁻¹' {r i} ∩ ↑S := by
      ext ⟨a, b⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.mk.injEq, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff, hS, Finset.coe_product, Set.mem_prod, hR,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      constructor
      · rintro ⟨b', hb', rfl, rfl⟩; exact ⟨rfl, ⟨i, rfl⟩, hb'⟩
      · rintro ⟨rfl, _, hb⟩; exact ⟨b, hb, rfl, rfl⟩
    rw [hset, measureReal_def, measure_inter_conull hSc, hfst _ (measurableSet_singleton _),
      ← measureReal_def, empMeasure_real_singleton]
  have hcol_mass : ∀ j, ∑ a ∈ R, γ.real {(a, u j)} = cu j / m := by
    intro j
    have himg : ∑ a ∈ R, γ.real {(a, u j)} = ∑ z ∈ R.image (fun a => (a, u j)), γ.real {z} :=
      (Finset.sum_image (f := fun z => γ.real {z}) (s := R) (g := fun a => (a, u j))
        (by intro a _ b _ h; exact (Prod.mk.inj h).1)).symm
    rw [himg, sum_measureReal_singleton]
    have hset : (↑(R.image (fun a => (a, u j))) : Set (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K))) =
        Prod.snd ⁻¹' {u j} ∩ ↑S := by
      ext ⟨a, b⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.mk.injEq, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff, hS, Finset.coe_product, Set.mem_prod, hU,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      constructor
      · rintro ⟨a', ha', rfl, rfl⟩; exact ⟨rfl, ha', ⟨j, rfl⟩⟩
      · rintro ⟨rfl, ha, _⟩; exact ⟨a, ha, rfl, rfl⟩
    rw [hset, measureReal_def, measure_inter_conull hSc, hsnd _ (measurableSet_singleton _),
      ← measureReal_def, empMeasure_real_singleton]
  -- the plan
  set P : Matrix (Fin n) (Fin m) ℝ := fun i j => γ.real {(r i, u j)} / (cr i * cu j) with hP
  have hdouble : ∀ G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) → ℝ,
      ∑ i, ∑ j, G (r i) (u j) / (cr i * cu j) = ∑ a ∈ R, ∑ b ∈ U, G a b := by
    intro G
    have : ∀ i, ∑ j, G (r i) (u j) / (cr i * cu j) = (∑ b ∈ U, G (r i) b) / cr i := by
      intro i
      rw [← sum_div_card_fiber u (G (r i)), sum_div]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_comm (cr i), div_div]
    simp_rw [this]
    exact sum_div_card_fiber r (fun a => ∑ b ∈ U, G a b)
  refine ⟨P, ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩, ?_⟩
  · exact div_nonneg measureReal_nonneg (mul_pos (hcr_pos i) (hcu_pos j)).le
  · have : ∑ j, P i j = (∑ b ∈ U, γ.real {(r i, b)}) / cr i := by
      rw [← sum_div_card_fiber u (fun b => γ.real {(r i, b)}), sum_div]
      refine sum_congr rfl fun j _ => ?_
      simp only [hP]; rw [mul_comm (cr i), div_div]
    rw [this, hrow_mass, unifW]
    have := (hcr_pos i).ne'
    field_simp
  · have : ∑ i, P i j = (∑ a ∈ R, γ.real {(a, u j)}) / cu j := by
      rw [← sum_div_card_fiber r (fun a => γ.real {(a, u j)}), sum_div]
      refine sum_congr rfl fun i _ => ?_
      simp only [hP]; rw [div_div]
    rw [this, hcol_mass, unifW]
    have := (hcu_pos j).ne'
    field_simp
  · have hcost : ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 =
        ∑ a ∈ R, ∑ b ∈ U, γ.real {(a, b)} * ‖a - b‖ ^ 2 := by
      rw [← hdouble (fun a b => γ.real {(a, b)} * ‖a - b‖ ^ 2)]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      simp only [hP]; ring
    rw [hcost, ← Measure.restrict_eq_self_of_ae_mem (μ := γ) (s := ↑S)
      (by rw [ae_iff]; exact hSc), lintegral_finset, hS, Finset.sum_product,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => sum_nonneg fun b _ => by positivity)]
    refine sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity)]
    refine sum_congr rfl fun b _ => ?_
    rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
      edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _), mul_comm]
    rw [← hS, Measure.restrict_eq_self_of_ae_mem (μ := γ) (s := ↑S) (by rw [ae_iff]; exact hSc)]

/-! ### From plans to `W₂` -/

lemma measurable_edist_E :
    Measurable fun z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => edist z.1 z.2 :=
  continuous_edist.measurable

/-- A bound against every plan with uniform marginals is a bound against `W₂(ν̂_n, μ_{K,m})`. -/
lemma ofReal_le_of_forall_plan (hn : 1 ≤ n) (hm : 1 ≤ m) (r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) {Y A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (h : ∀ P ∈ Matrix.transportPolytope (unifW n) (unifW m),
      Y ≤ A * √(∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) + δ) :
    ENNReal.ofReal Y ≤
      ENNReal.ofReal A * wassersteinEDist 2 (empMeasure r) (empMeasure u) + ENNReal.ofReal δ := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero m := ⟨by omega⟩
  by_cases hY : Y ≤ δ
  · exact (ENNReal.ofReal_le_ofReal hY).trans le_add_self
  push_neg at hY
  obtain ⟨P0, hP0, -⟩ :=
    exists_plan_of_coupling hn hm r u (TauCeti.isCoupling_prod (empMeasure r) (empMeasure u))
  have hApos : 0 < A := by
    rcases hA.eq_or_lt with h0 | h0
    · have := h P0 hP0
      rw [← h0, zero_mul, zero_add] at this
      linarith
    · exact h0
  set W := wassersteinEDist 2 (empMeasure r) (empMeasure u) with hWdef
  rcases eq_top_or_lt_top W with hW | hW
  · rw [hW, ENNReal.mul_top (by simpa using hApos), top_add]
    exact le_top
  have e2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  have hT : ENNReal.ofReal ((Y - δ) ^ 2 / A ^ 2) ≤ W ^ (2 : ℝ) := by
    rw [← e2, hWdef, TauCeti.wassersteinEDist_rpow_eq_transportCost measurable_edist_E (by norm_num)
      (by norm_num), TauCeti.transportCost_def]
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨P, hP, hcost⟩ := exists_plan_of_coupling hn hm r u hγ
    simp_rw [e2, ENNReal.rpow_two]
    rw [hcost]
    refine ENNReal.ofReal_le_ofReal ?_
    have hQ : 0 ≤ ∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2 :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (polytope_nonneg hP i j) (by positivity)
    have h1 := h P hP
    have h2 : 0 ≤ Y - δ := by linarith
    have h3 : Y - δ ≤ A * √(∑ i, ∑ j, P i j * ‖r i - u j‖ ^ 2) := by linarith
    rw [div_le_iff₀ (by positivity)]
    have := mul_self_le_mul_self h2 h3
    nlinarith [Real.mul_self_sqrt hQ]
  have hWr : W = ENNReal.ofReal W.toReal := (ENNReal.ofReal_toReal hW.ne).symm
  have hw : 0 ≤ W.toReal := ENNReal.toReal_nonneg
  rw [hWr, ENNReal.ofReal_rpow_of_nonneg hw (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by positivity), Real.rpow_two, div_le_iff₀ (by positivity)] at hT
  have key : Y - δ ≤ A * W.toReal := by
    have hsq : (Y - δ) ^ 2 ≤ (A * W.toReal) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).1 hsq
  calc ENNReal.ofReal Y ≤ ENNReal.ofReal (A * W.toReal) + ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) hδ]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal A * W + ENNReal.ofReal δ := by rw [ENNReal.ofReal_mul hA, ← hWr]

/-! ### The deterministic cores -/

theorem bijective_core : Claims.bijective_core := by
  intro K n α f x r u s σ hn hα hsub hone hopt
  have hA : 0 ≤ 2 / α * √(2 * ((1 / n : ℝ) * ∑ j, ‖s j‖ ^ 2) + 2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2)) := by
    positivity
  have := ofReal_le_of_forall_plan (Y := (1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) hn hn r u hA le_rfl ?_
  · simpa using this
  intro P hP
  have hgap : ∑ i, ∑ j, permPlan σ i j * ‖x i - u j‖ ^ 2 ≤ ∑ i, ∑ j, P i j * ‖x i - u j‖ ^ 2 + 0 := by
    rw [permPlan_sum, add_zero]
    exact perm_le_plan hn (fun i j => ‖x i - u j‖ ^ 2) σ hopt hP
  have hc := core_real hα hsub hone (permPlan_mem σ) hP hgap
  rw [permPlan_sum] at hc
  simpa using hc

lemma bary_jensen {π : Matrix (Fin n) (Fin m) ℝ} (hn : 1 ≤ n)
    (hπ : π ∈ Matrix.transportPolytope (unifW n) (unifW m)) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (r : Fin n → EuclideanSpace ℝ (Fin K)) :
    (1 / n : ℝ) * ∑ i, ‖entBary π u i - r i‖ ^ 2 ≤ ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow : ∀ i, ‖entBary π u i - r i‖ ^ 2 ≤ n * ∑ j, π i j * ‖u j - r i‖ ^ 2 := by
    intro i
    set w : Fin m → ℝ := fun j => (n : ℝ) * π i j with hw
    have hw0 : ∀ j, 0 ≤ w j := fun j => mul_nonneg hn'.le (polytope_nonneg hπ i j)
    have hw1 : ∑ j, w j = 1 := by
      simp only [hw, ← mul_sum, polytope_row hπ i]; field_simp
    have e : entBary π u i - r i = ∑ j, w j • (u j - r i) := by
      rw [show ∑ j, w j • (u j - r i) = ∑ j, w j • u j - (∑ j, w j) • r i by
        simp [smul_sub, sum_sub_distrib, sum_smul], hw1, one_smul]
      simp only [entBary, hw, smul_sum, mul_smul]
    have h1 : ‖entBary π u i - r i‖ ≤ ∑ j, w j * ‖u j - r i‖ := by
      rw [e]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine sum_congr rfl fun j _ => ?_
      rw [norm_smul, Real.norm_of_nonneg (hw0 j)]
    have h2 := weighted_cs w (fun _ => 1) (fun j => ‖u j - r i‖) hw0
    simp only [mul_one, one_pow, hw1, Real.sqrt_one, one_mul] at h2
    have h3 : ‖entBary π u i - r i‖ ≤ √(∑ j, w j * ‖u j - r i‖ ^ 2) := h1.trans h2
    have h4 : 0 ≤ ∑ j, w j * ‖u j - r i‖ ^ 2 := sum_nonneg fun j _ => mul_nonneg (hw0 j) (by positivity)
    calc ‖entBary π u i - r i‖ ^ 2 ≤ (√(∑ j, w j * ‖u j - r i‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = ∑ j, w j * ‖u j - r i‖ ^ 2 := Real.sq_sqrt h4
      _ = n * ∑ j, π i j * ‖u j - r i‖ ^ 2 := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; simp only [hw]; ring
  calc (1 / n : ℝ) * ∑ i, ‖entBary π u i - r i‖ ^ 2 ≤ (1 / n : ℝ) * ∑ i, n * ∑ j, π i j * ‖u j - r i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hrow i) (by positivity)
    _ = ∑ i, ∑ j, π i j * ‖u j - r i‖ ^ 2 := by
        rw [← mul_sum, ← mul_assoc, one_div, inv_mul_cancel₀ hn'.ne', one_mul]

lemma entropic_gap {ε : ℝ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε)
    {x : Fin n → EuclideanSpace ℝ (Fin K)} {u : Fin m → EuclideanSpace ℝ (Fin K)}
    {π : Matrix (Fin n) (Fin m) ℝ} (hπ : IsEntPlan ε x u π) {P : Matrix (Fin n) (Fin m) ℝ}
    (hP : P ∈ Matrix.transportPolytope (unifW n) (unifW m)) :
    ∑ i, ∑ j, π i j * ‖x i - u j‖ ^ 2 ≤
      ∑ i, ∑ j, P i j * ‖x i - u j‖ ^ 2 + ε * Real.log (min n m) := by
  have hobj := isMinOn_iff.1 hπ.2 P hP
  simp only [Matrix.entropicTransportObjective_def, sqCost, Matrix.of_apply] at hobj
  have hpos : ∀ i j, 0 < Matrix.vecMulVec (unifW n) (unifW m) i j := fun i j => by
    simp only [Matrix.vecMulVec_apply, unifW]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hmass : ∀ Q ∈ Matrix.transportPolytope (unifW n) (unifW m), ∑ i, ∑ j, Q i j = 1 := by
    intro Q hQ
    simp_rw [polytope_row hQ]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  have hprod : ∑ i, ∑ j, Matrix.vecMulVec (unifW n) (unifW m) i j = 1 := by
    simp only [Matrix.vecMulVec_apply, unifW, ← mul_sum, ← sum_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  have hKL0 : 0 ≤ Matrix.relEntropy π (Matrix.vecMulVec (unifW n) (unifW m)) :=
    Matrix.relEntropy_nonneg_of_nonneg (fun i j => polytope_nonneg hπ.1 i j)
      (fun i j => (hpos i j).le) (fun i j h => absurd h (hpos i j).ne')
      (by rw [hmass π hπ.1, hprod])
  have hKL := kl_le_log_min n m P hn hm hP
  have e1 : ∀ Q : Matrix (Fin n) (Fin m) ℝ, ∑ i, ∑ j, ‖x i - u j‖ ^ 2 * Q i j =
      ∑ i, ∑ j, Q i j * ‖x i - u j‖ ^ 2 := fun Q => by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, e1] at hobj
  nlinarith

theorem entropic_core : Claims.entropic_core := by
  intro K n m α ε f x r u s π hn hm hα hε hsub hone hπ
  have hlog : 0 ≤ Real.log (min n m) := by
    apply Real.log_nonneg
    rcases le_total n m with h | h
    · rw [min_eq_left (by exact_mod_cast h)]; exact_mod_cast hn
    · rw [min_eq_right (by exact_mod_cast h)]; exact_mod_cast hm
  have hA : 0 ≤ 2 / α * √(2 * ((1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2) + 2 * ((1 / n : ℝ) * ∑ i, ‖x i‖ ^ 2)) := by
    positivity
  have hδ : 0 ≤ ε * Real.log (min n m) / α := by positivity
  have := ofReal_le_of_forall_plan (Y := (1 / n : ℝ) * ∑ i, ‖entBary π u i - r i‖ ^ 2) hn hm r u hA hδ ?_
  · have e : ε * Real.log (min n m) / α = ε / α * Real.log (min n m) := by ring
    rw [e] at this
    exact this
  intro P hP
  have hgap := entropic_gap hn hm hε hπ hP
  have hc := core_real hα hsub hone hπ.1 hP hgap
  exact (bary_jensen hn hπ.1 u r).trans hc

/-! ### Cauchy–Schwarz for a lower integral with one measurable factor -/

lemma real_amgm_inf {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ t / 2 * a + 1 / (2 * t) * b) : X ≤ √a * √b := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    simp only [mul_zero, add_zero, Real.sqrt_zero] at h ⊢
    by_contra hcon
    push_neg at hcon
    have := h (X / a) (div_pos hcon ha)
    have e : X / a / 2 * a = X / 2 := by field_simp
    rw [e] at this
    linarith
  · have hsa := Real.sqrt_pos.2 ha
    have hsb := Real.sqrt_pos.2 hbpos
    have := h (√b / √a) (div_pos hsb hsa)
    have key : ∀ p q : ℝ, 0 < p → 0 < q →
        q / p / 2 * (p * p) + 1 / (2 * (q / p)) * (q * q) = p * q := by
      intro p q hp hq; field_simp; ring
    have e := key (√a) (√b) hsa hsb
    rw [Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb] at e
    linarith

lemma young_pt (A B : ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    A * B ≤ ENNReal.ofReal (t / 2) * A ^ 2 + ENNReal.ofReal (1 / (2 * t)) * B ^ 2 := by
  set s := ENNReal.ofReal (√t) with hsdef
  have hs0 : s ≠ 0 := by
    rw [hsdef, Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.sqrt_pos.2 ht
  have hs1 : s ≠ ⊤ := ENNReal.ofReal_ne_top
  have e : A * B = (s * A) * (s⁻¹ * B) := by
    calc A * B = (s * s⁻¹) * (A * B) := by rw [ENNReal.mul_inv_cancel hs0 hs1, one_mul]
      _ = _ := by ring
  have y := ENNReal.young_inequality (s * A) (s⁻¹ * B) Real.HolderConjugate.two_two
  rw [e]
  refine y.trans (le_of_eq ?_)
  have hs2 : s ^ 2 = ENNReal.ofReal t := by
    rw [hsdef, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ht.le]
  have hsi2 : s⁻¹ ^ 2 = ENNReal.ofReal (1 / t) := by
    rw [← ENNReal.inv_pow, hs2, one_div, ENNReal.ofReal_inv_of_pos ht]
  rw [ENNReal.rpow_two, ENNReal.rpow_two, mul_pow, mul_pow, hs2, hsi2,
    ENNReal.ofReal_div_of_pos two_pos, show (1 / (2 * t)) = (1 / t) / 2 by ring,
    ENNReal.ofReal_div_of_pos two_pos]
  simp only [div_eq_mul_inv]
  ring

lemma lintegral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {A : Ω → ℝ≥0∞}
    (hA : Measurable A) (B : Ω → ℝ≥0∞) (ha : ∫⁻ ω, A ω ^ 2 ∂P ≠ ⊤) :
    ∫⁻ ω, A ω * B ω ∂P ≤ (∫⁻ ω, A ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  set a := ∫⁻ ω, A ω ^ 2 ∂P with hadef
  set b := ∫⁻ ω, B ω ^ 2 ∂P with hbdef
  have step : ∀ t : ℝ, 0 < t →
      ∫⁻ ω, A ω * B ω ∂P ≤ ENNReal.ofReal (t / 2) * a + ENNReal.ofReal (1 / (2 * t)) * b := by
    intro t ht
    calc ∫⁻ ω, A ω * B ω ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (t / 2) * A ω ^ 2 + ENNReal.ofReal (1 / (2 * t)) * B ω ^ 2) ∂P :=
          lintegral_mono fun ω => young_pt (A ω) (B ω) ht
      _ = ENNReal.ofReal (t / 2) * a + ENNReal.ofReal (1 / (2 * t)) * b := by
          rw [lintegral_add_left ((hA.pow_const 2).const_mul _),
            lintegral_const_mul _ (hA.pow_const 2), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  by_cases ha0 : a = 0
  · have hAe : ∀ᵐ ω ∂P, A ω = 0 := by
      have := (lintegral_eq_zero_iff (hA.pow_const 2)).1 ha0
      filter_upwards [this] with ω hω
      simpa using hω
    have : ∫⁻ ω, A ω * B ω ∂P = ∫⁻ _ω, (0 : ℝ≥0∞) ∂P :=
      lintegral_congr_ae (hAe.mono fun ω h => by simp [h])
    rw [this, lintegral_zero]; exact bot_le
  by_cases hbt : b = ⊤
  · rw [hbt, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha).ne'
  have hX : ∫⁻ ω, A ω * B ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (by
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt⟩) (step 1 one_pos)
  have har : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
  have hbr : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbt).symm
  have hXr := (ENNReal.ofReal_toReal hX).symm
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 ha
  have key := real_amgm_inf (X := (∫⁻ ω, A ω * B ω ∂P).toReal) ENNReal.toReal_nonneg hapos
    ENNReal.toReal_nonneg (fun t ht => by
      have := step t ht
      rw [hXr, har, hbr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this)
  rw [hXr, har, hbr, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal key

/-! ### Taking expectations -/

lemma sqrt_combine {α β σ2 : ℝ} (hα : 0 < α) (hβσ : 0 ≤ β ^ 2 + σ2) :
    √((2 / α) ^ 2 * (2 * β ^ 2 + 2 * σ2)) * √2 = 4 / α * √(β ^ 2 + σ2) := by
  rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) (by linarith))]
  have e : (2 / α) ^ 2 * (2 * β ^ 2 + 2 * σ2) * 2 = (4 / α) ^ 2 * (β ^ 2 + σ2) := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

lemma expect_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K))
    {α β c : ℝ} (hn : 1 ≤ n) (hα : 0 < α) (hx : ∀ i, Measurable (x i)) (hlaw : ∀ i, P.map (x i) = PK)
    (hmom : Integrable (fun z => ‖z‖ ^ 2) PK) (Y : Ω → ℝ)
    (hcore : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
      ENNReal.ofReal (2 / α * √(2 * β ^ 2 + 2 * ((1 / n : ℝ) * ∑ i, ‖x i ω‖ ^ 2))) *
        wassersteinEDist 2 (empMeasure fun i => F (x i ω)) (empMeasure u) + ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤
      ENNReal.ofReal (4 / α * Real.sqrt (β ^ 2 + ∫ z, ‖z‖ ^ 2 ∂PK)) *
        (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
            wassersteinEDist 2 (empMeasure u) μ ^ 2) ^ (1 / 2 : ℝ) + ENNReal.ofReal c := by
  set σ2 := ∫ z, ‖z‖ ^ 2 ∂PK with hσ2
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun z => by positivity
  set S : Ω → ℝ := fun ω => (1 / n : ℝ) * ∑ i, ‖x i ω‖ ^ 2 with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => by simp only [hS]; positivity
  have hint : ∀ i, Integrable (fun ω => ‖x i ω‖ ^ 2) P := by
    intro i
    have h1 : Integrable (fun z : EuclideanSpace ℝ (Fin K) => ‖z‖ ^ 2) (P.map (x i)) := by
      rw [hlaw i]; exact hmom
    exact (integrable_map_measure h1.aestronglyMeasurable (hx i).aemeasurable).1 h1
  have hmean : ∀ i, ∫ ω, ‖x i ω‖ ^ 2 ∂P = σ2 := by
    intro i
    rw [hσ2, ← hlaw i, integral_map (hx i).aemeasurable (by fun_prop)]
  have hSint : Integrable S P := (integrable_finset_sum _ fun i _ => hint i).const_mul _
  have hSmean : ∫ ω, S ω ∂P = σ2 := by
    simp only [hS]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    simp only [hmean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  set k : ℝ := (2 / α) ^ 2 with hk
  set A : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (2 / α * √(2 * β ^ 2 + 2 * S ω)) with hA
  have hAm : Measurable A := by
    have : Measurable S := by
      simp only [hS]
      exact (Finset.measurable_sum _ fun i _ => ((hx i).norm).pow_const 2).const_mul _
    exact ((measurable_const.add (this.const_mul 2)).sqrt.const_mul _).ennreal_ofReal
  have hA2 : ∀ ω, A ω ^ 2 = ENNReal.ofReal (k * (2 * β ^ 2 + 2 * S ω)) := by
    intro ω
    simp only [hA, hk]
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (by have := hS0 ω; positivity)]
  have hIA : ∫⁻ ω, A ω ^ 2 ∂P = ENNReal.ofReal (k * (2 * β ^ 2 + 2 * σ2)) := by
    simp_rw [hA2]
    have hg : Integrable (fun ω => k * (2 * β ^ 2 + 2 * S ω)) P :=
      ((integrable_const _).add (hSint.const_mul 2)).const_mul k
    rw [← ofReal_integral_eq_lintegral_ofReal hg (.of_forall fun ω => by
      have := hS0 ω; positivity)]
    congr 1
    rw [integral_const_mul, integral_add (integrable_const _) (hSint.const_mul 2), integral_const,
      integral_const_mul, hSmean]
    simp
  set B : Ω → ℝ≥0∞ := fun ω => wassersteinEDist 2 (empMeasure fun i => F (x i ω)) (empMeasure u)
    with hB
  set W : Ω → ℝ≥0∞ := fun ω => wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ with hW
  set Wg := wassersteinEDist 2 (empMeasure u) μ with hWg
  -- step 1
  have h1 : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤ ∫⁻ ω, A ω * B ω ∂P + ENNReal.ofReal c := by
    calc ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤ ∫⁻ ω, (A ω * B ω + ENNReal.ofReal c) ∂P := by
          refine lintegral_mono_ae (hcore.mono fun ω h => ?_)
          simpa [hA, hB, hS] using h
      _ = ∫⁻ ω, A ω * B ω ∂P + ENNReal.ofReal c := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  -- step 2
  have h2 := lintegral_mul_le_sqrt P hAm B (by rw [hIA]; exact ENNReal.ofReal_ne_top)
  -- step 3
  have hB2 : ∀ ω, B ω ^ 2 ≤ 2 * (W ω ^ 2 + Wg ^ 2) := by
    intro ω
    have htri : B ω ≤ W ω + Wg := by
      simp only [hB, hW, hWg]
      rw [TauCeti.wassersteinEDist_comm measurable_edist_E 2 (empMeasure u) μ]
      exact TauCeti.wassersteinEDist_triangle measurable_edist_E (by norm_num) _ μ _
    have hp := ENNReal.rpow_add_le_mul_rpow_add_rpow (W ω) Wg (p := 2) one_le_two
    norm_num at hp
    try simp only [ENNReal.rpow_two, ENNReal.rpow_one] at hp
    calc B ω ^ 2 ≤ (W ω + Wg) ^ 2 := by gcongr
      _ ≤ 2 * (W ω ^ 2 + Wg ^ 2) := hp
  have h3 : ∫⁻ ω, B ω ^ 2 ∂P ≤ 2 * (∫⁻ ω, W ω ^ 2 ∂P + Wg ^ 2) := by
    calc ∫⁻ ω, B ω ^ 2 ∂P ≤ ∫⁻ ω, 2 * (W ω ^ 2 + Wg ^ 2) ∂P := lintegral_mono hB2
      _ = 2 * (∫⁻ ω, W ω ^ 2 ∂P + Wg ^ 2) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ measurable_const,
            lintegral_const, measure_univ, mul_one]
  -- step 4
  have h4 : (∫⁻ ω, A ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (4 / α * √(β ^ 2 + σ2)) * (∫⁻ ω, W ω ^ 2 ∂P + Wg ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hIA]
    calc ENNReal.ofReal (k * (2 * β ^ 2 + 2 * σ2)) ^ (1 / 2 : ℝ) * (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (k * (2 * β ^ 2 + 2 * σ2)) ^ (1 / 2 : ℝ) *
            (2 * (∫⁻ ω, W ω ^ 2 ∂P + Wg ^ 2)) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (4 / α * √(β ^ 2 + σ2)) * (∫⁻ ω, W ω ^ 2 ∂P + Wg ^ 2) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hk,
            sqrt_combine hα (by positivity)]
  calc ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤ ∫⁻ ω, A ω * B ω ∂P + ENNReal.ofReal c := h1
    _ ≤ _ := by gcongr; exact h2.trans h4

theorem emp_bijective_weak : Claims.emp_bijective_weak := by
  intro K n Ω _ P _ PK μ _ x F u s f α β σ hn hα hx hlaw hmom hβ hae hopt
  have := expect_bound (c := 0) (β := β) P PK μ x F u hn hα hx hlaw hmom
    (fun ω => (1 / n : ℝ) * ∑ i, ‖u (σ ω i) - F (x i ω)‖ ^ 2) ?_
  · simpa using this
  filter_upwards [hae] with ω hω
  have hcore := bijective_core K n α f (fun i => x i ω) (fun i => F (x i ω)) u s (σ ω) hn hα hω.1 hω.2
    (hopt ω)
  refine hcore.trans ?_
  rw [ENNReal.ofReal_zero, add_zero]
  gcongr

theorem app_entropic_weak : Claims.app_entropic_weak := by
  intro K n m Ω _ P _ PK μ _ x F u s f α β ε π hn hm hα hε hx hlaw hmom hβ hae hπ
  refine expect_bound (c := ε / α * Real.log (min n m)) (β := β) P PK μ x F u hn hα hx hlaw hmom
    (fun ω => (1 / n : ℝ) * ∑ i, ‖entBary (π ω) u i - F (x i ω)‖ ^ 2) ?_
  filter_upwards [hae] with ω hω
  have hcore := entropic_core K n m α ε f (fun i => x i ω) (fun i => F (x i ω)) u s (π ω) hn hm hα hε
    hω.1 hω.2 (hπ ω)
  refine hcore.trans ?_
  gcongr

end StatFormal.OTFD.Wave8b
