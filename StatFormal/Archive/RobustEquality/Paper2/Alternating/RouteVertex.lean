import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Set.Card
import TauCeti.MeasureTheory.OptimalTransport.Finite.Monotone

/-!
# Route: the transport polytope of two finite centres, its vertices and the quantile coupling

Paper 2, `lem:delta-inf` (`paper2/main.tex:296`), the finite part: for finitely supported centres
`P̂_s = Σ_i a^s_i δ_{x^s_i}` and real projections `u = h ∘ x⁰`, `v = h ∘ x¹`,

* `extreme_finite` — the transport polytope `Π(a₀, a₁)` has finitely many extreme points (an extreme
  point is determined by its support);
* `quantile_exists` — a quantile coupling exists (sorted projections, north-west corner, i.e. the
  unique non-crossing plan in the sorted order — Tau Ceti's `existsUnique_isMonotone`);
* `quantile_optimal` — every quantile coupling minimises `E_γ{h(X) − h(Y)}²` over the polytope (Tau
  Ceti's `IsMonotone.forall_cost_le` for the Monge cost `(u − v)²`);
* `quantile_extreme` — every quantile coupling is an extreme point (vertex) of the polytope;
* `optimal_noCross_sort` / `optimal_unique` — if the projections are pairwise distinct on the support
  of each centre, every optimal coupling is the quantile coupling of the canonical sort, so the
  optimal coupling is unique.
-/

noncomputable section
open Finset

namespace StatFormal.RobustEquality.Paper2.Alternating.Route

open TauCeti

variable {n₀ n₁ : ℕ}

/-! ### Definitions -/

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

/-! ### The sorted frame: bridge to Tau Ceti's transport matrices -/

section Frame

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}

/-- The weights read in the order `σ`, as a PMF. -/
def pmfOf {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (h0 : ∀ i, 0 ≤ a i)
    (h1 : ∑ i, a i = 1) : PMF (Fin n) :=
  PMF.ofFintype (fun k => ENNReal.ofReal (a (σ k))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => h0 (σ k)), Equiv.sum_comp σ a, h1,
      ENNReal.ofReal_one])

lemma pmfOf_toReal {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (h0 : ∀ i, 0 ≤ a i)
    (h1 : ∑ i, a i = 1) (k : Fin n) : (pmfOf a σ h0 h1 k).toReal = a (σ k) := by
  simp [pmfOf, PMF.ofFintype_apply, ENNReal.toReal_ofReal (h0 (σ k))]

/-- A plan read in the order `σ₀, σ₁`. -/
def fr (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) (γ : Fin n₀ → Fin n₁ → ℝ) :
    Fin n₀ × Fin n₁ → ℝ := fun q => γ (σ₀ q.1) (σ₁ q.2)

/-- Back from the order `σ₀, σ₁`. -/
def unfr (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) (f : Fin n₀ × Fin n₁ → ℝ) :
    Fin n₀ → Fin n₁ → ℝ := fun i j => f (σ₀.symm i, σ₁.symm j)

lemma unfr_fr (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) (γ : Fin n₀ → Fin n₁ → ℝ) :
    unfr σ₀ σ₁ (fr σ₀ σ₁ γ) = γ := by
  funext i j; simp [unfr, fr]

lemma fr_unfr (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) (f : Fin n₀ × Fin n₁ → ℝ) :
    fr σ₀ σ₁ (unfr σ₀ σ₁ f) = f := by
  funext q; simp [unfr, fr]

variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

include h00 h01 h10 h11 in
lemma fr_mem (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : γ ∈ Plans a₀ a₁) :
    fr σ₀ σ₁ γ ∈ RealPlans (pmfOf a₀ σ₀ h00 h01) (pmfOf a₁ σ₁ h10 h11) := by
  refine ⟨fun q => hγ.1 _ _, fun k => ?_, fun l => ?_⟩
  · rw [pmfOf_toReal]
    simp only [fr]
    rw [Equiv.sum_comp σ₁ (fun j => γ (σ₀ k) j)]
    exact hγ.2.1 _
  · rw [pmfOf_toReal]
    simp only [fr]
    rw [Equiv.sum_comp σ₀ (fun i => γ i (σ₁ l))]
    exact hγ.2.2 _

include h00 h01 h10 h11 in
lemma unfr_mem (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁)) {f : Fin n₀ × Fin n₁ → ℝ}
    (hf : f ∈ RealPlans (pmfOf a₀ σ₀ h00 h01) (pmfOf a₁ σ₁ h10 h11)) :
    unfr σ₀ σ₁ f ∈ Plans a₀ a₁ := by
  refine ⟨fun i j => hf.1 _, fun i => ?_, fun j => ?_⟩
  · simp only [unfr]
    rw [Equiv.sum_comp σ₁.symm (fun l => f (σ₀.symm i, l)), hf.2.1, pmfOf_toReal]
    simp
  · simp only [unfr]
    rw [Equiv.sum_comp σ₀.symm (fun k => f (k, σ₁.symm j)), hf.2.2, pmfOf_toReal]
    simp

/-- The Monge cost in the sorted frame. -/
def scost (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) (σ₀ : Equiv.Perm (Fin n₀))
    (σ₁ : Equiv.Perm (Fin n₁)) : Fin n₀ × Fin n₁ → ℝ :=
  fun q => (u (σ₀ q.1) - v (σ₁ q.2)) ^ 2

lemma pcost_fr (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) (σ₀ : Equiv.Perm (Fin n₀))
    (σ₁ : Equiv.Perm (Fin n₁)) (γ : Fin n₀ → Fin n₁ → ℝ) :
    pcost u v γ = ∑ q, scost u v σ₀ σ₁ q * fr σ₀ σ₁ γ q := by
  rw [Fintype.sum_prod_type]
  simp only [scost, fr, pcost]
  rw [← Equiv.sum_comp σ₀]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp σ₁]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma monge (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) (σ₀ : Equiv.Perm (Fin n₀))
    (σ₁ : Equiv.Perm (Fin n₁)) (hu : Monotone (u ∘ σ₀)) (hv : Monotone (v ∘ σ₁)) :
    ∀ ⦃i₁ i₂ : Fin n₀⦄ ⦃j₁ j₂ : Fin n₁⦄, i₁ < i₂ → j₁ < j₂ →
      scost u v σ₀ σ₁ (i₁, j₁) + scost u v σ₀ σ₁ (i₂, j₂) ≤
        scost u v σ₀ σ₁ (i₁, j₂) + scost u v σ₀ σ₁ (i₂, j₁) := by
  intro i₁ i₂ j₁ j₂ hi hj
  have h1 : u (σ₀ i₁) ≤ u (σ₀ i₂) := hu hi.le
  have h2 : v (σ₁ j₁) ≤ v (σ₁ j₂) := hv hj.le
  simp only [scost]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

lemma ofReal_ne_zero_iff {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero]
  constructor
  · intro h h'; exact h h'.le
  · intro h h'; exact h (le_antisymm h' hx)

include h00 h01 h10 h11 in
lemma noCross_iff (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁))
    {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) :
    NoCross σ₀ σ₁ γ ↔
      (TransportMatrix.ofRealFun (fr_mem h00 h01 h10 h11 σ₀ σ₁ hγ)).IsMonotone := by
  simp only [NoCross, TransportMatrix.IsMonotone, TransportMatrix.ofRealFun_apply, fr]
  constructor
  · intro h k₁ k₂ l₁ l₂ hk e1 e2
    exact h hk ((ofReal_ne_zero_iff (hγ.1 _ _)).1 e1) ((ofReal_ne_zero_iff (hγ.1 _ _)).1 e2)
  · intro h k₁ k₂ l₁ l₂ hk e1 e2
    exact h hk ((ofReal_ne_zero_iff (hγ.1 _ _)).2 e1) ((ofReal_ne_zero_iff (hγ.1 _ _)).2 e2)

include h00 h01 h10 h11 in
/-- Two plans that do not cross in the same order are equal. -/
lemma noCross_unique (σ₀ : Equiv.Perm (Fin n₀)) (σ₁ : Equiv.Perm (Fin n₁))
    {γ γ' : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) (hγ' : γ' ∈ Plans a₀ a₁)
    (h : NoCross σ₀ σ₁ γ) (h' : NoCross σ₀ σ₁ γ') : γ = γ' := by
  have hm := (noCross_iff h00 h01 h10 h11 σ₀ σ₁ hγ).1 h
  have hm' := (noCross_iff h00 h01 h10 h11 σ₀ σ₁ hγ').1 h'
  have heq := hm.eq hm'
  have hf := congrArg TransportMatrix.toRealFun heq
  rw [TransportMatrix.toRealFun_ofRealFun, TransportMatrix.toRealFun_ofRealFun] at hf
  rw [← unfr_fr σ₀ σ₁ γ, ← unfr_fr σ₀ σ₁ γ', hf]

end Frame

/-! ### The quantile coupling: existence, optimality, extremality -/

section Quantile

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}
variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

include h00 h01 h10 h11 in
/-- The quantile coupling of the canonical sort exists. -/
theorem quantile_exists_sort (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) :
    ∃ γ, γ ∈ Plans a₀ a₁ ∧ NoCross (Tuple.sort u) (Tuple.sort v) γ := by
  obtain ⟨A, hA, -⟩ := TransportMatrix.existsUnique_isMonotone
    (pmfOf a₀ (Tuple.sort u) h00 h01) (pmfOf a₁ (Tuple.sort v) h10 h11)
  refine ⟨unfr (Tuple.sort u) (Tuple.sort v) A.toRealFun,
    unfr_mem h00 h01 h10 h11 _ _ A.toRealFun_mem_realPlans, ?_⟩
  intro k₁ k₂ l₁ l₂ hk e1 e2
  simp only [unfr, Equiv.symm_apply_apply, TransportMatrix.toRealFun_apply] at e1 e2
  exact hA hk (fun h => e1 (by simp [h])) (fun h => e2 (by simp [h]))

include h00 h01 h10 h11 in
theorem quantile_exists (u : Fin n₀ → ℝ) (v : Fin n₁ → ℝ) :
    ∃ γ, IsQuantileCoupling a₀ a₁ u v γ := by
  obtain ⟨γ, hγ, hnc⟩ := quantile_exists_sort h00 h01 h10 h11 u v
  exact ⟨γ, hγ, Tuple.sort u, Tuple.sort v, Tuple.monotone_sort u, Tuple.monotone_sort v, hnc⟩

include h00 h01 h10 h11 in
theorem quantile_optimal {u : Fin n₀ → ℝ} {v : Fin n₁ → ℝ} {γ : Fin n₀ → Fin n₁ → ℝ}
    (hq : IsQuantileCoupling a₀ a₁ u v γ) :
    ∀ γ' ∈ Plans a₀ a₁, pcost u v γ ≤ pcost u v γ' := by
  intro γ' hγ'
  obtain ⟨hγ, σ₀, σ₁, hu, hv, hnc⟩ := hq
  have hm := (noCross_iff h00 h01 h10 h11 σ₀ σ₁ hγ).1 hnc
  have := hm.forall_cost_le (scost u v σ₀ σ₁) (monge u v σ₀ σ₁ hu hv)
    (TransportMatrix.ofRealFun (fr_mem h00 h01 h10 h11 σ₀ σ₁ hγ'))
  rw [TransportMatrix.cost_ofRealFun, TransportMatrix.cost_ofRealFun] at this
  rw [pcost_fr u v σ₀ σ₁, pcost_fr u v σ₀ σ₁]
  exact this

lemma noCross_mono {σ₀ : Equiv.Perm (Fin n₀)} {σ₁ : Equiv.Perm (Fin n₁)}
    {γ γ' : Fin n₀ → Fin n₁ → ℝ} (hsub : ∀ i j, γ' i j ≠ 0 → γ i j ≠ 0)
    (h : NoCross σ₀ σ₁ γ) : NoCross σ₀ σ₁ γ' :=
  fun _ _ _ _ hk e1 e2 => h hk (hsub _ _ e1) (hsub _ _ e2)

/-- In an open segment of nonnegative arrays, the endpoints are supported in the support of the
point. -/
lemma support_of_openSegment {γ x₁ x₂ : Fin n₀ → Fin n₁ → ℝ} (h1 : ∀ i j, 0 ≤ x₁ i j)
    (h2 : ∀ i j, 0 ≤ x₂ i j) (hseg : γ ∈ openSegment ℝ x₁ x₂) :
    (∀ i j, x₁ i j ≠ 0 → γ i j ≠ 0) ∧ (∀ i j, x₂ i j ≠ 0 → γ i j ≠ 0) := by
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hseg
  constructor
  · intro i j hx
    have hpos : 0 < x₁ i j := lt_of_le_of_ne (h1 i j) (Ne.symm hx)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_nonneg hb.le (h2 i j)
    nlinarith [mul_pos ha hpos]
  · intro i j hx
    have hpos : 0 < x₂ i j := lt_of_le_of_ne (h2 i j) (Ne.symm hx)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_nonneg ha.le (h1 i j)
    nlinarith [mul_pos hb hpos]

include h00 h01 h10 h11 in
theorem quantile_extreme {u : Fin n₀ → ℝ} {v : Fin n₁ → ℝ} {γ : Fin n₀ → Fin n₁ → ℝ}
    (hq : IsQuantileCoupling a₀ a₁ u v γ) : γ ∈ Set.extremePoints ℝ (Plans a₀ a₁) := by
  obtain ⟨hγ, σ₀, σ₁, -, -, hnc⟩ := hq
  rw [mem_extremePoints]
  refine ⟨hγ, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩
  obtain ⟨s1, s2⟩ := support_of_openSegment hx₁.1 hx₂.1 hseg
  exact ⟨noCross_unique h00 h01 h10 h11 σ₀ σ₁ hx₁ hγ (noCross_mono s1 hnc) hnc,
    noCross_unique h00 h01 h10 h11 σ₀ σ₁ hx₂ hγ (noCross_mono s2 hnc) hnc⟩

end Quantile

/-! ### Finitely many vertices -/

section Vertices

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}

lemma exists_pos_lower (γ : Fin n₀ → Fin n₁ → ℝ) (h0 : ∀ i j, 0 ≤ γ i j) :
    ∃ ε > 0, ∀ i j, γ i j ≠ 0 → ε ≤ γ i j := by
  classical
  let s := (Finset.univ : Finset (Fin n₀ × Fin n₁)).filter (fun q => γ q.1 q.2 ≠ 0)
  by_cases hs : s.Nonempty
  · obtain ⟨q, hq, hmin⟩ := s.exists_mem_eq_inf' hs (fun q => γ q.1 q.2)
    have hq' : γ q.1 q.2 ≠ 0 := (Finset.mem_filter.1 hq).2
    refine ⟨γ q.1 q.2, lt_of_le_of_ne (h0 _ _) (Ne.symm hq'), fun i j hij => ?_⟩
    rw [← hmin]
    exact Finset.inf'_le (f := fun q : Fin n₀ × Fin n₁ => γ q.1 q.2) (b := (i, j))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)
  · refine ⟨1, one_pos, fun i j hij => ?_⟩
    exact absurd ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩⟩ hs

/-- An extreme point of the transport polytope is the only plan supported in its support. -/
theorem extreme_eq_of_support {γ γ' : Fin n₀ → Fin n₁ → ℝ}
    (hγ : γ ∈ Set.extremePoints ℝ (Plans a₀ a₁)) (hγ' : γ' ∈ Plans a₀ a₁)
    (hsub : ∀ i j, γ' i j ≠ 0 → γ i j ≠ 0) : γ' = γ := by
  have hP := hγ.1
  obtain ⟨ε, hε, hεle⟩ := exists_pos_lower γ hP.1
  set M : ℝ := 1 + ∑ i, ∑ j, γ' i j with hM
  have hsumnn : 0 ≤ ∑ i, ∑ j, γ' i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hγ'.1 i j
  have hMpos : 0 < M := by linarith
  have hentry : ∀ i j, γ' i j ≤ M := by
    intro i j
    have h1 : γ' i j ≤ ∑ j, γ' i j :=
      Finset.single_le_sum (fun j _ => hγ'.1 i j) (Finset.mem_univ j)
    have h2 : ∑ j, γ' i j ≤ ∑ i, ∑ j, γ' i j :=
      Finset.single_le_sum (f := fun i => ∑ j, γ' i j)
        (fun i _ => Finset.sum_nonneg fun j _ => hγ'.1 i j) (Finset.mem_univ i)
    linarith
  set t : ℝ := ε / M with ht
  have htpos : 0 < t := div_pos hε hMpos
  let z : Fin n₀ → Fin n₁ → ℝ := fun i j => γ i j + t * (γ i j - γ' i j)
  have hz : z ∈ Plans a₀ a₁ := by
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · by_cases h : γ i j = 0
      · have h' : γ' i j = 0 := by
          by_contra hne; exact hsub i j hne h
        simp [z, h, h']
      · have h1 := hεle i j h
        have h2 : t * γ' i j ≤ ε := by
          calc t * γ' i j ≤ t * M := mul_le_mul_of_nonneg_left (hentry i j) htpos.le
            _ = ε := by rw [ht]; field_simp
        simp only [z]
        nlinarith [hP.1 i j]
    · simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        hP.2.1 i, hγ'.2.1 i]
      ring
    · simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        hP.2.2 j, hγ'.2.2 j]
      ring
  have hseg : γ ∈ openSegment ℝ z γ' := by
    refine ⟨1 / (1 + t), t / (1 + t), by positivity, by positivity, by field_simp, ?_⟩
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, z]
    field_simp
    ring
  exact ((mem_extremePoints.1 hγ).2 z hz γ' hγ' hseg).2

theorem extreme_finite : (Set.extremePoints ℝ (Plans a₀ a₁)).Finite := by
  apply Set.Finite.of_finite_image (f := fun γ : Fin n₀ → Fin n₁ → ℝ =>
    {q : Fin n₀ × Fin n₁ | γ q.1 q.2 ≠ 0}) (Set.toFinite _)
  intro γ hγ γ' hγ' hsupp
  simp only at hsupp
  have hsub : ∀ i j, γ' i j ≠ 0 → γ i j ≠ 0 := by
    intro i j h
    have : (i, j) ∈ {q : Fin n₀ × Fin n₁ | γ' q.1 q.2 ≠ 0} := h
    rw [← hsupp] at this
    exact this
  exact (extreme_eq_of_support hγ hγ'.1 hsub).symm

end Vertices

/-! ### Uniqueness of the optimal coupling under distinct projections -/

section Unique

variable {a₀ : Fin n₀ → ℝ} {a₁ : Fin n₁ → ℝ}
variable (h00 : ∀ i, 0 ≤ a₀ i) (h01 : ∑ i, a₀ i = 1) (h10 : ∀ j, 0 ≤ a₁ j)
  (h11 : ∑ j, a₁ j = 1)

lemma entry_le_row {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) (i j) : γ i j ≤ a₀ i := by
  rw [← hγ.2.1 i]; exact Finset.single_le_sum (fun j _ => hγ.1 i j) (Finset.mem_univ j)

lemma entry_le_col {γ : Fin n₀ → Fin n₁ → ℝ} (hγ : γ ∈ Plans a₀ a₁) (i j) : γ i j ≤ a₁ j := by
  rw [← hγ.2.2 j]; exact Finset.single_le_sum (fun i _ => hγ.1 i j) (Finset.mem_univ i)

include h00 h01 h10 h11 in
/-- With projections pairwise distinct on the support of each centre, an optimal coupling does not
cross in the canonical sorted order. -/
theorem optimal_noCross_sort {u : Fin n₀ → ℝ} {v : Fin n₁ → ℝ} {γ : Fin n₀ → Fin n₁ → ℝ}
    (hγ : γ ∈ Plans a₀ a₁) (hopt : ∀ γ' ∈ Plans a₀ a₁, pcost u v γ ≤ pcost u v γ')
    (hu : ∀ i k, i ≠ k → 0 < a₀ i → 0 < a₀ k → u i ≠ u k)
    (hv : ∀ j l, j ≠ l → 0 < a₁ j → 0 < a₁ l → v j ≠ v l) :
    NoCross (Tuple.sort u) (Tuple.sort v) γ := by
  classical
  set σ₀ := Tuple.sort u
  set σ₁ := Tuple.sort v
  intro k₁ k₂ l₁ l₂ hk e1 e2
  by_contra hl
  have hl : l₂ < l₁ := lt_of_not_ge hl
  set A := TransportMatrix.ofRealFun (fr_mem h00 h01 h10 h11 σ₀ σ₁ hγ) with hA
  have hAf : A.toRealFun = fr σ₀ σ₁ γ := TransportMatrix.toRealFun_ofRealFun _
  -- cells: (i₁, j₁) = (k₁, l₂), (i₂, j₂) = (k₂, l₁); crossing cells (k₁, l₁), (k₂, l₂)
  obtain ⟨B, δ, -, hδ, hB⟩ := A.exists_uncross (i₁ := k₁) (i₂ := k₂) (j₁ := l₂) (j₂ := l₁)
  have hcost := A.cost_eq_of_uncross_update B (scost u v σ₀ σ₁) δ k₁ k₂ l₂ l₁ hB
  have p1 : 0 < γ (σ₀ k₁) (σ₁ l₁) := lt_of_le_of_ne (hγ.1 _ _) (Ne.symm e1)
  have p2 : 0 < γ (σ₀ k₂) (σ₁ l₂) := lt_of_le_of_ne (hγ.1 _ _) (Ne.symm e2)
  have hδpos : 0 < δ := by
    rw [hδ, hAf]; exact lt_min p1 p2
  have hu1 : u (σ₀ k₁) < u (σ₀ k₂) := by
    refine lt_of_le_of_ne (Tuple.monotone_sort u hk.le) ?_
    exact hu _ _ (fun h => hk.ne (σ₀.injective h))
      (lt_of_lt_of_le p1 (entry_le_row hγ _ _)) (lt_of_lt_of_le p2 (entry_le_row hγ _ _))
  have hv1 : v (σ₁ l₂) < v (σ₁ l₁) := by
    refine lt_of_le_of_ne (Tuple.monotone_sort v hl.le) ?_
    exact hv _ _ (fun h => hl.ne (σ₁.injective h))
      (lt_of_lt_of_le p2 (entry_le_col hγ _ _)) (lt_of_lt_of_le p1 (entry_le_col hγ _ _))
  have hbr : scost u v σ₀ σ₁ (k₁, l₂) + scost u v σ₀ σ₁ (k₂, l₁) - scost u v σ₀ σ₁ (k₁, l₁) -
      scost u v σ₀ σ₁ (k₂, l₂) < 0 := by
    simp only [scost]
    nlinarith [mul_pos (sub_pos.2 hu1) (sub_pos.2 hv1)]
  have hlt : B.cost (scost u v σ₀ σ₁) < A.cost (scost u v σ₀ σ₁) := by
    rw [hcost]; nlinarith [mul_neg_of_pos_of_neg hδpos hbr]
  -- back to a plan
  have hBmem := unfr_mem h00 h01 h10 h11 σ₀ σ₁ B.toRealFun_mem_realPlans
  have := hopt _ hBmem
  rw [pcost_fr u v σ₀ σ₁, pcost_fr u v σ₀ σ₁ (unfr σ₀ σ₁ B.toRealFun), fr_unfr] at this
  rw [TransportMatrix.cost_def, TransportMatrix.cost_def, hAf] at hlt
  linarith

include h00 h01 h10 h11 in
/-- With projections pairwise distinct on the support of each centre, the optimal coupling is
unique. -/
theorem optimal_unique {u : Fin n₀ → ℝ} {v : Fin n₁ → ℝ} {γ γ' : Fin n₀ → Fin n₁ → ℝ}
    (hγ : γ ∈ Plans a₀ a₁) (hopt : ∀ g ∈ Plans a₀ a₁, pcost u v γ ≤ pcost u v g)
    (hγ' : γ' ∈ Plans a₀ a₁) (hopt' : ∀ g ∈ Plans a₀ a₁, pcost u v γ' ≤ pcost u v g)
    (hu : ∀ i k, i ≠ k → 0 < a₀ i → 0 < a₀ k → u i ≠ u k)
    (hv : ∀ j l, j ≠ l → 0 < a₁ j → 0 < a₁ l → v j ≠ v l) : γ = γ' :=
  noCross_unique h00 h01 h10 h11 _ _ hγ hγ'
    (optimal_noCross_sort h00 h01 h10 h11 hγ hopt hu hv)
    (optimal_noCross_sort h00 h01 h10 h11 hγ' hopt' hu hv)

end Unique

end StatFormal.RobustEquality.Paper2.Alternating.Route
