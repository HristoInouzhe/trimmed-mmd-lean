import StatFormal.Lib.OTLimits.Quadratic
import TauCeti.MeasureTheory.OptimalTransport.MeasurableSelection
import TauCeti.MeasureTheory.OptimalTransport.Disintegration

/-!
# Brenier uniqueness in a separable Hilbert space for laws that ignore Lipschitz hypersurfaces

Library component (potential-level OT limit theory, part 6). Untrusted library code; no frozen
statement is touched.

Let `H` be a separable real Hilbert space and `P` a finite Borel measure on `H` giving zero mass
to every **Lipschitz hypersurface** `A_w(τ) = {z + τ z • w : ⟪z, w⟫ = 0}` (`w ≠ 0`, `τ` Lipschitz
on `w^⊥`) — the class `𝒫^ℓ(H)` of Gigli / GHS, otfd-A `def:ghs-rank`; the definitions `lipGraph`,
`IsLipGraph` below are verbatim copies of the frozen `OTFD.Wave1.lipHyp`, `IsLipHyp`. Then the
optimal quadratic plan from `P` to any `ν` with finite cost is **unique and induced by a
measurable map** (Ambrosio–Gigli–Savaré, *Gradient Flows*, Thm 6.2.10).

## Proof

* Optimal plans of finite cost have support in the subdifferential graph `∂u` of a proper lsc
  convex `u : H → EReal` (Tau Ceti, Rockafellar; valid in any inner product space), so the support
  `Γ` is a **monotone** set (`isMonotoneSet_of_subset_subdifferential`).
* For a monotone `Γ`, the set of points `x` with two different `y`'s in `Γ` is covered by countably
  many Lipschitz hypersurfaces (`exists_countable_lipGraph_cover`, Zajíček / Alberti–Ambrosio):
  for a direction `w` from a countable dense set, rational levels `q ± δ` and a bound `R`, the
  points with a "low" (`⟪y₁, w⟫ ≤ q − δ`) and a "high" (`⟪y₂, w⟫ ≥ q + δ`) element, both of norm
  `≤ R`, form a graph over `w^⊥` with Lipschitz constant `R/δ` (monotonicity), which is extended
  by McShane (`exists_lipGraph_superset`). Hence `P`-a.e. fibre of `Γ` is a subsingleton
  (`measure_multivaluedSet_eq_zero`).
* A plan concentrated on `Γ` then has Dirac conditional laws and is a graph plan of a measurable
  map (`exists_eq_graphPlan_of_ae_mem`, Tau Ceti's measurable selection from Dirac kernels).
  Applied to the sum of two optimal plans (again optimal) this gives uniqueness.

## Main results

* `exists_countable_lipGraph_cover`, `measure_multivaluedSet_eq_zero`;
* `exists_eq_graphPlan_of_lipNull`: two optimal plans (finite cost) from a
  `P` null on Lipschitz hypersurfaces are the same graph plan of a measurable map;
* `exists_unique_optimal_graphPlan_of_lipNull` (**Brenier–Gigli theorem in Hilbert space**): for
  probability `P, ν` with finite second moments, there is a measurable `T` whose graph plan is
  optimal and is the only optimal plan;
* `eq_graphPlan_of_isCyclicallyMonotone_of_lipNull`: every coupling of `(P, ν)` concentrated on a
  `c`-cyclically monotone set (`c = ‖x − y‖²/2`) is that graph plan — the uniqueness hypothesis
  `BrenierUniq` of otfd-A `lem:plan-stability-H`, modulo the translation between Tau Ceti's
  permutation form of cyclical monotonicity and the cyclic-shift form `CycMon`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, §6.2 (Thm 6.2.10 and the covering of the
  multivalued set of monotone sets); N. Gigli, *On the inverse implication of Brenier–McCann
  theorems and the structure of `(P₂(M), W₂)`*, Methods Appl. Anal. 18 (2011).
* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czech. Math. J. 29 (1979).
-/

open Filter MeasureTheory Metric Set TauCeti ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace

namespace StatFormal.Potentials

section Geometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Lipschitz hypersurface `A_w(τ) = {z + τ z • w : ⟪z, w⟫ = 0}` (verbatim copy of the frozen
`OTFD.Wave1.lipHyp`). -/
def lipGraph (w : H) (τ : H → ℝ) : Set H := {x | ∃ z, ⟪z, w⟫_ℝ = 0 ∧ x = z + τ z • w}

/-- `S` is a Lipschitz hypersurface: `S = A_w(τ)` with `w ≠ 0` and `τ` Lipschitz on `w^⊥`
(verbatim copy of the frozen `OTFD.Wave1.IsLipHyp`). -/
def IsLipGraph (S : Set H) : Prop :=
  ∃ w : H, w ≠ 0 ∧ ∃ τ : H → ℝ, (∃ L, LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) ∧ S = lipGraph w τ

/-- A set `Γ ⊆ H × H` is **monotone** if `⟪y − y', x − x'⟫ ≥ 0` for `(x, y), (x', y') ∈ Γ`. -/
def IsMonotoneSet (Γ : Set (H × H)) : Prop :=
  ∀ p ∈ Γ, ∀ q ∈ Γ, 0 ≤ ⟪p.2 - q.2, p.1 - q.1⟫_ℝ

end Geometry

/-- The points over which the relation `Γ` has at least two different values. -/
def multivaluedSet {X Y : Type*} (Γ : Set (X × Y)) : Set X :=
  {x | ∃ y₁ y₂, (x, y₁) ∈ Γ ∧ (x, y₂) ∈ Γ ∧ y₁ ≠ y₂}

section Geometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Subdifferential graphs are monotone. -/
theorem isMonotoneSet_of_subset_subdifferential {u : H → EReal} {Γ : Set (H × H)}
    (hsub : Γ ⊆ {p | p.2 ∈ subdifferential (innerₗ H) u p.1}) : IsMonotoneSet Γ := by
  intro p hp q hq
  have hp' := hsub hp
  have hq' := hsub hq
  have h1 := hp'.2.2 q.1
  have h2 := hq'.2.2 p.1
  rw [← EReal.coe_toReal hp'.2.1 hp'.1, ← EReal.coe_toReal hq'.2.1 hq'.1, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h1 h2
  simp only [innerₗ_apply_apply] at h1 h2
  have : ⟪p.2 - q.2, p.1 - q.1⟫_ℝ = -(⟪q.1 - p.1, p.2⟫_ℝ + ⟪p.1 - q.1, q.2⟫_ℝ) := by
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm p.2 q.1, real_inner_comm p.2 p.1, real_inner_comm q.2 p.1,
      real_inner_comm q.2 q.1]
    ring
  rw [this]
  linarith

/-- **One "high–low" slice of the multivalued set is a Lipschitz graph.** Let `Γ` be monotone,
`w ≠ 0`, `δ > 0`, `R ≥ 0`, `q ∈ ℝ`. The points `x` carrying `y₁, y₂` with `(x, yᵢ) ∈ Γ`,
`‖yᵢ‖ ≤ R`, `⟪y₁, w⟫ ≤ q − δ` and `⟪y₂, w⟫ ≥ q + δ` lie in a Lipschitz hypersurface `A_w(τ)`;
the `w`-coordinate is an `R/δ`-Lipschitz function of the projection onto `w^⊥`. -/
theorem exists_lipGraph_superset {Γ : Set (H × H)} (hΓ : IsMonotoneSet Γ) {w : H} (hw : w ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (R : ℝ) (hR : 0 ≤ R) (q : ℝ) :
    ∃ τ : H → ℝ, (∃ L, LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) ∧
      {x | ∃ y₁ y₂, (x, y₁) ∈ Γ ∧ (x, y₂) ∈ Γ ∧ ‖y₁‖ ≤ R ∧ ‖y₂‖ ≤ R ∧
        ⟪y₁, w⟫_ℝ ≤ q - δ ∧ q + δ ≤ ⟪y₂, w⟫_ℝ} ⊆ lipGraph w τ := by
  classical
  set S : Set H := {x | ∃ y₁ y₂, (x, y₁) ∈ Γ ∧ (x, y₂) ∈ Γ ∧ ‖y₁‖ ≤ R ∧ ‖y₂‖ ≤ R ∧
    ⟪y₁, w⟫_ℝ ≤ q - δ ∧ q + δ ≤ ⟪y₂, w⟫_ℝ} with hS
  set c : ℝ := ‖w‖ ^ 2 with hc
  have hc0 : 0 < c := by have := norm_pos_iff.2 hw; positivity
  set a : H → ℝ := fun x => ⟪x, w⟫_ℝ / c with ha
  set pr : H → H := fun x => x - a x • w with hpr
  have hpr_w : ∀ x, ⟪pr x, w⟫_ℝ = 0 := by
    intro x
    simp only [hpr, ha, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hdecomp : ∀ x, x = pr x + a x • w := by intro x; simp [hpr]
  have hone : ∀ x ∈ S, ∀ x' ∈ S, -(R / δ * ‖pr x - pr x'‖) ≤ a x - a x' := by
    rintro x ⟨y₁, y₂, h1, h2, hn1, hn2, hw1, hw2⟩ x' ⟨y₁', y₂', h1', h2', hn1', hn2', hw1', hw2'⟩
    have hv : x - x' = (a x - a x') • w + (pr x - pr x') := by
      conv_lhs => rw [hdecomp x, hdecomp x']
      rw [sub_smul]; abel
    have hm : 0 ≤ (a x - a x') * ⟪y₂ - y₁', w⟫_ℝ + ⟪y₂ - y₁', pr x - pr x'⟫_ℝ := by
      have := hΓ (x, y₂) h2 (x', y₁') h1'
      simp only at this
      rwa [hv, inner_add_right, real_inner_smul_right] at this
    have hs : 2 * δ ≤ ⟪y₂ - y₁', w⟫_ℝ := by rw [inner_sub_left]; linarith
    have hb : |⟪y₂ - y₁', pr x - pr x'⟫_ℝ| ≤ 2 * R * ‖pr x - pr x'‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (by linarith [norm_sub_le y₂ y₁']) (norm_nonneg _))
    have hkey : -(2 * R * ‖pr x - pr x'‖) ≤ (a x - a x') * ⟪y₂ - y₁', w⟫_ℝ := by
      have := le_abs_self ⟪y₂ - y₁', pr x - pr x'⟫_ℝ
      linarith
    rcases le_or_gt 0 (a x - a x') with h | h
    · have : 0 ≤ R / δ * ‖pr x - pr x'‖ := by positivity
      linarith
    · have h3 : (a x - a x') * ⟪y₂ - y₁', w⟫_ℝ ≤ (a x - a x') * (2 * δ) :=
        mul_le_mul_of_nonpos_left hs h.le
      have h5 : -(R * ‖pr x - pr x'‖) ≤ (a x - a x') * δ := by linarith
      calc -(R / δ * ‖pr x - pr x'‖) = (-(R * ‖pr x - pr x'‖)) / δ := by ring
        _ ≤ ((a x - a x') * δ) / δ := div_le_div_of_nonneg_right h5 hδ.le
        _ = a x - a x' := by field_simp
  have habs : ∀ x ∈ S, ∀ x' ∈ S, |a x - a x'| ≤ R / δ * ‖pr x - pr x'‖ := by
    intro x hx x' hx'
    refine abs_le.2 ⟨hone x hx x' hx', ?_⟩
    have := hone x' hx' x hx
    rw [norm_sub_rev] at this
    linarith
  set f : H → ℝ := fun z => if h : ∃ x ∈ S, pr x = z then a h.choose else 0 with hfdef
  have hf : ∀ x ∈ S, f (pr x) = a x := by
    intro x hx
    have h : ∃ x' ∈ S, pr x' = pr x := ⟨x, hx, rfl⟩
    simp only [hfdef, h, dite_true]
    have hs := h.choose_spec
    have := habs _ hs.1 x hx
    rw [hs.2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hflip : LipschitzOnWith (R / δ).toNNReal f (pr '' S) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨x', hx', rfl⟩ := hz'
    rw [hf x hx, hf x' hx', Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact habs x hx x' hx'
  obtain ⟨g, hg, hfg⟩ := hflip.extend_real
  refine ⟨g, ⟨_, hg.lipschitzOnWith⟩, fun x hx => ⟨pr x, hpr_w x, ?_⟩⟩
  rw [← hfg (mem_image_of_mem pr hx), hf x hx]
  exact hdecomp x

/-- **The multivalued set of a monotone relation is covered by countably many Lipschitz
hypersurfaces** (Zajíček 1979; Alberti–Ambrosio 1999; AGS, *Gradient Flows*, §6.2). In a
separable real inner product space, for every monotone `Γ ⊆ H × H` there is a countable family
of Lipschitz hypersurfaces whose union contains every `x` over which `Γ` has two different
values. -/
theorem exists_countable_lipGraph_cover [TopologicalSpace.SeparableSpace H] {Γ : Set (H × H)}
    (hΓ : IsMonotoneSet Γ) :
    ∃ 𝓛 : Set (Set H), 𝓛.Countable ∧ (∀ L ∈ 𝓛, IsLipGraph L) ∧ multivaluedSet Γ ⊆ ⋃₀ 𝓛 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense H
  have : Countable D := hDc.to_subtype
  let J := {i : D × ℚ × ℚ × ℕ // (i.1 : H) ≠ 0 ∧ (0 : ℝ) < (i.2.2.1 : ℝ)}
  have hex : ∀ i : J, ∃ τ : H → ℝ, (∃ L, LipschitzOnWith L τ {z | ⟪z, (i.1.1 : H)⟫_ℝ = 0}) ∧
      {x | ∃ y₁ y₂, (x, y₁) ∈ Γ ∧ (x, y₂) ∈ Γ ∧ ‖y₁‖ ≤ (i.1.2.2.2 : ℝ) ∧
        ‖y₂‖ ≤ (i.1.2.2.2 : ℝ) ∧ ⟪y₁, (i.1.1 : H)⟫_ℝ ≤ (i.1.2.1 : ℝ) - (i.1.2.2.1 : ℝ) ∧
        (i.1.2.1 : ℝ) + (i.1.2.2.1 : ℝ) ≤ ⟪y₂, (i.1.1 : H)⟫_ℝ} ⊆ lipGraph (i.1.1 : H) τ :=
    fun i => exists_lipGraph_superset hΓ i.2.1 i.2.2 _ (Nat.cast_nonneg _) _
  choose τ hτL hτS using hex
  refine ⟨range fun i : J => lipGraph (i.1.1 : H) (τ i), countable_range _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.1.1, i.2.1, τ i, hτL i, rfl⟩
  rintro x ⟨y₁, y₂, h1, h2, hne⟩
  set u : H := y₂ - y₁ with hu
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  obtain ⟨w, hwD, hwu⟩ := hDd.exists_dist_lt u (half_pos hu0)
  have hinner : 0 < ⟪u, w⟫_ℝ := by
    have e : ⟪u, w⟫_ℝ = ‖u‖ ^ 2 + ⟪u, w - u⟫_ℝ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
    have h3 : |⟪u, w - u⟫_ℝ| ≤ ‖u‖ * ‖w - u‖ := abs_real_inner_le_norm _ _
    have h4 : ‖w - u‖ < ‖u‖ / 2 := by rw [← dist_eq_norm, dist_comm]; exact hwu
    have h5 : ‖u‖ * ‖w - u‖ ≤ ‖u‖ * (‖u‖ / 2) := mul_le_mul_of_nonneg_left h4.le hu0.le
    have := neg_abs_le ⟪u, w - u⟫_ℝ
    nlinarith
  have hw0 : w ≠ 0 := by rintro rfl; simp at hinner
  have hg : ⟪u, w⟫_ℝ = ⟪y₂, w⟫_ℝ - ⟪y₁, w⟫_ℝ := by rw [hu, inner_sub_left]
  obtain ⟨δ, hδ0, hδg⟩ := exists_rat_btwn (show (0 : ℝ) < ⟪u, w⟫_ℝ / 4 by positivity)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show ⟪y₁, w⟫_ℝ + δ < ⟪y₂, w⟫_ℝ - δ by linarith)
  set R : ℕ := ⌈max ‖y₁‖ ‖y₂‖⌉₊ with hR
  let i : J := ⟨(⟨w, hwD⟩, q, δ, R), hw0, by exact_mod_cast hδ0⟩
  refine mem_sUnion.2 ⟨_, ⟨i, rfl⟩, hτS i ⟨y₁, y₂, h1, h2, ?_, ?_, ?_, ?_⟩⟩
  · exact (le_max_left _ _).trans (Nat.le_ceil _)
  · exact (le_max_right _ _).trans (Nat.le_ceil _)
  · change ⟪y₁, w⟫_ℝ ≤ (q : ℝ) - (δ : ℝ); linarith
  · change (q : ℝ) + (δ : ℝ) ≤ ⟪y₂, w⟫_ℝ; linarith

/-- **Laws null on Lipschitz hypersurfaces see single-valued monotone relations.** If `P` gives
zero mass to every Lipschitz hypersurface of the separable space `H` and `Γ` is monotone, then
`P`-almost every point carries at most one value of `Γ`. -/
theorem measure_multivaluedSet_eq_zero [TopologicalSpace.SeparableSpace H] [MeasurableSpace H]
    {P : Measure H} (hP : ∀ S : Set H, IsLipGraph S → P S = 0) {Γ : Set (H × H)}
    (hΓ : IsMonotoneSet Γ) : P (multivaluedSet Γ) = 0 := by
  obtain ⟨𝓛, hc, hL, hcov⟩ := exists_countable_lipGraph_cover hΓ
  exact measure_mono_null hcov ((measure_sUnion_null_iff hc).2 fun L hL' => hP L (hL L hL'))

end Geometry

section Measure

/-- **A plan concentrated on an a.e. single-valued relation is a graph plan.** Let `π` be a
finite coupling of `μ` and `ν` (target standard Borel) concentrated on a measurable `Γ` such that
`μ`-a.e. point carries at most one value of `Γ`. Then `π = (id × T)#μ` for a measurable `T`
with `(x, T x) ∈ Γ` for `μ`-a.e. `x` (Dirac conditional laws, Tau Ceti's measurable
selection). -/
theorem exists_eq_graphPlan_of_ae_mem {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    [IsFiniteMeasure π] (hπ : IsCoupling π μ ν) {Γ : Set (X × Y)} (hΓm : MeasurableSet Γ)
    (hΓ : ∀ᵐ z ∂π, z ∈ Γ) (hM : μ (multivaluedSet Γ) = 0) :
    ∃ T : X → Y, Measurable T ∧ π = graphPlan T μ ∧ ∀ᵐ x ∂μ, (x, T x) ∈ Γ := by
  have : IsFiniteMeasure μ := by rw [← hπ.fst_eq]; infer_instance
  have hκ : ∀ᵐ x ∂μ, ∃ y, π.condKernel x = Measure.dirac y := by
    have h0 : π Γᶜ = 0 := ae_iff.1 hΓ
    rw [← hπ.compProd_condKernel, Measure.compProd_apply hΓm.compl] at h0
    have hmeas : Measurable fun x => π.condKernel x (Prod.mk x ⁻¹' Γᶜ) :=
      Kernel.measurable_kernel_prodMk_left hΓm.compl
    rw [lintegral_eq_zero_iff hmeas] at h0
    filter_upwards [h0, measure_eq_zero_iff_ae_notMem.1 hM] with x hx hxM
    have hx' : π.condKernel x (Prod.mk x ⁻¹' Γ)ᶜ = 0 := by
      rw [← preimage_compl]; exact hx
    have hone : π.condKernel x (Prod.mk x ⁻¹' Γ) = 1 :=
      (prob_compl_eq_zero_iff (measurable_prodMk_left hΓm)).1 hx'
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (μ := π.condKernel x)
      (by rw [hone]; exact one_ne_zero)
    have hsub : Prod.mk x ⁻¹' Γ ⊆ {y} := fun y' hy' => by
      by_contra hne
      exact hxM ⟨y, y', hy, hy', fun h => hne (h ▸ rfl)⟩
    refine ⟨y, Measure.ext fun s hs => ?_⟩
    rw [Measure.dirac_apply' y hs]
    by_cases hys : y ∈ s
    · rw [indicator_of_mem hys, Pi.one_apply]
      refine (prob_compl_eq_zero_iff hs).1 (measure_mono_null ?_ hx')
      intro y' hy' hy'Γ
      exact hy' ((mem_singleton_iff.1 (hsub hy'Γ)) ▸ hys)
    · rw [indicator_of_notMem hys]
      refine measure_mono_null ?_ hx'
      intro y' hy' hy'Γ
      exact hys ((mem_singleton_iff.1 (hsub hy'Γ)) ▸ hy')
  obtain ⟨T, hT, -, hgraph⟩ := hπ.exists_graphPlan_of_ae_exists_condKernel_eq_dirac hκ
  refine ⟨T, hT, hgraph, ?_⟩
  have h0 : graphPlan T μ Γᶜ = 0 := hgraph ▸ ae_iff.1 hΓ
  rw [graphPlan_apply hT.aemeasurable hΓm.compl] at h0
  exact ae_iff.2 h0

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

/-- **Uniqueness of optimal quadratic plans from a law null on Lipschitz hypersurfaces**
(Ambrosio–Gigli–Savaré, *Gradient Flows*, Thm 6.2.10; Gigli 2011). Let `H` be a separable real
Hilbert space, `P` a finite Borel measure giving zero mass to every Lipschitz hypersurface, and
`π, π'` optimal plans for `‖x − y‖²/2` between `P` and `ν`, with finite optimal cost. Then there
is a measurable `T : H → H` with `π = (id × T)#P = π'`. -/
theorem exists_eq_graphPlan_of_lipNull {P ν : Measure H} [IsFiniteMeasure P]
    (hP : ∀ S : Set H, IsLipGraph S → P S = 0) {π π' : Measure (H × H)}
    (h : IsOptimalCoupling (OTLimits.quadCost H) π P ν)
    (h' : IsOptimalCoupling (OTLimits.quadCost H) π' P ν)
    (hfin : transportCost (OTLimits.quadCost H) P ν ≠ ∞) :
    ∃ T : H → H, Measurable T ∧ π = graphPlan T P ∧ π' = graphPlan T P := by
  have hsum := h.add h'
  have hfin' : transportCost (OTLimits.quadCost H) (P + P) (ν + ν) ≠ ∞ := by
    rw [← hsum.lintegral_eq, lintegral_add_measure, h.lintegral_eq, h'.lintegral_eq]
    exact ENNReal.add_ne_top.2 ⟨hfin, hfin⟩
  obtain ⟨u, -, -, -, -, hsub⟩ := hsum.exists_support_subset_subdifferential hfin'
  set Γ := (π + π').support with hΓdef
  have hΓm : MeasurableSet Γ := Measure.isClosed_support.measurableSet
  have hmono : IsMonotoneSet Γ := isMonotoneSet_of_subset_subdifferential hsub
  have hM : P (multivaluedSet Γ) = 0 := measure_multivaluedSet_eq_zero hP hmono
  have hae : ∀ᵐ z ∂(π + π'), z ∈ Γ := Measure.support_mem_ae
  have hπfin : IsFiniteMeasure π :=
    ⟨by rw [← Measure.fst_univ, h.fst_eq]; exact measure_lt_top _ _⟩
  have hπfin' : IsFiniteMeasure π' :=
    ⟨by rw [← Measure.fst_univ, h'.fst_eq]; exact measure_lt_top _ _⟩
  obtain ⟨T, hT, hπT, hTΓ⟩ := exists_eq_graphPlan_of_ae_mem h.toIsCoupling hΓm
    (ae_mono (Measure.le_add_right le_rfl) hae) hM
  obtain ⟨T', -, hπT', hTΓ'⟩ := exists_eq_graphPlan_of_ae_mem h'.toIsCoupling hΓm
    (ae_mono (Measure.le_add_left le_rfl) hae) hM
  have hTT' : T =ᵐ[P] T' := by
    filter_upwards [hTΓ, hTΓ', measure_eq_zero_iff_ae_notMem.1 hM] with x h1 h2 hx
    by_contra hne
    exact hx ⟨_, _, h1, h2, hne⟩
  exact ⟨T, hT, hπT, hπT'.trans (graphPlan_congr hTT'.symm)⟩

/-- **Brenier's theorem in a separable Hilbert space for laws null on Lipschitz hypersurfaces**
(existence and uniqueness of the optimal map; AGS Thm 6.2.10). Let `P, ν` be Borel probability
measures on a separable real Hilbert space with finite second moments, `P` giving zero mass to
every Lipschitz hypersurface (the class `𝒫^ℓ(H)`). Then there is a measurable `T : H → H` whose
graph plan `(id × T)#P` is optimal for `‖x − y‖²/2`, and it is the **only** optimal plan. -/
theorem exists_unique_optimal_graphPlan_of_lipNull {P ν : Measure H} [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] (hP : ∀ S : Set H, IsLipGraph S → P S = 0)
    (hP2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂P ≠ ∞) (hν2 : ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν ≠ ∞) :
    ∃ T : H → H, Measurable T ∧ IsOptimalCoupling (OTLimits.quadCost H) (graphPlan T P) P ν ∧
      ∀ π, IsOptimalCoupling (OTLimits.quadCost H) π P ν → π = graphPlan T P := by
  have hfin := OTLimits.transportCost_quadCost_ne_top P ν hP2 hν2
  obtain ⟨π₀, hπ₀⟩ :=
    exists_isOptimalCoupling P ν OTLimits.continuous_quadCost.lowerSemicontinuous
  obtain ⟨T, hT, hπT, -⟩ := exists_eq_graphPlan_of_lipNull hP hπ₀ hπ₀ hfin
  refine ⟨T, hT, hπT ▸ hπ₀, fun π hπ => ?_⟩
  obtain ⟨T', -, h1, h2⟩ := exists_eq_graphPlan_of_lipNull hP hπ hπ₀ hfin
  rw [h1, ← h2, hπT]

/-- **Every cyclically monotone coupling is the Brenier plan** (the hypothesis `BrenierUniq` of
otfd-A `lem:plan-stability-H` / R `lem:plan-w2`, in Tau Ceti's permutation form of cyclical
monotonicity). Under the hypotheses of `exists_unique_optimal_graphPlan_of_lipNull`, with the
moments written as `MemLp id 2`, there is a measurable `T` such that every coupling `π` of
`(P, ν)` concentrated on a `c`-cyclically monotone set for `c(x, y) = ‖x − y‖²/2` equals
`(id × T)#P`. -/
theorem eq_graphPlan_of_isCyclicallyMonotone_of_lipNull {P ν : Measure H}
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hP : ∀ S : Set H, IsLipGraph S → P S = 0)
    (hP2 : MemLp id 2 P) (hν2 : MemLp id 2 ν) :
    ∃ T : H → H, Measurable T ∧ IsOptimalCoupling (OTLimits.quadCost H) (graphPlan T P) P ν ∧
      ∀ π : Measure (H × H), IsCoupling π P ν →
        (∃ S : Set (H × H), IsCyclicallyMonotone (fun p : H × H => ‖p.1 - p.2‖ ^ 2 / 2) S ∧
          ∀ᵐ z ∂π, z ∈ S) → π = graphPlan T P := by
  have hm : ∀ {μ : Measure H}, MemLp id 2 μ → ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ ≠ ∞ := fun {μ} h => by
    have e := OTLimits.lintegral_enorm_sq_eq (f := id) h.aestronglyMeasurable
    simp only [id] at e
    rw [e]
    exact ENNReal.pow_ne_top h.eLpNorm_lt_top.ne
  obtain ⟨T, hT, hopt, huniq⟩ := exists_unique_optimal_graphPlan_of_lipNull hP (hm hP2) (hm hν2)
  refine ⟨T, hT, hopt, fun π hπ ⟨S, hS, hπS⟩ => huniq π ?_⟩
  exact hπ.isOptimalCoupling_of_isCyclicallyMonotone_norm_sub_sq_div_two hP2 hν2 hS hπS

end Measure

end StatFormal.Potentials
