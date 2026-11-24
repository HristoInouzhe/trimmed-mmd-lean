import StatFormal.Lib.Potentials.Stability

/-!
# Automatic local bounds for potentials, and stability without compactness

Library component (potential-level OT limit theory, part 5). Untrusted library code; no frozen
statement is touched.

`Stability.lean` assumes the potentials `uᵢ` are pointwise eventually bounded on `U`. Here this is
**derived** from plan convergence and a one-point normalisation, so that no Lipschitz bound, no
compact target support and no Arzelà–Ascoli argument is needed: if `πᵢ → π` weakly, `U` is open
and convex with `U ⊆ supp (π.fst)`, the `uᵢ` are convex potentials of the `πᵢ` over `U` and
`uᵢ x₀ → a`, then the `uᵢ` are eventually bounded at each point of `U`.

Upper bound at `p ∈ U`: surround `p` by finitely many points `p + r w` (`w` in a finite net of
the unit ball, `exists_finite_net_neg`); each small ball around them times a large ball in the
target carries mass for `π`, hence eventually for `πᵢ`, hence contains a support point `(x, y)` of
`πᵢ`; there `uᵢ x ≤ uᵢ x₀ + ‖y‖ ‖x − x₀‖` (subgradient inequality) is bounded, and `p` lies in the
convex hull of these `x` (`mem_convexHull_of_near_net`, Hahn–Banach), so Jensen bounds `uᵢ p`.
Lower bound: convexity along the line through `p` and `x₀`.

## Main results

* `eventually_le_of_tendsto_plan`, `eventually_abs_le_of_tendsto_plan`: the local bounds.
* `tendsto_potential_of_tendsto_plan`, `tendstoLocallyUniformlyOn_potential_of_tendsto_plan`,
  `ae_tendsto_gradient_potential_of_tendsto_plan`: the stability theorems of `Stability.lean`
  without the boundedness hypothesis.
* `exists_tendstoLocallyUniformlyOn_potential`: moreover a limit potential exists — the `uᵢ`
  converge locally uniformly on `U` to a convex `φ` with `φ x₀ = a`, a potential of `π` over `U`,
  whose gradient is the plan's second coordinate (`π`-a.e. `y = ∇φ x`, the Brenier map).

This is the potential part of otfd-C `prop:conditional-potentials` (source `μ_K` with convex
support `𝒰_K`, `U = int 𝒰_K`, `μ_K (∂𝒰_K) = 0`), with the plan convergence as input.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology Gradient InnerProductSpace

namespace StatFormal.Potentials

section Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A finite net of the unit ball detecting every functional.** In a finite-dimensional real
normed space there is a finite set `W` of vectors of norm `≤ 1` such that every continuous
linear functional `f` satisfies `f w ≤ −‖f‖/2` for some `w ∈ W`. -/
theorem exists_finite_net_neg :
    ∃ W : Set E, W.Finite ∧ W ⊆ closedBall 0 1 ∧
      ∀ f : StrongDual ℝ E, ∃ w ∈ W, f w ≤ -(‖f‖ / 2) := by
  obtain ⟨W, hWsub, hWfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : E) 1) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨W, hWfin, hWsub, fun f => ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨w, hw, -⟩ := mem_iUnion₂.1 (hcover (mem_closedBall_self zero_le_one))
    exact ⟨w, hw, by simp⟩
  have hpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  obtain ⟨x, hx1, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (r := 3 / 4 * ‖f‖) (by linarith)
  rw [Real.norm_eq_abs] at hfx
  set v : E := if 0 ≤ f x then -x else x with hv
  have hv1 : ‖v‖ ≤ 1 := by
    by_cases h : 0 ≤ f x
    · simp only [hv, h, ite_true, norm_neg]; exact hx1.le
    · simp only [hv, h, ite_false]; exact hx1.le
  have hfv : f v ≤ -(3 / 4 * ‖f‖) := by
    by_cases h : 0 ≤ f x
    · simp only [hv, h, ite_true, map_neg]; rw [abs_of_nonneg h] at hfx; linarith
    · simp only [hv, h, ite_false]; rw [abs_of_neg (not_le.1 h)] at hfx; linarith
  obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.1 (hcover (mem_closedBall_zero_iff.2 hv1))
  refine ⟨w, hw, ?_⟩
  have hsplit : f w = f v + f (w - v) := by rw [map_sub]; ring
  have hwv : ‖w - v‖ ≤ 1 / 4 := by
    rw [← dist_eq_norm, dist_comm]; exact (mem_ball.1 hvw).le
  have h2 : f (w - v) ≤ ‖f‖ * (1 / 4) :=
    calc f (w - v) ≤ |f (w - v)| := le_abs_self _
      _ = ‖f (w - v)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖w - v‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (1 / 4) := mul_le_mul_of_nonneg_left hwv hpos.le
  linarith

variable {E}

omit [FiniteDimensional ℝ E] in
/-- **Points near a scaled net surround the centre.** With `W` as in `exists_finite_net_neg`, if
`r > 0` and `‖x w − (p + r w)‖ ≤ r/4` for every `w ∈ W`, then `p` lies in the convex hull of
`{x w | w ∈ W}` (else a separating functional `f` would satisfy `f p < f (x w)` for all `w`,
contradicting `f w ≤ −‖f‖/2`). -/
theorem mem_convexHull_of_near_net {W : Set E} (hWfin : W.Finite)
    (hW : ∀ f : StrongDual ℝ E, ∃ w ∈ W, f w ≤ -(‖f‖ / 2)) {p : E} {r : ℝ} (hr : 0 < r)
    {x : E → E} (hx : ∀ w ∈ W, ‖x w - (p + r • w)‖ ≤ r / 4) : p ∈ convexHull ℝ (x '' W) := by
  by_contra hp
  have hclosed : IsClosed (convexHull ℝ (x '' W)) :=
    ((hWfin.image x).isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hclosed hp
  obtain ⟨w, hw, hfw⟩ := hW f
  have hlt := hb (x w) (subset_convexHull ℝ _ (mem_image_of_mem x hw))
  have hsplit : f (x w) = f p + r * f w + f (x w - (p + r • w)) := by
    rw [map_sub, map_add, map_smul, smul_eq_mul]; ring
  have herr : f (x w - (p + r • w)) ≤ ‖f‖ * (r / 4) :=
    calc f (x w - (p + r • w)) ≤ |f (x w - (p + r • w))| := le_abs_self _
      _ = ‖f (x w - (p + r • w))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖x w - (p + r • w)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (r / 4) := mul_le_mul_of_nonneg_left (hx w hw) (norm_nonneg _)
  have hrf : r * f w ≤ -(r * (‖f‖ / 2)) := by nlinarith
  nlinarith [norm_nonneg f]

end Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Eventual upper bound for normalised potentials.** Let `πᵢ → π` weakly along `l`
(probability measures on `E × E`), `U` open with `U ⊆ supp (π.fst)`, `uᵢ` eventually
convex on `U` (so `U` is convex) and eventually potentials of `πᵢ` over `U`, and `uᵢ x₀ → a`
for some `x₀ ∈ U`. Then for every `p ∈ U` there is `M` with `uᵢ p ≤ M` eventually. -/
theorem eventually_le_of_tendsto_plan {ι : Type*} {l : Filter ι} {U : Set E} (hU : IsOpen U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {x₀ : E} (hx₀ : x₀ ∈ U) {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {p : E} (hp : p ∈ U) : ∃ M, ∀ᶠ i in l, us i p ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
  set r : ℝ := ε / 3 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨W, hWfin, hWball, hW⟩ := exists_finite_net_neg E
  set c : E → E := fun w => p + r • w with hc
  have hcball : ∀ w ∈ W, dist (c w) p ≤ r := by
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 (hWball hw)
    rw [hc, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  -- each small ball around `c w`, times a large target ball, carries `π`-mass
  have hmass : ∀ w ∈ W, ∃ n : ℕ,
      0 < π.toMeasure (ball (c w) (r / 4) ×ˢ ball (0 : E) n) := by
    intro w hw
    have hcU : c w ∈ U := hεU (mem_ball.2 ((hcball w hw).trans_lt (by linarith)))
    have hpos : 0 < π.toMeasure.fst (ball (c w) (r / 4)) :=
      (Measure.mem_support_iff_forall _).1 (hsupp hcU) _ (ball_mem_nhds _ (by positivity))
    rw [Measure.fst_apply measurableSet_ball] at hpos
    by_contra hcon
    push Not at hcon
    have hunion : Prod.fst ⁻¹' ball (c w) (r / 4) =
        ⋃ n : ℕ, ball (c w) (r / 4) ×ˢ ball (0 : E) n := by
      ext z
      simp only [mem_preimage, mem_iUnion, mem_prod, mem_ball_zero_iff]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_gt ‖z.2‖
        exact ⟨n, hz, hn⟩
      · rintro ⟨n, hz, -⟩; exact hz
    rw [hunion, measure_iUnion_null fun n => le_antisymm (hcon n) zero_le] at hpos
    exact lt_irrefl _ hpos
  choose! n hn using hmass
  set N : ℝ := ∑ w ∈ hWfin.toFinset, (n w : ℝ) with hN
  have hnN : ∀ w ∈ W, (n w : ℝ) ≤ N := fun w hw =>
    Finset.single_le_sum (f := fun w => (n w : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (hWfin.mem_toFinset.2 hw)
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hev : ∀ᶠ i in l, ∀ w ∈ W,
      0 < (πs i).toMeasure (ball (c w) (r / 4) ×ˢ ball (0 : E) (n w)) :=
    (eventually_all_finite hWfin).2 fun w hw =>
      OTLimits.eventually_pos_measure_of_tendsto hπ (isOpen_ball.prod isOpen_ball) (hn w hw)
  refine ⟨a + 1 + N * (‖x₀ - p‖ + 2 * r), ?_⟩
  filter_upwards [hev, hconv, hpot, hnorm.eventually (gt_mem_nhds (lt_add_one a))]
    with i hi hci hpi hai
  choose! z hzA hzs using fun w hw => Measure.nonempty_inter_support_of_pos (hi w hw)
  have hz1 : ∀ w ∈ W, dist (z w).1 (c w) < r / 4 := fun w hw => (hzA w hw).1
  have hz2 : ∀ w ∈ W, ‖(z w).2‖ < n w := fun w hw => mem_ball_zero_iff.1 (hzA w hw).2
  have hzp : ∀ w ∈ W, dist (z w).1 p < 2 * r := fun w hw => by
    linarith [dist_triangle (z w).1 (c w) p, hz1 w hw, hcball w hw]
  have hzU : ∀ w ∈ W, (z w).1 ∈ U := fun w hw =>
    hεU (mem_ball.2 ((hzp w hw).trans (by linarith)))
  have hval : ∀ w ∈ W, us i (z w).1 ≤ a + 1 + N * (‖x₀ - p‖ + 2 * r) := by
    intro w hw
    have h1 := hpi (z w) (hzs w hw) (hzU w hw) x₀ hx₀
    have h2 : -⟪(z w).2, x₀ - (z w).1⟫_ℝ ≤ ‖(z w).2‖ * ‖x₀ - (z w).1‖ := by
      have := abs_real_inner_le_norm (z w).2 (x₀ - (z w).1)
      linarith [neg_abs_le ⟪(z w).2, x₀ - (z w).1⟫_ℝ]
    have h3 : ‖x₀ - (z w).1‖ ≤ ‖x₀ - p‖ + 2 * r := by
      have := norm_sub_le_norm_sub_add_norm_sub x₀ p (z w).1
      rw [← dist_eq_norm p, dist_comm] at this
      linarith [hzp w hw]
    have h4 : ‖(z w).2‖ * ‖x₀ - (z w).1‖ ≤ N * (‖x₀ - p‖ + 2 * r) :=
      mul_le_mul ((hz2 w hw).le.trans (hnN w hw)) h3 (norm_nonneg _) hN0
    linarith
  have hhull : p ∈ convexHull ℝ ((fun w => (z w).1) '' W) := by
    refine mem_convexHull_of_near_net hWfin hW hr fun w hw => ?_
    rw [← dist_eq_norm]
    exact (hz1 w hw).le
  obtain ⟨y, ⟨w, hw, rfl⟩, hy⟩ :=
    hci.exists_ge_of_mem_convexHull (by rintro _ ⟨w, hw, rfl⟩; exact hzU w hw) hhull
  exact hy.trans (hval w hw)

/-- **Eventual two-sided bound for normalised potentials.** Under the hypotheses of
`eventually_le_of_tendsto_plan`, for every `p ∈ U` there is `M` with `|uᵢ p| ≤ M` eventually.
(Lower bound from convexity along the line through `p` and `x₀`, using the upper bound at a point
`q ∈ U` beyond `x₀`.) -/
theorem eventually_abs_le_of_tendsto_plan {ι : Type*} {l : Filter ι} {U : Set E}
    (hU : IsOpen U) {πs : ι → ProbabilityMeasure (E × E)}
    {π : ProbabilityMeasure (E × E)} (hπ : Tendsto πs l (𝓝 π))
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {x₀ : E} (hx₀ : x₀ ∈ U) {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {p : E} (hp : p ∈ U) : ∃ M, ∀ᶠ i in l, |us i p| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := eventually_le_of_tendsto_plan hU hπ hsupp hconv hpot hx₀ hnorm hp
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set ε : ℝ := δ / (2 * (‖x₀ - p‖ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set q : E := x₀ + ε • (x₀ - p) with hq
  have hqU : q ∈ U := by
    refine hδU (mem_ball.2 ?_)
    rw [hq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have h1 : ε * ‖x₀ - p‖ ≤ ε * (‖x₀ - p‖ + 1) := by nlinarith
    have h2 : ε * (‖x₀ - p‖ + 1) = δ / 2 := by
      rw [hεdef]; field_simp
    linarith
  obtain ⟨M₂, hM₂⟩ := eventually_le_of_tendsto_plan hU hπ hsupp hconv hpot hx₀ hnorm hqU
  set α : ℝ := (1 + ε)⁻¹ with hα
  set β : ℝ := ε * (1 + ε)⁻¹ with hβ
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hαβ : α + β = 1 := by rw [hα, hβ]; field_simp
  have hcomb : α • q + β • p = x₀ := by
    have hαε : α + α * ε = 1 := by rw [hα]; field_simp
    calc α • q + β • p = (α + α * ε) • x₀ + (β - α * ε) • p := by
          rw [hq]; simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]; abel
      _ = x₀ := by
          rw [hαε, show β - α * ε = 0 by rw [hα, hβ]; ring, zero_smul, one_smul, add_zero]
  refine ⟨max M₁ (-(((a - 1) - α * M₂) / β)), ?_⟩
  filter_upwards [hM₁, hM₂, hconv, hnorm.eventually (lt_mem_nhds (sub_one_lt a))]
    with i h1 h2 hci hai
  have hJ := hci.2 hqU hp hα0.le hβ0.le hαβ
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hJ
  have hlow : ((a - 1) - α * M₂) / β ≤ us i p := by
    rw [div_le_iff₀ hβ0]
    nlinarith
  exact abs_le.2 ⟨by linarith [le_max_right M₁ (-(((a - 1) - α * M₂) / β))],
    h1.trans (le_max_left _ _)⟩

/-- **Stability of normalised potentials, without boundedness assumptions** (Villani, *Optimal
Transport*, Thm 5.20, potential part; otfd-C `prop:conditional-potentials`). Let `ρ` be an
additive Haar measure on the finite-dimensional inner product space `E`, `U` open with
`x₀ ∈ U`, `πᵢ → π` weakly along `l`, and let `μ = π.fst` satisfy `μ ≪ ρ`, `μ Uᶜ = 0` and
`U ⊆ supp μ`. Let `uᵢ` be eventually convex on `U` and eventually potentials of `πᵢ` over `U`,
normalised by `uᵢ x₀ → a`, and let `φ` be convex on `U` and a potential of `π` over `U`. Then
`uᵢ x → φ x − φ x₀ + a` for every `x ∈ U`. -/
theorem tendsto_potential_of_tendsto_plan {ι : Type*} {l : Filter ι} {ρ : Measure E}
    [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (φ x - φ x₀ + a)) :=
  tendsto_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp hconv hpot
    (fun _ hp => eventually_abs_le_of_tendsto_plan hU hπ hsupp hconv hpot hx₀ hnorm hp)
    hnorm hφ hpφ

/-- **Locally uniform convergence of normalised potentials, without boundedness assumptions.**
Under the hypotheses of `tendsto_potential_of_tendsto_plan`, `uᵢ → φ − φ x₀ + a` uniformly on
compact subsets of `U`. -/
theorem tendstoLocallyUniformlyOn_potential_of_tendsto_plan {ι : Type*} {l : Filter ι}
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    TendstoLocallyUniformlyOn us (fun x => φ x - φ x₀ + a) l U :=
  StatFormal.Convex.tendstoLocallyUniformlyOn_of_tendsto hU hconv
    (tendsto_potential_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp hconv hpot hnorm hφ hpφ)

/-- **A.e. convergence of the maps, without boundedness assumptions.** Under the hypotheses of
`tendsto_potential_of_tendsto_plan`, along a countable index type with every `uₙ` convex on `U`,
`∇uₙ → ∇φ` at `ρ`-a.e. point of `U`. -/
theorem ae_tendsto_gradient_potential_of_tendsto_plan {ι : Type*} [Countable ι] {l : Filter ι}
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ i, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a))
    {φ : E → ℝ} (hφ : ConvexOn ℝ U φ) (hpφ : IsPotentialOn U φ π.toMeasure) :
    ∀ᵐ y ∂ρ, y ∈ U → Tendsto (fun i => ∇ (us i) y) l (𝓝 (∇ φ y)) :=
  ae_tendsto_gradient_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp hconv hpot
    (fun _ hp => eventually_abs_le_of_tendsto_plan hU hπ hsupp
      (Eventually.of_forall hconv) hpot hx₀ hnorm hp) hnorm hφ hpφ

/-- **Existence of the limit potential and convergence to it** (no limit potential assumed).
Let `l` be a nontrivial filter, `πᵢ → π` weakly, `μ = π.fst ≪ ρ` (Haar), `U` open with
`μ Uᶜ = 0` and `U ⊆ supp μ`, `x₀ ∈ U`, and `uᵢ` eventually convex on `U`, eventually
potentials of `πᵢ` over `U`, with `uᵢ x₀ → a`. Then there is `φ`, convex on `U` with
`φ x₀ = a` and a potential of `π` over `U`, such that `uᵢ → φ` locally uniformly on `U`, and
`y = ∇φ x` for `π`-a.e. `(x, y)` with `x ∈ U` (so `∇φ` is the Brenier map of the limit plan). -/
theorem exists_tendstoLocallyUniformlyOn_potential {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρ : Measure E} [ρ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hμ : π.toMeasure.fst ≪ ρ) (hUc : π.toMeasure.fst Uᶜ = 0)
    (hsupp : U ⊆ π.toMeasure.fst.support)
    {us : ι → E → ℝ} (hconv : ∀ᶠ i in l, ConvexOn ℝ U (us i))
    (hpot : ∀ᶠ i in l, IsPotentialOn U (us i) (πs i).toMeasure)
    {a : ℝ} (hnorm : Tendsto (fun i => us i x₀) l (𝓝 a)) :
    ∃ φ : E → ℝ, ConvexOn ℝ U φ ∧ φ x₀ = a ∧ IsPotentialOn U φ π.toMeasure ∧
      (∀ᵐ z ∂π.toMeasure, z.1 ∈ U → z.2 = ∇ φ z.1) ∧ TendstoLocallyUniformlyOn us φ l U := by
  have hbdd : ∀ x ∈ U, ∃ M, ∀ᶠ i in l, |us i x| ≤ M := fun _ hp =>
    eventually_abs_le_of_tendsto_plan hU hπ hsupp hconv hpot hx₀ hnorm hp
  obtain ⟨g, hlimg⟩ := exists_tendsto_ultrafilter hbdd (Ultrafilter.of l) (Ultrafilter.of_le l)
  have h𝒰 : (Ultrafilter.of l : Filter ι) ≤ l := Ultrafilter.of_le l
  have hgc : ConvexOn ℝ U g := StatFormal.Convex.convexOn_of_tendsto (h𝒰 hconv) hlimg
  have hgpot : IsPotentialOn U g π.toMeasure :=
    isPotentialOn_of_tendsto hU (h𝒰 hconv) hlimg (hπ.mono_left h𝒰) (h𝒰 hpot)
  have hg0 : g x₀ = a := tendsto_nhds_unique (hlimg x₀ hx₀) (hnorm.mono_left h𝒰)
  have hlim := tendsto_potential_of_tendsto_plan hU hx₀ hπ hμ hUc hsupp hconv hpot hnorm hgc hgpot
  have hlim' : ∀ x ∈ U, Tendsto (fun i => us i x) l (𝓝 (g x)) := fun x hx => by
    have := hlim x hx
    rwa [hg0, sub_add_cancel] at this
  exact ⟨g, hgc, hg0, hgpot, ae_snd_eq_gradient_of_isPotentialOn hU hgc hμ hgpot,
    StatFormal.Convex.tendstoLocallyUniformlyOn_of_tendsto hU hconv hlim'⟩

end StatFormal.Potentials
