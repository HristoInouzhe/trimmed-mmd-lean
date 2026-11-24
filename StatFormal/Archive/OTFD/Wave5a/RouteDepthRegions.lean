import StatFormal.Archive.OTFD.Wave5a.Statements
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Route: R `prop:depth-regions`

* Optimality: `A ⊆ D_{β(A)}`, so `β(A)` belongs to the set whose supremum is `β*`. Content: some
  `α' > α` has `ν(D_{α'}) ≥ p`, and `D_{α'} ⊆ D_α`.
* Convexity: the halfspace of a convex combination contains the halfspace of the endpoint with the
  smaller value of `⟨v,·⟩`. Closedness: right-continuity of `s ↦ ν{⟨v,z⟩ ≤ s}` (continuity from above).
* Compactness (`α > 0`): tightness gives `r` with `ν{‖z‖ > r} < α`; for `‖u‖ > r` the direction `−u`
  gives `TD(u) ≤ ν{‖z‖ ≥ ‖u‖} < α` (Cauchy–Schwarz); so `D_α ⊆ B(0,r)`, closed in a proper space.
* Support function: for `0 < α < 1`, `α ≤ ν{⟨X,v⟩ ≥ s} ↔ s ≤ q_v` (left-continuity), hence
  `D_α = {u : ⟨u,w⟩ ≤ q_w ∀w}`; Hahn–Banach (`exists_extension_of_le_sublinear`) extends `t v ↦ t q_v`
  from `ℝv` to a linear `g ≤ q`, whose Riesz vector lies in `D_α` and attains `q_v`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.OTFD.Wave5a

open StatFormal.OTFD.Wave1

section Lemmas

variable {K : ℕ}

lemma mem_depthRegion_iff (ν : Measure (EuclideanSpace ℝ (Fin K))) (α : ℝ≥0∞)
    (u : EuclideanSpace ℝ (Fin K)) :
    u ∈ depthRegion ν α ↔ ∀ v : EuclideanSpace ℝ (Fin K), v ≠ 0 → α ≤ ν {z | ⟪v, z - u⟫_ℝ ≤ 0} := by
  simp only [depthRegion, tukeyDepth, Set.mem_ofPred_eq, le_iInf_iff]

lemma measurable_inner_left' (v : EuclideanSpace ℝ (Fin K)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin K) => ⟪z, v⟫_ℝ) :=
  (continuous_id.inner continuous_const).measurable

lemma measurable_inner_right' (v : EuclideanSpace ℝ (Fin K)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin K) => ⟪v, z⟫_ℝ) :=
  (continuous_const.inner continuous_id).measurable

/-- Right-continuity of a distribution function, in the form used twice below. -/
lemma le_measure_le_of_forall {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (g : X → ℝ) (hg : Measurable g) (s : ℝ) (α : ℝ≥0∞)
    (h : ∀ n : ℕ, α ≤ ν {z | g z ≤ s + 1 / ((n : ℝ) + 1)}) : α ≤ ν {z | g z ≤ s} := by
  have hset : {z | g z ≤ s} = ⋂ n : ℕ, {z | g z ≤ s + 1 / ((n : ℝ) + 1)} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hz n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hz
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have := hz n
      linarith
  have hanti : Antitone (fun n : ℕ => {z | g z ≤ s + 1 / ((n : ℝ) + 1)}) := by
    intro a b hab z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hab'
    linarith
  rw [hset, hanti.measure_iInter
    (fun n => (measurableSet_le hg measurable_const).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact le_iInf h

end Lemmas

theorem depth_regions_optimal : Claims.depth_regions_optimal := by
  intro K ν p A hA
  have hmem : regionDepth ν A ∈ {α | p ≤ ν (depthRegion ν α)} := by
    show p ≤ ν (depthRegion ν (regionDepth ν A))
    refine hA.trans (measure_mono ?_)
    intro u hu
    change regionDepth ν A ≤ tukeyDepth ν u
    exact iInf₂_le u hu
  exact le_sSup hmem

theorem depth_regions_content : Claims.depth_regions_content := by
  intro K ν p α hα
  obtain ⟨α', hα'S, hαα'⟩ := lt_sSup_iff.mp hα
  have hα'S' : p ≤ ν (depthRegion ν α') := hα'S
  refine ⟨hα'S'.trans (measure_mono ?_), ?_⟩
  · intro u hu
    exact hαα'.le.trans hu
  · exact le_iInf₂ (fun u hu => hu)

theorem depth_regions_closed_convex : Claims.depth_regions_closed_convex := by
  intro K ν _ α
  constructor
  · apply isClosed_of_closure_subset
    intro u hu
    obtain ⟨x, hxD, hxlim⟩ := mem_closure_iff_seq_limit.mp hu
    rw [mem_depthRegion_iff]
    intro v hv
    have e : {z | ⟪v, z - u⟫_ℝ ≤ 0} = {z | ⟪v, z⟫_ℝ ≤ ⟪v, u⟫_ℝ} := by
      ext z; simp only [Set.mem_ofPred_eq, inner_sub_right, sub_nonpos]
    rw [e]
    apply le_measure_le_of_forall ν _ (measurable_inner_right' v) ⟪v, u⟫_ℝ α
    intro n
    have hlim : Tendsto (fun k => ⟪v, x k⟫_ℝ) atTop (𝓝 ⟪v, u⟫_ℝ) :=
      ((continuous_const.inner continuous_id).tendsto u).comp hxlim
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (show ⟪v, u⟫_ℝ < ⟪v, u⟫_ℝ + 1 / ((n : ℝ) + 1)
      by linarith))).exists
    have hxk := (mem_depthRegion_iff ν α (x k)).mp (hxD k) v hv
    refine hxk.trans (measure_mono ?_)
    intro z hz
    simp only [Set.mem_ofPred_eq, inner_sub_right] at hz ⊢
    linarith
  · intro u hu w hw a b ha hb hab
    rw [mem_depthRegion_iff] at hu hw ⊢
    intro v hv
    have hx : ⟪v, a • u + b • w⟫_ℝ = a * ⟪v, u⟫_ℝ + b * ⟪v, w⟫_ℝ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rcases le_total ⟪v, u⟫_ℝ ⟪v, w⟫_ℝ with h | h
    · refine (hu v hv).trans (measure_mono ?_)
      intro z hz
      simp only [Set.mem_ofPred_eq, inner_sub_right] at hz ⊢
      rw [hx]
      have key : a * ⟪v, u⟫_ℝ + b * ⟪v, w⟫_ℝ - ⟪v, u⟫_ℝ = b * (⟪v, w⟫_ℝ - ⟪v, u⟫_ℝ) := by
        have : a = 1 - b := by linarith
        rw [this]; ring
      nlinarith [mul_nonneg hb (sub_nonneg.mpr h)]
    · refine (hw v hv).trans (measure_mono ?_)
      intro z hz
      simp only [Set.mem_ofPred_eq, inner_sub_right] at hz ⊢
      rw [hx]
      have key : a * ⟪v, u⟫_ℝ + b * ⟪v, w⟫_ℝ - ⟪v, w⟫_ℝ = a * (⟪v, u⟫_ℝ - ⟪v, w⟫_ℝ) := by
        have : b = 1 - a := by linarith
        rw [this]; ring
      nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]

theorem depth_regions_compact : Claims.depth_regions_compact := by
  intro K ν _ α hα
  have hanti : Antitone (fun n : ℕ => {z : EuclideanSpace ℝ (Fin K) | (n : ℝ) < ‖z‖}) := by
    intro a b hab z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hz
  have hempty : ⋂ n : ℕ, {z : EuclideanSpace ℝ (Fin K) | (n : ℝ) < ‖z‖} = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact exists_nat_ge ‖z‖
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hα)).exists
  have hn' : ν {z : EuclideanSpace ℝ (Fin K) | (n : ℝ) < ‖z‖} < α := hn
  have hsub : depthRegion ν α ⊆ Metric.closedBall 0 n := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlt
      exact absurd hlt (not_lt.mpr (Nat.cast_nonneg n))
    have h1 := (mem_depthRegion_iff ν α u).mp hu (-u) (neg_ne_zero.mpr hu0)
    have h2 : {z | ⟪-u, z - u⟫_ℝ ≤ 0} ⊆ {z : EuclideanSpace ℝ (Fin K) | (n : ℝ) < ‖z‖} := by
      intro z hz
      simp only [Set.mem_ofPred_eq, inner_neg_left, inner_sub_right,
        real_inner_self_eq_norm_sq] at hz ⊢
      have hcs : ⟪u, z⟫_ℝ ≤ ‖u‖ * ‖z‖ := real_inner_le_norm u z
      have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have : ‖u‖ ≤ ‖z‖ := by nlinarith
      linarith
    exact absurd (h1.trans (measure_mono h2)) (not_le.mpr hn')
  exact (isCompact_closedBall 0 (n : ℝ)).of_isClosed_subset
    (depth_regions_closed_convex K ν α).1 hsub

theorem depth_regions_support : Claims.depth_regions_support := by
  intro K ν _ α hα0 hα1 hadd hhom
  set q := dirQuantile ν α with hq
  set T : EuclideanSpace ℝ (Fin K) → Set ℝ := fun v => {s : ℝ | α ≤ ν {X | s ≤ ⟪X, v⟫_ℝ}}
    with hT
  have hqT : ∀ v, q v = sSup (T v) := fun v => rfl
  -- bounded above
  have hbdd : ∀ v, BddAbove (T v) := by
    intro v
    have hanti : Antitone (fun n : ℕ => {X : EuclideanSpace ℝ (Fin K) | (n : ℝ) ≤ ⟪X, v⟫_ℝ}) := by
      intro a b hab z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      exact le_trans (by exact_mod_cast hab) hz
    have hempty : ⋂ n : ℕ, {X : EuclideanSpace ℝ (Fin K) | (n : ℝ) ≤ ⟪X, v⟫_ℝ} = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt ⟪z, v⟫_ℝ
      exact ⟨n, hn⟩
    have ht := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => (measurableSet_le measurable_const (measurable_inner_left' v)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hα0)).exists
    have hn' : ν {X : EuclideanSpace ℝ (Fin K) | (n : ℝ) ≤ ⟪X, v⟫_ℝ} < α := hn
    refine ⟨n, fun s hs => ?_⟩
    by_contra hlt
    push Not at hlt
    have hs' : α ≤ ν {X | s ≤ ⟪X, v⟫_ℝ} := hs
    refine absurd (hs'.trans (measure_mono ?_)) (not_le.mpr hn')
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  -- nonempty
  have hne : ∀ v, (T v).Nonempty := by
    intro v
    have hmono : Monotone (fun n : ℕ => {X : EuclideanSpace ℝ (Fin K) | -(n : ℝ) ≤ ⟪X, v⟫_ℝ}) := by
      intro a b hab z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have huniv : ⋃ n : ℕ, {X : EuclideanSpace ℝ (Fin K) | -(n : ℝ) ≤ ⟪X, v⟫_ℝ} = Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge (-⟪z, v⟫_ℝ)
      exact ⟨n, by linarith⟩
    have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [huniv, measure_univ] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hα1)).exists
    exact ⟨-(n : ℝ), hn.le⟩
  -- `α ≤ ν{⟨X,v⟩ ≥ s} ↔ s ≤ q_v`
  have hiff : ∀ v s, α ≤ ν {X | s ≤ ⟪X, v⟫_ℝ} ↔ s ≤ q v := by
    intro v s
    constructor
    · intro h; exact le_csSup (hbdd v) h
    · intro hs
      have e : {X : EuclideanSpace ℝ (Fin K) | s ≤ ⟪X, v⟫_ℝ} = {X | -⟪X, v⟫_ℝ ≤ -s} := by
        ext X; simp only [Set.mem_ofPred_eq, neg_le_neg_iff]
      rw [e]
      apply le_measure_le_of_forall ν (fun X => -⟪X, v⟫_ℝ) (measurable_inner_left' v).neg (-s) α
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨s', hs'T, hs'⟩ := exists_lt_of_lt_csSup (hne v)
        (show s - 1 / ((n : ℝ) + 1) < sSup (T v) by rw [← hqT]; linarith)
      have hs'' : α ≤ ν {X | s' ≤ ⟪X, v⟫_ℝ} := hs'T
      refine hs''.trans (measure_mono ?_)
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      linarith
  have hq0 : q 0 = 0 := by
    have h := hhom 2 0 (by norm_num)
    rw [smul_zero] at h
    linarith
  -- membership in `D_α`
  have hD1 : ∀ u ∈ depthRegion ν α, ∀ w, ⟪u, w⟫_ℝ ≤ q w := by
    intro u hu w
    by_cases hw : w = 0
    · rw [hw, inner_zero_right, hq0]
    · have h := (mem_depthRegion_iff ν α u).mp hu (-w) (neg_ne_zero.mpr hw)
      have e : {z | ⟪-w, z - u⟫_ℝ ≤ 0} = {X | ⟪u, w⟫_ℝ ≤ ⟪X, w⟫_ℝ} := by
        ext z
        simp only [Set.mem_ofPred_eq, inner_neg_left, inner_sub_right, real_inner_comm z w,
          real_inner_comm u w]
        constructor <;> intro h <;> linarith
      rw [e] at h
      exact (hiff w _).mp h
  have hD2 : ∀ u, (∀ w, ⟪u, w⟫_ℝ ≤ q w) → u ∈ depthRegion ν α := by
    intro u hu
    rw [mem_depthRegion_iff]
    intro v _
    have e : {z | ⟪v, z - u⟫_ℝ ≤ 0} = {X | ⟪u, -v⟫_ℝ ≤ ⟪X, -v⟫_ℝ} := by
      ext z
      simp only [Set.mem_ofPred_eq, inner_neg_right, inner_sub_right, real_inner_comm z v,
        real_inner_comm u v]
      constructor <;> intro h <;> linarith
    rw [e]
    exact (hiff (-v) _).mpr (hu (-v))
  -- Hahn–Banach
  have hHB : ∀ v, ∃ u, (∀ w, ⟪u, w⟫_ℝ ≤ q w) ∧ ⟪u, v⟫_ℝ = q v := by
    intro v
    have H : ∀ c : ℝ, c • v = 0 → (RingHom.id ℝ) c • q v = 0 := by
      intro c hc
      rcases smul_eq_zero.mp hc with h | h
      · simp [h]
      · simp [h, hq0]
    let f : EuclideanSpace ℝ (Fin K) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' v (q v) H
    have hfapp : ∀ (c : ℝ) (h), f ⟨c • v, h⟩ = c * q v := by
      intro c h
      exact LinearPMap.mkSpanSingleton'_apply v (q v) H c h
    have hdom : ∀ x : f.domain, f x ≤ q x := by
      intro x
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
      have hx : x = ⟨c • v, hc.symm ▸ x.2⟩ := Subtype.ext hc.symm
      rw [hx, hfapp]
      simp only
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · have e : c • v = (-c) • (-v) := by rw [neg_smul, smul_neg, neg_neg]
        rw [e, hhom (-c) (-v) (by linarith)]
        have := hadd v (-v)
        rw [add_neg_cancel, hq0] at this
        nlinarith
      · rw [hc0, zero_smul, zero_mul, hq0]
      · rw [hhom c v hc0]
    obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear f q (fun c hc x => hhom c x hc) hadd hdom
    let u := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin K))).symm
      (LinearMap.toContinuousLinearMap g)
    have hu : ∀ w, ⟪u, w⟫_ℝ = g w := by
      intro w
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    refine ⟨u, fun w => (hu w).trans_le (hg2 w), ?_⟩
    rw [hu]
    have hv : v ∈ f.domain := Submodule.mem_span_singleton_self v
    have := hg1 ⟨v, hv⟩
    simp only at this
    rw [this]
    have e : (⟨v, hv⟩ : f.domain) = ⟨(1 : ℝ) • v, by rw [one_smul]; exact hv⟩ := by
      ext; simp
    rw [e, hfapp, one_mul]
  intro v
  obtain ⟨u, hu1, hu2⟩ := hHB v
  have hgreat : IsGreatest ((fun u => ⟪v, u⟫_ℝ) '' depthRegion ν α) (q v) := by
    refine ⟨⟨u, hD2 u hu1, by show ⟪v, u⟫_ℝ = q v; rw [real_inner_comm]; exact hu2⟩, ?_⟩
    rintro _ ⟨u', hu', rfl⟩
    show ⟪v, u'⟫_ℝ ≤ q v
    rw [real_inner_comm]
    exact hD1 u' hu' v
  exact hgreat.csSup_eq

example : Claims.depth_regions_optimal := depth_regions_optimal
example : Claims.depth_regions_content := depth_regions_content
example : Claims.depth_regions_closed_convex := depth_regions_closed_convex
example : Claims.depth_regions_compact := depth_regions_compact
example : Claims.depth_regions_support := depth_regions_support

end StatFormal.OTFD.Wave5a
