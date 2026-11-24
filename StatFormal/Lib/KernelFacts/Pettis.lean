import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Weak measurability from the Gram function; Pettis in a separable Hilbert space (library, untrusted)

* `measurable_of_inner`: in a second-countable real inner-product space with its Borel σ-algebra, a map `G : X → ℋ` with
  `x ↦ ⟪h, G x⟫` measurable for every `h ∈ ℋ` is measurable (copy-adapted from the proved route lemma
  `StatFormal.Wave23d.measurable_of_inner`, `StatFormal/Archive/Wave23d/RouteGrad.lean`).
* `measurable_inner_of_gram`: in a complete real inner-product space, if `x ↦ ⟪φ x, φ x′⟫` is measurable for every `x′`, then
  `x ↦ ⟪h, φ x⟫` is measurable for every `h` (span induction, sequential closure of the span, orthogonal decomposition onto the
  closed span).
* `measurable_of_gram`, `stronglyMeasurable_of_gram`: hence `φ` is Borel and strongly measurable when `ℋ` is separable.
* `norm_le_of_gram`: `⟪φ x, φ x⟫ ≤ κ²`, `κ ≥ 0` give `‖φ x‖ ≤ κ`.
* `integrable_smul_of_bounded`: `g • φ` is Bochner integrable for bounded measurable `g`, strongly measurable bounded `φ`, finite `P`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.KernelFacts

section Pettis
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Weak ⇒ Borel measurability** in a second-countable real inner-product space: if `x ↦ ⟪h, G x⟫` is measurable for every `h`,
then `G` is Borel measurable. (Copy-adapted from `StatFormal.Wave23d.measurable_of_inner`.) -/
theorem measurable_of_inner [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {G : X → H}
    (hG : ∀ h : H, Measurable fun x => ⟪h, G x⟫) : Measurable G := by
  by_cases hH : ∃ v : H, v ≠ 0
  · obtain ⟨v, hv⟩ := hH
    have hne : Nonempty (Metric.sphere (0 : H) 1) :=
      ⟨⟨‖v‖⁻¹ • v, by simp [norm_smul, norm_ne_zero_iff.2 hv]⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Metric.sphere (0 : H) 1)
    have hnorm : ∀ (w : H) (r : ℝ), ‖w‖ ≤ r ↔ ∀ m, ⟪(u m : H), w⟫ ≤ r := by
      intro w r
      constructor
      · intro h m
        have := real_inner_le_norm (u m : H) w
        rw [show ‖(u m : H)‖ = 1 from by simpa using (u m).2, one_mul] at this
        linarith
      · intro h
        by_contra hlt
        push Not at hlt
        have hw : w ≠ 0 := by
          rintro rfl; have := h 0; simp at this; rw [norm_zero] at hlt; linarith
        have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
        set e : Metric.sphere (0 : H) 1 := ⟨‖w‖⁻¹ • w, by simp [norm_smul, hw]⟩
        have he : ⟪(e : H), w⟫ = ‖w‖ := by
          simp only [e, inner_smul_left, real_inner_self_eq_norm_sq, conj_trivial]; field_simp
        have hδ : 0 < (‖w‖ - r) / ‖w‖ := div_pos (by linarith) hwpos
        obtain ⟨m, hm⟩ := hu.exists_dist_lt e hδ
        have h1 : |⟪(u m : H) - e, w⟫| ≤ ‖(u m : H) - e‖ * ‖w‖ := abs_real_inner_le_norm _ _
        have h2 : ‖(u m : H) - e‖ < (‖w‖ - r) / ‖w‖ := by
          rw [← dist_eq_norm]; rw [dist_comm] at hm; exact hm
        have h3 : ‖(u m : H) - e‖ * ‖w‖ < ‖w‖ - r := by
          rwa [lt_div_iff₀ hwpos] at h2
        have := h m
        rw [show (u m : H) = ((u m : H) - e) + e by abel, inner_add_left, he] at this
        have := neg_abs_le ⟪(u m : H) - e, w⟫
        linarith
    have hball : ∀ (c : H) (r : ℝ), MeasurableSet (G ⁻¹' Metric.closedBall c r) := by
      intro c r
      have : G ⁻¹' Metric.closedBall c r = ⋂ m, {x | ⟪(u m : H), G x⟫ - ⟪(u m : H), c⟫ ≤ r} := by
        ext x
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, Set.mem_iInter, Set.mem_ofPred_eq,
          hnorm, inner_sub_right]
      rw [this]
      exact MeasurableSet.iInter fun m => measurableSet_le ((hG _).sub_const _) measurable_const
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
    refine measurable_of_isOpen fun U hU => ?_
    set S := {p : ℕ × ℚ | 0 < p.2 ∧ Metric.closedBall (d p.1) (p.2 : ℝ) ⊆ U}
    have hU' : U = ⋃ p ∈ S, Metric.closedBall (d p.1) (p.2 : ℝ) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
        obtain ⟨n, hn⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 4)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
        refine Set.mem_biUnion (x := (n, q)) ⟨by simp only; exact_mod_cast (by linarith : (0 : ℝ) < q), ?_⟩ ?_
        · intro y hy
          apply hεU
          rw [Metric.mem_closedBall] at hy
          rw [Metric.mem_ball]
          calc dist y x ≤ dist y (d n) + dist (d n) x := dist_triangle _ _ _
            _ < ε := by rw [dist_comm] at hn; simp only at hy; linarith
        · rw [Metric.mem_closedBall]; simp only; linarith
      · exact Set.iUnion₂_subset fun p hp => hp.2
    rw [hU', Set.preimage_iUnion₂]
    exact MeasurableSet.biUnion (Set.to_countable S) fun p _ => hball _ _
  · push Not at hH
    have : G = fun _ => 0 := funext fun x => hH (G x)
    rw [this]; exact measurable_const

/-- **Weak measurability from the Gram function.** In a complete real inner-product space, if `x ↦ ⟪φ x, φ x′⟫` is measurable for
every `x′`, then `x ↦ ⟪h, φ x⟫` is measurable for every `h ∈ ℋ`: on the span of `φ(X)` it is a finite combination of Gram sections,
on the closed span a pointwise limit, and the component of `h` orthogonal to the closed span contributes `0`. -/
theorem measurable_inner_of_gram [CompleteSpace H] {φ : X → H} (hk : ∀ x', Measurable fun x => ⟪φ x, φ x'⟫_ℝ) (h : H) :
    Measurable fun x => ⟪h, φ x⟫_ℝ := by
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range φ)
  have hspan : ∀ g ∈ S, Measurable fun x => ⟪g, φ x⟫_ℝ := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x', rfl⟩ := hg
      simpa only [real_inner_comm] using hk x'
    | zero => simp only [inner_zero_left]; exact measurable_const
    | add g g' _ _ ihg ihg' => simp only [inner_add_left]; exact ihg.add ihg'
    | smul c g _ ihg => simp only [real_inner_smul_left]; exact ihg.const_mul c
  set K : Submodule ℝ H := S.topologicalClosure
  have hK : ∀ g ∈ K, Measurable fun x => ⟪g, φ x⟫_ℝ := by
    intro g hg
    have hg' : g ∈ closure (S : Set H) := by rw [← Submodule.topologicalClosure_coe]; exact hg
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hg'
    exact measurable_of_tendsto_metrizable (fun n => hspan _ (hu n))
      (tendsto_pi_nhds.2 fun x => hlim.inner tendsto_const_nhds)
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure S).completeSpace_coe
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal h
  have hz0 : ∀ x, ⟪z, φ x⟫_ℝ = 0 := fun x =>
    Submodule.inner_left_of_mem_orthogonal (S.le_topologicalClosure (Submodule.subset_span ⟨x, rfl⟩)) hz
  simp only [inner_add_left, hz0, add_zero]
  exact hK y hy

/-- A map with measurable Gram sections into a complete separable real inner-product space (Borel) is Borel measurable. -/
theorem measurable_of_gram [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    {φ : X → H} (hk : ∀ x', Measurable fun x => ⟪φ x, φ x'⟫_ℝ) : Measurable φ :=
  measurable_of_inner (measurable_inner_of_gram hk)

/-- A map with measurable Gram sections into a complete separable real inner-product space is strongly measurable. -/
theorem stronglyMeasurable_of_gram [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    {φ : X → H} (hk : ∀ x', Measurable fun x => ⟪φ x, φ x'⟫_ℝ) : StronglyMeasurable φ :=
  (measurable_of_gram hk).stronglyMeasurable

omit [MeasurableSpace X] in
/-- `⟪φ x, φ x⟫ ≤ κ²` with `κ ≥ 0` gives `‖φ x‖ ≤ κ`. -/
theorem norm_le_of_gram {φ : X → H} {κ : ℝ} (hκ : 0 ≤ κ) (hd : ∀ x, ⟪φ x, φ x⟫_ℝ ≤ κ ^ 2) (x : X) : ‖φ x‖ ≤ κ := by
  have h := hd x
  rw [real_inner_self_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hκ two_ne_zero).1 h

/-- `g • φ` is Bochner integrable under a finite measure for `g` measurable with `|g| ≤ C` and `φ` strongly measurable with
`‖φ‖ ≤ κ`. -/
theorem integrable_smul_of_bounded (P : Measure X) [IsFiniteMeasure P] {φ : X → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hφκ : ∀ x, ‖φ x‖ ≤ κ) {g : X → ℝ} {C : ℝ} (hg : Measurable g) (hgC : ∀ x, |g x| ≤ C) :
    Integrable (fun x => g x • φ x) P := by
  refine ⟨(hg.stronglyMeasurable.smul hφ).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C * κ) (Eventually.of_forall fun x => ?_)⟩
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hgC x) (hφκ x) (norm_nonneg _) ((abs_nonneg _).trans (hgC x))

end Pettis

end StatFormal.KernelFacts
