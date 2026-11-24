import StatFormal.Archive.OTFD.Wave16b.Statements

/-!
# Route: C `lem:supp-small-cells` (untrusted)

A compactness route equivalent to the printed one (no subsequences): `μ(closedBall x r) → μ{x} = 0` gives each `x` an
open ball of mass `< η`; a closed ball `B` with `μ(Bᶜ) < η` exists by continuity from above; a Lebesgue number `δ` of the
cover of `B` by these balls handles every cube of side `2^{-ℓ} < δ` meeting `B` (a cube has sup-diameter `< 2^{-ℓ}`), and
cubes missing `B` lie in `Bᶜ`. The partition: `k_i = ⌊2^ℓ x_i⌋`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace StatFormal.OTFD.Wave16b

lemma mem_dyadicCube_iff {q ℓ : ℕ} {k : Fin q → ℤ} {x : Fin q → ℝ} :
    x ∈ dyadicCube q ℓ k ↔ ∀ i, (k i : ℝ) ≤ 2 ^ ℓ * x i ∧ 2 ^ ℓ * x i < k i + 1 := by
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  simp only [dyadicCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
  refine forall_congr' fun i => ?_
  rw [div_le_iff₀ h2, lt_div_iff₀ h2, mul_comm (x i)]

lemma dist_lt_of_mem_cube {q ℓ : ℕ} {k : Fin q → ℤ} {x y : Fin q → ℝ} (hx : x ∈ dyadicCube q ℓ k)
    (hy : y ∈ dyadicCube q ℓ k) : dist x y < (1 / 2) ^ ℓ := by
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hpos : (0 : ℝ) < (1 / 2) ^ ℓ := by positivity
  rw [dist_pi_lt_iff hpos]
  intro i
  have a := (mem_dyadicCube_iff.1 hx) i
  have b := (mem_dyadicCube_iff.1 hy) i
  have e : (1 / 2 : ℝ) ^ ℓ = 1 / 2 ^ ℓ := by rw [one_div_pow]
  have h : |2 ^ ℓ * x i - 2 ^ ℓ * y i| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  rw [Real.dist_eq, e, lt_div_iff₀ h2]
  rw [← mul_sub, abs_mul, abs_of_pos h2] at h
  linarith

theorem dyadic_partition : Claims.dyadic_partition := by
  intro q ℓ
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  refine ⟨inferInstance, fun k => ?_, fun k k' hkk' => ?_, ?_⟩
  · exact MeasurableSet.univ_pi fun i => measurableSet_Ico
  · show Disjoint _ _
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hkk'
    funext i
    have a := (mem_dyadicCube_iff.1 hx) i
    have b := (mem_dyadicCube_iff.1 hx') i
    have c1 : (k i : ℝ) < k' i + 1 := lt_of_le_of_lt a.1 b.2
    have c2 : (k' i : ℝ) < k i + 1 := lt_of_le_of_lt b.1 a.2
    have d1 : k i < k' i + 1 := by exact_mod_cast c1
    have d2 : k' i < k i + 1 := by exact_mod_cast c2
    omega
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨fun i => ⌊2 ^ ℓ * x i⌋, ?_⟩
    rw [mem_dyadicCube_iff]
    intro i
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem small_cells : Claims.small_cells := by
  intro q μ _ hatom η hη
  -- small balls around every point
  have hball : ∀ x : Fin q → ℝ, ∃ r > 0, μ (ball x r) < η := by
    intro x
    have ht := tendsto_measure_cthickening_of_isCompact (μ := μ) (isCompact_singleton (x := x))
    rw [hatom x] at ht
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (cthickening r {x}) < η :=
      (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hη)
    obtain ⟨r, hlt, hr⟩ := (hev.and self_mem_nhdsWithin).exists
    have hr : 0 < r := hr
    refine ⟨r, hr, lt_of_le_of_lt (measure_mono ?_) hlt⟩
    rw [cthickening_singleton _ hr.le]
    exact ball_subset_closedBall
  choose rad hrad hradη using hball
  -- tightness
  have htight : ∃ R : ℕ, μ (closedBall (0 : Fin q → ℝ) R)ᶜ < η := by
    have hanti : Antitone fun R : ℕ => (closedBall (0 : Fin q → ℝ) R)ᶜ := fun a b hab =>
      compl_subset_compl.2 (closedBall_subset_closedBall (by exact_mod_cast hab))
    have hT := tendsto_measure_iInter_atTop (μ := μ)
      (fun R : ℕ => isClosed_closedBall.isOpen_compl.measurableSet.nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ R : ℕ, (closedBall (0 : Fin q → ℝ) R)ᶜ) = ∅ := by
      rw [← compl_iUnion, iUnion_closedBall_nat, compl_univ]
    rw [hempty, measure_empty] at hT
    exact ((hT.eventually (gt_mem_nhds hη)).exists)
  obtain ⟨R, hR⟩ := htight
  set B := closedBall (0 : Fin q → ℝ) R
  have hB : IsCompact B := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hB (c := fun x => ball x (rad x))
    (fun x => isOpen_ball) (fun y _ => mem_iUnion.2 ⟨y, mem_ball_self (hrad y)⟩)
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨ℓ, fun k => ?_⟩
  by_cases hmeet : (dyadicCube q ℓ k ∩ B).Nonempty
  · obtain ⟨y, hyQ, hyB⟩ := hmeet
    obtain ⟨x, hx⟩ := hleb y hyB
    have hsub : dyadicCube q ℓ k ⊆ ball x (rad x) := by
      intro z hz
      exact hx (mem_ball.2 ((dist_lt_of_mem_cube hz hyQ).trans hℓ))
    exact (measure_mono hsub).trans (hradη x).le
  · have hsub : dyadicCube q ℓ k ⊆ Bᶜ := fun z hz hzB => hmeet ⟨z, hz, hzB⟩
    exact (measure_mono hsub).trans hR.le

end StatFormal.OTFD.Wave16b
