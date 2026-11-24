import StatFormal.Archive.Wave24e.RouteCondRank
import StatFormal.Archive.OTFD.WaveL4.RouteWeighted

/-!
# Route — otfd C `lem:cond-rank-consistency`, Step 4 discharged (untrusted)

* The certified OTFD wave-L4 `cond_potentials_weighted` (C `prop:conditional-potentials` under the verbatim
  `ass:conditional-oos`) gives `χ_n − c_n → χ` uniformly on compact subsets of `int 𝒰_K`, `c_n = inf_{𝒰_K} χ_n`.
* The Laguerre potentials are `R`-Lipschitz and `𝒰_K` is convex with nonempty interior, so shrinking `𝒰_K` towards an
  interior point (`w ↦ s c₀ + (1 − s) w`) moves points by `≤ 2Bs` and lands in a compact subset of `int 𝒰_K`; hence
  `X_n + c_n → X = (χ + ι_{int 𝒰_K})^*` pointwise (Step 4).
* Step 3's grid density: finitely many balls of radius `η/2` centred in `𝒰_K` cover it; each has positive
  `μ_K`-mass (`𝒰_K ⊆ cl int 𝒰_K ⊆ supp μ_K`), so by the portmanteau theorem each eventually holds a grid atom.
* Then the conditional `cond_rank_consistency` applies with `δ_n = sup_{w ∈ 𝒰_K} min_j ‖w − u_j‖`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24e

open StatFormal.Wave23c (lagPot lagPiece)

section UncondLemmas

variable {K : ℕ}

lemma exists_grid_mem {M : ℕ} {α : Measure (EuclideanSpace ℝ (Fin K))}
    {u : Fin (M + 1) → EuclideanSpace ℝ (Fin K)}
    (hα : α = ∑ j, ENNReal.ofReal (1 / ((M : ℝ) + 1)) • Measure.dirac (u j))
    {V : Set (EuclideanSpace ℝ (Fin K))} (hV : MeasurableSet V) (hpos : 0 < α V) : ∃ j, u j ∈ V := by
  by_contra h
  push Not at h
  apply hpos.ne'
  rw [hα, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hV, Set.indicator_of_notMem (h j), smul_zero]

lemma measure_ball_pos_of_closure {μ : Measure (EuclideanSpace ℝ (Fin K))}
    {U : Set (EuclideanSpace ℝ (Fin K))} (hcl : U ⊆ closure (interior U)) (hsupp : interior U ⊆ μ.support)
    {c : EuclideanSpace ℝ (Fin K)} (hc : c ∈ U) {η : ℝ} (hη : 0 < η) : 0 < μ (Metric.ball c η) := by
  obtain ⟨x, hxb, hxi⟩ : (Metric.ball c η ∩ interior U).Nonempty :=
    (mem_closure_iff.1 (hcl hc)) _ Metric.isOpen_ball (Metric.mem_ball_self hη)
  exact (Measure.mem_support_iff_forall x).1 (hsupp hxi) _ (Metric.isOpen_ball.mem_nhds hxb)

lemma eventually_grid_dense {M : ℕ → ℕ} {u : ∀ k, Fin (M k + 1) → EuclideanSpace ℝ (Fin K)}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))} {α : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))}
    {U : Set (EuclideanSpace ℝ (Fin K))} (hαμ : Tendsto α atTop (𝓝 μ))
    (hα : ∀ k, (α k : Measure (EuclideanSpace ℝ (Fin K))) =
      ∑ j, ENNReal.ofReal (1 / ((M k : ℝ) + 1)) • Measure.dirac (u k j))
    (hUk : IsCompact U) (hcl : U ⊆ closure (interior U))
    (hsupp : interior U ⊆ (μ : Measure (EuclideanSpace ℝ (Fin K))).support) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ w ∈ U, ∃ j, ‖w - u k j‖ < η := by
  obtain ⟨t, htU, htfin, hcov⟩ := finite_cover_balls_of_compact hUk (half_pos hη)
  have hev : ∀ c ∈ t, ∀ᶠ k in atTop, ∃ j, u k j ∈ Metric.ball c (η / 2) := by
    intro c hc
    have hpos := measure_ball_pos_of_closure hcl hsupp (htU hc) (half_pos hη)
    filter_upwards [StatFormal.OTFD.WaveL4.eventually_lt_measure_of_tendsto hαμ Metric.isOpen_ball hpos]
      with k hk
    exact exists_grid_mem (hα k) Metric.isOpen_ball.measurableSet hk
  filter_upwards [(Filter.eventually_all_finite htfin).2 hev] with k hk
  intro w hw
  obtain ⟨c, hc, hwc⟩ := mem_iUnion₂.1 (hcov hw)
  obtain ⟨j, hj⟩ := hk c hc
  refine ⟨j, ?_⟩
  have h1 : ‖w - u k j‖ ≤ ‖w - c‖ + ‖c - u k j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [Metric.mem_ball, dist_eq_norm] at hwc hj
  rw [norm_sub_rev] at hj
  linarith

end UncondLemmas

theorem cond_rank_consistency_uncond : Claims.cond_rank_consistency_uncond := by
  intro K n M ε R z f u g μ P U Q α ν ζ ρ hRef hm1 hQ hQP hCM hW hα hgrid hε hεlog hcol hz hρ
  have hpot := StatFormal.OTFD.WaveL4.cond_potentials_weighted K μ P U Q α ν
    (fun k => lagPot (z k) (f k)) (fun k => lagPot (z k) (f k)) ζ hRef hm1 hQ hQP hCM hW
  refine ⟨hpot.1, fun χ hχ hQχ hglb => ?_⟩
  have hne : (interior U).Nonempty := StatFormal.OTFD.WaveL3.interior_nonempty_of_refLaw hRef
  obtain ⟨-, hUc, hUk, -, hsupp⟩ := hRef
  have hcl := StatFormal.OTFD.WaveL3.subset_closure_interior hUc hne
  have hUne : U.Nonempty := hne.mono interior_subset
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (hz 0 0)
  -- the Laguerre potentials are `R`-Lipschitz
  have hlip : ∀ k w w', lagPot (z k) (f k) w ≤ lagPot (z k) (f k) w' + R * ‖w - w'‖ :=
    fun k w w' => lagPot_le_add (f k) (hz k) w w'
  have hcont : ∀ k, Continuous (lagPot (z k) (f k)) := fun k =>
    StatFormal.OTFD.WaveL4.continuous_of_le_add_mul (hlip k)
  set c : ℕ → ℝ := fun k => sInf (lagPot (z k) (f k) '' U) with hcdef
  have hc : ∀ k, IsGLB (lagPot (z k) (f k) '' U) (c k) := fun k =>
    isGLB_csInf (hUne.image _) (hUk.bddBelow_image (hcont k).continuousOn)
  have hconvS : ∀ S ⊆ interior U, IsCompact S →
      TendstoUniformlyOn (fun k w => lagPot (z k) (f k) w - c k) χ atTop S := fun S hS hSc =>
    (hpot.2 χ hχ hQχ hglb c hc S hS hSc).1
  obtain ⟨B₀, hB₀⟩ := hUk.isBounded.subset_closedBall 0
  set B := max B₀ 0
  have hB : ∀ w ∈ U, ‖w‖ ≤ B := fun w hw => by
    have := hB₀ hw
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  set X : EuclideanSpace ℝ (Fin K) → ℝ := fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U) with hXdef
  have hχ0 : ∀ w ∈ interior U, 0 ≤ χ w := fun w hw => hglb.1 ⟨w, hw, rfl⟩
  have hXbdd : ∀ y, BddAbove ((fun w => ⟪w, y⟫ - χ w) '' interior U) := fun y => by
    refine ⟨B * ‖y‖, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := real_inner_le_norm w y
    have h2 := hB w (interior_subset hw)
    have h3 := hχ0 w hw
    nlinarith [norm_nonneg y]
  have hle_X : ∀ y, ∀ w ∈ interior U, ⟪w, y⟫ - χ w ≤ X y := fun y w hw =>
    le_csSup (hXbdd y) ⟨w, hw, rfl⟩
  have hcbdd : ∀ k y, BddAbove ((fun w => ⟪w, y⟫ - lagPot (z k) (f k) w) '' U) := fun k y => by
    refine ⟨B * ‖y‖ - c k, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := real_inner_le_norm w y
    have h2 := hB w hw
    have h3 := (hc k).1 ⟨w, hw, rfl⟩
    nlinarith [norm_nonneg y]
  -- Step 4: `X_n + c_n → X` pointwise
  have hX : ∀ y, Tendsto (fun k => contConj (z k) (f k) U y - -c k) atTop (𝓝 (X y)) := by
    intro y
    rw [Metric.tendsto_nhds]
    intro η hη
    -- lower bound
    obtain ⟨_, ⟨w₀, hw₀, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image _)
      (show X y - η / 2 < X y by linarith)
    have hpt : Tendsto (fun k => lagPot (z k) (f k) w₀ - c k) atTop (𝓝 (χ w₀)) :=
      (hconvS {w₀} (singleton_subset_iff.2 hw₀) isCompact_singleton).tendsto_at rfl
    have hlow : ∀ᶠ k in atTop, X y - η < contConj (z k) (f k) U y + c k := by
      filter_upwards [(Metric.tendsto_nhds.1 hpt) (η / 2) (half_pos hη)] with k hk
      rw [Real.dist_eq] at hk
      have : ⟪w₀, y⟫ - lagPot (z k) (f k) w₀ ≤ contConj (z k) (f k) U y :=
        le_csSup (hcbdd k y) ⟨w₀, interior_subset hw₀, rfl⟩
      have := (abs_lt.1 hk).2
      simp only at hlt
      linarith
    -- upper bound: shrink `U` towards `c₀ ∈ int U`
    obtain ⟨c₀, hc₀⟩ := hne
    set L := ‖y‖ + R
    have hL : 0 ≤ L := add_nonneg (norm_nonneg _) hR
    set s : ℝ := min (1 / 2) (η / (4 * (L * (2 * B) + 1)))
    have hden : 0 < 4 * (L * (2 * B) + 1) := by positivity
    have hs0 : 0 < s := lt_min (by norm_num) (div_pos hη hden)
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hsη : L * (2 * B) * s ≤ η / 4 := by
      have h1 : s ≤ η / (4 * (L * (2 * B) + 1)) := min_le_right _ _
      have h2 : L * (2 * B) * s ≤ L * (2 * B) * (η / (4 * (L * (2 * B) + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : L * (2 * B) * (η / (4 * (L * (2 * B) + 1))) ≤ η / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
        nlinarith [hη.le, mul_nonneg hL (mul_nonneg (zero_le_two) hB0)]
      linarith
    set sh : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun w => s • c₀ + (1 - s) • w
    have hshc : Continuous sh := by fun_prop
    have hSsub : sh '' U ⊆ interior U := by
      rintro _ ⟨w, hw, rfl⟩
      exact hUc.combo_interior_self_mem_interior hc₀ hw hs0 (by linarith) (by ring)
    have hSc : IsCompact (sh '' U) := hUk.image hshc
    have hunif := (Metric.tendstoUniformlyOn_iff.1 (hconvS _ hSsub hSc)) (η / 4) (by linarith)
    have hup : ∀ᶠ k in atTop, contConj (z k) (f k) U y + c k ≤ X y + 3 * η / 4 := by
      filter_upwards [hunif] with k hk
      have : contConj (z k) (f k) U y ≤ X y + 3 * η / 4 - c k := by
        refine csSup_le (hUne.image _) ?_
        rintro _ ⟨w, hw, rfl⟩
        have hw' : sh w ∈ sh '' U := ⟨w, hw, rfl⟩
        have h1 := hk (sh w) hw'
        rw [Real.dist_eq, abs_lt] at h1
        have h2 := hle_X y (sh w) (hSsub hw')
        have hdiff : w - sh w = s • (w - c₀) := by
          simp only [sh, smul_sub, sub_smul, one_smul]; abel
        have hnd : ‖w - sh w‖ ≤ s * (2 * B) := by
          rw [hdiff, norm_smul, Real.norm_of_nonneg hs0.le]
          refine mul_le_mul_of_nonneg_left ?_ hs0.le
          have := norm_sub_le w c₀
          have := hB w hw
          have := hB c₀ (interior_subset hc₀)
          linarith
        have h3 := hlip k (sh w) w
        have h4 : ⟪w, y⟫ ≤ ⟪sh w, y⟫ + ‖y‖ * ‖w - sh w‖ := by
          have := real_inner_le_norm (w - sh w) y
          rw [inner_sub_left] at this
          rw [mul_comm]; linarith
        rw [norm_sub_rev] at h3
        have h5 : L * ‖w - sh w‖ ≤ L * (s * (2 * B)) := mul_le_mul_of_nonneg_left hnd hL
        have h6 : L * ‖w - sh w‖ = ‖y‖ * ‖w - sh w‖ + R * ‖w - sh w‖ := by simp only [L]; ring
        nlinarith
      linarith
    filter_upwards [hlow, hup] with k h1 h2
    rw [Real.dist_eq, sub_neg_eq_add, abs_lt]
    constructor <;> linarith
  -- Step 3: grid density with `δ_k = sup_{w ∈ U} min_j ‖w − u_j‖`
  set D : ℕ → EuclideanSpace ℝ (Fin K) → ℝ := fun k w =>
    Finset.univ.inf' Finset.univ_nonempty fun j => ‖w - u k j‖ with hDdef
  set δ : ℕ → ℝ := fun k => sSup (D k '' U) with hδdef
  have hDle : ∀ k w j, D k w ≤ ‖w - u k j‖ := fun k w j =>
    Finset.inf'_le (fun j => ‖w - u k j‖) (Finset.mem_univ j)
  have hDbdd : ∀ k, BddAbove (D k '' U) := fun k => by
    refine ⟨2 * B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hDle k w 0
    have h2 := norm_sub_le w (u k 0)
    have h3 := hB w hw
    have h4 := hB (u k 0) (hgrid k 0)
    linarith
  have hdense : ∀ k, ∀ w ∈ U, ∃ j, ‖w - u k j‖ ≤ δ k := by
    intro k w hw
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun j => ‖w - u k j‖
    exact ⟨j, hj ▸ le_csSup (hDbdd k) ⟨w, hw, rfl⟩⟩
  have hδ : Tendsto δ atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨w₁, hw₁⟩ := hUne
    have hev := eventually_grid_dense hW.1 hα hUk hcl hsupp (half_pos hη)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun k hk => ?_⟩
    have hδ0 : 0 ≤ δ k := by
      have : D k w₁ ≤ δ k := le_csSup (hDbdd k) ⟨w₁, hw₁, rfl⟩
      have : 0 ≤ D k w₁ := Finset.le_inf' _ _ fun j _ => norm_nonneg _
      linarith
    have hδη : δ k ≤ η / 2 := by
      refine csSup_le ⟨_, ⟨w₁, hw₁, rfl⟩⟩ ?_
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, hj⟩ := hN k hk w hw
      exact (hDle k w j).trans hj.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ0]
    linarith
  exact cond_rank_consistency K n M ε δ R z f u g U X (fun k => -c k) ρ hε hεlog hδ hcol hz hgrid hdense hX hρ

end StatFormal.Wave24e
