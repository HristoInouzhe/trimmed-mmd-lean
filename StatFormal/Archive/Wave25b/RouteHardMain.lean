import StatFormal.Archive.Wave25b.RouteHard

/-!
# Route (wave 25b): A `thm:app-hard-diagonal` (untrusted)

For each `K` let `G_K` be the Hilbert Brenier map of `P` onto the coherent embedded reference `(ι_K Π_K)#μ` (frozen
`brenier_exists_H`), made bounded on a `P`-null set. Then
`E n⁻¹ Σ ‖ι_K û_i − 𝔽_P(X_i)‖² ≤ 2 a_K(n) + 2 b_K` with `a_K(n) → 0` (fixed-`K` step, `RouteHard`) and
`b_K = ‖G_K − 𝔽_P‖²_{L²(P)} → 0` (frozen `plan_stab_b_map_uncond`, `(ι_K Π_K)#μ ⇀ μ`); a diagonal extraction gives
the staircase.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc continuous_truncK continuous_embed
  norm_embed_truncK_le tendsto_coherent)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Ranks (IsMin cost)

section Main
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem mom1_ne_top_of_pell {P : Measure H} (hP : PellClass P) : Mom1 P ≠ ∞ := by
  obtain ⟨hprob, h2, -⟩ := hP
  have hle : Mom1 P ≤ ∫⁻ x, (1 + ‖x‖ₑ ^ 2) ∂P := by
    refine lintegral_mono fun x => ?_
    rcases le_total ‖x‖ₑ 1 with h | h
    · exact h.trans le_self_add
    · calc ‖x‖ₑ = ‖x‖ₑ * 1 := (mul_one _).symm
        _ ≤ ‖x‖ₑ * ‖x‖ₑ := by gcongr
        _ = ‖x‖ₑ ^ 2 := (sq _).symm
        _ ≤ 1 + ‖x‖ₑ ^ 2 := le_add_self
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h2.ne⟩

/-- A bounded modification of a cyclically monotone map pushing to a law on the ball. -/
theorem bounded_version {P : Measure H} [IsProbabilityMeasure P] {G : H → H} (hG : Measurable G)
    {ρ : Measure H} (hpush : P.map G = ρ) (hcm : IsCMMapAE P G) {M : ℝ}
    (hρ : ρ (Metric.closedBall 0 M)ᶜ = 0) (hM : 0 ≤ M) :
    ∃ G' : H → H, Measurable G' ∧ P.map G' = ρ ∧ IsCMMapAE P G' ∧ (∀ x, ‖G' x‖ ≤ M) ∧ G' =ᵐ[P] G := by
  have hS : MeasurableSet {x | ‖G x‖ ≤ M} := measurableSet_le hG.norm measurable_const
  set G' : H → H := fun x => if ‖G x‖ ≤ M then G x else 0 with hG'
  have hG'm : Measurable G' := Measurable.ite hS hG measurable_const
  have hnull : P {x | ‖G x‖ ≤ M}ᶜ = 0 := by
    have : {x | ‖G x‖ ≤ M}ᶜ = G ⁻¹' (Metric.closedBall 0 M)ᶜ := by ext x; simp
    rw [this, ← Measure.map_apply hG Metric.isClosed_closedBall.measurableSet.compl, hpush, hρ]
  have hae : G' =ᵐ[P] G := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    simp only [mem_compl_iff, mem_setOf_eq, not_not] at hx
    simp [hG', hx]
  refine ⟨G', hG'm, ?_, ?_, fun x => ?_, hae⟩
  · rw [← hpush]; exact Measure.map_congr hae
  · obtain ⟨S, hSm, hS0, hSc⟩ := hcm
    refine ⟨S ∩ {x | ‖G x‖ ≤ M}, hSm.inter hS, ?_, ?_⟩
    · rw [compl_inter]; exact measure_union_null hS0 hnull
    · intro m z hz
      refine hSc m z fun i => ⟨(hz i).1.1, ?_⟩
      rw [(hz i).2]
      have h2 : ‖G (z i).1‖ ≤ M := (hz i).1.2
      simp [hG', h2]
  · by_cases h : ‖G x‖ ≤ M
    · simp [hG', h]
    · simp [hG', h, hM]

theorem app_hard_diagonal : Claims.app_hard_diagonal := by
  intro H _ _ _ _ _ _ e P μ F M Ω _ Pr _ X u sel he hsp hPell hμM hF hmap hcm hX hind hlaw hu hgrid hsel hselm
  have hLip : LipNull (P : Measure H) := hPell.2.2
  have hP1 : Mom1 (P : Measure H) ≠ ∞ := mom1_ne_top_of_pell hPell
  have hP2 : Mom2 (P : Measure H) ≠ ∞ := hPell.2.1.ne
  have hM : 0 ≤ M := by
    by_contra hneg
    have : Metric.closedBall (0 : H) M = ∅ := Metric.closedBall_eq_empty.2 (lt_of_not_ge hneg)
    rw [this, compl_empty, measure_univ] at hμM
    exact one_ne_zero hμM
  -- the coherent embedded references
  set μK : ℕ → ProbabilityMeasure H := fun K => μ.map fun y => embed e K (truncK e K y) with hμK
  have hpk : ∀ K, Measurable fun y : H => embed e K (truncK e K y) := fun K =>
    ((continuous_embed e K).comp (continuous_truncK e K)).measurable
  have hμKM : ∀ K, (μK K : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
    intro K
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (hpk K) Metric.isClosed_closedBall.measurableSet.compl]
    refine measure_mono_null (fun y hy => ?_) hμM
    simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hy ⊢
    exact lt_of_lt_of_le hy (norm_embed_truncK_le he K y)
  have hμK_eq : ∀ K, (μK K : Measure H) = ((μ : Measure H).map (truncK e K)).map (embed e K) := by
    intro K
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (continuous_embed e K).measurable
      (continuous_truncK e K).measurable]
    rfl
  -- Hilbert Brenier maps at each level, bounded versions
  have hex : ∀ K, ∃ G : H → H, Measurable G ∧ (P : Measure H).map G = μK K ∧ IsCMMapAE (P : Measure H) G ∧
      ∀ x, ‖G x‖ ≤ M := by
    intro K
    obtain ⟨G0, hG0, hG0push, hG0cm⟩ := StatFormal.OTFD.WaveL3.brenier_exists_H H P (μK K) hLip hP2
      (StatFormal.OTFD.WaveL1.mom2_ne_top_of_bounded (hμKM K))
    obtain ⟨G', hG'm, hG'push, hG'cm, hG'b, -⟩ := bounded_version hG0 hG0push hG0cm (hμKM K) hM
    exact ⟨G', hG'm, hG'push, hG'cm, hG'b⟩
  choose G hGm hGpush hGcm hGb using hex
  -- the fixed-`K` errors
  set a : ℕ → ℕ → ℝ≥0∞ := fun K n => ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
    ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - G K (X i ω)‖ₑ ^ 2 ∂Pr with ha
  have hfix : ∀ K, (∀ n : ℕ, Measurable fun ω => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - G K (X i ω)‖ₑ ^ 2) ∧
      Tendsto (a K) atTop (𝓝 0) := by
    intro K
    obtain ⟨R, hR⟩ := hu K
    exact fixedK_hard_exp he hLip hP1 (hGm K) ((hGpush K).trans (hμK_eq K)) (hGcm K) (hGb K) hX hind hlaw
      (hR) (hgrid K) (hsel K) (hselm K)
  -- the sieve errors
  set b : ℕ → ℝ≥0∞ := fun K => ∫⁻ x, ‖G K x - F x‖ₑ ^ 2 ∂(P : Measure H) with hb
  have hblim : Tendsto b atTop (𝓝 0) :=
    StatFormal.OTFD.WaveL3.plan_stab_b_map_uncond H P μ F M μK G hLip hP1 hF hmap hcm
      (tendsto_coherent he hsp μ) hμKM hGm hGpush hGcm
  -- the error decomposition
  have hdec : ∀ (K n : ℕ), ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
      ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - F (X i ω)‖ₑ ^ 2 ∂Pr ≤
        2 * a K n + 2 * b K := by
    intro K n
    have hGK := hGm K
    have hs : ∀ i : Fin n, Measurable fun ω => ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2 := fun i => by fun_prop
    have hBm : Measurable fun ω => (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2 :=
      (Finset.measurable_sum _ fun i _ => hs i).const_mul _
    have hpt : ∀ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
        ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - F (X i ω)‖ₑ ^ 2 ≤
          2 * ((n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
            ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - G K (X i ω)‖ₑ ^ 2) +
          2 * ((n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2) := by
      intro ω
      calc _ ≤ (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
            (2 * ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - G K (X i ω)‖ₑ ^ 2 +
              2 * ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2) := by
            gcongr with i
            refine (StatFormal.OTLimits.enorm_sub_sq_le _ (G K (X i ω)) _).trans_eq ?_
            rw [enorm_sub_rev (F (X i ω))]
        _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            ring
    calc _ ≤ ∫⁻ ω, (2 * ((n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
            ‖embed e K (u K n (sel K n (fun j => truncK e K (X j ω)) i)) - G K (X i ω)‖ₑ ^ 2) +
          2 * ((n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2)) ∂Pr := lintegral_mono hpt
      _ = 2 * a K n + 2 * ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2 ∂Pr := by
          rw [lintegral_add_right _ (hBm.const_mul 2), lintegral_const_mul _ ((hfix K).1 n),
            lintegral_const_mul _ hBm]
      _ ≤ 2 * a K n + 2 * b K := by
          gcongr
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hs i),
            lintegral_finset_sum _ (fun i _ => hs i)]
          have hi : ∀ i : Fin n, ∫⁻ ω, ‖G K (X i ω) - F (X i ω)‖ₑ ^ 2 ∂Pr = b K := by
            intro i
            have hbK : ∫⁻ x, ‖G K x - F x‖ₑ ^ 2 ∂(P : Measure H) = b K := rfl
            rw [← hbK, ← hlaw i, lintegral_map (by fun_prop) (hX i)]
          simp only [hi]
          exact avg_le n (fun _ => b K) fun _ => le_rfl
  -- diagonal
  obtain ⟨Kn, hmono, htend, hdiag⟩ := exists_diag a fun K => (hfix K).2
  refine ⟨Kn, hmono, htend, ?_⟩
  have hlim : Tendsto (fun n => 2 * a (Kn n) n + 2 * b (Kn n)) atTop (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul hdiag (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
      (ENNReal.Tendsto.const_mul (hblim.comp htend) (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => hdec (Kn n) n

end Main

end StatFormal.Wave25b
