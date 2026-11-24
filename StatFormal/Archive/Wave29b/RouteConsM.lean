import StatFormal.Archive.Wave29b.Statements
import StatFormal.Archive.WaveP3c.RouteGS
import StatFormal.Archive.OTFD.Wave8c.RouteTransfer
import StatFormal.Lib.BandSupport.MatrixGauge

/-!
# Route — B `thm:consistency` for a general symmetric positive definite `M_K` (untrusted)

The `M_K`-cost estimator for the reference `μ_K` is the Euclidean (Ghosal–Sen) estimator for the reference
`M_K#μ_K`: with `(z, u) ↦ (z, M_K u)` the coupling `γ_n` becomes a coupling of `P̂_n` and `M_K#μ_K` carried by the
subgradient graph of `ψ̂_n` (closed, as `ψ̂_n` is continuous), `M_K#μ_K` is carried by `B(0, L')`, and the population
map becomes `M_K F`. The certified WaveP3c `ghosal_sen_uniform` gives `M_K F̂_n → M_K F` uniformly on `𝒦` almost surely,
the uniformly continuous `M_K⁻¹` gives `F̂_n → F`, and the frozen Wave 24a `consistency_B` gives the depths.
This is the paper's reduction with the change of variables `u ↦ M_K u` on the reference side instead of
`L = M_K^{1/2}` on both sides (the data side is untouched).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29b

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open StatFormal.OTFD.Wave8c (mvec measurable_mvec continuous_mvec mvec_inv_mul det_ne_zero_of_posDef)

/-- The subgradient graph of a continuous function is closed. -/
lemma isClosed_subgradGraph {K : ℕ} {φ : Euc K → ℝ} (hφ : Continuous φ) :
    IsClosed {p : Euc K × Euc K | IsSubgrad φ p.1 p.2} := by
  have : {p : Euc K × Euc K | IsSubgrad φ p.1 p.2} =
      ⋂ z, {p : Euc K × Euc K | φ p.1 + ⟪p.2, z - p.1⟫ ≤ φ z} := by
    ext p; simp [IsSubgrad]
  rw [this]
  refine isClosed_iInter fun z => isClosed_le ?_ continuous_const
  exact (hφ.comp continuous_fst).add (continuous_snd.inner (continuous_const.sub continuous_fst))

theorem cons_general_M : Claims.cons_general_M := by
  intro K Ω H _ Pr _ Z P μ MK ψ F R L L' ψh γ Fh 𝒦 PiK g cK c' hMK hind hlaw hac hμR hML' hψc hψL hFm hmap hsub
    h𝒦c h𝒦i hgrad hfst hsnd hsupp hψhL hFh hg1 hg2 hg3 hcK hgF
  have hfm : Measurable (mvec MK) := measurable_mvec MK
  set μ' : ProbabilityMeasure (Euc K) := μ.map (mvec MK) with hμ'
  set G : Euc K × Euc K → Euc K × Euc K := fun p => (p.1, mvec MK p.2) with hG
  have hGm : Measurable G := measurable_fst.prodMk (hfm.comp measurable_snd)
  set γ' : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K) := fun n ω => (γ n ω).map G with hγ'
  -- the reference `M_K#μ_K` is carried by `B(0, L')`
  have hμ'R : (μ' : Measure (Euc K)) (closedBall 0 L')ᶜ = 0 := by
    rw [hμ', ProbabilityMeasure.toMeasure_map, Measure.map_apply hfm isClosed_closedBall.measurableSet.compl]
    refine measure_mono_null (fun u hu => ?_) hμR
    simp only [mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hu ⊢
    by_contra h
    push Not at h
    have := hML' u (by rw [mem_closedBall, dist_zero_right]; exact h)
    linarith
  have hmap' : (P : Measure (Euc K)).map (fun x => mvec MK (F x)) = μ' := by
    rw [hμ', ProbabilityMeasure.toMeasure_map, ← hmap, Measure.map_map hfm hFm]; rfl
  have hfst' : ∀ n ω, (γ' n ω : Measure (Euc K × Euc K)).fst =
      (TauCeti.Probability.empiricalMeasure (fun i => Z i ω) n : Measure (Euc K)) := by
    intro n ω
    rw [← hfst n ω, hγ', ProbabilityMeasure.toMeasure_map, hG,
      Measure.fst_map_prodMk (X := Prod.fst) (Y := fun p : Euc K × Euc K => mvec MK p.2) measurable_fst
        (hfm.comp measurable_snd)]
    rfl
  have hsnd' : ∀ n ω, (γ' n ω : Measure (Euc K × Euc K)).snd = μ' := by
    intro n ω
    rw [hγ', ProbabilityMeasure.toMeasure_map, hG,
      Measure.snd_map_prodMk (X := Prod.fst) (Y := fun p : Euc K × Euc K => mvec MK p.2) measurable_fst
        (hfm.comp measurable_snd),
      hμ', ProbabilityMeasure.toMeasure_map, ← hsnd n ω, Measure.snd, Measure.map_map hfm measurable_snd]
    rfl
  have hsupp' : ∀ n ω, (γ' n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 p.2} := by
    intro n ω
    have hcont : Continuous (ψh n ω) := by
      refine Metric.continuous_iff.2 fun x ε hε => ⟨ε / (|L'| + 1), div_pos hε (by positivity), fun y hy => ?_⟩
      rw [Real.dist_eq]
      have h1 := hψhL n ω y x
      have h2 : L' * ‖y - x‖ ≤ |L'| * ‖y - x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      have h3 : |L'| * ‖y - x‖ ≤ |L'| * (ε / (|L'| + 1)) := by
        rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left hy.le (abs_nonneg _)
      have h4 : |L'| * (ε / (|L'| + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg L']
      linarith
    have hC := isClosed_subgradGraph hcont
    refine Measure.support_subset_of_isClosed hC ?_
    rw [hγ', ProbabilityMeasure.toMeasure_map]
    refine (ae_map_iff hGm.aemeasurable hC.measurableSet).2 ?_
    filter_upwards [Measure.support_mem_ae (μ := (γ n ω : Measure (Euc K × Euc K)))] with q hq
    exact hsupp n ω hq
  have hGS := StatFormal.WaveP3c.ghosal_sen_uniform K Ω Pr Z P μ' ψ (fun x => mvec MK (F x)) L' L ψh γ'
    (fun n ω x => mvec MK (Fh n ω x)) 𝒦 hind hlaw hac hμ'R hψc hψL (hfm.comp hFm) hmap' hsub h𝒦c h𝒦i hgrad hfst'
    hsnd' hsupp' hψhL hFh
  have hdet := det_ne_zero_of_posDef hMK
  have hu : UniformContinuous (mvec MK⁻¹) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin MK⁻¹)).uniformContinuous
  have hconv : ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦 := by
    filter_upwards [hGS] with ω hω
    have := hu.comp_tendstoUniformlyOn hω
    simpa [Function.comp_def, mvec_inv_mul hdet] using this
  have hB := StatFormal.Wave24a.consistency_B Ω (Euc K) H Pr PiK g cK c' F Fh 𝒦 hg1 hg2 hg3 hcK hgF
  refine ⟨hB.1, ?_⟩
  filter_upwards [hconv, hB.2 hconv] with ω h1 h2
  exact ⟨h1, h2.1, h2.2⟩

theorem cons_cprime : Claims.cons_cprime := by
  intro K M hM hK
  have : NeZero K := ⟨hK.ne'⟩
  have hH := hM.isHermitian
  set Λ := ⨆ i, hH.eigenvalues i with hΛ
  obtain ⟨u₀, hu₀, hq₀⟩ := StatFormal.BandSupport.exists_top_eigenvector hH
  have hle : ∀ u, StatFormal.OTFD.Wave8c.mnorm M u ≤ Real.sqrt Λ * ‖u‖ := by
    intro u
    rw [StatFormal.BandSupport.mnorm_eq_sqrt_inner, ← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (StatFormal.BandSupport.inner_mvec_le hH u)
  have hat : StatFormal.OTFD.Wave8c.mnorm M u₀ = Real.sqrt Λ := by
    rw [StatFormal.BandSupport.mnorm_eq_sqrt_inner, hq₀]
  refine ⟨⟨⟨u₀, hu₀, hat.symm⟩, ?_⟩, fun c => ⟨fun h => ?_, fun h u => ?_⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    simpa [hu] using hle u
  · simpa [hat, hu₀] using h u₀
  · exact (hle u).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

end StatFormal.Wave29b
