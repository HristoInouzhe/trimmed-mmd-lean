import StatFormal.Archive.Wave23b.Statements
import StatFormal.Lib.Potentials.HilbertUniqueness

/-!
# Route — T `thm:population`, `eq:Hilbertinverse` (untrusted)

Foundations `exists_unique_optimal_graphPlan_of_lipNull` (Brenier–Gigli in a separable Hilbert space, for laws null on
Lipschitz hypersurfaces) gives unique optimal graph plans `(id × F)#ν` and `(id × Q)#μ`. The cost is symmetric, so the
swapped plan of the first is optimal from `μ` to `ν`, hence equals the second: this yields the a.e. inverse identities.
Tau Ceti's Rockafellar step puts each plan's support in a subdifferential graph (the convex potentials).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23b

open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap)

section Pop
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

lemma lintegral_sq_ne_top_of_bdd (ν : Measure H) [IsProbabilityMeasure ν] {B : ℝ} (hB : ∀ᵐ v ∂ν, ‖v‖ ≤ B) :
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal B ^ 2 ∂ν) (by simp) (lintegral_mono_ae ?_)
  filter_upwards [hB] with x hx
  rw [← ofReal_norm]
  exact pow_le_pow_left₀ (zero_le) (ENNReal.ofReal_le_ofReal hx) 2

lemma quadCost_symm (x y : H) : StatFormal.OTFD.Wave8c.quadCost (x, y) = StatFormal.OTFD.Wave8c.quadCost (y, x) := by
  simp only [StatFormal.OTFD.Wave8c.quadCost, norm_sub_rev]

lemma measurable_quadCost : Measurable (StatFormal.OTFD.Wave8c.quadCost (E := H)) :=
  (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)).measurable

/-- The swap of an optimal plan for the symmetric quadratic cost is optimal. -/
lemma isOptimal_swap {μ ν : Measure H} {π : Measure (H × H)}
    (h : IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost π ν μ) :
    IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost (π.map Prod.swap) μ ν := by
  refine ⟨h.toIsCoupling.swap, ?_⟩
  rw [lintegral_map measurable_quadCost measurable_swap,
    transportCost_comm measurable_quadCost (fun x y => quadCost_symm x y) μ ν, ← h.lintegral_eq]
  exact lintegral_congr fun z => quadCost_symm z.2 z.1

lemma lipNull_graph {ν : Measure H} (hν : StatFormal.OTFD.WaveL1.LipNull ν) :
    ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → ν S = 0 := fun S hS => hν S hS

/-- From one optimal graph plan to the inverse identity through uniqueness of the reverse plan. -/
lemma inverse_ae {μ ν : Measure H} {T S : H → H} (hT : Measurable T) (hS : Measurable S)
    (hTopt : IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost (graphPlan T ν) ν μ)
    (huniq : ∀ π, IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost π μ ν → π = graphPlan S μ) :
    ∀ᵐ x ∂ν, S (T x) = x := by
  have heq := huniq _ (isOptimal_swap hTopt)
  have hae : ∀ᵐ z ∂(graphPlan S μ), z.2 = S z.1 := ae_snd_eq_graphPlan hS.aemeasurable
  have hm : Measurable fun x : H => (x, T x) := measurable_id.prodMk hT
  rw [← heq, graphPlan_def, Measure.map_map measurable_swap hm] at hae
  have := ae_of_ae_map (measurable_swap.comp hm).aemeasurable hae
  filter_upwards [this] with x hx
  simp only [Function.comp_apply, Prod.swap_prod_mk, id] at hx
  exact hx.symm

lemma gradMap_of_opt {μ ν : Measure H} [IsProbabilityMeasure ν] {T : H → H} (hT : Measurable T)
    (hTopt : IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost (graphPlan T ν) ν μ)
    (hfin : transportCost StatFormal.OTFD.Wave8c.quadCost ν μ ≠ ∞) : IsGradMap ν μ T := by
  refine ⟨hT, ?_, ?_⟩
  · rw [← snd_graphPlan hT.aemeasurable, hTopt.toIsCoupling.snd_eq]
  · obtain ⟨u, -, -, -, -, hsub⟩ := hTopt.exists_support_subset_subdifferential hfin
    refine ⟨u, ?_⟩
    have hsupp : ∀ᵐ z ∂(graphPlan T ν), z ∈ (graphPlan T ν).support := Measure.support_mem_ae
    have : ∀ᵐ z ∂(graphPlan T ν), z.2 ∈ subdifferential (innerₗ H) u z.1 := hsupp.mono fun z hz => hsub hz
    rw [graphPlan_def] at this
    exact ae_of_ae_map (measurable_id.prodMk hT).aemeasurable this

end Pop

theorem pop_hilbert : Claims.pop_hilbert := by
  intro H _ _ _ _ _ _ ν μ _ _ B Bμ hν hμ hνB hμB
  have hν2 := lintegral_sq_ne_top_of_bdd ν hνB
  have hμ2 := lintegral_sq_ne_top_of_bdd μ hμB
  obtain ⟨T, hT, hTopt, hTu⟩ :=
    StatFormal.Potentials.exists_unique_optimal_graphPlan_of_lipNull (lipNull_graph hν) hν2 hμ2
  obtain ⟨S, hS, hSopt, hSu⟩ :=
    StatFormal.Potentials.exists_unique_optimal_graphPlan_of_lipNull (lipNull_graph hμ) hμ2 hν2
  have hfinνμ := StatFormal.OTLimits.transportCost_quadCost_ne_top ν μ hν2 hμ2
  have hfinμν := StatFormal.OTLimits.transportCost_quadCost_ne_top μ ν hμ2 hν2
  refine ⟨T, S, ⟨hT, hS, ?_, ?_, inverse_ae hS hT hSopt hTu, inverse_ae hT hS hTopt hSu⟩,
    gradMap_of_opt hT hTopt hfinνμ, gradMap_of_opt hS hSopt hfinμν, fun π => ⟨hTu π, ?_⟩,
    fun π => ⟨hSu π, ?_⟩⟩
  · rw [← snd_graphPlan hS.aemeasurable, hSopt.toIsCoupling.snd_eq]
  · rw [← snd_graphPlan hT.aemeasurable, hTopt.toIsCoupling.snd_eq]
  · rintro rfl; exact hTopt
  · rintro rfl; exact hSopt

end StatFormal.Wave23b
