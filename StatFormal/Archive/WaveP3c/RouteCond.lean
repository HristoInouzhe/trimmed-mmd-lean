import StatFormal.Archive.WaveP3c.Statements
import StatFormal.Archive.WaveP3c.RouteMcCann
import StatFormal.Archive.OTFD.WaveL8.RouteCond

/-!
# Route (wave P3c), part 2: McCann existence claims and the C discharges (untrusted)

`mccann_exists_fd` (`P ≪ Leb` ⇒ Lipschitz-null, then the moment-free existence of `RouteMcCann`) produces the
population map; the first conjunct of the certified wave-L8 `cond_potentials_weighted` produces its normalised
potential; the frozen wave-L8 claims give the second conjuncts verbatim.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3c

open StatFormal.OTFD.WaveL1 (IsCMMapAE LipNull Euc)
open StatFormal.OTFD.WaveL3 (RefLaw)
open StatFormal.OTFD.WaveL4 (WeightedFit)

theorem ghs_existence_lipNull : Claims.ghs_existence_lipNull :=
  fun _ _ _ _ _ _ _ P Q hP => exists_ghs_of_lipNull P Q hP

theorem mccann_exists_H : Claims.mccann_exists_H :=
  fun _ _ _ _ _ _ _ P Q hP => exists_isCMMapAE_of_lipNull P Q hP

theorem mccann_exists_fd : Claims.mccann_exists_fd :=
  fun _ P Q hP => exists_isCMMapAE_of_lipNull P Q (StatFormal.OTFD.WaveL3.lipNull_of_ac hP)

/-- The population pair: a McCann map from a reference law and its normalised potential. -/
theorem exists_pop_of_weightedFit {K : ℕ} {μ P : ProbabilityMeasure (Euc K)} {U : Set (Euc K)}
    {α ν : ℕ → ProbabilityMeasure (Euc K)} {χn g : ℕ → Euc K → ℝ} {ζ : ℕ → ℝ}
    (hR : RefLaw (μ : Measure (Euc K)) U) (hF : WeightedFit μ P U α ν χn g ζ) :
    ∃ (χ : Euc K → ℝ) (Q : Euc K → Euc K), Measurable Q ∧ (μ : Measure (Euc K)).map Q = P ∧
      IsCMMapAE (μ : Measure (Euc K)) Q ∧ ConvexOn ℝ (interior U) χ ∧
      Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧ IsGLB (χ '' interior U) 0 := by
  obtain ⟨Q, hQm, hmap, hcm⟩ := mccann_exists_fd K μ P hR.1
  obtain ⟨⟨χ, hχ, hQχ, h0⟩, -⟩ :=
    StatFormal.OTFD.WaveL8.cond_potentials_weighted K μ P U Q α ν χn g ζ hR hQm hmap hcm hF
  exact ⟨χ, Q, hQm, hmap, hcm, hχ, hQχ, h0⟩

theorem cond_potentials_weighted_mccann : Claims.cond_potentials_weighted_mccann := by
  intro K μ P U α ν χn g ζ hR hF
  refine ⟨mccann_exists_fd K μ P hR.1, fun Q hQm hmap hcm => ?_⟩
  exact StatFormal.OTFD.WaveL8.cond_potentials_weighted K μ P U Q α ν χn g ζ hR hQm hmap hcm hF

theorem cond_maps_ae_weighted_mccann : Claims.cond_maps_ae_weighted_mccann := by
  intro K μ P U Qn α ν χn g ζ hR hF hg hQn
  refine ⟨exists_pop_of_weightedFit hR hF, fun χ Q hQm hmap hχ hQχ => ?_⟩
  exact StatFormal.OTFD.WaveL8.cond_maps_ae_weighted K μ P U χ Q Qn α ν χn g ζ hR hQm hmap hχ hQχ hF hg hQn

theorem cond_band_one_sided_weighted_mccann : Claims.cond_band_one_sided_weighted_mccann := by
  intro K 𝒯 μ P U Qn α ν χn g ζ e EK hR hF hg hQn he
  refine ⟨exists_pop_of_weightedFit hR hF, fun A χ Q R hQm hmap hχ hQχ hA hQR => ?_⟩
  exact StatFormal.OTFD.WaveL8.cond_band_one_sided_weighted K 𝒯 μ P U A χ Q Qn α ν χn g ζ e R EK hR hQm hmap hχ
    hQχ hF hg hQn hA hQR he

theorem cond_test_coverage_weighted_mccann : Claims.cond_test_coverage_weighted_mccann := by
  intro K 𝒯 μ P U Qn α ν χn g ζ m e Ue Le EK κ hR hF hg hQn he hκ
  refine ⟨exists_pop_of_weightedFit hR hF, fun A χ Q R p hQm hmap hχ hQχ hA hQR hp hUL => ?_⟩
  exact StatFormal.OTFD.WaveL8.cond_test_coverage_weighted K 𝒯 μ P U A χ Q Qn α ν χn g ζ m e Ue Le R EK p κ hR hQm
    hmap hχ hQχ hF hg hQn hA hQR he hp hκ hUL

/-- A measure whose image is a probability measure is nonzero, so an a.e. property has a witness. -/
theorem exists_of_ae_of_map_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {K : ℕ}
    {G : Ω → Euc K} {μ : ProbabilityMeasure (Euc K)} (hG : P.map G = μ) {q : Ω → Prop}
    (hq : ∀ᵐ ω ∂P, q ω) : ∃ ω, q ω := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [Measure.map_zero] at hG
    have h1 := measure_univ (μ := (μ : Measure (Euc K)))
    rw [← hG, Measure.coe_zero, Pi.zero_apply] at h1
    exact zero_ne_one h1
  haveI : (ae P).NeBot := ae_neBot.2 hP
  exact hq.exists

theorem cond_transfer_consistency_weighted_mccann : Claims.cond_transfer_consistency_weighted_mccann := by
  intro K Ω _ P μ P' U DF Z F Fh Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hfit hQh
  refine ⟨?_, fun χ' Q' hχ' hQχ' hQm hmap => ?_⟩
  · obtain ⟨ω, hω, -⟩ := exists_of_ae_of_map_eq hmapP hfit
    exact exists_pop_of_weightedFit hR hω
  · exact StatFormal.OTFD.WaveL8.cond_transfer_consistency_weighted K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ hR hZ
      hFm hmapP hDF hFh hχ' hQχ' hQm hmap hfit hQh

theorem cond_transfer_consistency_prob_weighted_mccann : Claims.cond_transfer_consistency_prob_weighted_mccann := by
  intro K Ω _ P _ μ P' U DF Z F Fh Qh α ν χn g ζ hR hZ hFm hmapP hDF hFh hfit hQh hmeas
  refine ⟨?_, fun χ' Q' hχ' hQχ' hQm hmap => ?_⟩
  · obtain ⟨ω, hω, -⟩ := exists_of_ae_of_map_eq hmapP hfit
    exact exists_pop_of_weightedFit hR hω
  · exact StatFormal.OTFD.WaveL8.cond_transfer_consistency_prob_weighted K Ω P μ P' U DF Z F Fh χ' Q' Qh α ν χn g ζ
      hR hZ hFm hmapP hDF hFh hχ' hQχ' hQm hmap hfit hQh hmeas

theorem cond_rank_consistency_mccann : Claims.cond_rank_consistency_mccann := by
  intro K n M ε R z f u g μ P U α ν ζ ρ hR hF hα hu hε hεlog hcol hz hρ
  refine ⟨mccann_exists_fd K μ P hR.1, fun Q hQm hmap hcm => ?_⟩
  exact StatFormal.OTFD.WaveL8.cond_rank_consistency_uncond K n M ε R z f u g μ P U Q α ν ζ ρ hR hQm hmap hcm hF hα
    hu hε hεlog hcol hz hρ

end StatFormal.WaveP3c
