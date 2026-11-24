import StatFormal.Archive.OTFD.WaveL2.Statements
import StatFormal.Archive.OTFD.Wave22a.RouteLaws
import StatFormal.Archive.OTFD.Wave22a.RouteStability
import StatFormal.Lib.Empirical.EnergyDistanceEuclid

/-!
# Route (wave L2): energy-distance identifiability and its uses (untrusted)

* `energyD_eq_energyDist`: the frozen iterated-integral energy distance equals the library's product-measure
  `StatFormal.Empirical.energyDist` under finite first moments (Fubini).
* `ed_nonneg`, `ed_eq_zero_iff`: the library's Székely–Rizzo theorem (`energyDist_nonneg`, `energyDist_eq_zero_iff`).
* `rt_fixedK_sep`: Brenier–McCann (Tau Ceti) gives `∇u⋆ ∘ F = id` `Λ_K`-a.e., hence `F` injective on a conull set;
  the frozen-route `rt_fixedK_laws` and identifiability give `𝓔_K > 0 ⇔ P_K ≠ Q_K`.
* `rt_lift_sep`: the frozen-route `rt_lift_laws` and identifiability.
* `t_stability_ed`: `Υ` is bounded, so identifiability turns `ED = 0` into `Υ#G#P_K = Υ#μ_K`; then the frozen-route
  `t_stability_eq`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL2

open StatFormal.OTFD.Scale (IsGauge ScaleHyp ups)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE headT liftMap)

section ED

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The frozen `energyD` is the library `energyDist` under finite first moments. -/
theorem energyD_eq_energyDist (ν ν' : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : Integrable id ν) (hν' : Integrable id ν') :
    energyD ν ν' = StatFormal.Empirical.energyDist ν ν' := by
  have key : ∀ (a b : Measure E) [IsProbabilityMeasure a] [IsProbabilityMeasure b],
      Integrable id a → Integrable id b →
        StatFormal.Empirical.meanDist a b = ∫ u, ∫ v, ‖u - v‖ ∂b ∂a := by
    intro a b _ _ ha hb
    have hint : Integrable (fun z : E × E => ‖z.1 - z.2‖) (a.prod b) := by
      refine Integrable.mono' ((ha.norm.comp_fst b).add (hb.norm.comp_snd a)) ?_ ?_
      · exact (continuous_fst.sub continuous_snd).norm.aestronglyMeasurable
      · exact Eventually.of_forall fun z => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using norm_sub_le z.1 z.2
    unfold StatFormal.Empirical.meanDist
    exact integral_prod _ hint
  unfold energyD StatFormal.Empirical.energyDist
  rw [key ν ν' hν hν', key ν ν hν hν, key ν' ν' hν' hν']

end ED

theorem ed_nonneg : Claims.ed_nonneg := by
  intro E _ _ _ _ _ ν ν' _ _ hν hν'
  rw [energyD_eq_energyDist ν ν' hν hν']
  exact StatFormal.Empirical.energyDist_nonneg hν hν'

theorem ed_eq_zero_iff : Claims.ed_eq_zero_iff := by
  intro E _ _ _ _ _ ν ν' _ _ hν hν'
  rw [energyD_eq_energyDist ν ν' hν hν']
  exact StatFormal.Empirical.energyDist_eq_zero_iff hν hν'

/-- Positivity form of identifiability. -/
theorem energyD_pos_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν ν' : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : Integrable id ν) (hν' : Integrable id ν') : 0 < energyD ν ν' ↔ ν ≠ ν' := by
  rw [energyD_eq_energyDist ν ν' hν hν', lt_iff_le_and_ne]
  have h0 := StatFormal.Empirical.energyDist_nonneg hν hν'
  have h1 := StatFormal.Empirical.energyDist_eq_zero_iff hν hν'
  constructor
  · rintro ⟨-, hne⟩ heq; exact hne (h1.2 heq).symm
  · intro hne; exact ⟨h0, fun h => hne (h1.1 h.symm)⟩

/-- `Integrable F P` from `F ∈ L¹(Λ)`, `Λ = θP + (1−θ)Q`. -/
theorem integrable_of_mix_left {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {P Q : Measure X} {θ : ℝ} (hθ : 0 < θ) {F : X → E} (h : Integrable F (mix θ P Q)) :
    Integrable F P := by
  have h1 : Integrable F (ENNReal.ofReal θ • P) := h.mono_measure (Measure.le_add_right le_rfl)
  exact (integrable_smul_measure (ENNReal.ofReal_pos.2 hθ).ne' ENNReal.ofReal_ne_top).1 h1

theorem integrable_of_mix_right {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {P Q : Measure X} {θ : ℝ} (hθ1 : θ < 1) {F : X → E} (h : Integrable F (mix θ P Q)) :
    Integrable F Q := by
  have h1 : Integrable F (ENNReal.ofReal (1 - θ) • Q) := h.mono_measure (Measure.le_add_left le_rfl)
  exact (integrable_smul_measure (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top).1 h1

instance mix_isProb {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {θ : ℝ} [Fact (0 ≤ θ)] [Fact (θ ≤ 1)] : IsProbabilityMeasure (mix θ P Q) := by
  constructor
  have h0 : 0 ≤ θ := Fact.out
  have h1 : θ ≤ 1 := Fact.out
  simp only [mix, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem isProbabilityMeasure_mix {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : IsProbabilityMeasure (mix θ P Q) := by
  have : Fact (0 ≤ θ) := ⟨h0⟩
  have : Fact (θ ≤ 1) := ⟨h1⟩
  infer_instance

theorem memLp_mix {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {P Q : Measure X} {θ : ℝ}
    {f : X → E} (hP : MemLp f 2 P) (hQ : MemLp f 2 Q) : MemLp f 2 (mix θ P Q) := by
  have hP' := (memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).1 hP
  have hQ' := (memLp_two_iff_integrable_sq_norm hQ.aestronglyMeasurable).1 hQ
  exact (memLp_two_iff_integrable_sq_norm
    ((hP.aestronglyMeasurable.smul_measure _).add_measure (hQ.aestronglyMeasurable.smul_measure _))).2
    ((hP'.smul_measure ENNReal.ofReal_ne_top).add_measure (hQ'.smul_measure ENNReal.ofReal_ne_top))

/-- **Brenier–McCann**: with `Λ ≪ Leb`, `μ ≪ Leb` and finite second moments, a map `F` that is `Λ`-a.e. the gradient
of a finite convex function pushing `Λ` to `μ` is injective on a measurable `Λ`-conull set. -/
theorem injOn_of_brenier {K : ℕ} (Λ μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure Λ]
    [IsProbabilityMeasure μ] (hΛ2 : MemLp id 2 Λ) (hμ2 : MemLp id 2 μ) (hΛ : Λ ≪ volume) (hμ : μ ≪ volume)
    {F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)} (hF : Measurable F) (hpush : Λ.map F = μ)
    (hgrad : IsConvGradAE Λ F) :
    ∃ S, MeasurableSet S ∧ Λ Sᶜ = 0 ∧ InjOn F S := by
  obtain ⟨φ, hφ, hgF⟩ := hgrad
  set c : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  have hlawF : HasLaw F μ Λ := ⟨hF.aemeasurable, hpush⟩
  have hoptF : TauCeti.IsKantorovichOptimalTransportMap c Λ μ F :=
    TauCeti.isKantorovichOptimalTransportMap_of_ae_mem_subdifferential hΛ2 hμ2 hlawF
      (hgF.mono fun x hx => StatFormal.OTFD.Wave22a.grad_mem_subdiff hφ hx)
  have hc : Continuous c :=
    ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)
  have hfin : TauCeti.transportCost c Λ μ ≠ ∞ := by
    have hcoup := (TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlawF
      hc.measurable.aemeasurable).1 hoptF
    rw [← hcoup.lintegral_eq,
      (TauCeti.isCoupling_graphPlan hlawF).lintegral_norm_sub_sq_div_two hΛ2 hμ2]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, -, -, -, -, -, hopt, -, hinv, -⟩ :=
    TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate
      (ρ := volume) hΛ hμ hfin
  obtain ⟨u', -, -, -, -, -, -, huniq⟩ :=
    TauCeti.exists_isKantorovichOptimalTransportMap_gradient (ρ := volume) hΛ hfin
  have hFT : F =ᵐ[Λ] gradient fun x => (u x).toReal := (huniq F hoptF).trans (huniq _ hopt).symm
  set T' := gradient fun y => (TauCeti.fenchelConjugate (innerₗ (EuclideanSpace ℝ (Fin K))) u y).toReal
  have hT' : Measurable T' := TauCeti.measurable_gradient _
  refine ⟨{x | T' (F x) = x}, measurableSet_eq_fun (hT'.comp hF) measurable_id, ?_, ?_⟩
  · have hae : ∀ᵐ x ∂Λ, T' (F x) = x := by
      filter_upwards [hinv, hFT] with x h1 h2
      rw [h2]; exact h1
    exact ae_iff.1 hae
  · intro x hx y hy hxy
    simp only [mem_ofPred_eq] at hx hy
    rw [← hx, ← hy, hxy]

end StatFormal.OTFD.WaveL2

namespace StatFormal.OTFD.WaveL2

open StatFormal.OTFD.Scale (IsGauge ScaleHyp ups)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE headT liftMap)

/-- `F ∈ L¹(Λ)` when `F#Λ = μ ∈ L²`. -/
theorem integrable_of_push {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {Λ : Measure X} {μ : Measure E} [IsProbabilityMeasure μ]
    {F : X → E} (hF : Measurable F) (hpush : Λ.map F = μ) (hμ : MemLp id 2 μ) : Integrable F Λ := by
  have h : Integrable id (Λ.map F) := hpush ▸ hμ.integrable one_le_two
  exact (integrable_map_measure h.aestronglyMeasurable hF.aemeasurable).1 h

theorem integrable_id_map {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {P : Measure X} {F : X → E} (hF : Measurable F)
    (h : Integrable F P) : Integrable id (P.map F) :=
  (integrable_map_measure aestronglyMeasurable_id hF.aemeasurable).2 h

theorem rt_fixedK_sep : Claims.rt_fixedK_sep := by
  intro K P Q μ _ _ _ θ F hθ hθ1 hP2 hQ2 hμ2 hac hμac hF hpush hgrad
  haveI := isProbabilityMeasure_mix P Q hθ.le hθ1.le
  obtain ⟨S, hS, hnull, hinj⟩ :=
    injOn_of_brenier (mix θ P Q) μ (memLp_mix hP2 hQ2) hμ2 hac hμac hF hpush hgrad
  have hlaws := StatFormal.OTFD.Wave22a.rt_fixedK_laws _ _ P Q θ F S hθ hθ1 hF hS hnull hinj
  have hFΛ := integrable_of_push hF hpush hμ2
  rw [energyD_pos_iff _ _ (integrable_id_map hF (integrable_of_mix_left hθ hFΛ))
    (integrable_id_map hF (integrable_of_mix_right hθ1 hFΛ)), Ne, hlaws]

theorem rt_lift_sep : Claims.rt_lift_sep := by
  intro K m P Q _ _ θ FK SK t I hθ hθ1 hFK hSK hinjK hnullK ht hI hinjI hnullI hintP hintQ
  have hlaws := StatFormal.OTFD.Wave22a.rt_lift_laws K m P Q θ FK SK t I hθ hθ1 hFK hSK hinjK hnullK ht hI
    hinjI hnullI
  have hL : Measurable (liftMap FK t) := StatFormal.OTFD.Wave22a.measurable_liftMap hFK ht
  rw [energyD_pos_iff _ _ (integrable_id_map hL hintP) (integrable_id_map hL hintQ), Ne, hlaws]

/-- `Υ` is bounded: `‖Υ r‖ ≤ a⁻¹` where `a‖x‖ ≤ g x`. -/
theorem exists_norm_ups_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ}
    (hg : IsGauge g) (h : ScaleHyp μ g) : ∃ C, ∀ r, ‖ups μ g r‖ ≤ C := by
  obtain ⟨a, ha, hle⟩ := hg.exists_mul_norm_le
  refine ⟨a⁻¹, fun r => ?_⟩
  have h2 : a * ‖ups μ g r‖ ≤ 1 := (hle _).trans (StatFormal.OTFD.Scale.g_ups_le_one hg h r)
  rw [← one_div, le_div_iff₀ ha]
  linarith [mul_comm a ‖ups μ g r‖]

/-- Laws on the probability scale have finite first moments. -/
theorem integrable_id_map_ups {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ}
    (hg : IsGauge g) (h : ScaleHyp μ g) (ν : Measure E) [IsProbabilityMeasure ν] :
    Integrable id (ν.map (ups μ g)) := by
  have hc := StatFormal.OTFD.Scale.continuous_ups hg h
  obtain ⟨C, hC⟩ := exists_norm_ups_le hg h
  refine integrable_id_map hc.measurable ?_
  exact Integrable.of_bound hc.aestronglyMeasurable C (Eventually.of_forall hC)

theorem t_stability_ed : Claims.t_stability_ed := by
  intro K ρ _ μ _ g P _ F G hg h hμ2 hPρ hP2 hF hG hPF hgF hgG hED
  apply StatFormal.OTFD.Wave22a.t_stability_eq K ρ μ g P F G hg h hμ2 hPρ hP2 hF hG hPF hgF hgG
  exact (ed_eq_zero_iff _ _ _ (integrable_id_map_ups hg h _) (integrable_id_map_ups hg h _)).1 hED

end StatFormal.OTFD.WaveL2
