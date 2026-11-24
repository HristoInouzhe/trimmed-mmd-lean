import StatFormal.Wave31to.RouteB
import StatFormal.Wave30tx.RouteContact
import StatFormal.Wave31ti.RoutePath

/-!
# Route C (untrusted): `prop:newslopegeneral` and `prop:newslope` (a), (b)

For `z, z′` in the supports and `ρ > 0`, with `U = φ⁻¹B(z,ρ)`, `V = φ⁻¹B(z′,ρ)`, `a = (P−R)(U)`, `b = (Q−R)(V)` (`R = P ⊓ Q`), the
measures `P_ε = R + (ε/a)(P−R)|_U ≤ P` and `Q_ε = R + (ε/b)(Q−R)|_V ≤ Q` have mass `1 − α⋆ + ε` for `ε ≤ min(a,b)`; normalised, they
are `(α⋆−ε)`-trimmings, so `u(α⋆−ε) ≤ ‖∫φ dP_ε − ∫φ dQ_ε‖ ≤ ε(‖z−z′‖ + 2ρ)` (`dTrim = Dpop`, certified `Wave8a.georep_dist`).
Supports: closed (balls), of full mass (second countability of the separable `H`), nonempty (mass `α⋆ > 0`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31to.RouteC

open StatFormal.TrimmedMMD.Unconditional StatFormal.Distances StatFormal.Wave31to.RouteA StatFormal.Wave31to.RouteB

section Supp

variable {X K : Type*} [MeasurableSpace X] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem supp_closed (φ : X → K) (μ : Measure X) : IsClosed {z | InSuppImg φ μ z} := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro z hz
  simp only [mem_compl_iff, mem_setOf_eq, InSuppImg, not_forall, not_lt] at hz
  obtain ⟨ρ, hρ, h0⟩ := hz
  refine ⟨ρ / 2, by positivity, fun z' hz' => ?_⟩
  simp only [mem_compl_iff, mem_setOf_eq, InSuppImg, not_forall, not_lt]
  refine ⟨ρ / 2, by positivity, le_of_eq ?_⟩
  refine measure_mono_null (fun x hx => ?_) (nonpos_iff_eq_zero.1 h0)
  simp only [mem_preimage, Metric.mem_ball] at hx hz' ⊢
  calc dist (φ x) z ≤ dist (φ x) z' + dist z' z := dist_triangle _ _ _
    _ < ρ / 2 + ρ / 2 := add_lt_add hx hz'
    _ = ρ := by ring

theorem supp_full [TopologicalSpace.SeparableSpace K] (φ : X → K) (μ : Measure X) :
    μ (φ ⁻¹' {z | InSuppImg φ μ z}ᶜ) = 0 := by
  haveI : SecondCountableTopology K := UniformSpace.secondCountable_of_separable K
  have hrad : ∀ z : {z // z ∈ {z | InSuppImg φ μ z}ᶜ}, ∃ ρ : ℝ, 0 < ρ ∧ μ (φ ⁻¹' Metric.ball z.1 ρ) = 0 := by
    rintro ⟨z, hz⟩
    simp only [mem_compl_iff, mem_setOf_eq, InSuppImg, not_forall, not_lt] at hz
    obtain ⟨ρ, hρ, h0⟩ := hz
    exact ⟨ρ, hρ, nonpos_iff_eq_zero.1 h0⟩
  choose ρ hρ h0 using hrad
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun i => Metric.ball i.1 (ρ i))
    (fun i => Metric.isOpen_ball)
  have hsub : {z | InSuppImg φ μ z}ᶜ ⊆ ⋃ i ∈ T, Metric.ball i.1 (ρ i) := by
    intro z hz
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨z, hz⟩, Metric.mem_ball_self (hρ _)⟩
  refine measure_mono_null (preimage_mono hsub) ?_
  rw [preimage_iUnion₂]
  exact (measure_biUnion_null_iff hTc).2 fun i _ => h0 i

end Supp

section Main

variable {X : Type} [MeasurableSpace X] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

instance finite_inf (P Q : Measure X) [IsFiniteMeasure P] : IsFiniteMeasure (P ⊓ Q) :=
  isFiniteMeasure_of_le P inf_le_left

theorem mass_sub (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (P - P ⊓ Q) univ = ENNReal.ofReal (tvDist P Q) := by
  rw [Measure.sub_apply MeasurableSet.univ inf_le_left, measure_univ,
    StatFormal.Wave30tx.RContact.inf_univ P Q]
  have h0 := tvDist_nonneg P Q
  have h1 : tvDist P Q ≤ 1 := tvDist_le_one
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

theorem supp_nonempty (φ : X → K) (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hα0 : 0 < tvDist P Q) : ∃ z, InSuppImg φ (P - P ⊓ Q) z := by
  by_contra h
  push Not at h
  have hall : {z | InSuppImg φ (P - P ⊓ Q) z}ᶜ = univ := by
    ext z; simp [h z]
  have := supp_full φ (P - P ⊓ Q)
  rw [hall, preimage_univ, mass_sub] at this
  exact (ENNReal.ofReal_pos.2 hα0).ne' this

/-- The trimming built from the common part and a piece of the contamination. -/
theorem piece_mem (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {U : Set X}
    (hU : MeasurableSet U) {a ε : ℝ} (ha : (P - P ⊓ Q) U = ENNReal.ofReal a) (hapos : 0 < a)
    (hε0 : 0 < ε) (hεa : ε ≤ a) (hα1 : tvDist P Q < 1) :
    let Pε := P ⊓ Q + ENNReal.ofReal (ε / a) • (P - P ⊓ Q).restrict U
    Pε ≤ P ∧ Pε univ = ENNReal.ofReal (1 - tvDist P Q + ε) ∧
    ENNReal.ofReal (1 / (1 - (tvDist P Q - ε))) • Pε ∈ StatFormal.Wave8a.trimSet P (tvDist P Q - ε) := by
  intro Pε
  have hc1 : ENNReal.ofReal (ε / a) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by rw [div_le_one hapos]; exact hεa)
  have hle : Pε ≤ P := by
    have hpiece : ENNReal.ofReal (ε / a) • (P - P ⊓ Q).restrict U ≤ P - P ⊓ Q := by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.smul_apply, smul_eq_mul]
      calc ENNReal.ofReal (ε / a) * (P - P ⊓ Q).restrict U s ≤ 1 * (P - P ⊓ Q).restrict U s := by gcongr
        _ = (P - P ⊓ Q).restrict U s := one_mul _
        _ ≤ (P - P ⊓ Q) s := Measure.restrict_apply_le _ _
    rw [Measure.le_iff]
    intro s hs
    have h1 := (Measure.le_iff.1 hpiece) s hs
    calc Pε s = (P ⊓ Q) s + (ENNReal.ofReal (ε / a) • (P - P ⊓ Q).restrict U) s := Measure.add_apply _ _ _
      _ ≤ (P ⊓ Q) s + (P - P ⊓ Q) s := by gcongr
      _ = P s := by
        rw [← Measure.add_apply, add_comm, Measure.sub_add_cancel_of_le inf_le_left]
  have hmass : Pε univ = ENNReal.ofReal (1 - tvDist P Q + ε) := by
    simp only [Pε, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, ha, StatFormal.Wave30tx.RContact.inf_univ P Q]
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hapos.ne',
      ← ENNReal.ofReal_add (by linarith) hε0.le]
  refine ⟨hle, hmass, ?_⟩
  have hb : 0 < 1 - (tvDist P Q - ε) := by linarith
  have hfin : IsFiniteMeasure Pε := isFiniteMeasure_of_le P hle
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, hmass, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 - (tvDist P Q - ε) = 1 - tvDist P Q + ε by ring] at hb ⊢
    rw [one_div, inv_mul_cancel₀ hb.ne', ENNReal.ofReal_one]
  · exact (Measure.absolutelyContinuous_of_le hle).smul_left _
  · have h1 : Pε.rnDeriv P ≤ᵐ[P] 1 := Measure.rnDeriv_le_one_of_le hle
    have h2 := Measure.rnDeriv_smul_left_of_ne_top Pε P
      (r := ENNReal.ofReal (1 / (1 - (tvDist P Q - ε)))) ENNReal.ofReal_ne_top
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2, Pi.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (1 / (1 - (tvDist P Q - ε))) * Pε.rnDeriv P x
        ≤ ENNReal.ofReal (1 / (1 - (tvDist P Q - ε))) * 1 := by gcongr; exact hx1
      _ = _ := mul_one _

theorem piece_integral (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : X → K}
    (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {U : Set X} {a ε : ℝ} (hapos : 0 < a) (hε0 : 0 < ε) :
    ∫ x, φ x ∂(P ⊓ Q + ENNReal.ofReal (ε / a) • (P - P ⊓ Q).restrict U) =
      ∫ x, φ x ∂(P ⊓ Q) + (ε / a) • ∫ x in U, φ x ∂(P - P ⊓ Q) := by
  haveI : IsFiniteMeasure (P - P ⊓ Q) := isFiniteMeasure_of_le P Measure.sub_le
  haveI := Measure.smul_finite ((P - P ⊓ Q).restrict U) (ENNReal.ofReal_ne_top (r := ε / a))
  rw [integral_add_measure (integrable_phi _ hφ hκ) (integrable_phi _ hφ hκ), integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]

/-- On `U = φ⁻¹B(z,ρ)` of mass `a`, `‖∫_U φ − a z‖ ≤ ρ a`. -/
theorem piece_close (μ : Measure X) [IsFiniteMeasure μ] {φ : X → K} (hφ : StronglyMeasurable φ) {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {z : K} {ρ a : ℝ} {U : Set X} (hUdef : U = φ ⁻¹' Metric.ball z ρ) (hU : MeasurableSet U)
    (ha : μ U = ENNReal.ofReal a) (ha0 : 0 ≤ a) : ‖∫ x in U, φ x ∂μ - a • z‖ ≤ ρ * a := by
  have hint : ∫ x in U, z ∂μ = a • z := by
    rw [setIntegral_const, measureReal_def, ha, ENNReal.toReal_ofReal ha0]
  rw [← hint, ← integral_sub (integrable_phi _ hφ hκ) (integrable_const z)]
  have hle := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := U) (f := fun x => φ x - z) (C := ρ)
    (measure_lt_top μ U) (fun x hx => by
      rw [hUdef] at hx
      simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
      exact hx.le)
  rw [measureReal_def, ha, ENNReal.toReal_ofReal ha0] at hle
  exact hle

theorem slope_bound_pair (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : X → K}
    (hφ : StronglyMeasurable φ) {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 < tvDist P Q) (hα1 : tvDist P Q < 1)
    {z z' : K} (hz : InSuppImg φ (P - P ⊓ Q) z) (hz' : InSuppImg φ (Q - P ⊓ Q) z') {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ e₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) e₀,
      StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) / ε ≤ ‖z - z'‖ + 2 * ρ := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  have hφm : Measurable φ := hφ.measurable
  haveI : IsFiniteMeasure (P - P ⊓ Q) := isFiniteMeasure_of_le P Measure.sub_le
  haveI : IsFiniteMeasure (Q - P ⊓ Q) := isFiniteMeasure_of_le Q Measure.sub_le
  set U := φ ⁻¹' Metric.ball z ρ with hUdef
  set V := φ ⁻¹' Metric.ball z' ρ with hVdef
  have hU : MeasurableSet U := hφm measurableSet_ball
  have hV : MeasurableSet V := hφm measurableSet_ball
  set a := ((P - P ⊓ Q) U).toReal
  set b := ((Q - P ⊓ Q) V).toReal
  have haU : (P - P ⊓ Q) U = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hbV : (Q - P ⊓ Q) V = ENNReal.ofReal b := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hapos : 0 < a := ENNReal.toReal_pos (hz ρ hρ).ne' (measure_ne_top _ _)
  have hbpos : 0 < b := ENNReal.toReal_pos (hz' ρ hρ).ne' (measure_ne_top _ _)
  have hQinf : Q ⊓ P = P ⊓ Q := inf_comm Q P
  have htvc : tvDist Q P = tvDist P Q := tvDist_comm Q P
  refine ⟨min a b, lt_min hapos hbpos, fun ε hε => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεa : ε ≤ a := hε.2.le.trans (min_le_left _ _)
  have hεb : ε ≤ b := hε.2.le.trans (min_le_right _ _)
  obtain ⟨-, -, hPm⟩ := piece_mem P Q hU haU hapos hε0 hεa hα1
  have hQ := piece_mem Q P (U := V) hV (a := b) (by rw [hQinf]; exact hbV) hbpos hε0 hεb (by rw [htvc]; exact hα1)
  rw [hQinf, htvc] at hQ
  obtain ⟨-, -, hQm⟩ := hQ
  set c := 1 - (tvDist P Q - ε)
  have hc : 0 < c := by simp only [c]; linarith
  have hα0' : 0 ≤ tvDist P Q - ε := by
    have : a ≤ tvDist P Q := by
      have h1 : (P - P ⊓ Q) U ≤ (P - P ⊓ Q) univ := measure_mono (subset_univ _)
      rw [mass_sub, haU] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hα0.le).1 h1
    linarith
  have hα1' : tvDist P Q - ε < 1 := by linarith
  -- the distance at the level `α⋆ − ε`
  have hdist := StatFormal.Wave8a.georep_dist X K P Q φ κ (tvDist P Q - ε) hφ hκ hα0' hα1'
  set P' := ENNReal.ofReal (1 / c) • (P ⊓ Q + ENNReal.ofReal (ε / a) • (P - P ⊓ Q).restrict U)
  set Q' := ENNReal.ofReal (1 / c) • (P ⊓ Q + ENNReal.ofReal (ε / b) • (Q - P ⊓ Q).restrict V)
  have hD : Dpop φ P Q (tvDist P Q - ε) ≤ ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ := by
    rw [← hdist]
    refine csInf_le ⟨0, ?_⟩ ⟨P', hPm, Q', hQm, rfl⟩
    rintro r ⟨_, _, _, _, rfl⟩; exact norm_nonneg _
  have hP'i : ∫ x, φ x ∂P' = (1 / c) • (∫ x, φ x ∂(P ⊓ Q) + (ε / a) • ∫ x in U, φ x ∂(P - P ⊓ Q)) := by
    rw [integral_smul_measure, piece_integral P Q hφ hκ hapos hε0, ENNReal.toReal_ofReal (by positivity)]
  have hQ'i : ∫ x, φ x ∂Q' = (1 / c) • (∫ x, φ x ∂(P ⊓ Q) + (ε / b) • ∫ x in V, φ x ∂(Q - P ⊓ Q)) := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
    congr 1
    haveI : IsFiniteMeasure (Q - P ⊓ Q) := isFiniteMeasure_of_le Q Measure.sub_le
    haveI := Measure.smul_finite ((Q - P ⊓ Q).restrict V) (ENNReal.ofReal_ne_top (r := ε / b))
    rw [integral_add_measure (integrable_phi _ hφ hκ) (integrable_phi _ hφ hκ), integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity)]
  have hcU := piece_close (P - P ⊓ Q) hφ hκ hUdef hU haU hapos.le
  have hcV := piece_close (Q - P ⊓ Q) hφ hκ hVdef hV hbV hbpos.le
  -- the key estimate
  have hkey : ‖(ε / a) • ∫ x in U, φ x ∂(P - P ⊓ Q) - (ε / b) • ∫ x in V, φ x ∂(Q - P ⊓ Q)‖ ≤
      ε * (‖z - z'‖ + 2 * ρ) := by
    have hsplit : (ε / a) • ∫ x in U, φ x ∂(P - P ⊓ Q) - (ε / b) • ∫ x in V, φ x ∂(Q - P ⊓ Q) =
        (ε / a) • (∫ x in U, φ x ∂(P - P ⊓ Q) - a • z) - (ε / b) • (∫ x in V, φ x ∂(Q - P ⊓ Q) - b • z') +
          ε • (z - z') := by
      simp only [smul_sub, smul_smul]
      rw [div_mul_cancel₀ _ hapos.ne', div_mul_cancel₀ _ hbpos.ne']
      abel
    rw [hsplit]
    set X1 := ∫ x in U, φ x ∂(P - P ⊓ Q) - a • z
    set X2 := ∫ x in V, φ x ∂(Q - P ⊓ Q) - b • z'
    have h1 := norm_add_le ((ε / a) • X1 - (ε / b) • X2) (ε • (z - z'))
    have h2 := norm_sub_le ((ε / a) • X1) ((ε / b) • X2)
    have h3 : ‖(ε / a) • X1‖ ≤ (ε / a) * (ρ * a) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; gcongr
    have h4 : ‖(ε / b) • X2‖ ≤ (ε / b) * (ρ * b) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; gcongr
    have h5 : ‖ε • (z - z')‖ = ε * ‖z - z'‖ := by rw [norm_smul, Real.norm_of_nonneg hε0.le]
    have h6 : (ε / a) * (ρ * a) = ε * ρ := by field_simp
    have h7 : (ε / b) * (ρ * b) = ε * ρ := by field_simp
    nlinarith
  rw [div_le_iff₀ hε0]
  unfold StatFormal.Wave31ti.uPath
  have hdiff : ∫ x, φ x ∂P' - ∫ x, φ x ∂Q' =
      (1 / c) • ((ε / a) • ∫ x in U, φ x ∂(P - P ⊓ Q) - (ε / b) • ∫ x in V, φ x ∂(Q - P ⊓ Q)) := by
    rw [hP'i, hQ'i, ← smul_sub]; congr 1; abel
  rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity)] at hD
  calc c * Dpop φ P Q (tvDist P Q - ε) ≤ c * (1 / c * ε * (‖z - z'‖ + 2 * ρ)) := by
        refine mul_le_mul_of_nonneg_left (hD.trans ?_) hc.le
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (‖z - z'‖ + 2 * ρ) * ε := by field_simp

end Main

theorem newslopegeneral_route : Claims.newslopegeneral := by
  intro X K _ _ _ _ _ P Q _ _ φ κ hφ hκ hα0 hα1
  have hQinf : Q ⊓ P = P ⊓ Q := inf_comm Q P
  have htvc : tvDist Q P = tvDist P Q := tvDist_comm Q P
  refine ⟨?_, supp_closed φ _, supp_closed φ _, supp_nonempty φ P Q hα0, ?_, supp_full φ _, supp_full φ _⟩
  · intro s hs z z' hz hz'
    refine le_of_forall_pos_le_add fun ρ' hρ' => ?_
    have hρ : 0 < ρ' / 2 := by positivity
    obtain ⟨e₀, he₀, hb⟩ := slope_bound_pair P Q hφ hκ hα0 hα1 hz hz' hρ
    have hev : ∀ᶠ e in 𝓝[>] (0 : ℝ), StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - e) / e ≤ ‖z - z'‖ + 2 * (ρ' / 2) := by
      filter_upwards [Ioo_mem_nhdsGT he₀] with e he using hb e he
    have := le_of_tendsto hs hev
    linarith
  · have := supp_nonempty φ Q P (by rw [htvc]; exact hα0)
    rwa [hQinf] at this

theorem newslope_a_route : Claims.newslope_a := by
  intro X K _ _ _ _ _ _ _ P Q _ _ φ κ hφ hcont hκ hα0 hα1 s hs x hx y hy
  have hfun : (fun e => (1 - tvDist P Q + e) * Dpop φ P Q (tvDist P Q - e) / e) =
      fun e => StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - e) / e := by
    funext e; unfold StatFormal.Wave31ti.uPath; ring_nf
  rw [hfun] at hs
  have hsupp : ∀ (μ : Measure X) (w : X), w ∈ μ.support → InSuppImg φ μ (φ w) := by
    intro μ w hw ρ hρ
    exact (Measure.mem_support_iff_forall w).1 hw _
      (hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  exact (newslopegeneral_route X K P Q φ κ hφ hκ hα0 hα1).1 s hs (φ x) (φ y) (hsupp _ x hx) (hsupp _ y hy)

theorem newslope_b_route : Claims.newslope_b := by
  intro X K _ _ _ _ _ _ _ P Q _ _ φ κ hφ hcont hκ hα0 hα1 hmeet
  obtain ⟨x, hxP, hxQ⟩ := hmeet
  have hfun : (fun e => (1 - tvDist P Q + e) * Dpop φ P Q (tvDist P Q - e) / e) =
      fun e => StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - e) / e := by
    funext e; unfold StatFormal.Wave31ti.uPath; ring_nf
  have hpc := StatFormal.Wave31ti.pathconvex_ii X K P Q φ κ hφ hκ hα0 hα1
  have hzero : ∀ s, Tendsto (fun e => (1 - tvDist P Q + e) * Dpop φ P Q (tvDist P Q - e) / e) (𝓝[>] 0) (𝓝 s) →
      s = 0 := by
    intro s hs
    have h1 := newslope_a_route X K P Q φ κ hφ hcont hκ hα0 hα1 s hs x hxP x hxQ
    rw [sub_self, norm_zero] at h1
    rw [hfun] at hs
    have h2 := (hpc.2.2.1 s hs).1
    linarith
  refine ⟨hzero, ?_⟩
  obtain ⟨s₀, hs₀⟩ := hpc.2.1
  have h0 : s₀ = 0 := hzero s₀ (by rw [hfun]; exact hs₀)
  have hiff := (hpc.2.2.1 s₀ hs₀).2.1
  rw [hiff, h0]
  exact lt_irrefl 0

end StatFormal.Wave31to.RouteC
