import StatFormal.Wave30tj.RouteBlind
import Mathlib.MeasureTheory.Function.Floor

/-!
# Route (wave 30tj): the laws `P₀`, `Q_N` of the kernel-blindness construction (untrusted)
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace StatFormal.Wave30tj

open MeasureTheory Set Filter Topology
open scoped ENNReal

open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.Unconditional (Dpop setDist)
open StatFormal.Distances (tvDist)

instance unifLaw_isProb : IsProbabilityMeasure unifLaw := ⟨by simp [unifLaw, Real.volume_Icc]⟩

lemma integral_unifLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) :
    ∫ x, F x ∂unifLaw = ∫ x in Icc (0 : ℝ) 1, F x := rfl

section Law
variable {s : ℝ → ℝ} (hs : Measurable s) (hp : Function.Periodic s 1) (h1 : ∀ x, |s x| = 1)
  (h0 : ∫ x in (0 : ℝ)..1, s x = 0) {N : ℕ} (hN : 0 < N)
include hs hp h1 h0 hN

lemma sN_bounds (x : ℝ) : -1 ≤ s (N * x) ∧ s (N * x) ≤ 1 := abs_le.1 (h1 _).le

lemma sN_meas : Measurable fun x : ℝ => s (N * x) := hs.comp (measurable_const_mul _)

lemma sN_integrable : Integrable (fun x : ℝ => s (N * x)) unifLaw :=
  Integrable.of_bound (sN_meas hs hp h1 h0 hN).aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (h1 _).le)

lemma integral_sN : ∫ x, s (N * x) ∂unifLaw = 0 := by
  rw [integral_unifLaw, setIntegral_Icc01]
  exact intervalIntegral_sN_zero hs hp (fun x => (h1 x).le) h0 hN

lemma one_add_sN_integrable : Integrable (fun x : ℝ => 1 + s (N * x)) unifLaw :=
  (integrable_const 1).add (sN_integrable hs hp h1 h0 hN)

lemma blind_apply {A : Set ℝ} (hA : MeasurableSet A) :
    blindLaw s N A = ENNReal.ofReal (∫ x in A, (1 + s (N * x)) ∂unifLaw) := by
  rw [blindLaw, withDensity_apply _ hA, ofReal_integral_eq_lintegral_ofReal
    (one_add_sN_integrable hs hp h1 h0 hN).integrableOn
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; linarith [(sN_bounds hs hp h1 h0 hN x).1])]

lemma blind_real {A : Set ℝ} (hA : MeasurableSet A) :
    (blindLaw s N).real A = unifLaw.real A + ∫ x in A, s (N * x) ∂unifLaw := by
  rw [measureReal_def, blind_apply hs hp h1 h0 hN hA, ENNReal.toReal_ofReal
    (setIntegral_nonneg hA fun x _ => by linarith [(sN_bounds hs hp h1 h0 hN x).1]),
    integral_add (integrable_const _) (sN_integrable hs hp h1 h0 hN).integrableOn, setIntegral_const,
    smul_eq_mul, mul_one]

lemma blind_isProb : IsProbabilityMeasure (blindLaw s N) := by
  constructor
  rw [blind_apply hs hp h1 h0 hN MeasurableSet.univ, Measure.restrict_univ,
    integral_add (integrable_const _) (sN_integrable hs hp h1 h0 hN), integral_sN hs hp h1 h0 hN]
  simp

lemma abs_setIntegral_sN_le {A : Set ℝ} (hA : MeasurableSet A) : |∫ x in A, s (N * x) ∂unifLaw| ≤ 1 / 2 := by
  have hb := sN_bounds hs hp h1 h0 hN
  have hI := sN_integrable hs hp h1 h0 hN
  have hp1 : Integrable (fun x : ℝ => (1 + s (N * x)) / 2) unifLaw := ((integrable_const 1).add hI).div_const 2
  have hm1 : Integrable (fun x : ℝ => (1 - s (N * x)) / 2) unifLaw := ((integrable_const 1).sub hI).div_const 2
  have htot1 : ∫ x, (1 + s (N * x)) / 2 ∂unifLaw = 1 / 2 := by
    rw [integral_div, integral_add (integrable_const _) hI, integral_sN hs hp h1 h0 hN]; simp
  have htot2 : ∫ x, (1 - s (N * x)) / 2 ∂unifLaw = 1 / 2 := by
    rw [integral_div, integral_sub (integrable_const _) hI, integral_sN hs hp h1 h0 hN]; simp
  have hsplit : ∫ x in A, s (N * x) ∂unifLaw =
      ∫ x in A, (1 + s (N * x)) / 2 ∂unifLaw - ∫ x in A, (1 - s (N * x)) / 2 ∂unifLaw := by
    rw [← integral_sub hp1.integrableOn hm1.integrableOn]
    congr 1; ext x; ring
  have a1 : ∫ x in A, (1 + s (N * x)) / 2 ∂unifLaw ≤ 1 / 2 :=
    htot1 ▸ setIntegral_le_integral hp1 (ae_of_all _ fun x => by simp only [Pi.zero_apply]; linarith [(hb x).1])
  have a2 : ∫ x in A, (1 - s (N * x)) / 2 ∂unifLaw ≤ 1 / 2 :=
    htot2 ▸ setIntegral_le_integral hm1 (ae_of_all _ fun x => by simp only [Pi.zero_apply]; linarith [(hb x).2])
  have a3 : 0 ≤ ∫ x in A, (1 + s (N * x)) / 2 ∂unifLaw := setIntegral_nonneg hA fun x _ => by linarith [(hb x).1]
  have a4 : 0 ≤ ∫ x in A, (1 - s (N * x)) / 2 ∂unifLaw := setIntegral_nonneg hA fun x _ => by linarith [(hb x).2]
  rw [hsplit, abs_le]; constructor <;> linarith

lemma blind_tv : tvDist unifLaw (blindLaw s N) = 1 / 2 := by
  have := blind_isProb hs hp h1 h0 hN
  have hI := sN_integrable hs hp h1 h0 hN
  apply le_antisymm
  · refine StatFormal.Distances.tvDist_le_of_forall fun A hA => ?_
    rw [blind_real hs hp h1 h0 hN hA, show unifLaw.real A - (unifLaw.real A + ∫ x in A, s (N * x) ∂unifLaw) =
      -∫ x in A, s (N * x) ∂unifLaw by ring, abs_neg]
    exact abs_setIntegral_sN_le hs hp h1 h0 hN hA
  · set Ap : Set ℝ := {x | 0 < s (N * x)}
    have hAp : MeasurableSet Ap := measurableSet_lt measurable_const (sN_meas hs hp h1 h0 hN)
    have hon : ∀ x ∈ Ap, s (N * x) = 1 := fun x hx => by
      have := h1 (N * x); rw [abs_of_pos hx] at this; exact this
    have hoff : ∀ x ∈ Apᶜ, s (N * x) = -1 := fun x hx => by
      simp only [Ap, mem_compl_iff, mem_ofPred_eq, not_lt] at hx
      have := h1 (N * x); rw [abs_of_nonpos hx] at this; linarith
    have e1 : ∫ x in Ap, s (N * x) ∂unifLaw = unifLaw.real Ap := by
      rw [setIntegral_congr_fun hAp hon, setIntegral_const, smul_eq_mul, mul_one]
    have e2 : ∫ x in Apᶜ, s (N * x) ∂unifLaw = -unifLaw.real Apᶜ := by
      rw [setIntegral_congr_fun hAp.compl hoff, setIntegral_const, smul_eq_mul, mul_neg, mul_one]
    have e3 := integral_add_compl hAp hI
    rw [e1, e2, integral_sN hs hp h1 h0 hN, probReal_compl_eq_one_sub hAp] at e3
    have hhalf : unifLaw.real Ap = 1 / 2 := by linarith
    have := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := unifLaw) (ν := blindLaw s N) hAp
    rw [blind_real hs hp h1 h0 hN hAp, e1, hhalf] at this
    norm_num at this ⊢
    linarith [this]

end Law

theorem blind_construction : Claims.blind_construction := by
  intro s hs hp h1 h0 N hN
  have hb := sN_bounds hs hp h1 h0 hN
  refine ⟨fun x => by linarith [(hb x).1], ?_, blind_isProb hs hp h1 h0 hN, ?_, blind_tv hs hp h1 h0 hN⟩
  · rw [← integral_unifLaw, integral_add (integrable_const _) (sN_integrable hs hp h1 h0 hN),
      integral_sN hs hp h1 h0 hN]
    simp
  · rw [blind_tv hs hp h1 h0 hN]
    have : ∫ x in Icc (0 : ℝ) 1, |s (N * x)| = 1 := by
      simp only [h1, integral_const, smul_eq_mul, mul_one]
      simp [measureReal_def, Real.volume_Icc]
    rw [this]; ring

theorem dpop_le_mmd : Claims.dpop_le_mmd := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α hφ hκ hα0 hα1
  have hmem : ∀ R : Measure 𝒳, IsProbabilityMeasure R → ∫ x, φ x ∂R ∈ region φ α R := fun R _ =>
    ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, by rw [le_div_iff₀ (by linarith)]; linarith⟩,
      by simp, by simp⟩
  refine ⟨hmem P inferInstance, ?_⟩
  unfold Dpop setDist mmd
  exact csInf_le ⟨0, by rintro r ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩
    ⟨_, hmem P inferInstance, _, hmem Q inferInstance, rfl⟩

lemma phi_integrable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : ℝ → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable κ (ae_of_all _ hκ)

theorem blind_mmd : Claims.blind_mmd := by
  intro H _ _ _ φ κ s hφ hκ hs hp h1 h0
  have hdiff : ∀ N : ℕ, 0 < N →
      ∫ x, φ x ∂(blindLaw s N) - ∫ x, φ x ∂unifLaw = ∫ x in Icc (0 : ℝ) 1, s (N * x) • φ x := by
    intro N hN
    have hb := sN_bounds hs hp h1 h0 hN
    have hdm : Measurable fun x : ℝ => ENNReal.ofReal (1 + s (N * x)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add (sN_meas hs hp h1 h0 hN))
    rw [blindLaw, integral_withDensity_eq_integral_toReal_smul hdm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have hpi := phi_integrable hφ hκ unifLaw
    have hqi : Integrable (fun x => (ENNReal.ofReal (1 + s (N * x))).toReal • φ x) unifLaw := by
      refine hpi.bdd_smul 2 (ENNReal.measurable_toReal.comp hdm).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [ENNReal.toReal_ofReal (by linarith [(hb x).1]), Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hb x).1, (hb x).2]
    rw [← integral_sub hqi hpi, integral_unifLaw]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    rw [ENNReal.toReal_ofReal (by linarith [(hb x).1]), add_smul, one_smul, add_sub_cancel_left]
  have hlim : Tendsto (fun N : ℕ => mmd φ unifLaw (blindLaw s N)) atTop (𝓝 0) := by
    have hRL := riemann_lebesgue_periodic H φ s (show IntegrableOn φ (Icc 0 1) volume from by unfold IntegrableOn; exact phi_integrable hφ hκ unifLaw) hs hp (fun x => (h1 x).le) h0
    have hn := (tendsto_zero_iff_norm_tendsto_zero.1 hRL)
    refine hn.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [mmd, norm_sub_rev, hdiff N hN]
  have hle : ∀ N : ℕ, 0 < N → ∀ α : ℝ, 0 ≤ α → α < 1 →
      Dpop φ unifLaw (blindLaw s N) α ≤ mmd φ unifLaw (blindLaw s N) := by
    intro N hN α hα0 hα1
    have := blind_isProb hs hp h1 h0 hN
    exact (dpop_le_mmd ℝ H unifLaw (blindLaw s N) φ κ α hφ hκ hα0 hα1).2
  refine ⟨hdiff, hlim, hle, fun ε hε => ?_⟩
  filter_upwards [eventually_gt_atTop 0, (hlim.eventually (ge_mem_nhds hε))] with N hN hNε α hα0 hα1
  exact (hle N hN α hα0 hα1).trans hNε

/-! ### The witness: the square wave -/

theorem blind_witness : Claims.blind_witness := by
  set s : ℝ → ℝ := fun x => if Int.fract x ≤ 1 / 2 then 1 else -1 with hsdef
  have hs : Measurable s := Measurable.ite (measurableSet_le measurable_fract measurable_const)
    measurable_const measurable_const
  have h1 : ∀ x, |s x| = 1 := fun x => by simp only [s]; split_ifs <;> simp
  have hp : Function.Periodic s 1 := fun x => by simp only [s, Int.fract_add_one]
  refine ⟨s, hs, hp, h1, ?_⟩
  have hii : ∀ u v : ℝ, IntervalIntegrable s volume u v := fun u v => by
    have := intervalIntegrable_sN_smul (E := ℝ) hs (fun x => (h1 x).le) 1 (h := fun _ => (1 : ℝ)) (u := u) (v := v)
      intervalIntegrable_const
    simpa using this
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (1 / 2)) (hii (1 / 2) 1)]
  have ea : ∫ x in (0 : ℝ)..1 / 2, s x = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun x hx => ?_]
    · simp
    · rw [uIcc_of_le (by norm_num)] at hx
      simp only [s]
      rw [Int.fract_eq_self.2 ⟨hx.1, by linarith [hx.2]⟩, if_pos hx.2]
  have eb : ∫ x in (1 / 2 : ℝ)..1, s x = -(1 / 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (-1 : ℝ)) fun x hx => ?_]
    · rw [setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num)]; norm_num
    · simp only [s]
      rw [Int.fract_eq_self.2 ⟨by linarith [hx.1], hx.2⟩, if_neg (by linarith [hx.1])]
  rw [ea, eb]; ring

end StatFormal.Wave30tj
