import StatFormal.Lib.BandLimited.EvenDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The tail moment of an even probability density (library, untrusted)

For an even probability density `b` on `ℝ` with finite second moment `m₂ = ∫ t² b(t) dt`, the tail `b̄(v) = ∫_{(v,∞)} b`
satisfies (Tonelli, here through Mathlib's layer-cake formula `lintegral_comp_eq_lintegral_meas_lt_mul`)

  `∫₀^∞ v b̄(v) dv = ∫₀^∞ (t²/2) b(t) dt = m₂/4`,

and, after the substitution `v = Ω|x − x₀|` and the symmetry `x − x₀ ↦ −(x − x₀)`,

  `∫ |x − x₀| b̄(Ω|x − x₀|) dx = m₂/(2Ω²)` (`Ω > 0`), with an integrable integrand.

This is the computation `ℓ ∫ |x−x₀| b̄(Ω|x−x₀|) dx = ℓm₂/(2Ω²)` in the proof of Lemma S4.12 of the trimmed-MMD paper.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.BandLimited

variable {b : ℝ → ℝ}

/-- For an even `b` with `t² b(t)` integrable, half of the second moment sits on `(0, ∞)`. -/
theorem integral_Ioi_sq_mul_of_even (hev : ∀ t, b (-t) = b t) (hm : Integrable (fun t => t ^ 2 * b t)) :
    ∫ t in Ioi 0, t ^ 2 * b t = (∫ t, t ^ 2 * b t) / 2 := by
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hm.integrableOn hm.integrableOn
  have hneg : ∫ t in Iic (0 : ℝ), t ^ 2 * b t = ∫ t in Ioi 0, t ^ 2 * b t := by
    have := integral_comp_neg_Ioi (0 : ℝ) (fun t => t ^ 2 * b t)
    rw [neg_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [hev]
  linarith

/-- A function of `|x|` is integrable when the function is integrable on `(0, ∞)`. -/
theorem integrable_comp_abs_of_integrableOn {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hR : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (show (0 : ℝ) < x from hx)]) measurableSet_Ioi
  have hL : IntegrableOn (fun x => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hR
  have := hL.union hR
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- **The tail moment**: `v ↦ v b̄(v)` is integrable on `(0, ∞)` and `∫₀^∞ v b̄(v) dv = m₂/4`. -/
theorem tail_moment (hb : Measurable b) (h0 : ∀ t, 0 ≤ b t) (h1 : ∫ t, b t = 1) (hev : ∀ t, b (-t) = b t)
    (hm : Integrable (fun t => t ^ 2 * b t)) :
    IntegrableOn (fun v => v * ∫ x in Ioi v, b x) (Ioi 0) ∧
      ∫ v in Ioi 0, v * ∫ x in Ioi v, b x = (∫ t, t ^ 2 * b t) / 4 := by
  have hi := integrable_of_integral_eq_one h1
  set μ : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (b x) with hμ
  set T : ℝ → ℝ := fun v => ∫ x in Ioi v, b x with hT
  have hT0 : ∀ v, 0 ≤ T v := tail_nonneg h0
  have hTm : Measurable T := (tail_antitone h0 h1).measurable
  -- the layer-cake identity with `f = max x 0` and `g = id`
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun x => max x 0) (g := fun t => t)
    (ae_of_all _ fun x => le_max_right x 0) (measurable_id.max measurable_const).aemeasurable
    (fun t _ => continuous_id.intervalIntegrable 0 t) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => le_of_lt ht)
  -- the right side is `∫⁻_{(0,∞)} ofReal (v T(v))`
  have hR : ∫⁻ t in Ioi 0, μ {a | t < max a 0} * ENNReal.ofReal t = ∫⁻ t in Ioi 0, ENNReal.ofReal (t * T t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hset : {a : ℝ | t < max a 0} = Ioi t := by
      ext a
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · intro h
        rcases le_total a 0 with ha | ha
        · rw [max_eq_right ha] at h; linarith
        · rwa [max_eq_left ha] at h
      · intro h; exact lt_of_lt_of_le h (le_max_left a 0)
    rw [hset, hμ, withDensity_apply _ measurableSet_Ioi,
      ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => h0 x),
      ← ENNReal.ofReal_mul (hT0 t), mul_comm]
  -- the left side is `ofReal (m₂/4)`
  have hfi : Integrable (fun x => b x * (max x 0 ^ 2 / 2)) := by
    refine (hm.div_const 2).mono' ((hb.mul (((measurable_id.max measurable_const).pow_const 2).div_const 2))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 x) (by positivity))]
    have : max x 0 ^ 2 ≤ x ^ 2 := by
      rcases le_total x 0 with hx | hx
      · rw [max_eq_right hx, zero_pow two_ne_zero]; exact sq_nonneg x
      · rw [max_eq_left hx]
    have := mul_le_mul_of_nonneg_left this (h0 x)
    nlinarith
  have hfint : ∫ x, b x * (max x 0 ^ 2 / 2) = (∫ t, t ^ 2 * b t) / 4 := by
    have hsupp : ∫ x, b x * (max x 0 ^ 2 / 2) = ∫ x in Ioi 0, b x * (max x 0 ^ 2 / 2) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
      have : x ≤ 0 := not_lt.1 hx
      simp [max_eq_right this]
    rw [hsupp, show ∫ x in Ioi 0, b x * (max x 0 ^ 2 / 2) = ∫ x in Ioi 0, (x ^ 2 * b x) / 2 from
      setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        rw [max_eq_left (le_of_lt (show (0 : ℝ) < x from hx))]; ring,
      integral_div, integral_Ioi_sq_mul_of_even hev hm]
    ring
  have hL : ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..max x 0, t) ∂μ = ENNReal.ofReal ((∫ t, t ^ 2 * b t) / 4) := by
    have hcongr : (fun x => ENNReal.ofReal (∫ t in (0 : ℝ)..max x 0, t)) = fun x => ENNReal.ofReal (max x 0 ^ 2 / 2) := by
      funext x; simp [integral_id]
    rw [hcongr, hμ, lintegral_withDensity_eq_lintegral_mul _ (hb.ennreal_ofReal)
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (max x 0 ^ 2 / 2))]
    rw [← hfint, ofReal_integral_eq_lintegral_ofReal hfi
      (ae_of_all _ fun x => mul_nonneg (h0 x) (by positivity))]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (h0 x)]
  have hlint : ∫⁻ t in Ioi 0, ENNReal.ofReal (t * T t) = ENNReal.ofReal ((∫ t, t ^ 2 * b t) / 4) := by
    rw [← hR, ← hlc, hL]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun t => t * T t :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => mul_nonneg (le_of_lt ht) (hT0 t)
  have hmeas : AEStronglyMeasurable (fun t => t * T t) (volume.restrict (Ioi 0)) :=
    (measurable_id.mul hTm).aestronglyMeasurable
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [hlint]; exact ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hlint, ENNReal.toReal_ofReal]
  exact div_nonneg (integral_nonneg fun t => mul_nonneg (sq_nonneg t) (h0 t)) (by norm_num)

/-- **The weighted tail integral**: for `Ω > 0`, `x ↦ |x − x₀| b̄(Ω|x − x₀|)` is integrable and its integral is `m₂/(2Ω²)`. -/
theorem abs_tail_integral (hb : Measurable b) (h0 : ∀ t, 0 ≤ b t) (h1 : ∫ t, b t = 1) (hev : ∀ t, b (-t) = b t)
    (hm : Integrable (fun t => t ^ 2 * b t)) {Ω : ℝ} (hΩ : 0 < Ω) (x₀ : ℝ) :
    Integrable (fun x => |x - x₀| * ∫ v in Ioi (Ω * |x - x₀|), b v) ∧
      ∫ x, |x - x₀| * ∫ v in Ioi (Ω * |x - x₀|), b v = (∫ t, t ^ 2 * b t) / (2 * Ω ^ 2) := by
  obtain ⟨hIi, hIe⟩ := tail_moment hb h0 h1 hev hm
  set g : ℝ → ℝ := fun y => y * ∫ v in Ioi (Ω * y), b v with hg
  -- `g y = Ω⁻¹ G(Ω y)` with `G v = v b̄(v)`
  have hgG : ∀ y, g y = Ω⁻¹ * ((Ω * y) * ∫ v in Ioi (Ω * y), b v) := by
    intro y; simp only [hg]; field_simp
  have hgi : IntegrableOn g (Ioi 0) := by
    have h2 : IntegrableOn (fun y => (Ω * y) * ∫ v in Ioi (Ω * y), b v) (Ioi 0) := by
      have := (integrableOn_Ioi_comp_mul_left_iff (fun v => v * ∫ x in Ioi v, b x) 0 hΩ).2
        (by rwa [mul_zero])
      exact this
    exact IntegrableOn.congr_fun (Integrable.const_mul h2 Ω⁻¹) (fun y _ => (hgG y).symm) measurableSet_Ioi
  have hgint : ∫ y in Ioi 0, g y = (∫ t, t ^ 2 * b t) / (4 * Ω ^ 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hgG y), integral_const_mul,
      integral_comp_mul_left_Ioi (fun v => v * ∫ x in Ioi v, b x) 0 hΩ, mul_zero, hIe, smul_eq_mul]
    field_simp
  have hshift : (fun x => |x - x₀| * ∫ v in Ioi (Ω * |x - x₀|), b v) = fun x => g |x - x₀| := rfl
  have hab : Integrable (fun x => g |x|) := integrable_comp_abs_of_integrableOn hgi
  refine ⟨?_, ?_⟩
  · rw [hshift]; exact hab.comp_sub_right x₀
  · rw [hshift, integral_sub_right_eq_self (fun x => g |x|) x₀, integral_comp_abs, hgint]
    ring

end StatFormal.BandLimited
