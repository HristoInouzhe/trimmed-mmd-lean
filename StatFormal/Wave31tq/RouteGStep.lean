import StatFormal.Wave31tq.RouteG
import StatFormal.Lib.BandLimited.TailMoment
import StatFormal.Lib.BandLimited.Density

/-!
# Wave 31tq, chunk G: Lemma S4.12 (Q16 `newgaussstep`)

Route (the printed proof, S4 :686-703). `f = 1_{(x₀,x₀+ρ)} ⋆ b_Ω` (`b_Ω = dilateR Ω⁻¹ b = Ω b(Ω ·)`):
* `f(x) = Φ(Ω(x−x₀)) − Φ(Ω(x−x₀−ρ))` (`Φ` the distribution function of `b`), so `f` is continuous and `0 ≤ f ≤ 1`
  (`Lib/BandLimited/EvenDensity`); `∫ f = ρ` (Mathlib's `integral_convolution`), so `∫ f² ≤ ∫ f = ρ`;
* `𝓕 f = 𝓕 1_I · 𝓕 b(·/Ω)` (`FourierOps.fourier_mollify`, `fourier_dilate`) vanishes where `|ξ| > Ω` in the angular
  variable, and `ft2 f = 𝓕 f` a.e. (31tp L2), so Q14 (`bandlimited_angular_route`) gives the representer and the norm;
* `err(f) = ∫ |1_{(x₀,∞)} − f| |p − q|` (Q1(b), the hypothesis `Claims.tv_density`), with the pointwise bound
  `|1_{(x₀,∞)} − f| ≤ b̄(Ω|x−x₀|) + b̄(Ωρ/2) + 1_{(x₀+ρ/2,∞)}`, the Lipschitz bound of `|p − q|` on `|x − x₀| ≤ r₀`, `b̄` antitone
  off it, `∫ |x−x₀| b̄(Ω|x−x₀|) = m₂/(2Ω²)` (`Lib/BandLimited/TailMoment`), `∫ |p − q| = 2α⋆`, and `|P − Q| = |p − q|·Leb` (Q1(b)).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteG

open StatFormal StatFormal.Wave31tp

/-- The angular band limitation of a mollified interval: if `ftA b` vanishes off `[−1, 1]`, then the angular L² transform of
`1_{(a,a+ρ)} ⋆ b_Ω` vanishes a.e. off `[−Ω, Ω]`. -/
theorem ft2A_mollify_band {b : ℝ → ℝ} (hbi : Integrable b) (hbft : ∀ ξ : ℝ, 1 < |ξ| → ftA (fun t => (b t : ℂ)) ξ = 0)
    {Ω : ℝ} (hΩ : 0 < Ω) {ρ : ℝ} (a : ℝ)
    (hfi : Integrable (mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b)))
    (hf2 : MemLp (mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b)) 2) :
    ∀ᵐ ξ ∂(volume : Measure ℝ), Ω < |ξ| → ft2A (fun x => (mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x : ℂ)) ξ = 0 := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hIfin : volume (Ioo a (a + ρ)) ≠ ⊤ := by simp [Real.volume_Ioo]
  have hdi : Integrable (dilateR Ω⁻¹ b) := FourierOps.integrable_dilateR hbi (inv_pos.2 hΩ)
  have hae := (Wave31tp.ft2_ae ℝ (fun x => (mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x : ℂ)) hfi.ofReal hf2.ofReal).1
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (r := (2 * Real.pi)⁻¹) (inv_ne_zero hπ.ne')
  filter_upwards [hq.ae hae] with ξ hξ hlt
  rw [ft2A]
  refine hξ.trans ?_
  rw [FourierOps.fourier_mollify measurableSet_Ioo hIfin hdi, ← FourierOps.dilate_ofReal,
    FourierOps.fourier_dilate _ (inv_pos.2 hΩ)]
  have hz : 𝓕 (fun t => (b t : ℂ)) (Ω⁻¹ • (2 * Real.pi)⁻¹ • ξ) = 0 := by
    have h := hbft (Ω⁻¹ * ξ) (by
      rw [abs_mul, abs_of_pos (inv_pos.2 hΩ), lt_inv_mul_iff₀ hΩ, mul_one]; exact hlt)
    rw [ftA] at h
    rw [← h, show Ω⁻¹ • (2 * Real.pi)⁻¹ • ξ = (2 * Real.pi)⁻¹ • (Ω⁻¹ * ξ) by simp only [smul_eq_mul]; ring]
  rw [hz, mul_zero]

/-- Q16 `newgaussstep` (Lemma S4.12), with Q1(b) (`Claims.tv_density`, chunk A) as a hypothesis. -/
theorem newgaussstep_of (htv : Claims.tv_density) : Claims.newgaussstep := by
  intro H _ _ _ φ σ P Q _ _ p q b x₀ ℓ r₀ hσ hφ hp hq hp0 hq0 hP hQ hsgn1 hsgn2 hℓ hr₀ hlip hb hb0 hb1 hbev hbft hm
    Ω ρ hΩ hρ
  set f := mollify (Ioo x₀ (x₀ + ρ)) (dilateR Ω⁻¹ b) with hf
  have hbi : Integrable b := BandLimited.integrable_of_integral_eq_one hb1
  have hdi : Integrable (dilateR Ω⁻¹ b) := FourierOps.integrable_dilateR hbi (inv_pos.2 hΩ)
  have hd0 : ∀ t, 0 ≤ dilateR Ω⁻¹ b t := fun t => by
    rw [BandLimited.dilateR_inv_apply]; exact mul_nonneg hΩ.le (hb0 _)
  have hd1 : ∫ t, dilateR Ω⁻¹ b t = 1 := by rw [FourierOps.integral_dilateR b (inv_pos.2 hΩ), hb1]
  have hf0 : ∀ x, 0 ≤ f x := FourierOps.mollify_nonneg _ hd0
  have hf1 : ∀ x, f x ≤ 1 := FourierOps.mollify_le_one _ hd0 hdi hd1
  have hfc : Continuous f := BandLimited.continuous_mollify_Ioo hb1 hΩ hρ.le x₀
  have hIfin : volume (Ioo x₀ (x₀ + ρ)) ≠ ⊤ := by simp [Real.volume_Ioo]
  have hfi : Integrable f := FourierOps.integrable_mollify measurableSet_Ioo hIfin hdi
  have hf2 : MemLp f 2 := FourierOps.memLp_two_of_integrable_of_unit hfi hf0 hf1
  -- `∫ f = ρ`, hence `∫ f² ≤ ρ`
  have hfint : ∫ x, f x = ρ := by
    rw [hf, mollify, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (FourierOps.integrable_indicator_one measurableSet_Ioo hIfin) hdi, hd1]
    have : (Ioo x₀ (x₀ + ρ)).indicator (fun _ => (1 : ℝ)) = (Ioo x₀ (x₀ + ρ)).indicator 1 := rfl
    rw [this, integral_indicator_one measurableSet_Ioo]
    simp [Measure.real, Real.volume_Ioo, hρ.le]
  have hsq : ∫ x, f x ^ 2 ≤ ρ := by
    rw [← hfint]
    exact integral_mono hf2.integrable_sq hfi fun x => by nlinarith [hf0 x, hf1 x]
  -- the representer and its norm (Q14)
  have hband := ft2A_mollify_band hbi hbft hΩ x₀ hfi hf2
  obtain ⟨g, hg, hgn⟩ := bandlimited_angular_route H φ σ Ω hσ hΩ.le hφ f hfc hf2 hband
  refine ⟨⟨g, hg, hgn.trans ?_⟩, fun x => ⟨hf0 x, hf1 x⟩, ?_⟩
  · calc Real.exp (σ ^ 2 * Ω ^ 2 / 2) / (√(2 * Real.pi) * σ) * ∫ x, f x ^ 2
          ≤ Real.exp (σ ^ 2 * Ω ^ 2 / 2) / (√(2 * Real.pi) * σ) * ρ :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ρ * Real.exp (σ ^ 2 * Ω ^ 2 / 2) / (√(2 * Real.pi) * σ) := by ring
  -- the error (Q1(b) with `G = (x₀, ∞)`)
  obtain ⟨habs, -, -, htvd, herr⟩ := htv.2 ℝ P Q p q hp hq hp0 hq0 hP hQ
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ x₀ := by
    rw [ae_iff]; simp
  have hsgn2' : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioi x₀ → p x ≤ q x := by
    filter_upwards [hsgn2, hne] with x hx hx' hxn
    exact hx (lt_of_le_of_ne (not_lt.1 hxn) hx')
  rw [herr (Ioi x₀) f measurableSet_Ioi hfc.measurable (fun x => ⟨hf0 x, hf1 x⟩) hsgn1 hsgn2']
  -- notation
  set d : ℝ → ℝ := fun x => |p x - q x| with hd
  set T : ℝ → ℝ := fun s => ∫ v in Ioi s, b v with hT
  set E : ℝ := bbarE b Ω r₀ with hE
  set B : ℝ := bbar b (Ω * ρ / 2) with hB
  obtain ⟨hpi, hp1⟩ := BandLimited.integrable_and_integral_of_density hp hp0 hP
  obtain ⟨hqi, hq1⟩ := BandLimited.integrable_and_integral_of_density hq hq0 hQ
  have hdi' : Integrable d := (hpi.sub hqi).abs
  have hd0' : ∀ x, 0 ≤ d x := fun x => abs_nonneg _
  have hT0 : ∀ s, 0 ≤ T s := BandLimited.tail_nonneg hb0
  have hanti : Antitone T := BandLimited.tail_antitone hb0 hb1
  have hE0 : 0 ≤ E := by
    rw [hE, bbarE]; split_ifs
    · exact le_rfl
    · exact hT0 _
  have hB0 : 0 ≤ B := hT0 _
  obtain ⟨hwi, hwint⟩ := BandLimited.abs_tail_integral hb hb0 hb1 hbev hm hΩ x₀
  set w : ℝ → ℝ := fun x => |x - x₀| * ∫ v in Ioi (Ω * |x - x₀|), b v with hw
  set ind : ℝ → ℝ := (Ioi (x₀ + ρ / 2)).indicator fun _ => (1 : ℝ) with hind
  -- the pointwise bound
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ),
      |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| * d x ≤ ℓ * w x + (E + B) * d x + ind x * d x := by
    filter_upwards [hlip] with x hx
    have h1 := BandLimited.abs_indicator_sub_mollify_le hb0 hb1 hbev hΩ hρ.le x₀ x
    have hTd : T (Ω * |x - x₀|) * d x ≤ ℓ * w x + E * d x := by
      by_cases hr : ENNReal.ofReal |x - x₀| ≤ r₀
      · have := hx hr
        have hw' : ℓ * w x = T (Ω * |x - x₀|) * (ℓ * |x - x₀|) := by simp only [hw, hT]; ring
        rw [hw']
        nlinarith [hT0 (Ω * |x - x₀|), hd0' x, mul_nonneg hE0 (hd0' x)]
      · push Not at hr
        have hrt : r₀ ≠ ⊤ := ne_top_of_lt hr
        have hlt : r₀.toReal < |x - x₀| := ENNReal.toReal_lt_of_lt_ofReal hr
        have hET : T (Ω * |x - x₀|) ≤ E := by
          rw [hE, bbarE, ite_eq_right_iff.mpr (fun h => absurd h hrt)]
          exact hanti (by nlinarith [ENNReal.toReal_nonneg (a := r₀)])
        have hw0 : 0 ≤ w x := mul_nonneg (abs_nonneg _) (hT0 _)
        nlinarith [hd0' x]
    have hind0 : 0 ≤ ind x := indicator_nonneg (fun _ _ => zero_le_one) x
    calc |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| * d x
        ≤ (T (Ω * |x - x₀|) + B + ind x) * d x := mul_le_mul_of_nonneg_right h1 (hd0' x)
      _ = T (Ω * |x - x₀|) * d x + B * d x + ind x * d x := by ring
      _ ≤ ℓ * w x + E * d x + B * d x + ind x * d x := by linarith
      _ = ℓ * w x + (E + B) * d x + ind x * d x := by ring
  -- integrability
  have hindi : Integrable fun x => ind x * d x := by
    have : (fun x => ind x * d x) = (Ioi (x₀ + ρ / 2)).indicator d := by
      funext x; simp only [hind, indicator]; split_ifs <;> simp
    rw [this]; exact hdi'.indicator measurableSet_Ioi
  have hRi : Integrable fun x => ℓ * w x + (E + B) * d x + ind x * d x :=
    ((hwi.const_mul ℓ).add (hdi'.const_mul (E + B))).add hindi
  have hLm : AEStronglyMeasurable (fun x => |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| * d x) volume :=
    ((continuous_abs.measurable.comp ((measurable_const.indicator measurableSet_Ioi).sub hfc.measurable)).mul
      (continuous_abs.measurable.comp (hp.sub hq))).aestronglyMeasurable
  have hLi : Integrable fun x => |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| * d x := by
    refine hdi'.mono' hLm (ae_of_all _ fun x => ?_)
    have hle : |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| ≤ 1 := by
      rw [abs_le]
      by_cases hx : x ∈ Ioi x₀
      · rw [indicator_of_mem hx]; constructor <;> linarith [hf0 x, hf1 x]
      · rw [indicator_of_notMem hx]; constructor <;> linarith [hf0 x, hf1 x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hd0' x))]
    nlinarith [hd0' x, abs_nonneg ((Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x)]
  -- the integrals of the three pieces
  have hdint : ∫ x, d x = 2 * StatFormal.Distances.tvDist P Q := by
    rw [htvd]; exact BandLimited.integral_abs_sub_of_densities hp hq hp0 hq0 hP hQ
  have hindint : ∫ x, ind x * d x = tailPlus P Q x₀ (ρ / 2) := by
    have : (fun x => ind x * d x) = (Ioi (x₀ + ρ / 2)).indicator d := by
      funext x; simp only [hind, indicator]; split_ifs <;> simp
    rw [this, integral_indicator measurableSet_Ioi, tailPlus, habs,
      BandLimited.withDensity_real_eq_setIntegral hdi' hd0' measurableSet_Ioi]
  have hTp0 : 0 ≤ tailPlus P Q x₀ (ρ / 2) := ENNReal.toReal_nonneg
  calc ∫ x, |(Ioi x₀).indicator (fun _ => (1 : ℝ)) x - f x| * d x
      ≤ ∫ x, (ℓ * w x + (E + B) * d x + ind x * d x) := integral_mono_ae hLi hRi hpt
    _ = ℓ * (∫ x, w x) + (E + B) * (∫ x, d x) + ∫ x, ind x * d x := by
        rw [integral_add (f := fun x => ℓ * w x + (E + B) * d x) (g := fun x => ind x * d x)
            ((hwi.const_mul ℓ).add (hdi'.const_mul (E + B))) hindi,
          integral_add (f := fun x => ℓ * w x) (g := fun x => (E + B) * d x) (hwi.const_mul ℓ) (hdi'.const_mul (E + B)),
          integral_const_mul, integral_const_mul]
    _ = ℓ * (∫ t, t ^ 2 * b t) / (2 * Ω ^ 2) + tailPlus P Q x₀ (ρ / 2) +
          2 * StatFormal.Distances.tvDist P Q * (E + B) := by
        rw [hwint, hdint, hindint]; ring
    _ ≤ ℓ * (∫ t, t ^ 2 * b t) / (2 * Ω ^ 2) + 2 * tailPlus P Q x₀ (ρ / 2) +
          2 * StatFormal.Distances.tvDist P Q * (E + B) := by linarith

end StatFormal.Wave31tq.RouteG
