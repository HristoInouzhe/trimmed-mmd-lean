import StatFormal.Lib.JBall.Basic
import StatFormal.Lib.FourierOps.Translate

/-!
# The Fourier tail of a translation-Lipschitz function (library, untrusted)

Let `V` be a real inner-product space of dimension `d ≥ 1` and `f ∈ L¹ ∩ L²(V; ℂ)` with the L² translation bound
`‖f(· + h) − f‖₂² ≤ Π‖h‖` for all `h ∈ V` (for an indicator `f = 1_E` this is `Leb(E △ (E − h)) ≤ Π‖h‖`). Then the
Fourier mass beyond the (angular) frequency `t > 0` is at most `Π/(2c_d t)`:
`∫_{2π‖η‖ ≥ t} |𝓕 f(η)|² dη ≤ Π/(2 c_d t)`, `c_d = 1 − sup_{y ≥ 1} j_d(y)` (`j_d` the ball-averaged cosine of `Wave31tp.jBall`).

Proof (the printed proof of Lemma S4.9 of trimmed-mmd, Stein–Weiss style): Plancherel for translations
(`FourierOps.integral_norm_fourier_sq_mul_phase`) gives `∫ |𝓕 f(η)|² (2 − 2cos(2π⟪h, η⟫)) dη ≤ Π‖h‖`; average over `h` uniform in
the ball of radius `1/t` (Tonelli, `lintegral_lintegral_swap`); the mean of `cos⟪h, 2πη⟫` over that ball is `j_d(2π‖η‖/t)`
(`JBall.avg_cos_inner`, rotation invariance), and `1 − j_d(y) ≥ c_d` for `y ≥ 1`, `≥ 0` everywhere; the mean of `‖h‖` is
at most `1/t`.
-/

noncomputable section
open MeasureTheory Set Metric FourierTransform
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.MollifierNorm

open StatFormal.Wave31tp (jBall)

/-- `|𝐞(a) − 1|² = 2 − 2 cos(2πa)`. -/
theorem norm_fourierChar_sub_one_sq (a : ℝ) : ‖(𝐞 a : ℂ) - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * a) := by
  rw [Real.fourierChar_apply, Complex.sq_norm, Complex.normSq_apply]
  have hre : (Complex.exp (↑(2 * Real.pi * a) * Complex.I) - 1).re = Real.cos (2 * Real.pi * a) - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp (↑(2 * Real.pi * a) * Complex.I) - 1).im = Real.sin (2 * Real.pi * a) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  rw [hre, him]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * a)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier_of_integrable {f : V → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner hf

/-- The squared modulus of the Fourier transform of an `L¹ ∩ L²` function is integrable. -/
theorem integrable_norm_fourier_sq {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun η => ‖𝓕 f η‖ ^ 2) :=
  (FourierL2.plancherel_L1L2 hf1 hf2 hf1 hf2).1.integrable_norm_pow two_ne_zero

/-- **Plancherel for translations, in `[0, ∞]`**: `∫ |𝓕 f(η)|² (2 − 2cos(2π⟪h, η⟫)) dη = ‖f(· + h) − f‖₂²` for `f ∈ L¹ ∩ L²`. -/
theorem lintegral_fourier_sq_mul_one_sub_cos {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) (h : V) :
    ∫⁻ η, ENNReal.ofReal (‖𝓕 f η‖ ^ 2 * (2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫))) =
      ENNReal.ofReal (∫ x, ‖f (x + h) - f x‖ ^ 2) := by
  have hint : Integrable (fun η => ‖𝓕 f η‖ ^ 2 * (2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫))) := by
    refine (integrable_norm_fourier_sq hf1 hf2).mul_bdd (c := 4) ?_ (Filter.Eventually.of_forall fun η => ?_)
    · exact (continuous_const.sub (continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul (continuous_const.inner continuous_id))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [Real.neg_one_le_cos (2 * Real.pi * ⟪h, η⟫), Real.cos_le_one (2 * Real.pi * ⟪h, η⟫)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun η => ?_)]
  · congr 1
    rw [← FourierOps.integral_norm_fourier_sq_mul_phase hf1 hf2 h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [norm_fourierChar_sub_one_sq]
  · exact mul_nonneg (sq_nonneg _) (by nlinarith [Real.cos_le_one (2 * Real.pi * ⟪h, η⟫)])

variable {d : ℕ} [NeZero d]

/-- The ball average of `2 − 2cos(2π⟪h, η⟫)` over `h ∈ B(0, R)`: `∫_{B(0,R)} (2 − 2cos(2π⟪h, η⟫)) dh = 2 vol(B)(1 − j_d(2πR‖η‖))`. -/
theorem lintegral_ball_one_sub_cos (hd : Module.finrank ℝ V = d) {R : ℝ} (hR : 0 < R) (η : V) :
    ∫⁻ h in ball (0 : V) R, ENNReal.ofReal (2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫)) =
      ENNReal.ofReal (2 * (volume (ball (0 : V) R)).toReal * (1 - jBall d (R * (2 * Real.pi * ‖η‖)))) := by
  have hfin : volume (ball (0 : V) R) ≠ ⊤ := measure_ball_lt_top.ne
  have hcont : Continuous (fun h : V => Real.cos (2 * Real.pi * ⟪h, η⟫)) :=
    Real.continuous_cos.comp (continuous_const.mul (continuous_id.inner continuous_const))
  have h1int : IntegrableOn (fun _ : V => (1 : ℝ)) (ball 0 R) := integrableOn_const hfin
  have h2int : IntegrableOn (fun _ : V => (2 : ℝ)) (ball 0 R) := integrableOn_const hfin
  have hcosint : IntegrableOn (fun h : V => Real.cos (2 * Real.pi * ⟪h, η⟫)) (ball 0 R) :=
    h1int.mono' hcont.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun h => by simpa using Real.abs_cos_le_one _)
  have hint : IntegrableOn (fun h : V => 2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫)) (ball 0 R) :=
    h2int.sub (hcosint.const_mul 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun h => show (0 : ℝ) ≤ 2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫) by
      nlinarith [Real.cos_le_one (2 * Real.pi * ⟪h, η⟫)])]
  congr 1
  have havg := JBall.avg_cos_inner hd hR ((2 * Real.pi) • η)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at havg
  have hpos : 0 < (volume (ball (0 : V) R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' hfin
  have hcoe : ∫ h in ball (0 : V) R, Real.cos ⟪h, (2 * Real.pi) • η⟫ =
      ∫ h in ball (0 : V) R, Real.cos (2 * Real.pi * ⟪h, η⟫) := by
    simp_rw [inner_smul_right]
  rw [hcoe] at havg
  rw [integral_sub h2int (hcosint.const_mul 2), integral_const_mul, setIntegral_const,
    smul_eq_mul, ← havg, measureReal_def]
  field_simp

/-- **The Fourier tail bound**: for `f ∈ L¹ ∩ L²(V; ℂ)` with `‖f(· + h) − f‖₂² ≤ Π‖h‖` for all `h` (`Π ≥ 0`) and `t > 0`,
`∫_{2π‖η‖ ≥ t} |𝓕 f(η)|² dη ≤ Π/(2c_d t)` with `c_d = 1 − sup_{y ≥ 1} j_d(y)`. -/
theorem lintegral_fourier_tail_le (hd : Module.finrank ℝ V = d) {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2)
    {Per : ℝ} (hPer : 0 ≤ Per) (htr : ∀ h : V, ∫ x, ‖f (x + h) - f x‖ ^ 2 ≤ Per * ‖h‖) {t : ℝ} (ht : 0 < t) :
    ∫⁻ η in {η : V | t ≤ 2 * Real.pi * ‖η‖}, ENNReal.ofReal (‖𝓕 f η‖ ^ 2) ≤
      ENNReal.ofReal (Per / (2 * (1 - sSup (jBall d '' Ici 1)) * t)) := by
  set cd : ℝ := 1 - sSup (jBall d '' Ici 1) with hcd
  have hcd0 : 0 < cd := by rw [hcd]; linarith [JBall.sSup_jBall_Ici_one_lt_one (d := d)]
  set R : ℝ := t⁻¹ with hRdef
  have hR : 0 < R := inv_pos.2 ht
  set B : Set V := ball (0 : V) R
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : 0 < (volume B).toReal := ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' hBfin
  set G : V → V → ℝ≥0∞ := fun h η => ENNReal.ofReal (‖𝓕 f η‖ ^ 2 * (2 - 2 * Real.cos (2 * Real.pi * ⟪h, η⟫)))
  have hFc : Continuous (𝓕 f) := continuous_fourier_of_integrable hf1
  have hGm : AEMeasurable (Function.uncurry G) ((volume.restrict B).prod volume) := by
    refine (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)).aemeasurable
    exact ((continuous_norm.comp (hFc.comp continuous_snd)).pow 2).mul (continuous_const.sub (continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul (continuous_fst.inner continuous_snd)))))
  -- the averaged identity
  have hupper : ∫⁻ h in B, ∫⁻ η, G h η ≤ ENNReal.ofReal (Per * R) * volume B := by
    calc ∫⁻ h in B, ∫⁻ η, G h η ≤ ∫⁻ _h in B, ENNReal.ofReal (Per * R) := by
          refine setLIntegral_mono' measurableSet_ball fun h hh => ?_
          rw [lintegral_fourier_sq_mul_one_sub_cos hf1 hf2 h]
          refine ENNReal.ofReal_le_ofReal ((htr h).trans (mul_le_mul_of_nonneg_left ?_ hPer))
          exact (mem_ball_zero_iff.1 hh).le
      _ = ENNReal.ofReal (Per * R) * volume B := setLIntegral_const _ _
  have hswap : ∫⁻ h in B, ∫⁻ η, G h η = ∫⁻ η, ∫⁻ h in B, G h η := lintegral_lintegral_swap hGm
  have hinner : ∀ η, ∫⁻ h in B, G h η =
      ENNReal.ofReal (‖𝓕 f η‖ ^ 2) *
        ENNReal.ofReal (2 * (volume B).toReal * (1 - jBall d (R * (2 * Real.pi * ‖η‖)))) := by
    intro η
    simp only [G]
    simp_rw [ENNReal.ofReal_mul (sq_nonneg ‖𝓕 f η‖)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ball_one_sub_cos hd hR η]
  -- the lower bound on the tail set
  have hlower : ENNReal.ofReal (2 * (volume B).toReal * cd) *
      ∫⁻ η in {η : V | t ≤ 2 * Real.pi * ‖η‖}, ENNReal.ofReal (‖𝓕 f η‖ ^ 2) ≤ ∫⁻ η, ∫⁻ h in B, G h η := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ η in {η : V | t ≤ 2 * Real.pi * ‖η‖}, ENNReal.ofReal (2 * (volume B).toReal * cd) *
          ENNReal.ofReal (‖𝓕 f η‖ ^ 2)
        ≤ ∫⁻ η in {η : V | t ≤ 2 * Real.pi * ‖η‖}, ∫⁻ h in B, G h η := by
          refine setLIntegral_mono' (measurableSet_le measurable_const (by fun_prop)) fun η hη => ?_
          rw [hinner η, mul_comm]
          gcongr
          have h1 : 1 ≤ R * (2 * Real.pi * ‖η‖) := by
            rw [hRdef, ← div_eq_inv_mul, le_div_iff₀ ht, one_mul]; exact hη
          have := le_csSup (JBall.bddAbove_jBall (d := d) (Ici 1)) (mem_image_of_mem _ (show _ ∈ Ici (1 : ℝ) from h1))
          rw [hcd]; linarith
      _ ≤ ∫⁻ η, ∫⁻ h in B, G h η := setLIntegral_le_lintegral _ _
  have hupper' : ∫⁻ h in B, ∫⁻ η, G h η ≤ ENNReal.ofReal (Per * R * (volume B).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBfin]; exact hupper
  have hmain := hlower.trans (hswap ▸ hupper')
  have hc0 : 0 < 2 * (volume B).toReal * cd := by positivity
  calc ∫⁻ η in {η : V | t ≤ 2 * Real.pi * ‖η‖}, ENNReal.ofReal (‖𝓕 f η‖ ^ 2)
      ≤ ENNReal.ofReal (Per * R * (volume B).toReal) / ENNReal.ofReal (2 * (volume B).toReal * cd) :=
        (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc0).ne') (Or.inl ENNReal.ofReal_ne_top)).2
          (by rw [mul_comm]; exact hmain)
    _ = ENNReal.ofReal (Per * R * (volume B).toReal / (2 * (volume B).toReal * cd)) :=
        (ENNReal.ofReal_div_of_pos hc0).symm
    _ = ENNReal.ofReal (Per / (2 * cd * t)) := by
        congr 1; rw [hRdef]; field_simp

end StatFormal.MollifierNorm
