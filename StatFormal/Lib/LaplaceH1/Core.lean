import StatFormal.Lib.LaplaceH1.Feature
import StatFormal.Lib.NativeChar.Char
import StatFormal.Lib.RKHSReg.Smooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The `H¹` identity for the explicit Laplace feature (library, untrusted)

For `σ > 0` and `u ∈ L²(ℝ)` let `f_u(x) = ⟪u, ψ_σ x⟫ = √(2/σ) e^{−x/σ} ∫_{(−∞,x]} e^{t/σ} u(t) dt` (`witL`, with the explicit
feature `ψ_σ` of `LaplaceH1.Feature`). Then

* `ac_integral_Iic`, `ae_hasDerivAt_integral_Iic`: an indefinite integral `x ↦ ∫_{(−∞,x]} w` of a function integrable on every
  `(−∞, x]` is absolutely continuous on every interval, with derivative `w` almost everywhere (Lebesgue's differentiation theorem);
* `witL_ac`, `witL_hasDerivAt`: `f_u` is absolutely continuous on every interval, with `f_u′ = −f_u/σ + √(2/σ) u` a.e.;
* `witL_h1`: `f_u, f_u′ ∈ L²`, `∫ f_u f_u′ = 0` (since `f_u → 0` at `±∞`) and
  `∫ (f_u² + σ² f_u′²) = 2σ ‖u‖²` — the Laplace RKHS norm is the `H¹` norm `(1/(2σ)) ∫ (f² + σ² f′²)`.

The pointwise identity behind the last item is `f² + σ²f′² = 2σu² − 2σ f f′` when `σ f′ = −f + √(2σ) u`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.LaplaceH1

section Indefinite

variable {w : ℝ → ℝ}

lemma integral_Iic_eq_add (hw : ∀ x, IntegrableOn w (Iic x)) (a x : ℝ) :
    ∫ t in Iic x, w t = (∫ t in Iic a, w t) + ∫ t in a..x, w t := by
  rw [← intervalIntegral.integral_Iic_sub_Iic (hw a) (hw x)]; ring

lemma intervalIntegrable_of_Iic (hw : ∀ x, IntegrableOn w (Iic x)) (a b : ℝ) : IntervalIntegrable w volume a b := by
  rw [intervalIntegrable_iff]
  exact (hw (max a b)).mono_set fun t ht => mem_Iic.mpr ht.2

/-- An indefinite integral from `−∞` is absolutely continuous on every interval. -/
theorem ac_integral_Iic (hw : ∀ x, IntegrableOn w (Iic x)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in Iic x, w t) a b := by
  have hfun : (fun x => ∫ t in Iic x, w t) = (fun _ => ∫ t in Iic a, w t) + fun x => ∫ t in a..x, w t := by
    funext x; rw [integral_Iic_eq_add hw a x]; rfl
  rw [hfun]
  refine AbsolutelyContinuousOnInterval.add ?_ ?_
  · exact ContDiffOn.absolutelyContinuousOnInterval contDiffOn_const
  · exact (intervalIntegrable_of_Iic hw a b).absolutelyContinuousOnInterval_intervalIntegral (by simp)

/-- An indefinite integral from `−∞` has derivative `w` almost everywhere. -/
theorem ae_hasDerivAt_integral_Iic (hw : ∀ x, IntegrableOn w (Iic x)) :
    ∀ᵐ x, HasDerivAt (fun x => ∫ t in Iic x, w t) (w x) x := by
  have hloc : LocallyIntegrable w volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨M, hM⟩ := hk.bddAbove
    exact (hw M).mono_set fun t ht => mem_Iic.mpr (hM ht)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with x hx
  have hfun : (fun x => ∫ t in Iic x, w t) = fun x => (∫ t in Iic 0, w t) + ∫ t in (0 : ℝ)..x, w t :=
    funext fun x => integral_Iic_eq_add hw 0 x
  rw [hfun]
  exact (hx 0).const_add _

end Indefinite

variable {σ : ℝ}

/-- The function `f_u = ⟪u, ψ_σ ·⟫` of `u ∈ L²(ℝ)`. -/
def witL (σ : ℝ) (u : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ := ⟪u, lapFeat σ x⟫_ℝ

lemma witL_eq (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    witL σ u = fun x => √(2 / σ) * (Real.exp (-(σ⁻¹ * x)) * ∫ t in Iic x, Real.exp (σ⁻¹ * t) * u t) := by
  funext x
  rw [witL, inner_lapFeat hσ]; ring

lemma lapFeat_gram' (hσ : 0 < σ) (x y : ℝ) :
    ⟪lapFeat σ x, lapFeat σ y⟫_ℝ = (fun z : ℝ => Real.exp (-|z| / σ)) (x - y) := lapFeat_gram hσ x y

/-- `f_u` is absolutely continuous on every interval. -/
theorem witL_ac (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (witL σ u) a b := by
  rw [witL_eq hσ u]
  have h1 : AbsolutelyContinuousOnInterval (fun x => Real.exp (-(σ⁻¹ * x))) a b :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have h2 := ac_integral_Iic (integrableOn_exp_mul_Iic_of_memLp hσ (Lp.memLp u)) a b
  exact (h1.fun_mul h2).const_mul (√(2 / σ))

/-- `f_u′ = −f_u/σ + √(2/σ) u` almost everywhere. -/
theorem witL_hasDerivAt (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    ∀ᵐ x, HasDerivAt (witL σ u) (-σ⁻¹ * witL σ u x + √(2 / σ) * u x) x := by
  filter_upwards [ae_hasDerivAt_integral_Iic (integrableOn_exp_mul_Iic_of_memLp hσ (Lp.memLp u))] with x hx
  rw [witL_eq hσ u]
  have he : HasDerivAt (fun x => Real.exp (-(σ⁻¹ * x))) (Real.exp (-(σ⁻¹ * x)) * (-(σ⁻¹ * 1))) x :=
    (((hasDerivAt_id x).const_mul σ⁻¹).neg).exp
  have := (he.mul hx).const_mul (√(2 / σ))
  convert this using 1
  have hee : Real.exp (-(σ⁻¹ * x)) * Real.exp (σ⁻¹ * x) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(√(2 / σ) * u x)) * hee

lemma witL_deriv_ae (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    deriv (witL σ u) =ᵐ[volume] fun x => -σ⁻¹ * witL σ u x + √(2 / σ) * u x := by
  filter_upwards [witL_hasDerivAt hσ u] with x hx
  exact hx.deriv

/-- `f_u` is continuous and square integrable (Wave31tp L18 (a) for the Laplace profile). -/
lemma witL_cont_memLp (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    Continuous (witL σ u) ∧ MemLp (witL σ u) 2 volume := by
  obtain ⟨h1, h2, -⟩ := StatFormal.NativeChar.native_le_norm (lapFeat_gram' hσ) (laplaceProfile_continuous σ)
    (laplaceProfile_integrable hσ) u
  exact ⟨h1, h2⟩

/-- `f_u → 0` at `±∞` (Wave31tp L26 for the Laplace profile). -/
lemma witL_tendsto (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    Tendsto (witL σ u) atBot (𝓝 0) ∧ Tendsto (witL σ u) atTop (𝓝 0) := by
  have h := StatFormal.RKHSReg.rkhs_vanish_facts (lapFeat_gram' hσ) (laplaceProfile_continuous σ)
    (laplaceProfile_integrable hσ) u
  have hn : (fun x : ℝ => ‖x‖) = abs := funext fun x => Real.norm_eq_abs x
  rw [hn, comap_abs_atTop] at h
  exact tendsto_sup.1 h

/-- `f_u′ ∈ L²`. -/
lemma witL_deriv_memLp (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) : MemLp (deriv (witL σ u)) 2 volume := by
  have h := ((witL_cont_memLp hσ u).2.const_mul (-σ⁻¹)).add ((Lp.memLp u).const_mul (√(2 / σ)))
  exact h.ae_eq (witL_deriv_ae hσ u).symm

/-- `∫_{−n}^{n} f f′ = (f(n)² − f(−n)²)/2` for `f` absolutely continuous on `[−n, n]`. -/
lemma integral_mul_deriv_self {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ x in a..b, f x * deriv f x = (f b * f b - f a * f a) / 2 := by
  have h := hf.integral_deriv_mul_eq_sub hf
  have hfun : (fun x => deriv f x * f x + f x * deriv f x) = fun x => 2 * (f x * deriv f x) := by
    funext x; ring
  rw [hfun, intervalIntegral.integral_const_mul] at h
  linarith

/-- If `f` is absolutely continuous on every interval, `f, f′ ∈ L²` and `f → 0` at `±∞`, then `∫ f f′ = 0`. -/
theorem integral_mul_deriv_eq_zero {f : ℝ → ℝ} (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hf : MemLp f 2 volume) (hd : MemLp (deriv f) 2 volume) (hbot : Tendsto f atBot (𝓝 0))
    (htop : Tendsto f atTop (𝓝 0)) : ∫ x, f x * deriv f x = 0 := by
  have hint : Integrable (fun x => f x * deriv f x) volume := hf.integrable_mul hd
  have hlim := intervalIntegral_tendsto_integral hint
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have heq : ∀ n : ℕ, ∫ x in (-(n : ℝ))..(n : ℝ), f x * deriv f x =
      (f n * f n - f (-(n : ℝ)) * f (-(n : ℝ))) / 2 := fun n => integral_mul_deriv_self (hac _ _)
  have h1 : Tendsto (fun n : ℕ => f n) atTop (𝓝 0) := htop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => f (-(n : ℝ))) atTop (𝓝 0) :=
    hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have h3 : Tendsto (fun n : ℕ => (f n * f n - f (-(n : ℝ)) * f (-(n : ℝ))) / 2) atTop (𝓝 0) := by
    have := ((h1.mul h1).sub (h2.mul h2)).div_const 2
    simpa using this
  have hlim' : Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), f x * deriv f x) atTop (𝓝 0) := by
    simp_rw [heq]; exact h3
  exact tendsto_nhds_unique hlim hlim'

/-- The pointwise identity `f² + σ²(−f/σ + c u)² = 2σu² − 2σ f (−f/σ + c u)` for `c² σ = 2`. -/
lemma h1_pointwise (hσ : 0 < σ) {c : ℝ} (hc : c ^ 2 * σ = 2) (f u : ℝ) :
    f ^ 2 + σ ^ 2 * (-σ⁻¹ * f + c * u) ^ 2 = 2 * σ * u ^ 2 - 2 * σ * (f * (-σ⁻¹ * f + c * u)) := by
  have hs : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  linear_combination (f ^ 2 * (σ * σ⁻¹ - 1) - 2 * σ * c * f * u) * hs + σ * u ^ 2 * hc

lemma sqrt_two_div_sq (hσ : 0 < σ) : √(2 / σ) ^ 2 * σ = 2 := by
  rw [Real.sq_sqrt (by positivity)]; field_simp

/-- **The `H¹` identity for the explicit feature**: `f_u` is locally absolutely continuous, `f_u, f_u′ ∈ L²`, `f_u → 0` at `±∞`
and `∫ (f_u² + σ² f_u′²) = 2σ‖u‖²`. -/
theorem witL_h1 (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) :
    (∀ a b, AbsolutelyContinuousOnInterval (witL σ u) a b) ∧ MemLp (witL σ u) 2 volume ∧
      MemLp (deriv (witL σ u)) 2 volume ∧
      ∫ x, (witL σ u x ^ 2 + σ ^ 2 * deriv (witL σ u) x ^ 2) = 2 * σ * ‖u‖ ^ 2 := by
  set f := witL σ u
  have hac : ∀ a b, AbsolutelyContinuousOnInterval f a b := witL_ac hσ u
  have hf : MemLp f 2 volume := (witL_cont_memLp hσ u).2
  have hd : MemLp (deriv f) 2 volume := witL_deriv_memLp hσ u
  refine ⟨hac, hf, hd, ?_⟩
  have h0 := integral_mul_deriv_eq_zero hac hf hd (witL_tendsto hσ u).1 (witL_tendsto hσ u).2
  have hpt : (fun x => f x ^ 2 + σ ^ 2 * deriv f x ^ 2) =ᵐ[volume]
      fun x => 2 * σ * u x ^ 2 - 2 * σ * (f x * deriv f x) := by
    filter_upwards [witL_deriv_ae hσ u] with x hx
    rw [hx]
    exact h1_pointwise hσ (sqrt_two_div_sq hσ) (f x) (u x)
  have hu2 : Integrable (fun x => u x ^ 2) volume := (Lp.memLp u).integrable_sq
  have hfd : Integrable (fun x => f x * deriv f x) volume := hf.integrable_mul hd
  rw [integral_congr_ae hpt, integral_sub (hu2.const_mul _) (hfd.const_mul _), integral_const_mul,
    integral_const_mul, h0, norm_sq_L2_eq]
  ring

/-- `f² + σ² f′²` is integrable when `f, f′ ∈ L²`. -/
lemma integrable_h1 {f d : ℝ → ℝ} (hf : MemLp f 2 volume) (hd : MemLp d 2 volume) :
    Integrable (fun x => f x ^ 2 + σ ^ 2 * d x ^ 2) volume :=
  hf.integrable_sq.add (hd.integrable_sq.const_mul _)

/-- The `H¹` functional in `[0, ∞]` is the real one when `f, f′ ∈ L²`:
`(1/(2σ)) ∫⁻ (f² + σ² f′²) = ofReal ((1/(2σ)) ∫ (f² + σ² f′²))`. -/
lemma h1_lintegral_eq {f d : ℝ → ℝ} (hf : MemLp f 2 volume) (hd : MemLp d 2 volume) :
    ENNReal.ofReal (1 / (2 * σ)) * ∫⁻ x, ENNReal.ofReal (f x ^ 2 + σ ^ 2 * d x ^ 2) =
      ENNReal.ofReal (1 / (2 * σ) * ∫ x, (f x ^ 2 + σ ^ 2 * d x ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_h1 hf hd)
    (Eventually.of_forall fun x => by positivity)]
  by_cases hσ : 0 ≤ 1 / (2 * σ)
  · rw [ENNReal.ofReal_mul hσ]
  · push Not at hσ
    rw [ENNReal.ofReal_of_nonpos hσ.le, zero_mul, ENNReal.ofReal_of_nonpos]
    exact mul_nonpos_of_nonpos_of_nonneg hσ.le (integral_nonneg fun x => by positivity)

end StatFormal.LaplaceH1
