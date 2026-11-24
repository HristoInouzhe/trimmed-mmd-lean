import StatFormal.Lib.LaplaceH1.Rep

/-!
# The representation theorem for the Laplace RKHS on `ℝ` (library, untrusted)

Let `f : ℝ → ℝ` be in `H¹(ℝ)`: absolutely continuous on every interval, with `f, f′ ∈ L²`. Then

* `h1_bounded`: `f` is bounded (`f(x)² − f(y)² = 2∫_y^x f f′`, so `f² ≤ f(y)² + 2‖f f′‖₁`; were `f² > 2‖f f′‖₁ + 1` somewhere,
  `f² ≥ 1` everywhere, against `f ∈ L²`);
* `integral_Iic_exp_mul_deriv`: `∫_{(−∞,x]} e^{t/σ} (f′(t) + f(t)/σ) dt = e^{x/σ} f(x)` (integration by parts on `[a, x]`, `a → −∞`,
  `e^{a/σ} f(a) → 0` since `f` is bounded);
* `witL_h1Rep`: with `u = (σ f′ + f)/√(2σ) ∈ L²`, `⟪u, ψ_σ x⟫ = f(x)` for every `x` (the explicit feature `ψ_σ` of
  `LaplaceH1.Feature`);
* `h1_rep`: for any feature map `φ` with the Laplace Gram function into a Hilbert space, `f` is represented, and some representer
  `g₀` has `2σ‖g₀‖² = ∫ (f² + σ² f′²)` and the least norm among all representers (the transfer `TIKernel.gram_rep_le` from `ψ_σ`
  to `φ`, and `LaplaceH1.rep_h1` for the lower bound).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.LaplaceH1

open StatFormal.TIKernel

variable {σ : ℝ} {f : ℝ → ℝ}

/-- `|∫_a^b h| ≤ ∫_ℝ |h|` for integrable `h`. -/
lemma abs_intervalIntegral_le_integral_abs {h : ℝ → ℝ} (hh : Integrable h volume) (a b : ℝ) :
    |∫ x in a..b, h x| ≤ ∫ x, |h x| := by
  rw [← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [Real.norm_eq_abs]
  exact setIntegral_le_integral hh.abs (Eventually.of_forall fun x => abs_nonneg _)

/-- **An `H¹` function of the line is bounded.** -/
theorem h1_bounded (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b) (hf : MemLp f 2 volume)
    (hd : MemLp (deriv f) 2 volume) : ∃ C, ∀ x, |f x| ≤ C := by
  set M := ∫ x, |f x * deriv f x|
  have hint : Integrable (fun x => f x * deriv f x) volume := hf.integrable_mul hd
  have hdiff : ∀ x y, f x ^ 2 ≤ f y ^ 2 + 2 * M := by
    intro x y
    have h1 := integral_mul_deriv_self (hac y x)
    have h2 := abs_intervalIntegral_le_integral_abs hint y x
    rw [h1] at h2
    have h3 := (abs_le.mp h2).2
    nlinarith
  refine ⟨√(2 * M + 1), fun x => ?_⟩
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  by_contra hlt
  push Not at hlt
  have hge : ∀ y, 1 ≤ f y ^ 2 := fun y => by linarith [hdiff x y]
  have hfi := hf.integrable_sq.hasFiniteIntegral
  have hinf : ∫⁻ y, ‖f y ^ 2‖ₑ = ⊤ := by
    refine eq_top_iff.mpr (le_trans ?_ (lintegral_mono fun y => (?_ : (1 : ENNReal) ≤ ‖f y ^ 2‖ₑ)))
    · rw [lintegral_const, Real.volume_univ, one_mul]
    · rw [Real.enorm_eq_ofReal (sq_nonneg _)]
      exact ENNReal.one_le_ofReal.mpr (hge y)
  exact absurd hfi (by rw [HasFiniteIntegral, hinf]; exact lt_irrefl _)

lemma hasDerivAt_exp_inv_mul (σ t : ℝ) :
    HasDerivAt (fun t => Real.exp (σ⁻¹ * t)) (σ⁻¹ * Real.exp (σ⁻¹ * t)) t := by
  have := ((hasDerivAt_id t).const_mul σ⁻¹).exp
  simpa [mul_comm] using this

/-- `∫_{(−∞,x]} e^{t/σ} (f′(t) + f(t)/σ) dt = e^{x/σ} f(x)` for `f ∈ H¹`. -/
theorem integral_Iic_exp_mul_deriv (hσ : 0 < σ) (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hf : MemLp f 2 volume) (hd : MemLp (deriv f) 2 volume) (x : ℝ) :
    ∫ t in Iic x, (Real.exp (σ⁻¹ * t) * deriv f t + σ⁻¹ * (Real.exp (σ⁻¹ * t) * f t)) =
      Real.exp (σ⁻¹ * x) * f x := by
  set E : ℝ → ℝ := fun t => Real.exp (σ⁻¹ * t)
  have hint : IntegrableOn (fun t => E t * deriv f t + σ⁻¹ * (E t * f t)) (Iic x) :=
    (integrableOn_exp_mul_Iic_of_memLp hσ hd x).add ((integrableOn_exp_mul_Iic_of_memLp hσ hf x).const_mul σ⁻¹)
  have hlim := intervalIntegral_tendsto_integral_Iic (l := atBot) (a := id) x hint tendsto_id
  have hEac : ∀ a b, AbsolutelyContinuousOnInterval E a b := fun a b =>
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hdE : deriv E = fun t => σ⁻¹ * E t := funext fun t => (hasDerivAt_exp_inv_mul σ t).deriv
  have heq : ∀ a, ∫ t in a..x, (E t * deriv f t + σ⁻¹ * (E t * f t)) = E x * f x - E a * f a := by
    intro a
    rw [← (hEac a x).integral_deriv_mul_eq_sub (hac a x), hdE]
    congr 1
    funext t
    ring
  obtain ⟨C, hC⟩ := h1_bounded hac hf hd
  have hE0 : Tendsto E atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot (inv_pos.mpr hσ) tendsto_id)
  have hEf : Tendsto (fun a => E a * f a) atBot (𝓝 0) := by
    refine squeeze_zero_norm (fun a => ?_) (by simpa using hE0.mul_const C)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hC a) (Real.exp_pos _).le
  have hlim' : Tendsto (fun a => ∫ t in id a..x, (E t * deriv f t + σ⁻¹ * (E t * f t))) atBot
      (𝓝 (E x * f x)) := by
    simp only [id, heq]
    simpa using (tendsto_const_nhds (x := E x * f x)).sub hEf
  exact tendsto_nhds_unique hlim hlim'

/-- `√(2/σ) σ = √(2σ)`. -/
lemma sqrt_two_div_mul (hσ : 0 < σ) : √(2 / σ) * σ = √(2 * σ) := by
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have h := Real.mul_self_sqrt (show 0 ≤ 2 / σ by positivity)
  symm
  calc √(2 / σ) * σ * (√(2 / σ) * σ) = (√(2 / σ) * √(2 / σ)) * σ ^ 2 := by ring
    _ = 2 * σ := by rw [h]; field_simp

/-- The `L²` element `u = (σ f′ + f)/√(2σ)` of an `H¹` function. -/
def h1Rep (σ : ℝ) (f : ℝ → ℝ) (hf : MemLp f 2 volume) (hd : MemLp (deriv f) 2 volume) : Lp ℝ 2 (volume : Measure ℝ) :=
  (((hd.const_mul σ).add hf).const_mul (√(2 * σ))⁻¹).toLp _

/-- **Every `H¹` function is a function of the explicit feature**: `⟪(σ f′ + f)/√(2σ), ψ_σ x⟫ = f(x)`. -/
theorem witL_h1Rep (hσ : 0 < σ) (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b) (hf : MemLp f 2 volume)
    (hd : MemLp (deriv f) 2 volume) : witL σ (h1Rep σ f hf hd) = f := by
  funext x
  rw [witL, inner_lapFeat hσ]
  have hae : (h1Rep σ f hf hd : ℝ → ℝ) =ᵐ[volume] fun t => (√(2 * σ))⁻¹ * (σ * deriv f t + f t) :=
    MemLp.coeFn_toLp _
  have h1 : ∫ t in Iic x, Real.exp (σ⁻¹ * t) * h1Rep σ f hf hd t =
      ∫ t in Iic x, (σ * (√(2 * σ))⁻¹) * (Real.exp (σ⁻¹ * t) * deriv f t + σ⁻¹ * (Real.exp (σ⁻¹ * t) * f t)) := by
    refine setIntegral_congr_ae measurableSet_Iic ?_
    filter_upwards [hae] with t ht _
    rw [ht]
    field_simp
  rw [h1, integral_const_mul, integral_Iic_exp_mul_deriv hσ hac hf hd x]
  have hs := sqrt_two_div_mul hσ
  have hpos : 0 < √(2 * σ) := Real.sqrt_pos.mpr (by positivity)
  have hee : Real.exp (-(σ⁻¹ * x)) * Real.exp (σ⁻¹ * x) = 1 := by rw [← Real.exp_add]; simp
  calc √(2 / σ) * Real.exp (-(σ⁻¹ * x)) * (σ * (√(2 * σ))⁻¹ * (Real.exp (σ⁻¹ * x) * f x))
      = (√(2 / σ) * σ) * (√(2 * σ))⁻¹ * (Real.exp (-(σ⁻¹ * x)) * Real.exp (σ⁻¹ * x)) * f x := by ring
    _ = f x := by rw [hs, hee, mul_inv_cancel₀ hpos.ne']; ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {φ : ℝ → H}

/-- **The representation theorem**: every `H¹` function `f` is represented by the Laplace feature map `φ`, by some `g₀` with
`2σ‖g₀‖² = ∫ (f² + σ² f′²)` and the least norm among all representers. -/
theorem h1_rep (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-|x - y| / σ))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b) (hf : MemLp f 2 volume) (hd : MemLp (deriv f) 2 volume) :
    ∃ g₀ : H, (∀ x, ⟪g₀, φ x⟫_ℝ = f x) ∧ 2 * σ * ‖g₀‖ ^ 2 = ∫ x, (f x ^ 2 + σ ^ 2 * deriv f x ^ 2) ∧
      ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ‖g₀‖ ≤ ‖g‖ := by
  set u := h1Rep σ f hf hd
  have hu : witL σ u = f := witL_h1Rep hσ hac hf hd
  have hG' : ∀ x y, ⟪lapFeat σ x, lapFeat σ y⟫_ℝ = ⟪φ x, φ y⟫_ℝ := fun x y => (gram_lap hσ hφ x y).symm
  obtain ⟨g₀, hg₀u, hg₀⟩ := gram_rep_le hG' u
  have hrep : ∀ x, ⟪g₀, φ x⟫_ℝ = f x := fun x => by rw [hg₀ x, ← hu]; rfl
  have hI : ∫ x, (f x ^ 2 + σ ^ 2 * deriv f x ^ 2) = 2 * σ * ‖u‖ ^ 2 := by
    have := (witL_h1 hσ u).2.2.2
    rwa [hu] at this
  -- every representer has `∫ (f² + σ²f′²) ≤ 2σ‖g‖²`
  have hlow : ∀ g : H, (∀ x, ⟪g, φ x⟫_ℝ = f x) → ∫ x, (f x ^ 2 + σ ^ 2 * deriv f x ^ 2) ≤ 2 * σ * ‖g‖ ^ 2 := by
    intro g hg
    obtain rfl : (fun x => ⟪g, φ x⟫_ℝ) = f := funext hg
    exact (rep_h1 hσ hφ g).2.2.2.1
  have hsq : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 2 * σ * a ^ 2 ≤ 2 * σ * b ^ 2 → a ≤ b := by
    intro a b ha hb hab
    have : a ^ 2 ≤ b ^ 2 := le_of_mul_le_mul_left hab (by positivity)
    exact pow_le_pow_iff_left₀ ha hb two_ne_zero |>.mp this
  have hug : ‖u‖ ≤ ‖g₀‖ := hsq _ _ (norm_nonneg _) (norm_nonneg _) (hI ▸ hlow g₀ hrep)
  have heq : ‖g₀‖ = ‖u‖ := le_antisymm hg₀u hug
  refine ⟨g₀, hrep, by rw [hI, heq], fun g hg => ?_⟩
  rw [heq]
  exact hsq _ _ (norm_nonneg _) (norm_nonneg _) (hI ▸ hlow g hg)

end StatFormal.LaplaceH1
