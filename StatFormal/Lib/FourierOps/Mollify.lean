import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierOps.Dilate
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollified indicators (library, untrusted)

For a set `E` of a finite-dimensional real inner-product space `V` and a real `g`, `mollify E g = 1_E ⋆ g`
(`(1_E ⋆ g)(x) = ∫ 1_E(t) g(x − t) dt`, Mathlib's `convolution` with `lsmul ℝ ℝ`). Classical facts (Evans, *PDE*, App. C.4):

* for a probability density `g` (`g ≥ 0`, `∫ g = 1`): `0 ≤ 1_E ⋆ g ≤ 1`;
* if `g` vanishes off `closedBall 0 r`: `1_E ⋆ g (x) = 1` when `closedBall x r ⊆ E` (and `∫ g = 1`), and `= 0` when
  `closedBall x r ∩ E = ∅`;
* `1_E ⋆ g` is integrable, square integrable, and `𝓕 (1_E ⋆ g) = 𝓕 1_E · 𝓕 g` when `E` has finite measure and `g ∈ L¹`
  (Mathlib's `Real.fourier_mul_convolution_eq` after casting to `ℂ`);
* smooth with compact support for `E` bounded and `g` smooth with compact support (`HasCompactSupport.contDiff_convolution_right`),
  continuous for `g` bounded continuous (`BddAbove.continuous_convolution_right_of_integrable`).

The two bundles `mollify_smooth_facts` (dilated smooth mollifier `b_w`, with `𝓕 b_w(ξ) = 𝓕 b(w ξ)`) and `mollify_cont_facts`
(bounded continuous density) are the statements L8 (a), (b) of Wave 31tp.
-/

noncomputable section
open MeasureTheory FourierTransform Set Metric
open scoped InnerProductSpace RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false

namespace StatFormal.FourierOps

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- Unfolding: `mollify E g x = ∫ 1_E(t) g(x − t) dt`. -/
theorem mollify_apply (E : Set V) (g : V → ℝ) (x : V) :
    mollify E g x = ∫ t, E.indicator (fun _ => (1 : ℝ)) t * g (x - t) := by
  simp [mollify, convolution_def]

/-- The indicator of a measurable set of finite measure is integrable. -/
theorem integrable_indicator_one {E : Set V} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    Integrable (E.indicator fun _ => (1 : ℝ)) :=
  (integrable_indicator_iff hE).2 (integrableOn_const hfin)

/-- A mollified indicator is nonnegative when the mollifier is. -/
theorem mollify_nonneg (E : Set V) {g : V → ℝ} (hg0 : ∀ x, 0 ≤ g x) (x : V) : 0 ≤ mollify E g x := by
  rw [mollify_apply]
  exact integral_nonneg fun t => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) t) (hg0 _)

/-- A set mollified by a probability density is at most `1`. -/
theorem mollify_le_one (E : Set V) {g : V → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) (hg1 : ∫ x, g x = 1)
    (x : V) : mollify E g x ≤ 1 := by
  rw [mollify_apply]
  calc ∫ t, E.indicator (fun _ => (1 : ℝ)) t * g (x - t) ≤ ∫ t, g (x - t) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) t) (hg0 _))
          (hgi.comp_sub_left x) (Filter.Eventually.of_forall fun t => ?_)
        by_cases ht : t ∈ E <;> simp [ht, hg0]
    _ = ∫ t, g t := integral_sub_left_eq_self g volume x
    _ = 1 := hg1

/-- If `g` vanishes off `closedBall 0 r`, then `1_E ⋆ g (x) = ∫ g` whenever `closedBall x r ⊆ E`. -/
theorem mollify_eq_integral_of_closedBall_subset {E : Set V} {g : V → ℝ} {r : ℝ}
    (hgs : Function.support g ⊆ closedBall 0 r) {x : V} (hx : closedBall x r ⊆ E) :
    mollify E g x = ∫ t, g t := by
  rw [mollify_apply, ← integral_sub_left_eq_self g volume x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases hg : g (x - t) = 0
  · simp [hg]
  · have hmem : x - t ∈ closedBall (0 : V) r := hgs hg
    have ht : t ∈ E := hx (by rwa [mem_closedBall_zero_iff, ← dist_eq_norm, dist_comm] at hmem)
    simp [ht]

/-- If `g` vanishes off `closedBall 0 r`, then `1_E ⋆ g (x) = 0` whenever `closedBall x r ∩ E = ∅`. -/
theorem mollify_eq_zero_of_closedBall_inter {E : Set V} {g : V → ℝ} {r : ℝ}
    (hgs : Function.support g ⊆ closedBall 0 r) {x : V} (hx : closedBall x r ∩ E = ∅) :
    mollify E g x = 0 := by
  rw [mollify_apply]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans (integral_zero V ℝ)
  by_cases hg : g (x - t) = 0
  · simp [hg]
  · have hmem : x - t ∈ closedBall (0 : V) r := hgs hg
    have ht : t ∉ E := fun ht => by
      have : t ∈ closedBall x r ∩ E :=
        ⟨by rwa [mem_closedBall_zero_iff, ← dist_eq_norm, dist_comm] at hmem, ht⟩
      rw [hx] at this
      exact this
    simp [ht]

/-- A mollified indicator of a finite-measure set with an integrable mollifier is integrable. -/
theorem integrable_mollify {E : Set V} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) {g : V → ℝ} (hgi : Integrable g) :
    Integrable (mollify E g) :=
  (integrable_indicator_one hE hfin).integrable_convolution _ hgi

/-- An integrable function with values in `[0, 1]` is square integrable. -/
theorem memLp_two_of_integrable_of_unit {f : V → ℝ} (hfi : Integrable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    MemLp f 2 := by
  rw [memLp_two_iff_integrable_sq hfi.aestronglyMeasurable]
  refine hfi.mono' (hfi.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [h0 x, h1 x]

/-- The complex cast of a mollified indicator is the complex convolution of the casts. -/
theorem ofReal_mollify (E : Set V) (g : V → ℝ) (x : V) :
    ((mollify E g x : ℝ) : ℂ) =
      convolution (fun t => ((E.indicator (fun _ => (1 : ℝ)) t : ℝ) : ℂ)) (fun t => (g t : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume x := by
  rw [mollify_apply, convolution_def, ← integral_complex_ofReal]
  simp

/-- **Convolution theorem for mollified indicators**: `𝓕 (1_E ⋆ g) = 𝓕 1_E · 𝓕 g` (`E` of finite measure, `g ∈ L¹`). -/
theorem fourier_mollify {E : Set V} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) {g : V → ℝ} (hgi : Integrable g)
    (ξ : V) :
    𝓕 (fun x => (mollify E g x : ℂ)) ξ =
      𝓕 (fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) ξ * 𝓕 (fun x => (g x : ℂ)) ξ := by
  rw [show (fun x => (mollify E g x : ℂ)) = _ from funext (ofReal_mollify E g)]
  exact Real.fourier_mul_convolution_eq (integrable_indicator_one hE hfin).ofReal hgi.ofReal ξ

section Smooth

variable {b : V → ℝ} {w : ℝ}

/-- The dilation `b_w` of a smooth `b` supported in the closed unit ball is smooth. -/
theorem contDiff_dilateR (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (dilateR w b) :=
  contDiff_const.mul (hb.comp (contDiff_const_smul w⁻¹))

/-- The dilation `b_w` of a function supported in the closed unit ball has compact support. -/
theorem hasCompactSupport_dilateR (hbs : Function.support b ⊆ closedBall 0 1) (hw : 0 < w) :
    HasCompactSupport (dilateR w b) :=
  HasCompactSupport.intro (isCompact_closedBall 0 w) fun _ hx =>
    Function.notMem_support.1 fun h => hx (support_dilateR_subset hbs hw h)

/-- **Mollified indicators with a smooth compactly supported mollifier** (L8 (a)): for `E` measurable and bounded and `b`
a smooth probability density supported in the closed unit ball, `f = 1_E ⋆ b_w` is `C^∞` with compact support, takes values in
`[0, 1]`, equals `1` on points whose `w`-ball lies in `E` and `0` on points whose `w`-ball misses `E`, is in `L¹ ∩ L²`, and
`𝓕 f(ξ) = 𝓕 1_E(ξ) · 𝓕 b(w ξ)`. -/
theorem mollify_smooth_facts {E : Set V} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) (hb : ContDiff ℝ ∞ b)
    (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∫ x, b x = 1) (hbs : Function.support b ⊆ closedBall 0 1) (hw : 0 < w) :
    ContDiff ℝ ∞ (mollify E (dilateR w b)) ∧ HasCompactSupport (mollify E (dilateR w b)) ∧
      (∀ x, 0 ≤ mollify E (dilateR w b) x ∧ mollify E (dilateR w b) x ≤ 1) ∧
      (∀ x, closedBall x w ⊆ E → mollify E (dilateR w b) x = 1) ∧
      (∀ x, closedBall x w ∩ E = ∅ → mollify E (dilateR w b) x = 0) ∧
      Integrable (mollify E (dilateR w b)) ∧ MemLp (mollify E (dilateR w b)) 2 ∧
      ∀ ξ, 𝓕 (fun x => (mollify E (dilateR w b) x : ℂ)) ξ =
        𝓕 (fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) ξ * 𝓕 (fun x => (b x : ℂ)) (w • ξ) := by
  have hfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hbc : HasCompactSupport b := HasCompactSupport.intro (isCompact_closedBall 0 1) fun x hx =>
    Function.notMem_support.1 fun h => hx (hbs h)
  have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
  have hbwi : Integrable (dilateR w b) := integrable_dilateR hbi hw
  have hbw0 : ∀ x, 0 ≤ dilateR w b x := dilateR_nonneg hb0 hw
  have hbw1 : ∫ x, dilateR w b x = 1 := by rw [integral_dilateR b hw, hb1]
  have hbws : Function.support (dilateR w b) ⊆ closedBall 0 w := support_dilateR_subset hbs hw
  have hzero : ∀ x, closedBall x w ∩ E = ∅ → mollify E (dilateR w b) x = 0 := fun x hx =>
    mollify_eq_zero_of_closedBall_inter hbws hx
  have hbd : ∀ x, 0 ≤ mollify E (dilateR w b) x ∧ mollify E (dilateR w b) x ≤ 1 := fun x =>
    ⟨mollify_nonneg E hbw0 x, mollify_le_one E hbw0 hbwi hbw1 x⟩
  have hint : Integrable (mollify E (dilateR w b)) := integrable_mollify hE hfin hbwi
  refine ⟨?_, ?_, hbd, fun x hx => by rw [mollify_eq_integral_of_closedBall_subset hbws hx, hbw1], hzero, hint,
    memLp_two_of_integrable_of_unit hint (fun x => (hbd x).1) (fun x => (hbd x).2), fun ξ => ?_⟩
  · exact (hasCompactSupport_dilateR hbs hw).contDiff_convolution_right _
      (integrable_indicator_one hE hfin).locallyIntegrable (contDiff_dilateR hb)
  · obtain ⟨R, hR⟩ := hEb.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + w)) fun x hx => hzero x ?_
    refine eq_empty_of_forall_notMem fun t ⟨htx, htE⟩ => hx ?_
    have h1 : ‖t‖ ≤ R := mem_closedBall_zero_iff.1 (hR htE)
    have h2 : ‖t - x‖ ≤ w := by rw [← dist_eq_norm]; exact htx
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖t - (t - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖t‖ + ‖t - x‖ := norm_sub_le _ _
      _ ≤ R + w := add_le_add h1 h2
  · rw [fourier_mollify hE hfin hbwi, ← dilate_ofReal, fourier_dilate _ hw]

end Smooth

/-- **Indicators mollified by a bounded continuous probability density** (L8 (b)): for `E` measurable of finite measure and
`b` a bounded continuous probability density, `f = 1_E ⋆ b` is continuous, in `L¹ ∩ L²`, takes values in `[0, 1]`, and
`𝓕 f = 𝓕 1_E · 𝓕 b`. -/
theorem mollify_cont_facts {E : Set V} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) {b : V → ℝ} (hbc : Continuous b)
    (hbB : ∃ C, ∀ x, |b x| ≤ C) (hbi : Integrable b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∫ x, b x = 1) :
    Continuous (mollify E b) ∧ Integrable (mollify E b) ∧ MemLp (mollify E b) 2 ∧
      (∀ x, 0 ≤ mollify E b x ∧ mollify E b x ≤ 1) ∧
      ∀ ξ, 𝓕 (fun x => (mollify E b x : ℂ)) ξ =
        𝓕 (fun x => ((E.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) ξ * 𝓕 (fun x => (b x : ℂ)) ξ := by
  obtain ⟨C, hC⟩ := hbB
  have hbd : ∀ x, 0 ≤ mollify E b x ∧ mollify E b x ≤ 1 := fun x =>
    ⟨mollify_nonneg E hb0 x, mollify_le_one E hb0 hbi hb1 x⟩
  have hint : Integrable (mollify E b) := integrable_mollify hE hfin hbi
  refine ⟨?_, hint, memLp_two_of_integrable_of_unit hint (fun x => (hbd x).1) (fun x => (hbd x).2), hbd,
    fourier_mollify hE hfin hbi⟩
  have hB : BddAbove (range fun x => ‖b x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; simpa [Real.norm_eq_abs] using hC x⟩
  exact hB.continuous_convolution_right_of_integrable _ (integrable_indicator_one hE hfin) hbc

end StatFormal.FourierOps
