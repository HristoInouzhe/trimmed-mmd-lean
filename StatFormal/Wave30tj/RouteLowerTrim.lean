import StatFormal.Wave30tj.Statements
import StatFormal.Lib.TrimmedMean.Population
import StatFormal.Lib.TrimmedMean.Empirical
import StatFormal.Archive.Wave8a.RouteGeorep
import StatFormal.Archive.Wave30z.RouteDual
import StatFormal.Archive.Wave30az.RouteTrimmed
import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Route (wave 30tj): the set-up paragraph of `lem:trimlinear` (untrusted)

`Φ(s) = ∫ ψ_s dF = s − β G(s)`, `G(s) = ∫ (s − u)_+ dF(u)`. For `s ≤ t`,
`(t − s) F(s) ≤ G(t) − G(s) ≤ (t − s) F(t−)` (pointwise `(t−s)1{u ≤ s} ≤ (t−u)_+ − (s−u)_+ ≤ (t−s)1{u < t}`). This gives
the one-sided derivatives (with the right continuity of the cdf and its left limit `F(s−)`), the maximiser
characterisation, and with a `(1−α)`-quantile `q ∈ [−κ,κ]` (constructed as `inf {t : F(t) ≥ 1 − α}`) the value
`L(F) = Φ(q)`; the infimum over trimmings is the library `isLeast_region` (Rockafellar–Uryasev, attained) for the
clamped identity feature map `ℝ → ℝ`; the empirical law is the library `trimLo_eq` / `trimDual_le_trimLo`, and the
order-statistic form is the frozen (certified) Wave 30az `trimmedmean_min`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace StatFormal.Wave30tj

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

open StatFormal.TrimmedMMD.Concentration (empirical region)
open StatFormal.TrimmedMMD.BangBang (capped cap kfloor ord)

/-- The clamp `u ↦ max (−κ) (min κ u)`. -/
def clampK (κ u : ℝ) : ℝ := max (-κ) (min κ u)

lemma clampK_measurable (κ : ℝ) : Measurable (clampK κ) :=
  measurable_const.max (measurable_const.min measurable_id)

lemma clampK_abs {κ : ℝ} (hκ : 0 ≤ κ) (u : ℝ) : |clampK κ u| ≤ κ := by
  unfold clampK; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clampK_of_mem {κ u : ℝ} (hu : u ∈ Icc (-κ) κ) : clampK κ u = u := by
  unfold clampK; rw [min_eq_right hu.2, max_eq_right hu.1]

section Pop
variable {F : Measure ℝ} [IsProbabilityMeasure F] {κ α : ℝ}

lemma kappa_nonneg_of (hF : F (Icc (-κ) κ) = 1) : 0 ≤ κ := by
  by_contra h
  push_neg at h
  rw [Icc_eq_empty (by linarith), measure_empty] at hF
  exact zero_ne_one hF

lemma ae_mem_Icc (hF : F (Icc (-κ) κ) = 1) : ∀ᵐ u ∂F, u ∈ Icc (-κ) κ := by
  rw [ae_iff]
  have : {u | ¬ u ∈ Icc (-κ) κ} = (Icc (-κ) κ)ᶜ := rfl
  rw [this, prob_compl_eq_zero_iff measurableSet_Icc]
  exact hF

lemma ae_clampK (hF : F (Icc (-κ) κ) = 1) : ∀ᵐ u ∂F, clampK κ u = u := by
  filter_upwards [ae_mem_Icc hF] with u hu using clampK_of_mem hu

lemma integrable_of_bdd_on (hF : F (Icc (-κ) κ) = 1) {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ u ∈ Icc (-κ) κ, |f u| ≤ C) : Integrable f F :=
  Integrable.of_bound hf.aestronglyMeasurable C (by
    filter_upwards [ae_mem_Icc hF] with u hu; rw [Real.norm_eq_abs]; exact hC u hu)

lemma integrable_pos (hF : F (Icc (-κ) κ) = 1) (s : ℝ) : Integrable (fun u => max (s - u) 0) F :=
  integrable_of_bdd_on hF ((measurable_const.sub measurable_id).max measurable_const) (|s| + κ) fun u hu => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by have := abs_nonneg s; have := kappa_nonneg_of hF; linarith)
    have := neg_abs_le s; have := le_abs_self s; linarith [hu.1]

/-- `G(s) = ∫ (s − u)_+ dF`. -/
def Gpos (F : Measure ℝ) (s : ℝ) : ℝ := ∫ u, max (s - u) 0 ∂F

lemma integral_psi (hF : F (Icc (-κ) κ) = 1) (s : ℝ) :
    ∫ u, psi α s u ∂F = s - (1 - α)⁻¹ * Gpos F s := by
  unfold psi Gpos
  rw [integral_sub (integrable_const _) ((integrable_pos hF s).const_mul _), integral_const, integral_const_mul]
  simp

lemma pt_lower {s t : ℝ} (hst : s ≤ t) (u : ℝ) :
    (Iic s).indicator (fun _ => t - s) u ≤ max (t - u) 0 - max (s - u) 0 := by
  by_cases hu : u ≤ s
  · rw [indicator_of_mem (show u ∈ Iic s from hu), max_eq_left (by linarith), max_eq_left (by linarith)]; ring_nf
    exact le_rfl
  · rw [indicator_of_notMem (show u ∉ Iic s from hu)]
    have : max (s - u) 0 ≤ max (t - u) 0 := max_le_max (by linarith) le_rfl
    linarith

lemma pt_upper {s t : ℝ} (hst : s ≤ t) (u : ℝ) :
    max (t - u) 0 - max (s - u) 0 ≤ (Iio t).indicator (fun _ => t - s) u := by
  by_cases hu : u < t
  · rw [indicator_of_mem (show u ∈ Iio t from hu)]
    have h1 : t - u ≤ max (s - u) 0 + (t - s) := by have := le_max_left (s - u) 0; linarith
    have h2 : (0 : ℝ) ≤ max (s - u) 0 + (t - s) := by have := le_max_right (s - u) 0; linarith
    have := max_le h1 h2
    linarith
  · rw [indicator_of_notMem (show u ∉ Iio t from hu)]
    push_neg at hu
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp

lemma G_incr (hF : F (Icc (-κ) κ) = 1) {s t : ℝ} (hst : s ≤ t) :
    (t - s) * F.real (Iic s) ≤ Gpos F t - Gpos F s ∧ Gpos F t - Gpos F s ≤ (t - s) * F.real (Iio t) := by
  have hd : Gpos F t - Gpos F s = ∫ u, (max (t - u) 0 - max (s - u) 0) ∂F := by
    unfold Gpos; rw [integral_sub (integrable_pos hF t) (integrable_pos hF s)]
  have hI : Integrable (fun u => max (t - u) 0 - max (s - u) 0) F := (integrable_pos hF t).sub (integrable_pos hF s)
  rw [hd]
  constructor
  · have := integral_mono ((integrable_const (t - s)).indicator measurableSet_Iic) hI (pt_lower hst)
    rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul] at this
    linarith
  · have := integral_mono hI ((integrable_const (t - s)).indicator measurableSet_Iio) (pt_upper hst)
    rw [integral_indicator measurableSet_Iio, setIntegral_const, smul_eq_mul] at this
    linarith

lemma Phi_diff (hF : F (Icc (-κ) κ) = 1) (s t : ℝ) :
    ∫ u, psi α t u ∂F - ∫ u, psi α s u ∂F = (t - s) - (1 - α)⁻¹ * (Gpos F t - Gpos F s) := by
  rw [integral_psi hF, integral_psi hF]; ring

/-- `F(Iic ·)` is right-continuous. -/
lemma tendsto_Iic_right (s : ℝ) : Tendsto (fun t => F.real (Iic t)) (𝓝[>] s) (𝓝 (F.real (Iic s))) := by
  have h := ((cdf F).right_continuous s).tendsto
  have e : (cdf F : ℝ → ℝ) = fun t => F.real (Iic t) := funext fun t => cdf_eq_real F t
  rw [e] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

lemma real_Iio_eq_leftLim (s : ℝ) : F.real (Iio s) = Function.leftLim (cdf F) s := by
  have h := (cdf F).measure_Iio (tendsto_cdf_atBot F) s
  rw [measure_cdf, sub_zero] at h
  rw [measureReal_def, h, ENNReal.toReal_ofReal]
  exact (cdf_nonneg F (s - 1)).trans ((monotone_cdf F).le_leftLim (by linarith))

/-- `F(Iic t) → F(s−)` as `t ↑ s`. -/
lemma tendsto_Iic_left (s : ℝ) : Tendsto (fun t => F.real (Iic t)) (𝓝[<] s) (𝓝 (F.real (Iio s))) := by
  have h := (monotone_cdf F).tendsto_leftLim s
  rw [real_Iio_eq_leftLim]
  have e : (cdf F : ℝ → ℝ) = fun t => F.real (Iic t) := funext fun t => cdf_eq_real F t
  rwa [e] at h ⊢

lemma real_Iio_le_Iic (s : ℝ) : F.real (Iio s) ≤ F.real (Iic s) := measureReal_mono Iio_subset_Iic_self

lemma isMaxOn_iff (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (s : ℝ) :
    IsMaxOn (fun s => ∫ u, psi α s u ∂F) univ s ↔ (F.real (Iio s) ≤ 1 - α ∧ 1 - α ≤ F.real (Iic s)) := by
  have hβ : 0 < 1 - α := by linarith
  have hβi : 0 < (1 - α)⁻¹ := inv_pos.2 hβ
  constructor
  · intro hmax
    constructor
    · by_contra hc
      push_neg at hc
      -- some `t < s` has `F(t) > 1 − α`
      have hev := (tendsto_Iic_left (F := F) s).eventually (lt_mem_nhds hc)
      obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
      have hts : t ≤ s := le_of_lt ht2
      obtain ⟨-, hup⟩ := G_incr hF hts
      have hlow := (G_incr hF hts).1
      have hd := Phi_diff (α := α) hF t s
      have hm : (∫ u, psi α t u ∂F) ≤ ∫ u, psi α s u ∂F := hmax (mem_univ t)
      -- Φ s − Φ t = (s − t) − β(G s − G t) ≤ (s − t)(1 − β F(t)) < 0
      have hst : 0 < s - t := by linarith [ht2]
      have h3 : (1 - α)⁻¹ * ((s - t) * F.real (Iic t)) ≤ (1 - α)⁻¹ * (Gpos F s - Gpos F t) :=
        mul_le_mul_of_nonneg_left hlow hβi.le
      have h4 : (s - t) < (1 - α)⁻¹ * ((s - t) * F.real (Iic t)) := by
        have : 1 < (1 - α)⁻¹ * F.real (Iic t) := by
          rw [← div_eq_inv_mul, lt_div_iff₀ hβ]; linarith
        nlinarith
      linarith
    · by_contra hc
      push_neg at hc
      have hev := (tendsto_Iic_right (F := F) s).eventually (gt_mem_nhds hc)
      obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
      have hst' : s ≤ t := le_of_lt ht2
      have hup := (G_incr hF hst').2
      have hd := Phi_diff (α := α) hF s t
      have hm : (∫ u, psi α t u ∂F) ≤ ∫ u, psi α s u ∂F := hmax (mem_univ t)
      have hts : 0 < t - s := by linarith [ht2]
      have hlt : F.real (Iio t) < 1 - α := lt_of_le_of_lt (real_Iio_le_Iic t) ht1
      have h3 : (1 - α)⁻¹ * (Gpos F t - Gpos F s) ≤ (1 - α)⁻¹ * ((t - s) * F.real (Iio t)) :=
        mul_le_mul_of_nonneg_left hup hβi.le
      have h4 : (1 - α)⁻¹ * ((t - s) * F.real (Iio t)) < t - s := by
        have : (1 - α)⁻¹ * F.real (Iio t) < 1 := by
          rw [← div_eq_inv_mul, div_lt_iff₀ hβ]; linarith
        nlinarith
      linarith
  · rintro ⟨h1, h2⟩ t -
    show (∫ u, psi α t u ∂F) ≤ ∫ u, psi α s u ∂F
    rcases le_total s t with hst | hts
    · have hup := (G_incr hF hst).1
      have hd := Phi_diff (α := α) hF s t
      have h3 : (1 - α)⁻¹ * ((t - s) * F.real (Iic s)) ≤ (1 - α)⁻¹ * (Gpos F t - Gpos F s) :=
        mul_le_mul_of_nonneg_left hup hβi.le
      have h4 : t - s ≤ (1 - α)⁻¹ * ((t - s) * F.real (Iic s)) := by
        have : 1 ≤ (1 - α)⁻¹ * F.real (Iic s) := by
          rw [← div_eq_inv_mul, le_div_iff₀ hβ]; linarith
        nlinarith
      linarith
    · have hlow := (G_incr hF hts).2
      have hd := Phi_diff (α := α) hF t s
      have h3 : (1 - α)⁻¹ * (Gpos F s - Gpos F t) ≤ (1 - α)⁻¹ * ((s - t) * F.real (Iio s)) :=
        mul_le_mul_of_nonneg_left hlow hβi.le
      have h4 : (1 - α)⁻¹ * ((s - t) * F.real (Iio s)) ≤ s - t := by
        have : (1 - α)⁻¹ * F.real (Iio s) ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_iff₀ hβ]; linarith
        nlinarith
      linarith

theorem lowertrim_shape : Claims.lowertrim_shape := by
  intro F _ κ α hF hα0 hα1
  have hβ : 0 < 1 - α := by linarith
  have hβi : 0 < (1 - α)⁻¹ := inv_pos.2 hβ
  refine ⟨?_, fun s => ?_, fun s => ?_, isMaxOn_iff hF hα0 hα1⟩
  · -- concavity
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [integral_psi hF, integral_psi hF, integral_psi hF]
    have hG : Gpos F (a * x + b * y) ≤ a * Gpos F x + b * Gpos F y := by
      unfold Gpos
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((integrable_pos hF x).const_mul a)
        ((integrable_pos hF y).const_mul b)]
      refine integral_mono (integrable_pos hF _) (((integrable_pos hF x).const_mul a).add
        ((integrable_pos hF y).const_mul b)) fun u => ?_
      simp only
      refine max_le ?_ (by positivity)
      have e : a * x + b * y - u = a * (x - u) + b * (y - u) := by linear_combination u * hab
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    have := mul_le_mul_of_nonneg_left hG hβi.le
    nlinarith
  · -- right derivative
    rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
    have hlow : Tendsto (fun t => 1 - (1 - α)⁻¹ * F.real (Iic t)) (𝓝[>] s)
        (𝓝 (1 - (1 - α)⁻¹ * F.real (Iic s))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_Iic_right s))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : s < t)
      have hst : 0 < t - s := by linarith
      rw [slope_def_field, Phi_diff hF, le_div_iff₀ hst]
      have hup := (G_incr hF ht.le).2
      have := mul_le_mul_of_nonneg_left (hup.trans (mul_le_mul_of_nonneg_left (real_Iio_le_Iic t) hst.le)) hβi.le
      nlinarith
    · filter_upwards [self_mem_nhdsWithin] with t (ht : s < t)
      have hst : 0 < t - s := by linarith
      rw [slope_def_field, Phi_diff hF, div_le_iff₀ hst]
      have hlo := (G_incr hF ht.le).1
      have := mul_le_mul_of_nonneg_left hlo hβi.le
      nlinarith
  · -- left derivative
    rw [hasDerivWithinAt_iff_tendsto_slope, Iic_sdiff_right]
    have hup : Tendsto (fun t => 1 - (1 - α)⁻¹ * F.real (Iic t)) (𝓝[<] s)
        (𝓝 (1 - (1 - α)⁻¹ * F.real (Iio s))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_Iic_left s))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < s)
      have hst : 0 < s - t := by linarith
      have e : slope (fun s => ∫ u, psi α s u ∂F) s t =
          (∫ u, psi α s u ∂F - ∫ u, psi α t u ∂F) / (s - t) := by
        rw [slope_def_field, ← neg_div_neg_eq]; ring_nf
      rw [e, Phi_diff hF, le_div_iff₀ hst]
      have hG := (G_incr hF ht.le).2
      have := mul_le_mul_of_nonneg_left hG hβi.le
      nlinarith
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < s)
      have hst : 0 < s - t := by linarith
      have e : slope (fun s => ∫ u, psi α s u ∂F) s t =
          (∫ u, psi α s u ∂F - ∫ u, psi α t u ∂F) / (s - t) := by
        rw [slope_def_field, ← neg_div_neg_eq]; ring_nf
      rw [e, Phi_diff hF, div_le_iff₀ hst]
      have hG := (G_incr hF ht.le).1
      have := mul_le_mul_of_nonneg_left hG hβi.le
      nlinarith

/-- A `(1−α)`-quantile in `[−κ, κ]`. -/
lemma exists_quantile (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ q ∈ Icc (-κ) κ, F.real (Iio q) ≤ 1 - α ∧ 1 - α ≤ F.real (Iic q) := by
  have hκ := kappa_nonneg_of hF
  set S : Set ℝ := {t | 1 - α ≤ F.real (Iic t)}
  have hκS : κ ∈ S := by
    show 1 - α ≤ F.real (Iic κ)
    have : F.real (Icc (-κ) κ) ≤ F.real (Iic κ) := measureReal_mono Icc_subset_Iic_self
    rw [measureReal_def, hF] at this; simp at this; linarith
  have hlow : ∀ t, t < -κ → F.real (Iic t) = 0 := fun t ht => by
    have hsub : Iic t ⊆ (Icc (-κ) κ)ᶜ := fun u hu hu' => by linarith [hu'.1, (show u ≤ t from hu)]
    have h0 : F (Icc (-κ) κ)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 hF
    rw [measureReal_def, measure_mono_null hsub h0, ENNReal.toReal_zero]
  have hbdd : BddBelow S := ⟨-κ, fun t (ht : 1 - α ≤ F.real (Iic t)) => by
    by_contra h; push_neg at h; rw [hlow t h] at ht; linarith⟩
  set q := sInf S
  have hqκ : q ≤ κ := csInf_le hbdd hκS
  have hqlow : -κ ≤ q := le_csInf ⟨κ, hκS⟩ fun t (ht : 1 - α ≤ F.real (Iic t)) => by
    by_contra h; push_neg at h; rw [hlow t h] at ht; linarith
  refine ⟨q, ⟨hqlow, hqκ⟩, ?_, ?_⟩
  · refine le_of_tendsto (tendsto_Iic_left q) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < q)
    have : t ∉ S := fun h => absurd (csInf_le hbdd h) (not_le.2 ht)
    simp only [S, mem_setOf_eq, not_le] at this
    exact this.le
  · refine ge_of_tendsto (tendsto_Iic_right q) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : q < t)
    obtain ⟨t', ht'S, ht't⟩ := exists_lt_of_csInf_lt ⟨κ, hκS⟩ ht
    exact ht'S.trans (measureReal_mono (Iic_subset_Iic.2 ht't.le))

lemma lowerTrim_eq (hF : F (Icc (-κ) κ) = 1) (hα0 : 0 ≤ α) (hα1 : α < 1) {q : ℝ}
    (hq : IsMaxOn (fun s => ∫ u, psi α s u ∂F) univ q) : lowerTrim F α = ∫ u, psi α q u ∂F := by
  have hbdd : BddAbove (range fun s => ∫ u, psi α s u ∂F) := ⟨_, by rintro _ ⟨s, rfl⟩; exact hq (mem_univ s)⟩
  exact le_antisymm (ciSup_le fun s => hq (mem_univ s)) (le_ciSup hbdd q)

theorem lowertrim_value : Claims.lowertrim_value := by
  intro F _ κ α hF hα0 hα1
  have hκ := kappa_nonneg_of hF
  obtain ⟨q, hqI, hq1, hq2⟩ := exists_quantile hF hα0 hα1
  have hmax := (isMaxOn_iff hF hα0 hα1 q).2 ⟨hq1, hq2⟩
  have hL := lowerTrim_eq hF hα0 hα1 hmax
  refine ⟨?_, ?_, ?_⟩
  · -- the infimum over trimmings: `isLeast_region` for the clamped identity
    have hcl := ae_clampK hF
    have hφ : StronglyMeasurable (clampK κ) := (clampK_measurable κ).stronglyMeasurable
    have hφb : ∀ x, ‖clampK κ x‖ ≤ κ := fun x => by rw [Real.norm_eq_abs]; exact clampK_abs hκ x
    have hin : ∀ x : ℝ, ⟪(1 : ℝ), clampK κ x⟫ = clampK κ x := fun x => by simp
    have e1 : F.real {x | ⟪(1 : ℝ), clampK κ x⟫ < q} = F.real (Iio q) := by
      simp only [hin]
      refine measureReal_congr ?_
      filter_upwards [hcl] with u hu
      simp only [eq_iff_iff]
      show clampK κ u < q ↔ u < q
      rw [hu]
    have e2 : F.real {x | ⟪(1 : ℝ), clampK κ x⟫ ≤ q} = F.real (Iic q) := by
      simp only [hin]
      refine measureReal_congr ?_
      filter_upwards [hcl] with u hu
      simp only [eq_iff_iff]
      show clampK κ u ≤ q ↔ u ≤ q
      rw [hu]
    have hLR := StatFormal.Foundations.TrimmedMean.isLeast_region F hφ hφb hα0 hα1 (1 : ℝ) (e1 ▸ hq1) (e2 ▸ hq2)
    have hval : q - (1 - α)⁻¹ * ∫ x, max (q - ⟪(1 : ℝ), clampK κ x⟫) 0 ∂F = ∫ u, psi α q u ∂F := by
      rw [integral_psi hF]
      unfold Gpos
      congr 2
      refine integral_congr_ae ?_
      filter_upwards [hcl] with u hu
      simp [hu]
    have hin1 : ∀ z : ℝ, ⟪(1 : ℝ), z⟫ = z := fun z => by simp
    have hset : (fun a => ⟪(1 : ℝ), a⟫) '' region (clampK κ) α F = lowerTrimVals F α := by
      ext v
      constructor
      · rintro ⟨z, ⟨g, hg, hgb, hg1, rfl⟩, rfl⟩
        refine ⟨g, hg, hgb, hg1, ?_⟩
        simp only [hin1]
        refine integral_congr_ae ?_
        filter_upwards [hcl] with u hu
        simp only [smul_eq_mul, hu]
      · rintro ⟨g, hg, hgb, hg1, rfl⟩
        refine ⟨∫ x, g x • clampK κ x ∂F, ⟨g, hg, hgb, hg1, rfl⟩, ?_⟩
        simp only [hin1]
        refine integral_congr_ae ?_
        filter_upwards [hcl] with u hu
        simp only [smul_eq_mul, hu]
    rw [hset, hval] at hLR
    rw [hL]
    exact hLR.isGLB
  · rw [hL]
    exact (IsGreatest.isLUB ⟨⟨q, rfl⟩, by rintro _ ⟨s, rfl⟩; exact hmax (mem_univ s)⟩)
  · rw [hL]
    exact (IsGreatest.isLUB ⟨⟨q, hqI, rfl⟩, by rintro _ ⟨s, -, rfl⟩; exact hmax (mem_univ s)⟩)

end Pop

/-! ### The empirical law -/

lemma integral_psi_empirical {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) {α : ℝ} (hα1 : α < 1) (s : ℝ) :
    ∫ u, psi α s u ∂(empirical v) = StatFormal.Foundations.TrimmedMean.trimDual n α v s := by
  have hm : StronglyMeasurable fun u => psi α s u :=
    (measurable_const.sub (measurable_const.mul ((measurable_const.sub measurable_id).max measurable_const))).stronglyMeasurable
  rw [StatFormal.Wave8a.integral_empirical_smul v hm]
  unfold psi StatFormal.Foundations.TrimmedMean.trimDual cap
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hβ0 : (1 - α) ≠ 0 := by intro h; linarith
  have hsum : ∑ i : Fin n, ((n : ℝ)⁻¹ * s - 1 / (n * (1 - α)) * max (s - v i) 0) =
      s - 1 / (n * (1 - α)) * ∑ i, max (s - v i) 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
      ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]; field_simp

lemma lowerTrim_empirical_eq {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    lowerTrim (empirical v) α = sInf ((fun w => ∑ i, w i * v i) '' capped n α) := by
  unfold lowerTrim
  simp only [integral_psi_empirical hn v hα1]
  have hle := StatFormal.Foundations.TrimmedMean.trimDual_le_trimLo hn hα0 hα1 v
  have heq := StatFormal.Foundations.TrimmedMean.trimLo_eq hn hα0 hα1 v
  refine le_antisymm (ciSup_le hle) ?_
  rw [heq]
  exact le_ciSup ⟨_, by rintro _ ⟨c, rfl⟩; exact hle c⟩ _

theorem lowertrim_empirical : Claims.lowertrim_empirical := by
  intro n v α hn hα0 hα1
  have h1 := lowerTrim_empirical_eq hn v hα0 hα1
  refine ⟨h1, ?_⟩
  rw [h1]
  exact (StatFormal.Wave30az.trimmedmean_min n v α hn hα0 hα1).csInf_eq

end StatFormal.Wave30tj
