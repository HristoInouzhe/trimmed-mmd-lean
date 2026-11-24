import StatFormal.Wave31td.RouteRegions
import StatFormal.Archive.Wave8a.RouteGeorep

/-!
# Wave 31td, route: the ten claims (untrusted)

`linear_setting`, `linear_tv`, `linear_regions`, `linear_trimmed_means`, `linear_D`, `linear_witness`, `linear_laws`,
`linear_quantiles`, `linear_Q_Qprime`, `finite_support_not_Q`. `dTrim = Dpop` is the certified `Wave8a.georep_dist` (κ = 1).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31td

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.Wave8a StatFormal.Wave12c StatFormal.Wave30tx

/-! ### Generic facts about a law with constant density `k` on `[lo, hi]` -/

lemma volume_Iio_inter_Icc {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) :
    volume (Iio t ∩ Icc lo hi) = ENNReal.ofReal (min (max t lo) hi - lo) := by
  rcases le_or_gt t lo with h1 | h1
  · have : Iio t ∩ Icc lo hi = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro hy h2; linarith
    rw [this, measure_empty, max_eq_right h1, min_eq_left h, sub_self, ENNReal.ofReal_zero]
  rcases le_or_gt t hi with h2 | h2
  · have : Iio t ∩ Icc lo hi = Ico lo t := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨hy, h3, _⟩; exact ⟨h3, hy⟩
      · rintro ⟨h3, hy⟩; exact ⟨hy, h3, by linarith⟩
    rw [this, Real.volume_Ico, max_eq_left h1.le, min_eq_left h2]
  · have : Iio t ∩ Icc lo hi = Icc lo hi := inter_eq_right.2 fun y hy => lt_of_le_of_lt hy.2 h2
    rw [this, Real.volume_Icc, max_eq_left h1.le, min_eq_right h2.le]

lemma volume_Iic_inter_Icc {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) :
    volume (Iic t ∩ Icc lo hi) = ENNReal.ofReal (min (max t lo) hi - lo) := by
  rw [← volume_Iio_inter_Icc h t]
  exact measure_congr ((Iio_ae_eq_Iic (μ := (volume : Measure ℝ))).symm.inter (Filter.EventuallyEq.refl _ _))

lemma isQuantile_iff_of_law {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {f : 𝒳 → ℝ} {lo hi : ℝ} (hlh : lo < hi)
    (hlaw : ∀ B : Set ℝ, MeasurableSet B → μ (f ⁻¹' B) = ENNReal.ofReal (1 / (hi - lo)) * volume (B ∩ Icc lo hi))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ) :
    IsQuantile μ f p t ↔ t = lo + p * (hi - lo) := by
  have hd : 0 < hi - lo := by linarith
  set F : ℝ := (min (max t lo) hi - lo) / (hi - lo) with hF
  have hm0 : 0 ≤ min (max t lo) hi - lo := by
    have : lo ≤ min (max t lo) hi := le_min (le_max_right _ _) hlh.le
    linarith
  have hF1 : μ.real {x | f x < t} = F := by
    have : {x | f x < t} = f ⁻¹' Iio t := rfl
    rw [this, measureReal_def, hlaw _ measurableSet_Iio, volume_Iio_inter_Icc hlh.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hm0, hF]
    ring
  have hF2 : μ.real {x | f x ≤ t} = F := by
    have : {x | f x ≤ t} = f ⁻¹' Iic t := rfl
    rw [this, measureReal_def, hlaw _ measurableSet_Iic, volume_Iic_inter_Icc hlh.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hm0, hF]
    ring
  unfold IsQuantile
  rw [hF1, hF2]
  constructor
  · rintro ⟨h1, h2⟩
    have hFp : F = p := le_antisymm h1 h2
    rcases le_or_gt t lo with ht | ht
    · rw [hF, max_eq_right ht, min_eq_left hlh.le, sub_self, zero_div] at hFp; linarith
    rcases le_or_gt hi t with ht' | ht'
    · rw [hF, max_eq_left ht.le, min_eq_right ht', div_self hd.ne'] at hFp; linarith
    · rw [hF, max_eq_left ht.le, min_eq_left ht'.le, div_eq_iff hd.ne'] at hFp; linarith
  · rintro rfl
    have h1 : lo < lo + p * (hi - lo) := by nlinarith
    have h2 : lo + p * (hi - lo) < hi := by nlinarith
    have : F = p := by
      rw [hF, max_eq_left h1.le, min_eq_left h2.le]; field_simp; ring
    exact ⟨this.le, this.ge⟩

lemma qdensity_of_law {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {f : 𝒳 → ℝ} {lo hi k t r : ℝ}
    (hlaw : ∀ B : Set ℝ, MeasurableSet B → μ (f ⁻¹' B) = ENNReal.ofReal k * volume (B ∩ Icc lo hi))
    (hwin : Icc (t - r) (t + r) ⊆ Icc lo hi) : QDensity μ f t r k k := by
  refine ⟨fun _ => k, measurable_const, fun s _ => ⟨le_rfl, le_rfl⟩, fun A hA hAW => ?_⟩
  rw [hlaw A hA, setLIntegral_const, inter_eq_left.2 (hAW.trans hwin)]

lemma qdensityLower_of_law {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {f : 𝒳 → ℝ} {lo hi k t r : ℝ}
    (hlaw : ∀ B : Set ℝ, MeasurableSet B → μ (f ⁻¹' B) = ENNReal.ofReal k * volume (B ∩ Icc lo hi))
    (hwin : Icc (t - r) (t + r) ⊆ Icc lo hi) : QDensityLower μ f t r k := by
  obtain ⟨g, hg, hb, hP⟩ := qdensity_of_law hlaw hwin
  exact ⟨g, hg, fun s hs => (hb s hs).1, hP⟩

/-! ### The scaled witness `x ↦ D x` under `unifLin a b` -/

lemma unifLin_preimage_mul {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {D : ℝ} (hD : 0 < D) (B : Set ℝ) :
    unifLin a b ((fun x : XL => D * (x : ℝ)) ⁻¹' B) =
      ENNReal.ofReal (1 / (D * (b - a))) * volume (B ∩ Icc (D * a) (D * b)) := by
  have h1 : (fun x : XL => D * (x : ℝ)) ⁻¹' B = Subtype.val ⁻¹' ((fun y => D * y) ⁻¹' B) := rfl
  have h2 : (fun y => D * y) ⁻¹' B ∩ Icc a b = (fun y => D * y) ⁻¹' (B ∩ Icc (D * a) (D * b)) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hy, h3, h4⟩
      exact ⟨hy, mul_le_mul_of_nonneg_left h3 hD.le, mul_le_mul_of_nonneg_left h4 hD.le⟩
    · rintro ⟨hy, h3, h4⟩
      exact ⟨hy, le_of_mul_le_mul_left h3 hD, le_of_mul_le_mul_left h4 hD⟩
  rw [h1, unifLin_preimage hab ha hb, h2, Real.volume_preimage_mul_left hD.ne', ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith)), abs_of_pos (inv_pos.2 hD)]
  congr 2
  field_simp

lemma witFn_eq (d : ℝ) : witFn d phiLin = fun x : XL => d * (x : ℝ) := by
  funext x; simp [witFn, phiLin, mul_comm]

/-! ### The objects at a level `α` -/

lemma regions_lin {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    region phiLin α Plin = Icc (-1 / 2 + 3 / 4 * (1 - α)) (1 - 3 / 4 * (1 - α)) ∧
    region phiLin α Qlin = Icc (-1 + 3 / 4 * (1 - α)) (1 / 2 - 3 / 4 * (1 - α)) := by
  constructor
  · rw [Plin, region_unifLin (by norm_num) (by norm_num) (by norm_num) hα0 hα1]
    congr 1 <;> ring
  · rw [Qlin, region_unifLin (by norm_num) (by norm_num) (by norm_num) hα0 hα1]
    congr 1 <;> ring

lemma Dpop_lin {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Dpop phiLin Plin Qlin α = max (3 / 2 * (1 / 3 - α)) 0 := by
  obtain ⟨hP, hQ⟩ := regions_lin hα0 hα1
  rw [Dpop, hP, hQ, setDist_Icc (by linarith) (by linarith) (by linarith)]
  congr 1; ring

lemma minNorm_lin {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (d : ℝ) :
    IsMinNorm (region phiLin α Plin - region phiLin α Qlin) d ↔ d = Dpop phiLin Plin Qlin α := by
  obtain ⟨hP, hQ⟩ := regions_lin hα0 hα1
  rw [Dpop_lin hα0 hα1, hP, hQ, isMinNorm_Icc_sub_iff (by linarith) (by linarith) (by linarith)]
  have : -1 / 2 + 3 / 4 * (1 - α) - (1 / 2 - 3 / 4 * (1 - α)) = 3 / 2 * (1 / 3 - α) := by ring
  rw [this]

lemma Plin_isProb : IsProbabilityMeasure Plin := unifLin_isProb (by norm_num) (by norm_num) (by norm_num)
lemma Qlin_isProb : IsProbabilityMeasure Qlin := unifLin_isProb (by norm_num) (by norm_num) (by norm_num)

lemma lawP {D : ℝ} (hD : 0 < D) (B : Set ℝ) :
    Plin ((fun x : XL => D * (x : ℝ)) ⁻¹' B) = ENNReal.ofReal (2 / (3 * D)) * volume (B ∩ Icc (-D / 2) D) := by
  rw [Plin, unifLin_preimage_mul (by norm_num) (by norm_num) (by norm_num) hD]
  have e1 : 1 / (D * (1 - -1 / 2)) = 2 / (3 * D) := by field_simp; ring
  have e2 : D * (-1 / 2) = -D / 2 := by ring
  rw [e1, e2, mul_one]

lemma lawQ {D : ℝ} (hD : 0 < D) (B : Set ℝ) :
    Qlin ((fun x : XL => D * (x : ℝ)) ⁻¹' B) = ENNReal.ofReal (2 / (3 * D)) * volume (B ∩ Icc (-D) (D / 2)) := by
  rw [Qlin, unifLin_preimage_mul (by norm_num) (by norm_num) (by norm_num) hD]
  have e1 : 1 / (D * (1 / 2 - -1)) = 2 / (3 * D) := by field_simp; ring
  have e2 : D * (-1) = -D := by ring
  have e3 : D * (1 / 2) = D / 2 := by ring
  rw [e1, e2, e3]

/-- At `α ∈ (0,⅓)`: `D > 0` and every minimal-norm `dstar` gives the witness `x ↦ D x`. -/
lemma witness_at {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) {dstar : ℝ}
    (hd : IsMinNorm (region phiLin α Plin - region phiLin α Qlin) dstar) :
    Dpop phiLin Plin Qlin α = 3 / 2 * (1 / 3 - α) ∧ 0 < Dpop phiLin Plin Qlin α ∧
      witFn dstar phiLin = fun x : XL => Dpop phiLin Plin Qlin α * (x : ℝ) := by
  have hD := Dpop_lin hα0.le (by linarith : α < 1)
  rw [max_eq_left (by linarith)] at hD
  refine ⟨hD, by rw [hD]; linarith, ?_⟩
  rw [(minNorm_lin hα0.le (by linarith) dstar).1 hd, witFn_eq]

/-! ### The claims -/

theorem linear_setting : Claims.linear_setting := by
  refine ⟨Plin_isProb, Qlin_isProb, fun B _ => ?_, fun B _ => ?_, ?_, fun x => ?_, fun x y => ?_⟩
  · rw [Plin, unifLin_preimage (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [Qlin, unifLin_preimage (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · exact measurable_subtype_coe.stronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_val_le_one x
  · simp [phiLin, mul_comm]

theorem linear_tv : Claims.linear_tv := by
  unfold Claims.linear_tv
  have := Plin_isProb
  have := Qlin_isProb
  apply le_antisymm
  · apply StatFormal.Distances.tvDist_le_of_forall
    intro A _
    obtain ⟨B, hB⟩ : ∃ B : Set ℝ, B = Subtype.val '' A := ⟨_, rfl⟩
    have hPA : Plin A = ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1 / 2) 1) := by
      rw [hB, Plin, unifLin_apply (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hQA : Qlin A = ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1) (1 / 2)) := by
      rw [hB, Qlin, unifLin_apply (by norm_num) (by norm_num) (by norm_num)]; norm_num
    have hv0P : volume (B ∩ Icc (-1 / 2) (1 / 2)) ≤ volume (B ∩ Icc (-1 / 2) 1) :=
      measure_mono (inter_subset_inter_right _ (Icc_subset_Icc le_rfl (by norm_num)))
    have hv0Q : volume (B ∩ Icc (-1 / 2) (1 / 2)) ≤ volume (B ∩ Icc (-1) (1 / 2)) :=
      measure_mono (inter_subset_inter_right _ (Icc_subset_Icc (by norm_num) le_rfl))
    have hv1 : volume (B ∩ Icc (-1 / 2) 1) ≤ volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2) := by
      calc volume (B ∩ Icc (-1 / 2) 1) ≤ volume ((B ∩ Icc (-1 / 2) (1 / 2)) ∪ Ioc (1 / 2) 1) := by
            apply measure_mono
            rintro y ⟨hy, h1, h2⟩
            by_cases h : y ≤ 1 / 2
            · exact Or.inl ⟨hy, h1, h⟩
            · exact Or.inr ⟨lt_of_not_ge h, h2⟩
        _ ≤ volume (B ∩ Icc (-1 / 2) (1 / 2)) + volume (Ioc (1 / 2 : ℝ) 1) := measure_union_le _ _
        _ = volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2) := by rw [Real.volume_Ioc]; norm_num
    have hv2 : volume (B ∩ Icc (-1) (1 / 2)) ≤ volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2) := by
      calc volume (B ∩ Icc (-1) (1 / 2)) ≤ volume ((B ∩ Icc (-1 / 2) (1 / 2)) ∪ Ico (-1) (-1 / 2)) := by
            apply measure_mono
            rintro y ⟨hy, h1, h2⟩
            by_cases h : -1 / 2 ≤ y
            · exact Or.inl ⟨hy, h, h2⟩
            · exact Or.inr ⟨h1, lt_of_not_ge h⟩
        _ ≤ volume (B ∩ Icc (-1 / 2) (1 / 2)) + volume (Ico (-1 : ℝ) (-1 / 2)) := measure_union_le _ _
        _ = volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2) := by rw [Real.volume_Ico]; norm_num
    have hthird : ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 3) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
    have hPQ : Plin A ≤ Qlin A + ENNReal.ofReal (1 / 3) := by
      rw [hPA, hQA, ← hthird]
      calc ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1 / 2) 1)
          ≤ ENNReal.ofReal (2 / 3) * (volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2)) := by gcongr
        _ ≤ ENNReal.ofReal (2 / 3) * (volume (B ∩ Icc (-1) (1 / 2)) + ENNReal.ofReal (1 / 2)) := by gcongr
        _ = _ := by rw [mul_add]
    have hQP : Qlin A ≤ Plin A + ENNReal.ofReal (1 / 3) := by
      rw [hPA, hQA, ← hthird]
      calc ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1) (1 / 2))
          ≤ ENNReal.ofReal (2 / 3) * (volume (B ∩ Icc (-1 / 2) (1 / 2)) + ENNReal.ofReal (1 / 2)) := by gcongr
        _ ≤ ENNReal.ofReal (2 / 3) * (volume (B ∩ Icc (-1 / 2) 1) + ENNReal.ofReal (1 / 2)) := by gcongr
        _ = _ := by rw [mul_add]
    have hr1 : Plin.real A ≤ Qlin.real A + 1 / 3 := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hPQ
      rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num)] at this
    have hr2 : Qlin.real A ≤ Plin.real A + 1 / 3 := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hQP
      rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num)] at this
    rw [abs_sub_le_iff]; constructor <;> linarith
  · have hA : MeasurableSet (Subtype.val ⁻¹' Ioi (1 / 2 : ℝ) : Set XL) := measurable_subtype_coe measurableSet_Ioi
    have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := Plin) (ν := Qlin) hA
    have hP : Plin.real (Subtype.val ⁻¹' Ioi (1 / 2 : ℝ)) = 1 / 3 := by
      rw [Plin, unifLin_real_preimage (by norm_num) (by norm_num) (by norm_num)]
      have : Ioi (1 / 2 : ℝ) ∩ Icc (-1 / 2) 1 = Ioc (1 / 2) 1 := by
        ext y; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
      rw [this, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]; norm_num
    have hQ : Qlin.real (Subtype.val ⁻¹' Ioi (1 / 2 : ℝ)) = 0 := by
      rw [Qlin, unifLin_real_preimage (by norm_num) (by norm_num) (by norm_num)]
      have : Ioi (1 / 2 : ℝ) ∩ Icc (-1) (1 / 2) = ∅ := by
        ext y; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro h1 _ h3; linarith
      rw [this, measureReal_empty, mul_zero]
    rw [hP, hQ, sub_zero, abs_of_pos (by norm_num)] at h
    exact h

theorem linear_regions : Claims.linear_regions := fun _ hα0 hα1 => regions_lin hα0 hα1

theorem linear_trimmed_means : Claims.linear_trimmed_means := by
  intro α hα0 hα1
  have h1α : 0 < 1 - α := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Plin, unifLin_real_le (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]; ring
  · rw [Plin, unifLin_setIntegral_le (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]
    field_simp; ring
  · rw [Plin, unifLin_real_ge (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]; ring
  · rw [Plin, unifLin_setIntegral_ge (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]
    field_simp; ring
  · rw [Qlin, unifLin_real_le (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]; ring
  · rw [Qlin, unifLin_setIntegral_le (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]
    field_simp; ring
  · rw [Qlin, unifLin_real_ge (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]; ring
  · rw [Qlin, unifLin_setIntegral_ge (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)]
    field_simp; ring

theorem linear_D : Claims.linear_D := by
  have := Plin_isProb
  have := Qlin_isProb
  refine ⟨fun α hα0 hα1 => ⟨Dpop_lin hα0 hα1, ?_⟩, fun α hα0 hα1 => ?_⟩
  · rw [StatFormal.Wave8a.georep_dist (Icc (-1 : ℝ) 1) ℝ Plin Qlin phiLin 1 α measurable_subtype_coe.stronglyMeasurable
      (fun x => by rw [Real.norm_eq_abs]; exact abs_val_le_one x) hα0 hα1, Dpop_lin hα0 hα1]
  · have hD := Dpop_lin hα0.le (by linarith : α < 1)
    rw [max_eq_left (by linarith)] at hD
    exact ⟨hD, by rw [hD]; linarith⟩

theorem linear_witness : Claims.linear_witness := by
  intro α hα0 hα1
  refine ⟨(minNorm_lin hα0 hα1 _).2 rfl, fun d hd => (minNorm_lin hα0 hα1 d).1 hd, fun x => ?_⟩
  rw [witFn_eq]

theorem linear_laws : Claims.linear_laws := by
  intro α hα0 hα1 dstar hd
  dsimp only
  obtain ⟨_, hDpos, hw⟩ := witness_at hα0 hα1 hd
  set D := Dpop phiLin Plin Qlin α
  rw [hw]
  have hmeas : Measurable fun x : XL => D * (x : ℝ) := measurable_const.mul measurable_subtype_coe
  refine ⟨fun B _ => lawP hDpos B, fun B _ => lawQ hDpos B, ?_, ?_⟩
  · ext B hB
    rw [Measure.map_apply hmeas hB, lawP hDpos B, cond_Icc_apply (by linarith)]
    congr 2
    field_simp; ring
  · ext B hB
    rw [Measure.map_apply hmeas hB, lawQ hDpos B, cond_Icc_apply (by linarith)]
    congr 2
    field_simp; ring

lemma lawP' {D : ℝ} (hD : 0 < D) (B : Set ℝ) (_ : MeasurableSet B) :
    Plin ((fun x : XL => D * (x : ℝ)) ⁻¹' B) = ENNReal.ofReal (1 / (D - -D / 2)) * volume (B ∩ Icc (-D / 2) D) := by
  rw [lawP hD]; congr 2; field_simp; ring

lemma lawQ' {D : ℝ} (hD : 0 < D) (B : Set ℝ) (_ : MeasurableSet B) :
    Qlin ((fun x : XL => D * (x : ℝ)) ⁻¹' B) = ENNReal.ofReal (1 / (D / 2 - -D)) * volume (B ∩ Icc (-D) (D / 2)) := by
  rw [lawQ hD]; congr 2; field_simp; ring

lemma quantiles_at {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) {D : ℝ} (hD : 0 < D) :
    (∀ t : ℝ, IsQuantile Plin (fun x : XL => D * (x : ℝ)) (1 - α) t ↔ t = D * (-1 / 2 + 3 / 2 * (1 - α))) ∧
    (∀ u : ℝ, IsQuantile Qlin (fun x : XL => D * (x : ℝ)) α u ↔ u = D * (-1 + 3 / 2 * α)) := by
  constructor
  · intro t
    rw [isQuantile_iff_of_law (by linarith) (lawP' hD) (by linarith) (by linarith) t]
    have : -D / 2 + (1 - α) * (D - -D / 2) = D * (-1 / 2 + 3 / 2 * (1 - α)) := by ring
    rw [this]
  · intro u
    rw [isQuantile_iff_of_law (by linarith) (lawQ' hD) hα0 (by linarith) u]
    have : -D + α * (D / 2 - -D) = D * (-1 + 3 / 2 * α) := by ring
    rw [this]

theorem linear_quantiles : Claims.linear_quantiles := by
  intro α hα0 hα1 dstar hd
  dsimp only
  obtain ⟨_, hDpos, hw⟩ := witness_at hα0 hα1 hd
  set D := Dpop phiLin Plin Qlin α
  rw [hw]
  obtain ⟨hqP, hqQ⟩ := quantiles_at hα0 hα1 hDpos
  refine ⟨hqP, hqQ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

theorem linear_Q_Qprime : Claims.linear_Q_Qprime := by
  intro α hα0 hα1 dstar hd
  dsimp only
  obtain ⟨_, hDpos, hw⟩ := witness_at hα0 hα1 hd
  set D := Dpop phiLin Plin Qlin α
  rw [hw]
  refine ⟨by positivity, fun tα uα htα huα => ?_⟩
  obtain ⟨hqP, hqQ⟩ := quantiles_at hα0 hα1 hDpos
  rw [(hqP tα).1 htα, (hqQ uα).1 huα]
  refine ⟨3 / 2 * D * α, by positivity, qdensity_of_law (fun B _ => lawP hDpos B) ?_,
    qdensityLower_of_law (fun B _ => lawQ hDpos B) ?_⟩
  · exact Icc_subset_Icc (by nlinarith) (by nlinarith)
  · exact Icc_subset_Icc (by nlinarith) (by nlinarith)

theorem finite_support_not_Q : Claims.finite_support_not_Q := by
  intro 𝒳 _ P S hS hPS f t r c C hr hc
  have hL : ¬ QDensityLower P f t r c := by
    rintro ⟨g, hg, hb, hP⟩
    set A : Set ℝ := Icc (t - r) (t + r) \ f '' S with hAdef
    have hfin : (f '' S).Finite := hS.image f
    have hAm : MeasurableSet A := measurableSet_Icc.diff hfin.measurableSet
    have hAsub : A ⊆ Icc (t - r) (t + r) := sdiff_subset
    have h0 : P (f ⁻¹' A) = 0 := measure_mono_null (fun x hx hxS => hx.2 ⟨x, hxS, rfl⟩) hPS
    have hvol : volume A = ENNReal.ofReal (2 * r) := by
      rw [hAdef, measure_sdiff_null (hfin.measure_zero _), Real.volume_Icc]; ring_nf
    have hlow : ENNReal.ofReal c * volume A ≤ ∫⁻ s in A, ENNReal.ofReal (g s) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono hg.ennreal_ofReal fun s hs => ENNReal.ofReal_le_ofReal (hb s (hAsub hs))
    rw [← hP A hAm hAsub, h0, hvol] at hlow
    have hpos : 0 < ENNReal.ofReal c * ENNReal.ofReal (2 * r) :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc).ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
    exact absurd hlow (not_le.2 hpos)
  refine ⟨fun hQ => hL ?_, hL⟩
  obtain ⟨g, hg, hb, hP⟩ := hQ
  exact ⟨g, hg, fun s hs => (hb s hs).1, hP⟩

end StatFormal.Wave31td
