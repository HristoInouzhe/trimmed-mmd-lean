import StatFormal.Archive.Wave18b.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs

/-!
# Route: TM `lem:continuity` (untrusted)

* For `0 ≤ α ≤ α' < 1` the regions are nested, `𝒞_α ⊆ 𝒞_{α'}`, and every `x' = E[g'φ] ∈ 𝒞_{α'}` is within
  `2κ(α' − α)/(1 − α)` of `x = E[gφ] ∈ 𝒞_α`, `g = (1−θ)g' + θ`, `θ = (β' − β)/(β' − 1)`: indeed
  `|g' − 1| ≤ 2(1 − 1/β')g' + 1 − g'` pointwise (as `0 ≤ g' ≤ β'`), so `E|g' − 1| ≤ 2(1 − 1/β')`.
* `|setDist(A',B') − setDist(A,B)| ≤ d_H(A,A') + d_H(B,B')` (certified `abs_setDist_sub_le`) gives
  `|D_α − D_{α'}| ≤ 4κ|α − α'|/(1 − max) ≤ (4κ/η)|α − α'|`, hence the paper's `4κ/η²` (`η ≤ 1`) and continuity.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric Filter Topology

namespace StatFormal.Wave18b

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma region_mono (P : Measure 𝒳) (φ : 𝒳 → H) {α α' : ℝ} (hα : α ≤ α') (hα' : α' < 1) :
    region φ α P ⊆ region φ α' P := by
  rintro _ ⟨g, hg, hgb, hint, rfl⟩
  refine ⟨g, hg, fun x => ⟨(hgb x).1, (hgb x).2.trans ?_⟩, hint, rfl⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma near_point [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {α α' : ℝ} (h0 : 0 ≤ α) (hlt : α < α')
    (hα' : α' < 1) {x' : H} (hx' : x' ∈ region φ α' P) :
    ∃ x ∈ region φ α P, dist x' x ≤ 2 * κ * ((α' - α) / (1 - α)) := by
  obtain ⟨g', hg', hgb', hint', rfl⟩ := hx'
  set β := 1 / (1 - α) with hβ
  set β' := 1 / (1 - α') with hβ'
  have h1α : 0 < 1 - α := by linarith
  have h1α' : 0 < 1 - α' := by linarith
  have hβ1 : 1 ≤ β := by rw [hβ, le_div_iff₀ h1α]; linarith
  have hββ' : β < β' := by
    rw [hβ, hβ']; exact one_div_lt_one_div_of_lt h1α' (by linarith)
  have hβ'1 : 0 < β' - 1 := by linarith
  set θ := (β' - β) / (β' - 1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hβ'1.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hβ'1]; linarith
  set g : 𝒳 → ℝ := fun x => (1 - θ) * g' x + θ with hgdef
  have hgm : Measurable g := (measurable_const.mul hg').add measurable_const
  have hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α) := by
    intro x
    refine ⟨by have := (hgb' x).1; simp only [hgdef]; nlinarith, ?_⟩
    have hle : g' x ≤ β' := (hgb' x).2
    have : (1 - θ) * β' + θ = β := by
      rw [hθ]; field_simp; ring
    simp only [hgdef]
    calc (1 - θ) * g' x + θ ≤ (1 - θ) * β' + θ := by nlinarith
      _ = β := this
      _ = 1 / (1 - α) := rfl
  have hint1 : Integrable g' P := Integrable.of_bound hg'.aestronglyMeasurable β'
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgb' x).1]; exact (hgb' x).2)
  have hintg : ∫ x, g x ∂P = 1 := by
    simp only [hgdef]
    rw [integral_add (hint1.const_mul _) (integrable_const _), integral_const_mul, hint',
      integral_const, probReal_univ, smul_eq_mul]
    ring
  refine ⟨∫ x, g x • φ x ∂P, ⟨g, hgm, hgb, hintg, rfl⟩, ?_⟩
  have hI' := integrable_smul_of_bound P hφ hκ hg' hgb'
  have hI := integrable_smul_of_bound P hφ hκ hgm hgb
  rw [dist_eq_norm, ← integral_sub hI' hI]
  have hdiff : ∀ x, g' x • φ x - g x • φ x = (θ * (g' x - 1)) • φ x := by
    intro x; rw [← sub_smul]; congr 1; simp only [hgdef]; ring
  simp_rw [hdiff]
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ : Nonempty 𝒳 := by
      by_contra h; rw [not_nonempty_iff] at h
      have := measure_univ (μ := P); rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    exact (norm_nonneg _).trans (hκ x)
  have hpt : ∀ x, |g' x - 1| ≤ 2 * (1 - 1 / β') * g' x + 1 - g' x := by
    intro x
    have h0' := (hgb' x).1
    have hle := (hgb' x).2
    have hβ'0 : 0 < β' := by linarith
    rcases le_total (g' x) 1 with h | h
    · rw [abs_of_nonpos (by linarith)]
      have : 0 ≤ (1 - 1 / β') * g' x := mul_nonneg (by rw [sub_nonneg, div_le_one hβ'0]; linarith) h0'
      linarith
    · rw [abs_of_nonneg (by linarith)]
      have : g' x / β' ≤ 1 := by rw [div_le_one hβ'0]; exact hle
      have h2 : (1 - 1 / β') * g' x = g' x - g' x / β' := by ring
      nlinarith
  calc ‖∫ x, (θ * (g' x - 1)) • φ x ∂P‖
      ≤ ∫ x, θ * κ * (2 * (1 - 1 / β') * g' x + 1 - g' x) ∂P := by
        refine norm_integral_le_of_norm_le ?_ (ae_of_all _ fun x => ?_)
        · exact ((hint1.const_mul (2 * (1 - 1 / β'))).add (integrable_const 1) |>.sub hint1).const_mul _
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ0]
          have := hpt x
          calc θ * |g' x - 1| * ‖φ x‖ ≤ θ * |g' x - 1| * κ :=
                mul_le_mul_of_nonneg_left (hκ x) (mul_nonneg hθ0 (abs_nonneg _))
            _ ≤ θ * (2 * (1 - 1 / β') * g' x + 1 - g' x) * κ := by
                apply mul_le_mul_of_nonneg_right _ hκ0
                exact mul_le_mul_of_nonneg_left this hθ0
            _ = θ * κ * (2 * (1 - 1 / β') * g' x + 1 - g' x) := by ring
    _ = θ * κ * (2 * (1 - 1 / β')) := by
        have hA : Integrable (fun x => 2 * (1 - 1 / β') * g' x + 1) P :=
          (hint1.const_mul _).add (integrable_const 1)
        have hB : Integrable (fun x => 2 * (1 - 1 / β') * g' x) P := hint1.const_mul _
        rw [integral_const_mul, integral_sub hA hint1, integral_add hB (integrable_const 1),
          integral_const_mul, hint', integral_const, probReal_univ, smul_eq_mul]
        ring
    _ = 2 * κ * ((α' - α) / (1 - α)) := by
        have hα'0 : α' ≠ 0 := by linarith
        have h1 : (1 - α) ≠ 0 := h1α.ne'
        have h2 : (1 - α') ≠ 0 := h1α'.ne'
        rw [hθ, hβ, hβ']
        field_simp
        have hinv : α' * α'⁻¹ = 1 := mul_inv_cancel₀ hα'0
        linear_combination (-(α * κ) + α' * κ) * hinv

lemma hausdorff_region_le [CompleteSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H}
    {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hκ0 : 0 ≤ κ) {α α' : ℝ} (h0 : 0 ≤ α)
    (hle : α ≤ α') (hα' : α' < 1) :
    hausdorffDist (region φ α P) (region φ α' P) ≤ 2 * κ * ((α' - α) / (1 - α)) := by
  have hr : 0 ≤ 2 * κ * ((α' - α) / (1 - α)) :=
    mul_nonneg (by linarith) (div_nonneg (by linarith) (by linarith))
  refine hausdorffDist_le_of_mem_dist hr (fun x hx => ⟨x, region_mono P φ hle hα' hx, by simpa using hr⟩)
    (fun x' hx' => ?_)
  rcases hle.lt_or_eq with hlt | heq
  · exact near_point P hφ hκ h0 hlt hα' hx'
  · subst heq; exact ⟨x', hx', by simpa using hr⟩

lemma kappa_nonneg {P : Measure 𝒳} [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : 0 ≤ κ := by
  obtain ⟨x⟩ : Nonempty 𝒳 := by
    by_contra h; rw [not_nonempty_iff] at h
    have := measure_univ (μ := P); rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  exact (norm_nonneg _).trans (hκ x)

lemma Dpop_lip_ordered [CompleteSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {α α' : ℝ} (h0 : 0 ≤ α)
    (hle : α ≤ α') (hα' : α' < 1) :
    |Dpop φ P Q α' - Dpop φ P Q α| ≤ 4 * κ * ((α' - α) / (1 - α)) := by
  have hκ0 := kappa_nonneg (P := P) hκ
  have h0' : 0 ≤ α' := h0.trans hle
  have hα1 : α < 1 := hle.trans_lt hα'
  have h := abs_setDist_sub_le (A := region φ α P) (B := region φ α Q) (A' := region φ α' P)
    (B' := region φ α' Q) (region_nonempty P h0 hα1) (region_nonempty Q h0 hα1)
    (region_nonempty P h0' hα') (region_nonempty Q h0' hα') (region_isBounded P hκ)
    (region_isBounded Q hκ) (region_isBounded P hκ) (region_isBounded Q hκ)
  have h1 := hausdorff_region_le P hφ hκ hκ0 h0 hle hα'
  have h2 := hausdorff_region_le Q hφ hκ hκ0 h0 hle hα'
  unfold Dpop
  linarith

theorem continuity_lip_sharp : Claims.continuity_lip_sharp := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ η α α' hφ hκ hη0 hη1 hα hα'
  have hκ0 := kappa_nonneg (P := P) hκ
  rcases le_total α α' with hle | hle
  · have h := Dpop_lip_ordered P Q hφ hκ hα.1 hle (by linarith [hα'.2])
    rw [abs_sub_comm, abs_of_nonpos (by linarith : α - α' ≤ 0)]
    refine h.trans ?_
    have h1 : η ≤ 1 - α := by linarith [hα.2]
    rw [show 4 * κ * ((α' - α) / (1 - α)) = 4 * κ * (α' - α) / (1 - α) by ring,
      show 4 * κ / η * -(α - α') = 4 * κ * (α' - α) / η by ring]
    exact div_le_div_of_nonneg_left (by nlinarith) hη0 h1
  · have h := Dpop_lip_ordered P Q hφ hκ hα'.1 hle (by linarith [hα.2])
    rw [abs_of_nonneg (by linarith : 0 ≤ α - α')]
    refine h.trans ?_
    have h1 : η ≤ 1 - α' := by linarith [hα'.2]
    rw [show 4 * κ * ((α - α') / (1 - α')) = 4 * κ * (α - α') / (1 - α') by ring,
      show 4 * κ / η * (α - α') = 4 * κ * (α - α') / η by ring]
    exact div_le_div_of_nonneg_left (by nlinarith) hη0 h1

theorem continuity_lip : Claims.continuity_lip := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ η α α' hφ hκ hη0 hη1 hα hα'
  have hκ0 := kappa_nonneg (P := P) hκ
  refine (continuity_lip_sharp 𝒳 H P Q φ κ η α α' hφ hκ hη0 hη1 hα hα').trans ?_
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  nlinarith

theorem continuity_cont : Claims.continuity_cont := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ hφ hκ
  have hκ0 := kappa_nonneg (P := P) hκ
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set η := (1 - x) / 2 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith [hx.2]
  have hη1 : η < 1 := by rw [hηdef]; linarith [hx.1]
  refine ⟨min η (ε * η / (4 * κ + 1)), lt_min hη0 (by positivity), fun y hy hyx => ?_⟩
  rw [Real.dist_eq] at hyx ⊢
  have hy1 : |y - x| < η := hyx.trans_le (min_le_left _ _)
  have hy2 : |y - x| < ε * η / (4 * κ + 1) := hyx.trans_le (min_le_right _ _)
  have hyI : y ∈ Icc 0 (1 - η) := ⟨hy.1, by have := (abs_lt.1 hy1).2; rw [hηdef] at this ⊢; linarith⟩
  have hxI : x ∈ Icc 0 (1 - η) := ⟨hx.1, by rw [hηdef]; linarith [hx.2]⟩
  have h := continuity_lip_sharp 𝒳 H P Q φ κ η y x hφ hκ hη0 hη1 hyI hxI
  calc |Dpop φ P Q y - Dpop φ P Q x| ≤ 4 * κ / η * |y - x| := h
    _ ≤ (4 * κ + 1) / η * |y - x| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact div_le_div_of_nonneg_right (by linarith) hη0.le
    _ < (4 * κ + 1) / η * (ε * η / (4 * κ + 1)) := by
        apply mul_lt_mul_of_pos_left hy2 (by positivity)
    _ = ε := by field_simp

end StatFormal.Wave18b
