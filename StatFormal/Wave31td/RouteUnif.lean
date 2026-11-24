import StatFormal.Wave31td.Statements

/-!
# Wave 31td, route: the uniform law on `[a,b] ⊆ [−1,1]` seen on `𝒳 = [−1,1]` (untrusted)

Masses, integrals and the regions of the linear kernel for `unifLin a b`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31td

open StatFormal.TrimmedMMD.Concentration

/-- `𝒳 = [−1,1]`. -/
abbrev XL : Type := ↥(Icc (-1 : ℝ) 1)

lemma embX : MeasurableEmbedding (Subtype.val : XL → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

/-- `volume[|Icc a b] B = (b−a)⁻¹ λ(B ∩ [a,b])`. -/
lemma cond_Icc_apply {a b : ℝ} (hab : a < b) (B : Set ℝ) :
    cond volume (Icc a b) B = ENNReal.ofReal (1 / (b - a)) * volume (B ∩ Icc a b) := by
  rw [cond_apply measurableSet_Icc, Real.volume_Icc, inter_comm]
  congr 1
  rw [one_div, ENNReal.ofReal_inv_of_pos (by linarith)]

lemma unifLin_apply {a b : ℝ} (hab : a < b) (_ha : -1 ≤ a) (_hb : b ≤ 1) (A : Set XL) :
    unifLin a b A = ENNReal.ofReal (1 / (b - a)) * volume (Subtype.val '' A ∩ Icc a b) := by
  rw [unifLin, embX.comap_apply, cond_Icc_apply hab]

lemma unifLin_preimage {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) (B : Set ℝ) :
    unifLin a b (Subtype.val ⁻¹' B) = ENNReal.ofReal (1 / (b - a)) * volume (B ∩ Icc a b) := by
  rw [unifLin_apply hab ha hb, Subtype.image_preimage_coe]
  congr 2
  ext y
  simp only [mem_inter_iff, mem_Icc]
  constructor
  · rintro ⟨⟨_, hy⟩, h1, h2⟩; exact ⟨hy, h1, h2⟩
  · rintro ⟨hy, h1, h2⟩; exact ⟨⟨⟨by linarith, by linarith⟩, hy⟩, h1, h2⟩

lemma unifLin_isProb {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) :
    IsProbabilityMeasure (unifLin a b) := by
  constructor
  have : (univ : Set XL) = Subtype.val ⁻¹' (univ : Set ℝ) := rfl
  rw [this, unifLin_preimage hab ha hb, univ_inter, Real.volume_Icc, ← ENNReal.ofReal_mul (by
    have : 0 < b - a := by linarith
    positivity)]
  rw [one_div, inv_mul_cancel₀ (by linarith), ENNReal.ofReal_one]

lemma unifLin_real_preimage {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) (B : Set ℝ) :
    (unifLin a b).real (Subtype.val ⁻¹' B) = (b - a)⁻¹ * volume.real (B ∩ Icc a b) := by
  rw [measureReal_def, unifLin_preimage hab ha hb, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    have : 0 < b - a := by linarith
    positivity), one_div, measureReal_def]

/-- Integrals against `unifLin a b` of functions of `x : ℝ`. -/
lemma integral_unifLin {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) (F : ℝ → ℝ) :
    ∫ x, F (x : ℝ) ∂(unifLin a b) = (b - a)⁻¹ * ∫ y in Icc a b, F y := by
  have h1 : ∫ x, F (x : ℝ) ∂(unifLin a b) = ∫ y, F y ∂(cond volume (Icc a b)).restrict (Icc (-1 : ℝ) 1) := by
    rw [← map_comap_subtype_coe measurableSet_Icc, embX.integral_map]
    rfl
  have h2 : (cond volume (Icc a b)).restrict (Icc (-1 : ℝ) 1) = cond volume (Icc a b) := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    rw [cond_Icc_apply hab]
    have : {x : ℝ | ¬ x ∈ Icc (-1 : ℝ) 1} ∩ Icc a b = ∅ := by
      ext y
      refine ⟨fun ⟨h, h1⟩ => (h ⟨by linarith [h1.1], by linarith [h1.2]⟩).elim, fun h => h.elim⟩
    rw [this, measure_empty, mul_zero]
  rw [h1, h2, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]

lemma integrable_unifLin {a b : ℝ} (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {g : XL → ℝ}
    (hg : Measurable g) (M : ℝ) (hM : ∀ x, |g x| ≤ M) : Integrable g (unifLin a b) := by
  have := unifLin_isProb hab ha hb
  exact Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hM x)

lemma abs_val_le_one (x : XL) : |(x : ℝ)| ≤ 1 := abs_le.mpr ⟨x.2.1, x.2.2⟩

/-! ### One-dimensional integrals -/

lemma setIntegral_Icc_indicator_Iic {a b t : ℝ} (_hat : a ≤ t) (htb : t ≤ b) (F : ℝ → ℝ) :
    ∫ y in Icc a b, (Iic t).indicator F y = ∫ y in Icc a t, F y := by
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith⟩

lemma setIntegral_Icc_indicator_Ici {a b s : ℝ} (has : a ≤ s) (_hsb : s ≤ b) (F : ℝ → ℝ) :
    ∫ y in Icc a b, (Ici s).indicator F y = ∫ y in Icc s b, F y := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  congr 2
  ext y; simp only [mem_inter_iff, mem_Ici, mem_Icc]
  constructor
  · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩

lemma setIntegral_Icc_const {a b : ℝ} (hab : a ≤ b) (c : ℝ) : ∫ _ in Icc a b, c = c * (b - a) := by
  rw [setIntegral_const, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
    mul_comm]

lemma setIntegral_Icc_id {a b : ℝ} (hab : a ≤ b) : ∫ y in Icc a b, y = (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_id]

/-! ### Masses and means of the lower and upper parts -/

variable {a b : ℝ}

lemma unifLin_real_le (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (unifLin a b).real {x : XL | (x : ℝ) ≤ c} = (c - a) / (b - a) := by
  have : {x : XL | (x : ℝ) ≤ c} = Subtype.val ⁻¹' Iic c := rfl
  rw [this, unifLin_real_preimage hab ha hb]
  have h2 : Iic c ∩ Icc a b = Icc a c := by
    ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith⟩
  rw [h2, Real.volume_real_Icc, max_eq_left (by linarith)]
  field_simp

lemma unifLin_real_ge (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (unifLin a b).real {x : XL | c ≤ (x : ℝ)} = (b - c) / (b - a) := by
  have : {x : XL | c ≤ (x : ℝ)} = Subtype.val ⁻¹' Ici c := rfl
  rw [this, unifLin_real_preimage hab ha hb]
  have h2 : Ici c ∩ Icc a b = Icc c b := by
    ext y; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  rw [h2, Real.volume_real_Icc, max_eq_left (by linarith)]
  field_simp

lemma unifLin_setIntegral_le (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x in {x : XL | (x : ℝ) ≤ c}, phiLin x ∂(unifLin a b) = (b - a)⁻¹ * ((c ^ 2 - a ^ 2) / 2) := by
  have hm : MeasurableSet {x : XL | (x : ℝ) ≤ c} := measurableSet_le measurable_subtype_coe measurable_const
  rw [← integral_indicator hm]
  have : ({x : XL | (x : ℝ) ≤ c}.indicator phiLin) = fun x : XL => (Iic c).indicator (fun y => y) (x : ℝ) := by
    funext x; simp only [indicator, mem_ofPred_eq, mem_Iic, phiLin]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Iic hac hcb, setIntegral_Icc_id hac]

lemma unifLin_setIntegral_ge (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x in {x : XL | c ≤ (x : ℝ)}, phiLin x ∂(unifLin a b) = (b - a)⁻¹ * ((b ^ 2 - c ^ 2) / 2) := by
  have hm : MeasurableSet {x : XL | c ≤ (x : ℝ)} := measurableSet_le measurable_const measurable_subtype_coe
  rw [← integral_indicator hm]
  have : ({x : XL | c ≤ (x : ℝ)}.indicator phiLin) = fun x : XL => (Ici c).indicator (fun y => y) (x : ℝ) := by
    funext x; simp only [indicator, mem_ofPred_eq, mem_Ici, phiLin]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Ici hac hcb, setIntegral_Icc_id hcb]

end StatFormal.Wave31td
