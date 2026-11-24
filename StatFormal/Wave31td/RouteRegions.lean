import StatFormal.Wave31td.RouteUnif

/-!
# Wave 31td, route: the regions of the linear kernel, their distance and the minimal-norm element (untrusted)

`region_unifLin`: for `unifLin a b` the region `𝒞_α` is the interval between the lower and upper one-sided trimmed means
(bathtub inequality, pointwise: `(g − g⋆)(x − t) ≥ 0` for the bang-bang density `g⋆ = β 1{x ≤ t}`; convex combination of the two
bang-bang densities for the converse). `setDist_Icc`, `isMinNorm_Icc_sub_iff`: distance and minimal-norm element of two intervals.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31td

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection

variable {a b : ℝ}

lemma integral_ind_le (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {t c : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    ∫ x : XL, (if (x : ℝ) ≤ t then c else 0) ∂(unifLin a b) = (b - a)⁻¹ * (c * (t - a)) := by
  have : (fun x : XL => if (x : ℝ) ≤ t then c else 0) = fun x : XL => (Iic t).indicator (fun _ => c) (x : ℝ) := by
    funext x; simp only [indicator, mem_Iic]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Iic hat htb, setIntegral_Icc_const hat]

lemma integral_ind_le_mul (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {t c : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    ∫ x : XL, (if (x : ℝ) ≤ t then c else 0) * (x : ℝ) ∂(unifLin a b) = (b - a)⁻¹ * (c * ((t ^ 2 - a ^ 2) / 2)) := by
  have : (fun x : XL => (if (x : ℝ) ≤ t then c else 0) * (x : ℝ)) =
      fun x : XL => (Iic t).indicator (fun y => c * y) (x : ℝ) := by
    funext x; by_cases h : (x : ℝ) ≤ t <;> simp [indicator, h]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Iic hat htb, integral_const_mul,
    setIntegral_Icc_id hat]

lemma integral_ind_ge (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {s c : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    ∫ x : XL, (if s ≤ (x : ℝ) then c else 0) ∂(unifLin a b) = (b - a)⁻¹ * (c * (b - s)) := by
  have : (fun x : XL => if s ≤ (x : ℝ) then c else 0) = fun x : XL => (Ici s).indicator (fun _ => c) (x : ℝ) := by
    funext x; simp only [indicator, mem_Ici]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Ici has hsb, setIntegral_Icc_const hsb]

lemma integral_ind_ge_mul (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {s c : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    ∫ x : XL, (if s ≤ (x : ℝ) then c else 0) * (x : ℝ) ∂(unifLin a b) = (b - a)⁻¹ * (c * ((b ^ 2 - s ^ 2) / 2)) := by
  have : (fun x : XL => (if s ≤ (x : ℝ) then c else 0) * (x : ℝ)) =
      fun x : XL => (Ici s).indicator (fun y => c * y) (x : ℝ) := by
    funext x; by_cases h : s ≤ (x : ℝ) <;> simp [indicator, h]
  rw [this, integral_unifLin hab ha hb, setIntegral_Icc_indicator_Ici has hsb, integral_const_mul,
    setIntegral_Icc_id hsb]

/-- The region of the linear kernel for the uniform law on `[a,b]`: the interval between the lower and the upper one-sided
`α`-trimmed means, `a + (b−a)(1−α)/2` and `b − (b−a)(1−α)/2`. -/
lemma region_unifLin (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    region phiLin α (unifLin a b) = Icc (a + (b - a) * (1 - α) / 2) (b - (b - a) * (1 - α) / 2) := by
  have h1α : 0 < 1 - α := by linarith
  have hba : 0 < b - a := by linarith
  set β : ℝ := 1 / (1 - α) with hβ
  have hβpos : 0 < β := by positivity
  set L : ℝ := (b - a) * (1 - α) with hL
  have hβL : β * L = b - a := by rw [hβ, hL]; field_simp
  have hL0 : 0 ≤ L := by positivity
  have hLba : L ≤ b - a := by rw [hL]; nlinarith
  set t : ℝ := a + L with ht
  set s : ℝ := b - L with hs
  have hat : a ≤ t := by linarith
  have htb : t ≤ b := by linarith
  have has : a ≤ s := by linarith
  have hsb : s ≤ b := by linarith
  set gL : XL → ℝ := fun x => if (x : ℝ) ≤ t then β else 0 with hgL
  set gU : XL → ℝ := fun x => if s ≤ (x : ℝ) then β else 0 with hgU
  have hgLm : Measurable gL :=
    Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const) measurable_const measurable_const
  have hgUm : Measurable gU :=
    Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe) measurable_const measurable_const
  have hgLb : ∀ x, 0 ≤ gL x ∧ gL x ≤ β := fun x => by
    simp only [hgL]; split_ifs <;> constructor <;> linarith
  have hgUb : ∀ x, 0 ≤ gU x ∧ gU x ≤ β := fun x => by
    simp only [hgU]; split_ifs <;> constructor <;> linarith
  -- integrability of bounded measurable functions (and their products with `x`)
  have hint : ∀ g : XL → ℝ, Measurable g → (∀ x, 0 ≤ g x ∧ g x ≤ β) →
      Integrable g (unifLin a b) ∧ Integrable (fun x => g x * (x : ℝ)) (unifLin a b) := by
    intro g hg hgb
    refine ⟨integrable_unifLin hab ha hb hg β fun x => ?_,
      integrable_unifLin hab ha hb (hg.mul measurable_subtype_coe) β fun x => ?_⟩
    · rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
    · rw [abs_mul, abs_of_nonneg (hgb x).1]
      calc g x * |(x : ℝ)| ≤ β * 1 := mul_le_mul (hgb x).2 (abs_val_le_one x) (abs_nonneg _) hβpos.le
        _ = β := mul_one β
  have hgL1 : ∫ x, gL x ∂(unifLin a b) = 1 := by
    rw [hgL, integral_ind_le hab ha hb hat htb, show t - a = L by rw [ht]; ring, hβL, inv_mul_cancel₀ hba.ne']
  have hgU1 : ∫ x, gU x ∂(unifLin a b) = 1 := by
    rw [hgU, integral_ind_ge hab ha hb has hsb, show b - s = L by rw [hs]; ring, hβL, inv_mul_cancel₀ hba.ne']
  have hgLx : ∫ x, gL x * (x : ℝ) ∂(unifLin a b) = a + (b - a) * (1 - α) / 2 := by
    rw [hgL, integral_ind_le_mul hab ha hb hat htb, ht]
    have : β * (((a + L) ^ 2 - a ^ 2) / 2) = (β * L) * (2 * a + L) / 2 := by ring
    rw [this, hβL, hL]; field_simp
  have hgUx : ∫ x, gU x * (x : ℝ) ∂(unifLin a b) = b - (b - a) * (1 - α) / 2 := by
    rw [hgU, integral_ind_ge_mul hab ha hb has hsb, hs]
    have : β * ((b ^ 2 - (b - L) ^ 2) / 2) = (β * L) * (2 * b - L) / 2 := by ring
    rw [this, hβL, hL]; field_simp
  ext z
  constructor
  · rintro ⟨g, hg, hgb, hg1, rfl⟩
    have hgb' : ∀ x, 0 ≤ g x ∧ g x ≤ β := hgb
    obtain ⟨Ig, Igx⟩ := hint g hg hgb'
    obtain ⟨IgL, IgLx⟩ := hint gL hgLm hgLb
    obtain ⟨IgU, IgUx⟩ := hint gU hgUm hgUb
    have hsm : (∫ x, g x • phiLin x ∂(unifLin a b)) = ∫ x, g x * (x : ℝ) ∂(unifLin a b) := by
      simp only [phiLin, smul_eq_mul]
    rw [hsm]
    constructor
    · -- bathtub, lower end: `(g − gL)(x − t) ≥ 0`
      have hmono : ∫ x, (gL x * (x : ℝ) - t * gL x) ∂(unifLin a b) ≤ ∫ x, (g x * (x : ℝ) - t * g x) ∂(unifLin a b) := by
        apply integral_mono (IgLx.sub (IgL.const_mul t)) (Igx.sub (Ig.const_mul t))
        intro x
        simp only [Pi.sub_apply]
        have hx := hgb' x
        by_cases h : (x : ℝ) ≤ t
        · simp only [hgL, h, ite_true]
          nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (sub_nonneg.2 h)]
        · simp only [hgL, h, ite_false, zero_mul, mul_zero, sub_zero]
          push Not at h
          nlinarith [mul_nonneg hx.1 (sub_nonneg.2 h.le)]
      rw [integral_sub IgLx (IgL.const_mul t), integral_sub Igx (Ig.const_mul t), integral_const_mul,
        integral_const_mul, hgLx, hgL1, hg1] at hmono
      linarith
    · -- bathtub, upper end: `(g − gU)(x − s) ≤ 0`
      have hmono : ∫ x, (g x * (x : ℝ) - s * g x) ∂(unifLin a b) ≤ ∫ x, (gU x * (x : ℝ) - s * gU x) ∂(unifLin a b) := by
        apply integral_mono (Igx.sub (Ig.const_mul s)) (IgUx.sub (IgU.const_mul s))
        intro x
        simp only [Pi.sub_apply]
        have hx := hgb' x
        by_cases h : s ≤ (x : ℝ)
        · simp only [hgU, h, ite_true]
          nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (sub_nonneg.2 h)]
        · simp only [hgU, h, ite_false, zero_mul, mul_zero, sub_zero]
          push Not at h
          nlinarith [mul_nonneg hx.1 (sub_nonneg.2 h.le)]
      rw [integral_sub IgUx (IgU.const_mul s), integral_sub Igx (Ig.const_mul s), integral_const_mul,
        integral_const_mul, hgUx, hgU1, hg1] at hmono
      linarith
  · rintro ⟨hz1, hz2⟩
    set lo := a + (b - a) * (1 - α) / 2 with hlo
    set hi := b - (b - a) * (1 - α) / 2 with hhi
    obtain ⟨θ, hθ0, hθ1, hθz⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = (1 - θ) * lo + θ * hi := by
      by_cases hd : hi - lo = 0
      · exact ⟨0, le_rfl, zero_le_one, by linarith⟩
      · have hpos : 0 < hi - lo := lt_of_le_of_ne (by linarith) (Ne.symm hd)
        refine ⟨(z - lo) / (hi - lo), div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith), ?_⟩
        field_simp; ring
    obtain ⟨IgL, IgLx⟩ := hint gL hgLm hgLb
    obtain ⟨IgU, IgUx⟩ := hint gU hgUm hgUb
    refine ⟨fun x => (1 - θ) * gL x + θ * gU x, (hgLm.const_mul _).add (hgUm.const_mul _), fun x => ?_, ?_, ?_⟩
    · have h1 := hgLb x; have h2 := hgUb x
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) h1.1, mul_nonneg hθ0 h2.1]
      · have : (1 - θ) * gL x + θ * gU x ≤ (1 - θ) * β + θ * β := by
          nlinarith [mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.2 hθ1), mul_le_mul_of_nonneg_left h2.2 hθ0]
        linarith
    · rw [integral_add (IgL.const_mul _) (IgU.const_mul _), integral_const_mul, integral_const_mul, hgL1, hgU1]; ring
    · have : (fun x : XL => ((1 - θ) * gL x + θ * gU x) • phiLin x) =
          fun x => (1 - θ) * (gL x * (x : ℝ)) + θ * (gU x * (x : ℝ)) := by
        funext x; simp only [phiLin, smul_eq_mul]; ring
      rw [this, integral_add (IgLx.const_mul _) (IgUx.const_mul _), integral_const_mul, integral_const_mul, hgLx, hgUx]
      exact hθz

/-- Distance between two intervals `[l1,h1]`, `[l2,h2]` with `l2 ≤ h1`: `max(l1 − h2, 0)`. -/
lemma setDist_Icc {l1 h1 l2 h2 : ℝ} (hl1 : l1 ≤ h1) (hl2 : l2 ≤ h2) (h21 : l2 ≤ h1) :
    setDist (Icc l1 h1) (Icc l2 h2) = max (l1 - h2) 0 := by
  unfold setDist
  apply IsLeast.csInf_eq
  constructor
  · by_cases h : h2 ≤ l1
    · exact ⟨l1, ⟨le_rfl, hl1⟩, h2, ⟨hl2, le_rfl⟩, by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith), max_eq_left (by linarith)]⟩
    · push Not at h
      refine ⟨max l1 l2, ⟨le_max_left _ _, max_le hl1 h21⟩, max l1 l2, ⟨le_max_right _ _, max_le h.le hl2⟩, ?_⟩
      rw [sub_self, norm_zero, max_eq_right (by linarith)]
  · rintro r ⟨x, hx, y, hy, rfl⟩
    rw [Real.norm_eq_abs]
    exact max_le (by linarith [le_abs_self (x - y), hx.1, hy.2]) (abs_nonneg _)

/-- The minimal-norm element of `[l1,h1] − [l2,h2]` (with `l2 ≤ h1`) is `max(l1 − h2, 0)`, and it is unique. -/
lemma isMinNorm_Icc_sub_iff {l1 h1 l2 h2 : ℝ} (hl1 : l1 ≤ h1) (hl2 : l2 ≤ h2) (h21 : l2 ≤ h1) (d : ℝ) :
    IsMinNorm (Icc l1 h1 - Icc l2 h2) d ↔ d = max (l1 - h2) 0 := by
  have hmem : max (l1 - h2) 0 ∈ Icc l1 h1 - Icc l2 h2 := by
    by_cases h : h2 ≤ l1
    · rw [max_eq_left (by linarith)]
      exact ⟨l1, ⟨le_rfl, hl1⟩, h2, ⟨hl2, le_rfl⟩, rfl⟩
    · push Not at h
      rw [max_eq_right (by linarith)]
      exact ⟨max l1 l2, ⟨le_max_left _ _, max_le hl1 h21⟩, max l1 l2, ⟨le_max_right _ _, max_le h.le hl2⟩, sub_self _⟩
  have hlow : ∀ q ∈ Icc l1 h1 - Icc l2 h2, l1 - h2 ≤ q := by
    rintro q ⟨x, hx, y, hy, rfl⟩; linarith [hx.1, hy.2]
  constructor
  · rintro ⟨hd, hmin⟩
    have hd1 := hlow d hd
    have hd2 := hmin _ hmem
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hd2
    by_cases h : 0 < l1 - h2
    · rw [max_eq_left h.le] at hd2 ⊢
      rw [abs_of_pos (by linarith), abs_of_pos h] at hd2
      linarith
    · push Not at h
      rw [max_eq_right h] at hd2 ⊢
      rw [abs_zero] at hd2
      exact abs_nonpos_iff.1 hd2
  · rintro rfl
    refine ⟨hmem, fun q hq => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have := hlow q hq
    by_cases h : 0 ≤ l1 - h2
    · rw [max_eq_left h, abs_of_nonneg h]; exact this.trans (le_abs_self q)
    · push Not at h
      rw [max_eq_right h.le, abs_zero]; exact abs_nonneg q

end StatFormal.Wave31td
