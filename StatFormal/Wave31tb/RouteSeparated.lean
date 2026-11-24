import StatFormal.Wave31tb.Statements
import StatFormal.Archive.Wave8a.RouteGeorep

set_option linter.style.longLine false

/-!
# Route: wave 31tb, `ex:separated` (untrusted proof file)

* TV: `P − Q = α⋆(P₀ − Q₀)` on every set, `|P₀(A) − Q₀(A)| ≤ 1`, and at `A = S_P` the difference is `α⋆`.
* The bound for the regions (`Dpop`): for `z = E_P[gφ] ∈ 𝒞_α(P)`, `⟪f, z⟫ = E_P[g f] = 1 − (1−α⋆)E_R[g] ≥ 1 − (1−α⋆)/(1−α)`
  (`f = 0` `R`-a.e., `f = 1` `P₀`-a.e., `E_P g = 1`, `g ≤ (1−α)⁻¹`), symmetrically `⟪f, w⟫ ≤ −(1 − (1−α⋆)/(1−α))` for `w ∈ 𝒞_α(Q)`,
  and Cauchy–Schwarz `⟪f, z − w⟫ ≤ ‖f‖‖z − w‖`; then `le_csInf` over the (nonempty) set of distances.
* The bound for `dTrim` (the printed infimum over trimmings): the certified `Wave8a.georep_dist` (`dTrim = Dpop`).
* The margin and the `γ = 1` form: substitute `α = α⋆ − ε` and use `1 − α ≤ 1`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tb

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave8a StatFormal.Wave30tu

section Route

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The mixture `(1−a)R + aP₀` of two probability measures is a probability measure. -/
lemma mix_isProb (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) ha0]
  simp

/-- `((1−a)R + aP₀)(A) = (1−a)R(A) + aP₀(A)` in `ℝ`. -/
lemma mix_real (R P₀ : Measure 𝒳) [IsFiniteMeasure R] [IsFiniteMeasure P₀] {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (A : Set 𝒳) :
    (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀).real A = (1 - a) * R.real A + a * P₀.real A := by
  rw [measureReal_add_apply (by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top R A))
      (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P₀ A)),
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ha0]

/-- The integral against the mixture. -/
lemma integral_mix (R P₀ : Measure 𝒳) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h : 𝒳 → ℝ)
    (hR : Integrable h R) (hP : Integrable h P₀) :
    ∫ x, h x ∂(ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) =
      (1 - a) * ∫ x, h x ∂R + a * ∫ x, h x ∂P₀ := by
  rw [integral_add_measure (hR.smul_measure ENNReal.ofReal_ne_top) (hP.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ha0,
    smul_eq_mul, smul_eq_mul]

/-- Integrability of a bounded strongly measurable function against a finite measure. -/
lemma integrable_bdd {E : Type*} [NormedAddCommGroup E] (μ : Measure 𝒳) [IsFiniteMeasure μ] {F : 𝒳 → E}
    (hF : StronglyMeasurable F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)

/-- The key computation: if `f = 0` `R`-a.e. and `f = c` `P₀`-a.e., `P = (1−a)R + aP₀`, and `z = E_P[gφ]` with `0 ≤ g ≤ B` measurable
and `E_P g = 1`, then `⟪f, z⟫ = c(1 − (1−a)E_R g)`. -/
lemma inner_mix (φ : 𝒳 → H) {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f : H) (c : ℝ) (hf0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0) (hf1 : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = c)
    (g : 𝒳 → ℝ) (hg : Measurable g) {B : ℝ} (hgB : ∀ x, 0 ≤ g x ∧ g x ≤ B)
    (hg1 : ∫ x, g x ∂(ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) = 1) :
    ⟪f, ∫ x, g x • φ x ∂(ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀)⟫_ℝ =
      c * (1 - (1 - a) * ∫ x, g x ∂R) := by
  set P := ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀ with hPdef
  have : IsProbabilityMeasure P := mix_isProb R P₀ ha0 ha1
  have hgabs : ∀ x, ‖g x‖ ≤ B := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgB x).1]; exact (hgB x).2
  have hgs : StronglyMeasurable g := hg.stronglyMeasurable
  have hgφ : StronglyMeasurable fun x => g x • φ x := hgs.smul hφ
  have hgφB : ∀ x, ‖g x • φ x‖ ≤ B * κ := fun x => by
    rw [norm_smul]
    exact mul_le_mul (hgabs x) (hκ x) (norm_nonneg _) ((norm_nonneg _).trans (hgabs x))
  have hint : Integrable (fun x => g x • φ x) P := integrable_bdd P hgφ hgφB
  have hfs : StronglyMeasurable fun x => ⟪f, φ x⟫_ℝ :=
    (continuous_const.inner continuous_id).comp_stronglyMeasurable hφ
  have hh : StronglyMeasurable fun x => g x * ⟪f, φ x⟫_ℝ := hgs.mul hfs
  have hhB : ∀ x, ‖g x * ⟪f, φ x⟫_ℝ‖ ≤ B * (‖f‖ * κ) := fun x => by
    rw [norm_mul]
    refine mul_le_mul (hgabs x) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hgabs x))
    exact (norm_inner_le_norm f (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _))
  rw [← integral_inner hint f]
  simp_rw [inner_smul_right]
  rw [hPdef, integral_mix R P₀ ha0 ha1 _ (integrable_bdd R hh hhB) (integrable_bdd P₀ hh hhB)] at *
  have hR0 : ∫ x, g x * ⟪f, φ x⟫_ℝ ∂R = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [hf0] with x hx; rw [hx, mul_zero]
  have hP1 : ∫ x, g x * ⟪f, φ x⟫_ℝ ∂P₀ = c * ∫ x, g x ∂P₀ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hf1] with x hx; rw [hx, mul_comm]
  have hg1' := hg1
  rw [integral_mix R P₀ ha0 ha1 g (integrable_bdd R hgs hgabs) (integrable_bdd P₀ hgs hgabs)] at hg1'
  rw [hR0, hP1]
  have : a * ∫ x, g x ∂P₀ = 1 - (1 - a) * ∫ x, g x ∂R := by linarith
  calc (1 - a) * 0 + a * (c * ∫ x, g x ∂P₀) = c * (a * ∫ x, g x ∂P₀) := by ring
    _ = c * (1 - (1 - a) * ∫ x, g x ∂R) := by rw [this]

/-- `E_R g ≤ B` for measurable `0 ≤ g ≤ B` and a probability measure `R`. -/
lemma integral_le_bound (R : Measure 𝒳) [IsProbabilityMeasure R] (g : 𝒳 → ℝ) (hg : Measurable g) {B : ℝ}
    (hgB : ∀ x, 0 ≤ g x ∧ g x ≤ B) : ∫ x, g x ∂R ≤ B := by
  have hgabs : ∀ x, ‖g x‖ ≤ B := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgB x).1]; exact (hgB x).2
  calc ∫ x, g x ∂R ≤ ∫ _x, B ∂R :=
        integral_mono (integrable_bdd R hg.stronglyMeasurable hgabs) (integrable_const B) (fun x => (hgB x).2)
    _ = B := by simp

/-- An element of `𝒞_α((1−a)R + aP₀)` paired with `f` (`f = 0` `R`-a.e., `f = c` `P₀`-a.e.) is `c(1 − (1−a)t)` with `t ≤ (1−α)⁻¹`. -/
lemma region_inner (φ : 𝒳 → H) {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (f : H) (c : ℝ) (hf0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0) (hf1 : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = c) (α : ℝ) {z : H}
    (hz : z ∈ region φ α (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀)) :
    ∃ t, t ≤ 1 / (1 - α) ∧ ⟪f, z⟫_ℝ = c * (1 - (1 - a) * t) := by
  obtain ⟨g, hg, hgB, hg1, rfl⟩ := hz
  exact ⟨∫ x, g x ∂R, integral_le_bound R g hg hgB,
    inner_mix φ hφ hκ R P₀ ha0 ha1 f c hf0 hf1 g hg hgB hg1⟩

omit [CompleteSpace H] in
/-- `𝒞_α(P)` is nonempty for a probability measure `P` and `α ∈ [0,1)` (`g ≡ 1`). -/
lemma region_nonempty (φ : 𝒳 → H) (P : Measure 𝒳) [IsProbabilityMeasure P] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ x, (fun _ => (1 : ℝ)) x • φ x ∂P) ∈ region φ α P := by
  refine ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, ?_⟩, by simp, rfl⟩
  rw [le_div_iff₀ (by linarith)]; linarith

/-- The bound for the regions' distance: `2(α⋆ − α)/((1−α)‖f‖) ≤ D_α(P,Q)` (`Dpop`). -/
lemma dpop_bound (φ : 𝒳 → H) {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q₀] {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (f : H) (hfpos : 0 < ‖f‖) (hf0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0)
    (hfP : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = 1) (hfQ : ∀ᵐ x ∂Q₀, ⟪f, φ x⟫_ℝ = -1) {α : ℝ} (hα : α ∈ Icc 0 a) :
    2 * (a - α) / ((1 - α) * ‖f‖) ≤
      Dpop φ (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • Q₀) α := by
  have := mix_isProb R P₀ ha0 ha1.le
  have := mix_isProb R Q₀ ha0 ha1.le
  have hα1 : α < 1 := lt_of_le_of_lt hα.2 ha1
  have h1α : 0 < 1 - α := by linarith
  unfold Dpop setDist
  refine le_csInf ⟨_, _, region_nonempty φ _ hα.1 hα1, _, region_nonempty φ _ hα.1 hα1, rfl⟩ ?_
  rintro r ⟨z, hz, w, hw, rfl⟩
  obtain ⟨t₁, ht₁, hz'⟩ := region_inner φ hφ hκ R P₀ ha0 ha1.le f 1 hf0 hfP α hz
  obtain ⟨t₂, ht₂, hw'⟩ := region_inner φ hφ hκ R Q₀ ha0 ha1.le f (-1) hf0 hfQ α hw
  have ht₁' : (1 - α) * t₁ ≤ 1 := by rw [le_div_iff₀ h1α] at ht₁; linarith
  have ht₂' : (1 - α) * t₂ ≤ 1 := by rw [le_div_iff₀ h1α] at ht₂; linarith
  have hcs : ⟪f, z - w⟫_ℝ ≤ ‖f‖ * ‖z - w‖ := real_inner_le_norm f (z - w)
  rw [inner_sub_right, hz', hw'] at hcs
  have k1 : 0 ≤ (1 - a) * (1 - (1 - α) * t₁) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ (1 - a) * (1 - (1 - α) * t₂) := mul_nonneg (by linarith) (by linarith)
  have key : 2 * (a - α) ≤ (1 - α) * (‖f‖ * ‖z - w‖) := by
    have := mul_le_mul_of_nonneg_left hcs h1α.le
    nlinarith
  rw [div_le_iff₀ (mul_pos h1α hfpos)]
  linarith

/-- `TV((1−a)R + aP₀, (1−a)R + aQ₀) = a` when `P₀`, `Q₀` are concentrated on disjoint measurable sets. -/
lemma tv_mix (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q₀]
    {SP SQ : Set 𝒳} (hSP : MeasurableSet SP) (hPQ : Disjoint SP SQ) (hP₀ : P₀ SPᶜ = 0) (hQ₀ : Q₀ SQᶜ = 0)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    StatFormal.Distances.tvDist (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀)
      (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • Q₀) = a := by
  have := mix_isProb R P₀ ha0 ha1
  have := mix_isProb R Q₀ ha0 ha1
  apply le_antisymm
  · refine StatFormal.Distances.tvDist_le_of_forall fun A _ => ?_
    rw [mix_real R P₀ ha0 ha1, mix_real R Q₀ ha0 ha1]
    have hP1 : P₀.real A ≤ 1 := (measureReal_mono (subset_univ A)).trans_eq probReal_univ
    have hQ1 : Q₀.real A ≤ 1 := (measureReal_mono (subset_univ A)).trans_eq probReal_univ
    have hP0 : 0 ≤ P₀.real A := measureReal_nonneg
    have hQ0 : 0 ≤ Q₀.real A := measureReal_nonneg
    have : (1 - a) * R.real A + a * P₀.real A - ((1 - a) * R.real A + a * Q₀.real A) = a * (P₀.real A - Q₀.real A) := by ring
    rw [this, abs_mul, abs_of_nonneg ha0]
    exact mul_le_of_le_one_right ha0 (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
  · have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist
      (μ := ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) (ν := ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • Q₀) hSP
    rw [mix_real R P₀ ha0 ha1, mix_real R Q₀ ha0 ha1] at h
    have hP1 : P₀.real SP = 1 := by
      rw [measureReal_def, (prob_compl_eq_zero_iff hSP).1 hP₀, ENNReal.toReal_one]
    have hQ1 : Q₀.real SP = 0 := by
      rw [measureReal_def, measure_mono_null hPQ.subset_compl_right hQ₀, ENNReal.toReal_zero]
    rw [hP1, hQ1] at h
    have : (1 - a) * R.real SP + a * 1 - ((1 - a) * R.real SP + a * 0) = a := by ring
    rwa [this, abs_of_nonneg ha0] at h

end Route

/-- `ex:separated (v3)`. -/
theorem separated : Claims.separated := by
  intro 𝒳 H _ _ _ _ φ κ R P₀ Q₀ P Q _ _ _ SR SP SQ a hφ hκ _ hSP _ _ _ hPQ hR hP₀ hQ₀ ha0 ha1 hP hQ
  subst hP hQ
  have := mix_isProb R P₀ ha0.le ha1.le
  have := mix_isProb R Q₀ ha0.le ha1.le
  have htv := tv_mix R P₀ Q₀ hSP hPQ hP₀ hQ₀ ha0.le ha1.le
  refine ⟨htv, ?_⟩
  intro f hfR hfP hfQ
  have hfpos : 0 < ‖f‖ := by
    have hSPne : SP.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, compl_empty, measure_univ] at hP₀
      exact one_ne_zero hP₀
    obtain ⟨x, hx⟩ := hSPne
    have hx1 := hfP x hx
    rw [norm_pos_iff]
    rintro rfl
    simp at hx1
  have hR0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0 := by
    filter_upwards [(ae_iff.2 hR : ∀ᵐ x ∂R, x ∈ SR)] with x hx using hfR x hx
  have hP1 : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = 1 := by
    filter_upwards [(ae_iff.2 hP₀ : ∀ᵐ x ∂P₀, x ∈ SP)] with x hx using hfP x hx
  have hQ1 : ∀ᵐ x ∂Q₀, ⟪f, φ x⟫_ℝ = -1 := by
    filter_upwards [(ae_iff.2 hQ₀ : ∀ᵐ x ∂Q₀, x ∈ SQ)] with x hx using hfQ x hx
  have hD := fun α (hα : α ∈ Icc 0 a) => dpop_bound φ hφ hκ R P₀ Q₀ ha0.le ha1 f hfpos hR0 hP1 hQ1 hα
  have hweak : ∀ α ∈ Icc 0 a, 2 * (a - α) / ‖f‖ ≤ 2 * (a - α) / ((1 - α) * ‖f‖) := by
    intro α hα
    have h1α : 0 < 1 - α := by linarith [hα.2]
    refine div_le_div_of_nonneg_left (by linarith [hα.2]) (mul_pos h1α hfpos) ?_
    have : (1 - α) * ‖f‖ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (by linarith [hα.1]) hfpos.le
    linarith
  have hc : 0 < 2 / ‖f‖ := by positivity
  have hmarg : ∀ e ∈ Icc 0 a, 2 / ‖f‖ * e ≤
      Dpop φ (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • P₀) (ENNReal.ofReal (1 - a) • R + ENNReal.ofReal a • Q₀) (a - e) := by
    intro e he
    have hα : a - e ∈ Icc 0 a := ⟨by linarith [he.2], by linarith [he.1]⟩
    have h1 := hD (a - e) hα
    have h2 := hweak (a - e) hα
    have h3 : 2 * (a - (a - e)) / ‖f‖ = 2 / ‖f‖ * e := by ring
    linarith
  refine ⟨hfpos, fun α hα => ⟨?_, hD α hα, hweak α hα⟩, ?_, hc, ?_⟩
  · rw [StatFormal.Wave8a.georep_dist 𝒳 H _ _ φ κ α hφ hκ hα.1 (lt_of_le_of_lt hα.2 ha1)]
    exact hD α hα
  · unfold Margin
    rw [htv]
    refine ⟨(strictMono_mul_left_of_pos hc).strictMonoOn _, (continuous_const.mul continuous_id).continuousOn,
      by simp, fun e he => mul_nonneg hc.le he.1, hmarg⟩
  · rw [htv]
    intro ε hε
    rw [Real.rpow_one]
    exact hmarg ε hε

end StatFormal.Wave31tb
