import StatFormal.Archive.TrimmedMMD.Concentration.Statements
import StatFormal.Archive.Wave17a.Statements
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Population extreme trimmed means of a direction (library)

For a bounded strongly measurable feature map `φ`, a direction `f` and `h = ⟨f, φ(·)⟩`, with `β = 1 − α`:

* `isLeast_region`: if `q` is a `β`-quantile of `h` under `P` (`P(h < q) ≤ β ≤ P(h ≤ q)`), then
  `min_{a ∈ 𝒞_α(P)} ⟨f, a⟩ = q − β⁻¹ ∫ (q − h)_+ dP` (Rockafellar–Uryasev form), attained at
  `g = β⁻¹ 1{h < q} + t 1{h = q}`;
* `isGreatest_region`: if `q'` is an `α`-quantile of `h` under `Q`, then
  `max_{b ∈ 𝒞_α(Q)} ⟨f, b⟩ = q' + β⁻¹ ∫ (h − q')_+ dQ`;
* `sepVal_eq`: hence `sep(f; 𝒞_α(P), 𝒞_α(Q))` is the real number `L − U`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace StatFormal.Foundations.TrimmedMean

open StatFormal.TrimmedMMD.Concentration StatFormal.Wave17a

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma measurable_inner_comp {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (f : H) :
    Measurable fun x => ⟪f, φ x⟫ :=
  ((innerSL ℝ f).continuous.comp_stronglyMeasurable hφ).measurable

lemma abs_inner_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (f : H) (x : 𝒳) :
    |⟪f, φ x⟫| ≤ ‖f‖ * κ :=
  (abs_real_inner_le_norm f (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg f))

/-- `⟨f, ∫ g φ dP⟩ = ∫ g ⟨f, φ⟩ dP` for bounded measurable `g`. -/
lemma inner_integral_smul (P : Measure 𝒳) [IsFiniteMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {g : 𝒳 → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (f : H) :
    ⟪f, ∫ x, g x • φ x ∂P⟫ = ∫ x, g x * ⟪f, φ x⟫ ∂P := by
  have hint : Integrable (fun x => g x • φ x) P := by
    refine Integrable.of_bound (hg.stronglyMeasurable.smul hφ).aestronglyMeasurable (C * κ)
      (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hgC x) (hκ x) (norm_nonneg _) ((abs_nonneg _).trans (hgC x))
  rw [← integral_inner hint]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [inner_smul_right])

theorem isLeast_region (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ α q : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H)
    (hq1 : P.real {x | ⟪f, φ x⟫ < q} ≤ 1 - α) (hq2 : 1 - α ≤ P.real {x | ⟪f, φ x⟫ ≤ q}) :
    IsLeast ((fun a => ⟪f, a⟫) '' region φ α P) (q - (1 - α)⁻¹ * ∫ x, max (q - ⟪f, φ x⟫) 0 ∂P) := by
  set h : 𝒳 → ℝ := fun x => ⟪f, φ x⟫ with hh
  have hhm : Measurable h := measurable_inner_comp hφ f
  have hhb := abs_inner_le hκ f
  have hβ : 0 < 1 - α := by linarith
  set β := 1 - α
  have hgq_int : Integrable (fun x => max (q - h x) 0) P :=
    Integrable.of_bound ((hhm.const_sub q).max measurable_const).aestronglyMeasurable (|q| + ‖f‖ * κ)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        have := hhb x
        refine max_le ?_ (by linarith [abs_nonneg q, (abs_nonneg _).trans (hhb x)])
        have := le_abs_self q
        have := neg_abs_le (h x)
        linarith)
  refine ⟨?_, ?_⟩
  · -- attainment
    set S1 : Set 𝒳 := {x | h x < q}
    set S2 : Set 𝒳 := {x | h x = q}
    have hS1 : MeasurableSet S1 := measurableSet_lt hhm measurable_const
    have hS2 : MeasurableSet S2 := measurableSet_eq_fun hhm measurable_const
    have hdisj : Disjoint S1 S2 := Set.disjoint_left.2 fun x h1 h2 => by
      simp only [S1, S2, mem_ofPred_eq] at h1 h2; linarith
    have hU : {x | h x ≤ q} = S1 ∪ S2 := by
      ext x; simp only [S1, S2, mem_ofPred_eq, mem_union]; exact le_iff_lt_or_eq
    have hF : P.real {x | h x ≤ q} = P.real S1 + P.real S2 := by
      rw [hU, measureReal_union hdisj hS2]
    set G := P.real S1
    set A := P.real S2
    have hA0 : 0 ≤ A := measureReal_nonneg
    set t : ℝ := (β - G) / (β * A)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
    have htc : t ≤ 1 / β := by
      rcases hA0.eq_or_lt with h0 | h0
      · simp only [t, ← h0, mul_zero, div_zero]; positivity
      · rw [div_le_div_iff₀ (by positivity) hβ]
        nlinarith
    set g : 𝒳 → ℝ := S1.indicator (fun _ => 1 / β) + S2.indicator (fun _ => t)
    have hgm : Measurable g :=
      (measurable_const.indicator hS1).add (measurable_const.indicator hS2)
    have hgval : ∀ x, g x = if h x < q then 1 / β else if h x = q then t else 0 := fun x => by
      simp only [g, Pi.add_apply, Set.indicator, S1, S2, mem_ofPred_eq]
      split_ifs with h1 h2 h2 <;> first | linarith | simp
    have hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α) := fun x => by
      rw [hgval x]
      split_ifs
      · exact ⟨by positivity, le_rfl⟩
      · exact ⟨ht0, htc⟩
      · exact ⟨le_rfl, by positivity⟩
    have hgabs : ∀ x, |g x| ≤ 1 / β := fun x => by
      rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
    have hgint : ∫ x, g x ∂P = 1 := by
      have hi1 : Integrable (S1.indicator fun _ => (1 / β : ℝ)) P := (integrable_const _).indicator hS1
      have hi2 : Integrable (S2.indicator fun _ => (t : ℝ)) P := (integrable_const _).indicator hS2
      show ∫ x, (S1.indicator (fun _ => 1 / β) x + S2.indicator (fun _ => t) x) ∂P = 1
      rw [integral_add hi1 hi2,
        integral_indicator_const _ hS1, integral_indicator_const _ hS2, smul_eq_mul, smul_eq_mul]
      change G * (1 / β) + A * t = 1
      rcases hA0.eq_or_lt with h0 | h0
      · have hG : G = β := le_antisymm hq1 (by rw [hF, ← h0, add_zero] at hq2; exact hq2)
        rw [← h0, zero_mul, add_zero, hG]; field_simp
      · simp only [t]; field_simp; ring
    refine ⟨∫ x, g x • φ x ∂P, ⟨g, hgm, hgb, hgint, rfl⟩, ?_⟩
    simp only
    rw [inner_integral_smul P hφ hκ hgm hgabs f]
    have hpt : ∀ x, g x * h x = q * g x - (1 / β) * max (q - h x) 0 := fun x => by
      rw [hgval x]
      rcases lt_trichotomy (h x) q with h1 | h1 | h1
      · rw [if_pos h1, max_eq_left (by linarith)]; ring
      · rw [if_neg (not_lt.2 h1.ge), if_pos h1, h1, sub_self, max_self]; ring
      · rw [if_neg (not_lt.2 h1.le), if_neg h1.ne', max_eq_right (by linarith)]; ring
    have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable (1 / β)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgabs x)
    calc ∫ x, g x * ⟪f, φ x⟫ ∂P = ∫ x, (q * g x - (1 / β) * max (q - h x) 0) ∂P :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = q - β⁻¹ * ∫ x, max (q - h x) 0 ∂P := by
          rw [integral_sub (hgi.const_mul q) (hgq_int.const_mul _), integral_const_mul, integral_const_mul,
            hgint]
          ring
  · -- weak duality
    rintro _ ⟨a, ⟨g, hgm, hgb, hgint, rfl⟩, rfl⟩
    have hgabs : ∀ x, |g x| ≤ 1 / β := fun x => by
      rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
    simp only
    rw [inner_integral_smul P hφ hκ hgm hgabs f]
    have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable (1 / β)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgabs x)
    have hpt : ∀ x, q * g x - (1 / β) * max (q - h x) 0 ≤ g x * h x := fun x => by
      have h1 : g x * (q - h x) ≤ g x * max (q - h x) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (hgb x).1
      have h2 : g x * max (q - h x) 0 ≤ (1 / β) * max (q - h x) 0 :=
        mul_le_mul_of_nonneg_right (hgb x).2 (le_max_right _ _)
      nlinarith
    have hint2 : Integrable (fun x => g x * h x) P :=
      Integrable.of_bound (hgm.mul hhm).aestronglyMeasurable (1 / β * (‖f‖ * κ))
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hgabs x) (hhb x) (abs_nonneg _) (by positivity))
    calc q - β⁻¹ * ∫ x, max (q - h x) 0 ∂P = ∫ x, (q * g x - (1 / β) * max (q - h x) 0) ∂P := by
          rw [integral_sub (hgi.const_mul q) (hgq_int.const_mul _), integral_const_mul, integral_const_mul,
            hgint]
          ring
      _ ≤ ∫ x, g x * h x ∂P := integral_mono ((hgi.const_mul q).sub (hgq_int.const_mul _)) hint2 hpt

theorem isGreatest_region (Q : Measure 𝒳) [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ α q : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H)
    (hq1 : Q.real {x | ⟪f, φ x⟫ < q} ≤ α) (hq2 : α ≤ Q.real {x | ⟪f, φ x⟫ ≤ q}) :
    IsGreatest ((fun b => ⟪f, b⟫) '' region φ α Q) (q + (1 - α)⁻¹ * ∫ x, max (⟪f, φ x⟫ - q) 0 ∂Q) := by
  have hm := measurable_inner_comp hφ f
  have e1 : {x | ⟪-f, φ x⟫ < -q} = {x | ⟪f, φ x⟫ ≤ q}ᶜ := by
    ext x; simp only [inner_neg_left, mem_ofPred_eq, mem_compl_iff, not_le, neg_lt_neg_iff]
  have e2 : {x | ⟪-f, φ x⟫ ≤ -q} = {x | ⟪f, φ x⟫ < q}ᶜ := by
    ext x; simp only [inner_neg_left, mem_ofPred_eq, mem_compl_iff, not_lt, neg_le_neg_iff]
  have h1 : Q.real {x | ⟪-f, φ x⟫ < -q} ≤ 1 - α := by
    rw [e1, probReal_compl_eq_one_sub (measurableSet_le hm measurable_const)]; linarith
  have h2 : 1 - α ≤ Q.real {x | ⟪-f, φ x⟫ ≤ -q} := by
    rw [e2, probReal_compl_eq_one_sub (measurableSet_lt hm measurable_const)]; linarith
  obtain ⟨⟨a, ha, hav⟩, hlb⟩ := isLeast_region Q hφ hκ hα0 hα1 (-f) h1 h2
  have hfun : ∀ x, max (-q - ⟪-f, φ x⟫) 0 = max (⟪f, φ x⟫ - q) 0 := fun x => by
    rw [inner_neg_left]; ring_nf
  simp only [hfun] at hav hlb
  refine ⟨⟨a, ha, ?_⟩, ?_⟩
  · simp only [inner_neg_left] at hav ⊢
    linarith
  · rintro _ ⟨b, hb, rfl⟩
    have := hlb ⟨b, hb, rfl⟩
    simp only [inner_neg_left] at this ⊢
    linarith

lemma iInf_coe_of_isLeast {S : Set H} {u : H → ℝ} {L : ℝ} (h : IsLeast (u '' S) L) :
    (⨅ a ∈ S, ((u a : ℝ) : EReal)) = (L : EReal) := by
  obtain ⟨⟨a, ha, rfl⟩, hlb⟩ := h
  refine le_antisymm (biInf_le (fun a => ((u a : ℝ) : EReal)) ha) (le_iInf₂ fun b hb => ?_)
  exact EReal.coe_le_coe_iff.2 (hlb ⟨b, hb, rfl⟩)

lemma iSup_coe_of_isGreatest {S : Set H} {u : H → ℝ} {U : ℝ} (h : IsGreatest (u '' S) U) :
    (⨆ b ∈ S, ((u b : ℝ) : EReal)) = (U : EReal) := by
  obtain ⟨⟨a, ha, rfl⟩, hub⟩ := h
  refine le_antisymm (iSup₂_le fun b hb => ?_) (le_biSup (fun a => ((u a : ℝ) : EReal)) ha)
  exact EReal.coe_le_coe_iff.2 (hub ⟨b, hb, rfl⟩)

theorem sepVal_eq (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α q q' : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (f : H)
    (hq1 : P.real {x | ⟪f, φ x⟫ < q} ≤ 1 - α) (hq2 : 1 - α ≤ P.real {x | ⟪f, φ x⟫ ≤ q})
    (hq1' : Q.real {x | ⟪f, φ x⟫ < q'} ≤ α) (hq2' : α ≤ Q.real {x | ⟪f, φ x⟫ ≤ q'}) :
    sepVal f (region φ α P) (region φ α Q) =
      (((q - (1 - α)⁻¹ * ∫ x, max (q - ⟪f, φ x⟫) 0 ∂P) -
        (q' + (1 - α)⁻¹ * ∫ x, max (⟪f, φ x⟫ - q') 0 ∂Q) : ℝ) : EReal) := by
  unfold sepVal
  rw [iInf_coe_of_isLeast (isLeast_region P hφ hκ hα0 hα1 f hq1 hq2),
    iSup_coe_of_isGreatest (isGreatest_region Q hφ hκ hα0 hα1 f hq1' hq2')]
  exact (EReal.coe_sub _ _).symm

end StatFormal.Foundations.TrimmedMean
