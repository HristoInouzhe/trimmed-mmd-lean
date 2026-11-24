import StatFormal.Wave31tu.Statements
import StatFormal.Wave31ti.Proofs

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y9 `lap_ratio` (Lemma S4.20 `lem:lapratio`, S4 :1075-1086)

For any probability measures `P, Q` on a measurable space, `α ∈ [0,1)` and `g ≠ 0` with `osc(⟪g, φ ·⟫) ≤ 1`:
`D̄_α(P,Q) ≥ {L(f) − α}/‖g‖`, `f = ⟪g, φ ·⟫`; in particular `V(ε′) ≥ {ε′ − err(f)}/‖g‖` for `ε′ ∈ [0, α⋆]`.

Route (printed): for parts `a = ∫γ_P φ dP`, `b = ∫γ_Q φ dQ` of the regions, the removed weights `1 − (1−α)γ` lie in `[0,1]` with
mass `α`, so `L(f) − (1−α)⟪g, a − b⟫ ≤ α·osc(f) ≤ α` (`trim_dev`); Cauchy–Schwarz and the infimum over the regions.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration

/-- **Mass removed by a trimming.** For a probability `P`, `m ≤ f ≤ M` measurable, and a trimming density `γ`
(`0 ≤ γ ≤ (1−α)⁻¹`, `∫γ dP = 1`, `α < 1`): `αm ≤ ∫ f dP − (1−α)∫γf dP ≤ αM`. -/
theorem trim_dev {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] {f γ : 𝒳 → ℝ} {α M m : ℝ}
    (hf : Measurable f) (hfM : ∀ x, f x ≤ M) (hmf : ∀ x, m ≤ f x) (hγ : Measurable γ)
    (hγb : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1 / (1 - α)) (hγ1 : ∫ x, γ x ∂P = 1) (hα : α < 1) :
    α * m ≤ (∫ x, f x ∂P) - (1 - α) * ∫ x, γ x * f x ∂P ∧
      (∫ x, f x ∂P) - (1 - α) * ∫ x, γ x * f x ∂P ≤ α * M := by
  have h1α : 0 < 1 - α := by linarith
  have hfb : ∀ x, ‖f x‖ ≤ max |M| |m| := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hmf x, neg_abs_le m, le_max_right |M| |m|]
    · linarith [hfM x, le_abs_self M, le_max_left |M| |m|]
  have hfi : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable _ (ae_of_all _ hfb)
  have hγi : Integrable γ P := Integrable.of_bound hγ.aestronglyMeasurable (1 / (1 - α))
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hγb x).1]; exact (hγb x).2)
  have hγfi : Integrable (fun x => γ x * f x) P := hfi.bdd_mul hγ.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hγb x).1]; exact (hγb x).2)
  set w : 𝒳 → ℝ := fun x => 1 - (1 - α) * γ x with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    have := mul_le_mul_of_nonneg_left (hγb x).2 h1α.le
    rw [mul_one_div_cancel h1α.ne'] at this; simp only [hw]; linarith
  have hwi : Integrable w P := (integrable_const 1).sub (hγi.const_mul _)
  have hwint : ∫ x, w x ∂P = α := by
    simp only [hw]; rw [integral_sub (integrable_const 1) (hγi.const_mul _), integral_const_mul, hγ1]; simp
  have hkey : (∫ x, f x ∂P) - (1 - α) * ∫ x, γ x * f x ∂P = ∫ x, w x * f x ∂P := by
    rw [← integral_const_mul, ← integral_sub hfi (hγfi.const_mul _)]
    congr 1; ext x; simp only [hw]; ring
  have hwfi : Integrable (fun x => w x * f x) P := by
    refine hfi.bdd_mul (c := 1) (measurable_const.sub (hγ.const_mul _)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
    simp only [hw]; nlinarith [(hγb x).1]
  rw [hkey]
  constructor
  · have h := integral_mono (hwi.mul_const m) hwfi (fun x => mul_le_mul_of_nonneg_left (hmf x) (hw0 x))
    rwa [integral_mul_const, hwint] at h
  · have h := integral_mono hwfi (hwi.mul_const M) (fun x => mul_le_mul_of_nonneg_left (hfM x) (hw0 x))
    rwa [integral_mul_const, hwint] at h

/-- `⟪g, ∫ γ φ dP⟫ = ∫ γ ⟪g, φ⟫ dP` for a bounded trimming density and a bounded strongly measurable `φ`. -/
theorem inner_region {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {γ : 𝒳 → ℝ} {c : ℝ} (hγ : Measurable γ) (hγb : ∀ x, 0 ≤ γ x ∧ γ x ≤ c) (g : H) :
    ⟪g, ∫ x, γ x • φ x ∂P⟫_ℝ = ∫ x, γ x * ⟪g, φ x⟫_ℝ ∂P := by
  have hi : Integrable (fun x => γ x • φ x) P := by
    refine Integrable.of_bound (hγ.stronglyMeasurable.smul hφ).aestronglyMeasurable (c * κ) (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hγb x).1]
    exact mul_le_mul (hγb x).2 (hκ x) (norm_nonneg _) ((hγb x).1.trans (hγb x).2)
  rw [← integral_inner hi]
  congr 1; ext x; rw [inner_smul_right]

/-- **Lemma S4.20 (a), general form.** -/
theorem ratio_le_uPath {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : 𝒳 → H} {κ : ℝ} {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {α : ℝ} {g : H}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hg : g ≠ 0)
    (hosc : Wave31to.oscFn (Wave31to.wit φ g) ≤ 1) :
    (linL P Q (Wave31to.wit φ g) - α) / ‖g‖ ≤ Wave31ti.uPath φ P Q α := by
  set f := Wave31to.wit φ g with hfdef
  have h1α : 0 < 1 - α := by linarith
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hfb : ∀ x, |f x| ≤ ‖g‖ * κ := fun x =>
    (abs_real_inner_le_norm g (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _))
  have hbdA : BddAbove (range f) := ⟨‖g‖ * κ, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (hfb x)).2⟩
  have hbdB : BddBelow (range f) := ⟨-(‖g‖ * κ), by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (hfb x)).1⟩
  have hfM : ∀ x, f x ≤ ⨆ z, f z := fun x => le_ciSup hbdA x
  have hmf : ∀ x, ⨅ z, f z ≤ f x := fun x => ciInf_le hbdB x
  have hfmeas : Measurable f := by
    have : Continuous fun h : H => ⟪g, h⟫_ℝ := continuous_const.inner continuous_id
    exact (this.comp_stronglyMeasurable hφ).measurable
  -- the bound at every pair of parts
  have hpair : ∀ a ∈ region φ α P, ∀ b ∈ region φ α Q, (linL P Q f - α) / ‖g‖ / (1 - α) ≤ ‖a - b‖ := by
    rintro a ⟨γP, hγPm, hγPb, hγP1, rfl⟩ b ⟨γQ, hγQm, hγQb, hγQ1, rfl⟩
    have hP := trim_dev P hfmeas hfM hmf hγPm hγPb hγP1 hα1
    have hQ := trim_dev Q hfmeas hfM hmf hγQm hγQb hγQ1 hα1
    have hiP := inner_region P hφ hκ hγPm hγPb g
    have hiQ := inner_region Q hφ hκ hγQm hγQb g
    have hin : ⟪g, (∫ x, γP x • φ x ∂P) - ∫ x, γQ x • φ x ∂Q⟫_ℝ =
        (∫ x, γP x * f x ∂P) - ∫ x, γQ x * f x ∂Q := by
      rw [inner_sub_right, hiP, hiQ]; rfl
    have hcs := real_inner_le_norm g ((∫ x, γP x • φ x ∂P) - ∫ x, γQ x • φ x ∂Q)
    have hosc' : (⨆ z, f z) - (⨅ z, f z) ≤ 1 := hosc
    have hL : linL P Q f - α ≤ (1 - α) * (‖g‖ * ‖(∫ x, γP x • φ x ∂P) - ∫ x, γQ x • φ x ∂Q‖) := by
      have h3 : α * ((⨆ z, f z) - ⨅ z, f z) ≤ α := by nlinarith
      have h4 : linL P Q f - α ≤ (1 - α) * ((∫ x, γP x * f x ∂P) - ∫ x, γQ x * f x ∂Q) := by
        unfold linL; nlinarith [hP.2, hQ.1]
      rw [hin] at hcs
      exact h4.trans (mul_le_mul_of_nonneg_left hcs h1α.le)
    rw [div_div, div_le_iff₀ (mul_pos hgpos h1α)]
    linarith
  -- nonempty regions
  have hmem : ∀ μ : Measure 𝒳, IsProbabilityMeasure μ → (∫ x, (1 : ℝ) • φ x ∂μ) ∈ region φ α μ := by
    intro μ _
    refine ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, ?_⟩, by simp, rfl⟩
    rw [le_div_iff₀ h1α]; linarith
  have hne : {r | ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, r = ‖a - b‖}.Nonempty :=
    ⟨_, _, hmem P inferInstance, _, hmem Q inferInstance, rfl⟩
  have hD : (linL P Q f - α) / ‖g‖ / (1 - α) ≤ Dpop φ P Q α := by
    refine le_csInf hne ?_
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact hpair a ha b hb
  unfold Wave31ti.uPath
  rw [div_le_iff₀ h1α] at hD
  linarith

/-- Y9 `lap_ratio`. -/
theorem lap_ratio_route : Claims.lap_ratio := by
  intro 𝒳 H _ _ _ _ φ κ P Q _ _ α g hφ hκ hα0 hα1 hg hosc
  refine ⟨ratio_le_uPath hφ hκ hα0 hα1 hg hosc, fun htv e he => ?_⟩
  have h := ratio_le_uPath (P := P) (Q := Q) (α := tvDist P Q - e) hφ hκ (by linarith [he.2]) (by linarith [he.1]) hg hosc
  have heq : e - errL P Q (Wave31to.wit φ g) = linL P Q (Wave31to.wit φ g) - (tvDist P Q - e) := by
    unfold errL; ring
  rw [heq]; exact h

end StatFormal.Wave31tu.RouteP
