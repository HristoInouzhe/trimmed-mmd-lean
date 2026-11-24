import StatFormal.Archive.Wave8a.Statements
import StatFormal.Archive.TrimmedMMD.Concentration.Region

/-!
# Route: trimmed MMD `lem:cvar` (support function = CVaR)

1. Easy half (`integral_mul_le_cvar`): every admissible `g` has `E[gY] ≤ t + β E(Y − t)₊` for every `t`.
2. Attainment (`exists_cvar_witness`): an upper-tail quantile `q` and a bang-bang `g` (fractional on `{Y = q}`)
   with `E[gY] = q + β E(Y − q)₊`. Hence the common value is a maximum of the left and a minimum of the right.
3. For `f ∈ H`: `⟪∫ g φ, f⟫ = ∫ g ⟪f, φ⟫` (`inner_integral_smul`), and `|⟪f, φ⟫| ≤ κ‖f‖`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace StatFormal.Wave8a

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.ZeroSet

theorem cvar_core {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P]
    {Y : 𝒳 → ℝ} (hY : Measurable Y) {κ : ℝ} (hYb : ∀ x, |Y x| ≤ κ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ v : ℝ, IsGreatest {r | ∃ g, IsTrimDensity P α g ∧ r = ∫ x, g x * Y x ∂P} v ∧
      IsLeast (range fun t : ℝ => t + 1 / (1 - α) * ∫ x, max (Y x - t) 0 ∂P) v := by
  have hβ : 1 ≤ 1 / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨q, -, g, hg, hgb, hg1, hval⟩ := exists_cvar_witness P hY hYb hβ
  refine ⟨∫ x, g x * Y x ∂P, ⟨⟨g, ⟨hg, hgb, hg1⟩, rfl⟩, ?_⟩, ⟨⟨q, hval.symm⟩, ?_⟩⟩
  · rintro _ ⟨g', ⟨hg', hgb', hg1'⟩, rfl⟩
    rw [hval]
    exact integral_mul_le_cvar P hY hYb hg' hgb' hg1' q
  · rintro _ ⟨t, rfl⟩
    exact integral_mul_le_cvar P hY hYb hg hgb hg1 t

theorem cvar_bounded : Claims.cvar_bounded := by
  intro 𝒳 _ P _ f α hf ⟨C, hC⟩ hα0 hα1
  exact cvar_core P hf hC hα0 hα1

theorem cvar_rkhs : Claims.cvar_rkhs := by
  intro 𝒳 H _ _ _ _ P _ φ κ α f hφ hκ hα0 hα1
  have hY : Measurable fun x => ⟪f, φ x⟫_ℝ :=
    (stronglyMeasurable_const.inner hφ).measurable
  have hYb : ∀ x, |⟪f, φ x⟫_ℝ| ≤ ‖f‖ * κ := fun x =>
    (abs_real_inner_le_norm f (φ x)).trans (mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg f))
  obtain ⟨v, hv1, hv2⟩ := cvar_core P hY hYb hα0 hα1
  have hset : (fun a => ⟪a, f⟫_ℝ) '' region φ α P =
      {r | ∃ g, IsTrimDensity P α g ∧ r = ∫ x, g x * ⟪f, φ x⟫_ℝ ∂P} := by
    ext r
    constructor
    · rintro ⟨_, ⟨g, hg, hgb, hg1, rfl⟩, rfl⟩
      refine ⟨g, ⟨hg, hgb, hg1⟩, ?_⟩
      simp only
      rw [real_inner_comm, inner_integral_smul P hφ hκ hg hgb f]
    · rintro ⟨g, ⟨hg, hgb, hg1⟩, rfl⟩
      refine ⟨∫ x, g x • φ x ∂P, ⟨g, hg, hgb, hg1, rfl⟩, ?_⟩
      simp only
      rw [real_inner_comm, inner_integral_smul P hφ hκ hg hgb f]
  exact ⟨v, hset ▸ hv1, hv1, hv2⟩

end StatFormal.Wave8a
