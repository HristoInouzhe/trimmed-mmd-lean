import StatFormal.Wave31tr.RouteExcessLaplace
import StatFormal.Lib.ExcessRamp.Quantile

/-!
# Wave 31tr route (E1): the Laplace kernel violates (Q) (T47 (a)) (untrusted)

`laplace_qdens_fails_route`: the printed cuts exist (library `ExcessRamp.exists_isLeast_quantile`,
`exists_isGreatest_quantile`), so Proposition 5.10 (iii) in its printed form (`excess_laplace_route`) gives `f⋆ ≤ t⋆` on `ℝ` and
`P(f⋆ = t⋆) ≥ α`. With `d⋆ = a − b = ‖a − b‖ f⋆` the cut is `T = ‖a − b‖t⋆`: an atom of mass `≥ α > 0`; it is the only
`(1−α)`-quantile of `d⋆(X)` (a larger `q` has `P(d⋆ < q) = 1 > 1 − α`, a smaller one contradicts the minimality of `t⋆`); and
(Q) at `T` would give `P(d⋆ = T) = ∫_{{T}} g = 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31tr.RouteExcess

open StatFormal.Wave30tq StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.ExcessRamp

theorem laplace_qdens_fails_route : Claims.laplace_qdens_fails := by
  intro H _ _ _ _ σ φ P Q _ _ α a b hσ hφ hgram hchar hα0 hαtv htv1 ha hb hab
  have hκ := norm_le_one_of_gram hgram
  have hα1 : α < 1 := hαtv.trans htv1
  have hD := dpop_pos_of_lt_tv hφ hκ hchar hα0.le hα1 hαtv
  have hc0 : 0 < ‖a - b‖ := hab ▸ hD
  set c := ‖a - b‖ with hc
  set F : ℝ → ℝ := fun x => ⟪c⁻¹ • (a - b), φ x⟫_ℝ with hF
  have hFm : Measurable F := measurable_wit hφ _
  have hFb : ∀ x, |F x| ≤ 1 := abs_wit_le hκ (norm_dir hc0)
  -- the printed cuts exist
  obtain ⟨t, ht⟩ := exists_isLeast_quantile P hFm hFb (p := 1 - α) (by linarith) (by linarith)
  obtain ⟨u, hu⟩ := exists_isGreatest_quantile Q hFm hFb (p := α) hα0.le hα1
  obtain ⟨hab', -, hPt, -⟩ := (excess_laplace_route).2 H σ φ P Q α a b t u hσ hφ hgram hchar (hα0.trans hαtv) htv1
    hα0.le hαtv ha hb hab ht hu
  have hup : ∀ x, F x ≤ t := fun x => (hab' x).2
  have key : ∀ x, ⟪a - b, φ x⟫_ℝ = c * F x := fun x => inner_eq_norm_mul_dir hc0 (φ x)
  have hset_eq : {x | ⟪a - b, φ x⟫_ℝ = c * t} = {x | F x = t} := by
    ext x; simp only [mem_ofPred_eq, key, mul_right_inj' hc0.ne']
  have hatom : α ≤ (P {x | ⟪a - b, φ x⟫_ℝ = c * t}).toReal := by
    rw [hset_eq]; exact hPt
  refine ⟨c * t, hatom, fun q => ⟨fun hq => ?_, fun hq => ?_⟩, fun r cc C hr hQd => ?_⟩
  · -- uniqueness of the `(1−α)`-quantile
    have hsets1 : {x | ⟪a - b, φ x⟫_ℝ < q} = {x | F x < q / c} := by
      ext x; simp only [mem_ofPred_eq, key, lt_div_iff₀ hc0, mul_comm]
    have hsets2 : {x | ⟪a - b, φ x⟫_ℝ ≤ q} = {x | F x ≤ q / c} := by
      ext x; simp only [mem_ofPred_eq, key, le_div_iff₀ hc0, mul_comm]
    have hq' : q / c ∈ quantileSet P F (1 - α) := by
      have h1 := hq.1; have h2 := hq.2
      rw [hsets1] at h1; rw [hsets2] at h2
      exact ⟨h1, h2⟩
    have hle : t ≤ q / c := ht.2 hq'
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have huniv : {x | F x < q / c} = univ := eq_univ_of_forall fun x => (hup x).trans_lt hlt
      have := hq'.1
      rw [huniv, probReal_univ] at this
      linarith
    · rw [heq]; field_simp
  · -- the cut is a quantile
    rw [hq]
    have hsets1 : {x | ⟪a - b, φ x⟫_ℝ < c * t} = {x | F x < t} := by
      ext x; simp only [mem_ofPred_eq, key, mul_lt_mul_iff_right₀ hc0]
    have hsets2 : {x | ⟪a - b, φ x⟫_ℝ ≤ c * t} = {x | F x ≤ t} := by
      ext x; simp only [mem_ofPred_eq, key, mul_le_mul_iff_right₀ hc0]
    refine ⟨?_, ?_⟩
    · rw [hsets1]; exact ht.1.1
    · rw [hsets2]; exact ht.1.2
  · -- (Q) at an atom is impossible
    obtain ⟨g, -, -, hgA⟩ := hQd
    have hsub : ({c * t} : Set ℝ) ⊆ Icc (c * t - r) (c * t + r) := by
      intro s hs; rw [mem_singleton_iff] at hs; subst hs; constructor <;> linarith
    have h0 := hgA {c * t} (measurableSet_singleton _) hsub
    rw [Measure.restrict_eq_zero.2 (Real.volume_singleton), lintegral_zero_measure] at h0
    have hpre : (fun x => ⟪a - b, φ x⟫_ℝ) ⁻¹' {c * t} = {x | ⟪a - b, φ x⟫_ℝ = c * t} := by
      ext x; simp
    rw [hpre] at h0
    rw [h0, ENNReal.toReal_zero] at hatom
    linarith

end StatFormal.Wave31tr.RouteExcess
