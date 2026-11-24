import StatFormal.Archive.SBFairness.Decay.Statements
import TauCeti.MeasureTheory.OptimalTransport.Gluing

/-!
# Proofs — SB fairness repair: certified decay

Proofs of `Claims.gluing_exists`, `Claims.decay`, `Claims.tdelta_bound`
(paper proof `schrodinger_bridge_fairness_repair.tex:2721-2740`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.SBFairness.Decay

local notation "E" d => EuclideanSpace ℝ (Fin d)

theorem gluing_exists : Claims.gluing_exists := by
  intro d π₀ π₁ _ _ h
  obtain ⟨γ, hγ1, hγ2⟩ := TauCeti.Measure.exists_glue_of_standardBorel_right π₀
    (π₁.map Prod.swap) (by rw [Measure.fst_map_swap, h])
  refine ⟨γ.map (fun q => (q.1, q.2.2, q.2.1)), ?_, ?_⟩
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact hγ1
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hf : ((fun q : (E d) × (E d) × (E d) => (q.2.1, q.2.2)) ∘
        (fun q : (E d) × (E d) × (E d) => (q.1, q.2.2, q.2.1))) = Prod.swap ∘ Prod.snd := rfl
    rw [hf, ← Measure.map_map measurable_swap measurable_snd, ← Measure.snd, hγ2,
      Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

/-- A gluing of probability plans is a probability measure. -/
lemma isProbabilityMeasure_of_isGluing {d : ℕ} {Γ : Measure ((E d) × (E d) × (E d))}
    {π₀ π₁ : Measure ((E d) × (E d))} [IsProbabilityMeasure π₀] (hΓ : IsGluing Γ π₀ π₁) :
    IsProbabilityMeasure Γ := by
  constructor
  have h1 := congrArg (fun m => m univ) hΓ.1
  simp only [Measure.map_apply (by fun_prop : Measurable fun q : (E d) × (E d) × (E d) =>
    (q.1, q.2.2)) MeasurableSet.univ, preimage_univ, measure_univ] at h1
  exact h1

lemma measurable_edist_E (d : ℕ) : Measurable fun z : (E d) × (E d) => edist z.1 z.2 :=
  continuous_edist.measurable

/-- The core estimate for a single gluing. -/
lemma decay_gluing {d : ℕ} (π₀ π₁ : Measure ((E d) × (E d))) [IsProbabilityMeasure π₀]
    [IsProbabilityMeasure π₁] (ε t : ℝ) (Γ : Measure ((E d) × (E d) × (E d)))
    (hΓ : IsGluing Γ π₀ π₁) :
    wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ^ 2 ≤
      ENNReal.ofReal ((1 - t) ^ 2) * ∫⁻ q, edist q.1 q.2.1 ^ 2 ∂Γ := by
  have := isProbabilityMeasure_of_isGluing hΓ
  set s := Real.sqrt (ε * t * (1 - t))
  set γ := stdGaussian (E d)
  let F : ((E d) × (E d) × (E d)) × (E d) → (E d) × (E d) := fun x =>
    ((1 - t) • x.1.1 + t • x.1.2.2 + s • x.2, (1 - t) • x.1.2.1 + t • x.1.2.2 + s • x.2)
  have hF : Measurable F := by fun_prop
  have key : ∀ g : (E d) × (E d) × (E d) → (E d) × (E d), Measurable g →
      (Γ.map g).prod γ = (Γ.prod γ).map (Prod.map g id) := by
    intro g hg
    rw [← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id]
  have hcoup : IsCoupling ((Γ.prod γ).map F) (bridge π₀ ε t) (bridge π₁ ε t) := by
    constructor
    · rw [Measure.fst_map_prodMk (by fun_prop) (by fun_prop), bridge, ← hΓ.1,
        key _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    · rw [Measure.snd_map_prodMk (by fun_prop) (by fun_prop), bridge, ← hΓ.2,
        key _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
  have h := wassersteinEDist_rpow_le_lintegral (measurable_edist_E d) (p := 2) (by norm_num)
    (by norm_num) hcoup
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2, ENNReal.rpow_two] at h
  refine h.trans (le_of_eq ?_)
  simp_rw [ENNReal.rpow_two]
  rw [lintegral_map (by fun_prop) hF]
  have hpt : ∀ x : ((E d) × (E d) × (E d)) × (E d),
      edist (F x).1 (F x).2 ^ 2 = ENNReal.ofReal ((1 - t) ^ 2) * edist x.1.1 x.1.2.1 ^ 2 := by
    intro x
    simp only [F]
    rw [edist_add_right, edist_add_right, edist_smul₀, ENNReal.smul_def, smul_eq_mul, mul_pow]
    congr 1
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm,
      enorm_eq_nnnorm]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  have hm : Measurable fun q : (E d) × (E d) × (E d) => edist q.1 q.2.1 ^ 2 := by fun_prop
  rw [← (measurePreserving_fst (μ := Γ) (ν := γ)).lintegral_comp hm]

/-- At `t = 1` the bridge is the common second marginal. -/
lemma bridge_one {d : ℕ} (π : Measure ((E d) × (E d))) [IsProbabilityMeasure π] (ε : ℝ) :
    bridge π ε 1 = π.snd := by
  have hf : (fun p : ((E d) × (E d)) × (E d) =>
      (1 - 1 : ℝ) • p.1.1 + (1 : ℝ) • p.1.2 + Real.sqrt (ε * 1 * (1 - 1)) • p.2) =
      Prod.snd ∘ Prod.fst := by
    funext p; simp
  rw [bridge, hf, ← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.snd]

theorem decay : Claims.decay := by
  intro d π₀ π₁ _ _ ε t h _ ht
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · rw [bridge_one, bridge_one, h, wassersteinEDist_self_of_measurable_edist (measurable_edist_E d)]
    simp
  · have hc0 : ENNReal.ofReal ((1 - t) ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : 0 < 1 - t := by linarith
      positivity
    rw [Gsq, ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine le_iInf fun Γ => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    exact le_iInf fun hΓ => decay_gluing π₀ π₁ ε t Γ hΓ

theorem tdelta_bound : Claims.tdelta_bound := by
  intro d π₀ π₁ _ _ ε δ h hε hG hδ hδG
  set G := Real.sqrt (Gsq π₀ π₁).toReal with hGdef
  have hGpos : 0 < G := hδ.trans hδG
  have hq0 : 0 < δ / G := div_pos hδ hGpos
  have hq1 : δ / G < 1 := (div_lt_one hGpos).2 hδG
  refine csInf_le ⟨0, fun t ht => ht.1.1⟩ ⟨⟨by linarith, by linarith⟩, ?_⟩
  have hd := decay d π₀ π₁ ε (1 - δ / G) h hε ⟨by linarith, by linarith⟩
  have hGsq : Gsq π₀ π₁ = ENNReal.ofReal (G ^ 2) := by
    rw [hGdef, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hG]
  rw [hGsq, ← ENNReal.ofReal_mul (by positivity), sub_sub_cancel, div_pow,
    div_mul_cancel₀ _ (by positivity), ENNReal.ofReal_pow hδ.le] at hd
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hd

end StatFormal.SBFairness.Decay
