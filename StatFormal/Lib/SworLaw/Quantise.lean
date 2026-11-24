import StatFormal.Lib.SworLaw.Basic

/-!
# Stability of the law of distinct contexts under quantisation

Let `μ` be a probability law carried by `S`, and `q_k : Z → Z` measurable quantisers with `d(q_k x, x) ≤ δ_k → 0`
on `S` that merge two points of `S` only if they are `2δ_k`-close. Then `q_k` preserves the distinctness pattern of
`μ^{⊗M}`-almost every tuple eventually (collisions are kept, distinct points are eventually separated), so for every
`f` bounded and continuous on `D_M`:
* `∫ 1_{D_M} f ∘ q_k^{⊗M} dμ^{⊗M} → ∫ 1_{D_M} f dμ^{⊗M}` (dominated convergence);
* if `μ^{⊗M}(D_M) > 0`, then `(μ∘q_k⁻¹)^{⊗M}(D_M) > 0` eventually and
  `∫ f d(μ∘q_k⁻¹)^{⊗M}(· | D_M) → ∫ f dμ^{⊗M}(· | D_M)`.
This is the "collisions" and "risk" step of the proof of `cor:consistency` (context-distribution-ICL).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Foundations.SworLaw

variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- The quantiser hypotheses on `S`: measurable, `δ_k`-close to the identity, merging only `2δ_k`-close points. -/
structure IsQuantiser (S : Set Z) (q : ℕ → Z → Z) (δ : ℕ → ℝ) : Prop where
  meas : ∀ k, Measurable (q k)
  tendsto : Tendsto δ atTop (𝓝 0)
  close : ∀ k, ∀ x ∈ S, dist (q k x) x ≤ δ k
  merge : ∀ k, ∀ x ∈ S, ∀ y ∈ S, q k x = q k y → dist x y ≤ 2 * δ k

lemma ae_pi_mem {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z} (hS : MeasurableSet S)
    (hμS : μ Sᶜ = 0) : ∀ᵐ t ∂(Measure.pi fun _ : Fin M => μ), ∀ s, t s ∈ S := by
  rw [ae_all_iff]
  intro s
  rw [ae_iff]
  have h := (measurePreserving_eval (fun _ : Fin M => μ) s).measure_preimage hS.compl.nullMeasurableSet
  rw [hμS] at h
  exact h

/-- Pointwise: along a quantiser, `1_{D_M} f (q_k ∘ t) → 1_{D_M} f (t)` for every tuple `t ∈ S^M`. -/
lemma tendsto_indicator_quantise {M : ℕ} {S : Set Z} {q : ℕ → Z → Z} {δ : ℕ → ℝ} (hq : IsQuantiser S q δ)
    {f : (Fin M → Z) → ℝ} (hf : ContinuousOn f {t | Function.Injective t}) {t : Fin M → Z} (ht : ∀ s, t s ∈ S) :
    Tendsto (fun k => {t : Fin M → Z | Function.Injective t}.indicator f (fun s => q k (t s))) atTop
      (𝓝 ({t : Fin M → Z | Function.Injective t}.indicator f t)) := by
  set D := {t : Fin M → Z | Function.Injective t} with hD
  have hQt : Tendsto (fun k => fun s => q k (t s)) atTop (𝓝 t) := by
    refine tendsto_pi_nhds.2 fun s => ?_
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => hq.close k _ (ht s))
      hq.tendsto)
  by_cases hinj : Function.Injective t
  · have hev : ∀ᶠ k in atTop, Function.Injective fun s => q k (t s) := by
      have hpair : ∀ a b : Fin M, ∀ᶠ k in atTop, a ≠ b → q k (t a) ≠ q k (t b) := by
        intro a b
        by_cases hab : a = b
        · exact Eventually.of_forall fun _ h => absurd hab h
        · have hpos : 0 < dist (t a) (t b) := dist_pos.2 (hinj.ne hab)
          have hlim : Tendsto (fun k => 2 * δ k) atTop (𝓝 0) := by simpa using hq.tendsto.const_mul 2
          filter_upwards [hlim.eventually (gt_mem_nhds hpos)] with k hk _ heq
          have := hq.merge k _ (ht a) _ (ht b) heq
          linarith
      have hall : ∀ᶠ k in atTop, ∀ a b : Fin M, a ≠ b → q k (t a) ≠ q k (t b) := by
        rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b; exact hpair a b
      filter_upwards [hall] with k hk a b hab
      by_contra hne
      exact hk a b hne hab
    have hft : Tendsto (fun k => f fun s => q k (t s)) atTop (𝓝 (f t)) :=
      ((hf.continuousAt ((isOpen_injective M).mem_nhds hinj)).tendsto).comp hQt
    rw [indicator_of_mem (show t ∈ D from hinj)]
    refine hft.congr' ?_
    filter_upwards [hev] with k hk
    exact (indicator_of_mem (show (fun s => q k (t s)) ∈ D from hk) f).symm
  · rw [indicator_of_notMem (show t ∉ D from hinj)]
    have hall : ∀ k, (fun s => q k (t s)) ∉ D := by
      intro k hk
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      exact hne (hk (show q k (t a) = q k (t b) by rw [hab]))
    simp only [indicator_of_notMem (hall _)]
    exact tendsto_const_nhds

/-- Numerators: `∫ 1_{D_M} f ∘ q_k^{⊗M} dμ^{⊗M} → ∫ 1_{D_M} f dμ^{⊗M}`. -/
lemma tendsto_integral_indicator_quantise {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z}
    (hS : MeasurableSet S) (hμS : μ Sᶜ = 0) {q : ℕ → Z → Z} {δ : ℕ → ℝ} (hq : IsQuantiser S q δ)
    {f : (Fin M → Z) → ℝ} {C : ℝ} (hf : ContinuousOn f {t | Function.Injective t}) (hfb : ∀ t, |f t| ≤ C) :
    Tendsto (fun k => ∫ t, {t : Fin M → Z | Function.Injective t}.indicator f (fun s => q k (t s))
        ∂(Measure.pi fun _ : Fin M => μ)) atTop
      (𝓝 (∫ t, {t : Fin M → Z | Function.Injective t}.indicator f t ∂(Measure.pi fun _ : Fin M => μ))) := by
  set D := {t : Fin M → Z | Function.Injective t} with hD
  have hfm : Measurable (D.indicator f) :=
    measurable_indicator_of_continuousOn (isOpen_injective M).measurableSet hf
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) (integrable_const _)
    (fun k => Eventually.of_forall fun t => ?_) ?_
  · exact (hfm.comp (measurable_pi_iff.mpr fun s => (hq.meas k).comp (measurable_pi_apply s))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    by_cases h : (fun s => q k (t s)) ∈ D
    · rw [indicator_of_mem h]; exact hfb _
    · rw [indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hfb t)
  · filter_upwards [ae_pi_mem (M := M) μ hS hμS] with t ht
    exact tendsto_indicator_quantise hq hf ht

/-- The integral of `g` against `(μ ∘ q⁻¹)^{⊗M}` is the integral of `g ∘ q^{⊗M}` against `μ^{⊗M}`. -/
lemma integral_pi_map {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {q : Z → Z} (hq : Measurable q)
    {g : (Fin M → Z) → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin M => μ.map q) =
      ∫ t, g (fun s => q (t s)) ∂(Measure.pi fun _ : Fin M => μ) := by
  have hφ : Measurable fun (t : Fin M → Z) (s : Fin M) => q (t s) :=
    measurable_pi_iff.mpr fun s => hq.comp (measurable_pi_apply s)
  rw [← Measure.pi_map_pi (fun _ => hq.aemeasurable)]
  exact integral_map hφ.aemeasurable hg.aestronglyMeasurable

lemma real_pi_map_eq {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {q : Z → Z} (hq : Measurable q) :
    (Measure.pi fun _ : Fin M => μ.map q).real {t | Function.Injective t} =
      ∫ t, {t : Fin M → Z | Function.Injective t}.indicator (fun _ => (1 : ℝ)) (fun s => q (t s))
        ∂(Measure.pi fun _ : Fin M => μ) := by
  rw [← integral_pi_map μ hq (measurable_const.indicator (measurableSet_injective M)),
    integral_indicator (measurableSet_injective M), setIntegral_const, smul_eq_mul, mul_one]

/-- Denominators: if `μ^{⊗M}(D_M) > 0`, eventually `(μ ∘ q_k⁻¹)^{⊗M}(D_M) > 0`. -/
lemma eventually_pos_quantise {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z}
    (hS : MeasurableSet S) (hμS : μ Sᶜ = 0) {q : ℕ → Z → Z} {δ : ℕ → ℝ} (hq : IsQuantiser S q δ)
    (hpos : 0 < Measure.pi (fun _ : Fin M => μ) {t | Function.Injective t}) :
    ∀ᶠ k in atTop, 0 < Measure.pi (fun _ : Fin M => μ.map (q k)) {t | Function.Injective t} := by
  have hlim := tendsto_integral_indicator_quantise (M := M) μ hS hμS hq (f := fun _ => (1 : ℝ)) (C := 1)
    continuousOn_const (fun _ => by simp)
  rw [integral_indicator (measurableSet_injective M), setIntegral_const, smul_eq_mul, mul_one] at hlim
  have hreal : 0 < (Measure.pi fun _ : Fin M => μ).real {t | Function.Injective t} :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  filter_upwards [hlim.eventually (lt_mem_nhds hreal)] with k hk
  rw [← real_pi_map_eq μ (hq.meas k)] at hk
  exact (ENNReal.toReal_pos_iff.1 hk).1

/-- Conditional laws: `∫ f d(μ∘q_k⁻¹)^{⊗M}(· | D_M) → ∫ f dμ^{⊗M}(· | D_M)` when `μ^{⊗M}(D_M) > 0`. -/
theorem tendsto_integral_cond_quantise {M : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ] {S : Set Z}
    (hS : MeasurableSet S) (hμS : μ Sᶜ = 0) {q : ℕ → Z → Z} {δ : ℕ → ℝ} (hq : IsQuantiser S q δ)
    (hpos : 0 < Measure.pi (fun _ : Fin M => μ) {t | Function.Injective t})
    {f : (Fin M → Z) → ℝ} {C : ℝ} (hf : ContinuousOn f {t | Function.Injective t}) (hfb : ∀ t, |f t| ≤ C) :
    Tendsto (fun k => ∫ t, f t ∂(ProbabilityTheory.cond (Measure.pi fun _ : Fin M => μ.map (q k))
        {t | Function.Injective t})) atTop
      (𝓝 (∫ t, f t ∂(ProbabilityTheory.cond (Measure.pi fun _ : Fin M => μ) {t | Function.Injective t}))) := by
  set D := {t : Fin M → Z | Function.Injective t} with hD
  have hDm : MeasurableSet D := measurableSet_injective M
  have hfm : Measurable (D.indicator f) := measurable_indicator_of_continuousOn (isOpen_injective M).measurableSet hf
  have hnum := tendsto_integral_indicator_quantise (M := M) μ hS hμS hq hf hfb
  have hden := tendsto_integral_indicator_quantise (M := M) μ hS hμS hq (f := fun _ => (1 : ℝ)) (C := 1)
    continuousOn_const (fun _ => by simp)
  rw [integral_indicator hDm, setIntegral_const, smul_eq_mul, mul_one] at hden
  have hreal : (Measure.pi fun _ : Fin M => μ).real D ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)).ne'
  have hlim := (hden.inv₀ hreal).mul hnum
  rw [integral_cond_eq _ hDm]
  refine hlim.congr fun k => ?_
  rw [integral_cond_eq _ hDm, real_pi_map_eq μ (hq.meas k), integral_pi_map μ (hq.meas k) hfm]

end StatFormal.Foundations.SworLaw
