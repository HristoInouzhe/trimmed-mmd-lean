import StatFormal.Archive.OTFD.Wave16b.Statements

/-!
# Route: T `eq:dualmap` (untrusted)

Every coupling of `μ, ν` is carried by `S_u × S_v`, so the hypotheses hold `π₀`- and `π₁`-a.e. and `c₀, c₁` are integrable
under both plans. The chain `∫c₀dπ₁ ≤ ∫c₁dπ₁ + δ ≤ ∫c₁dπ₀ + δ ≤ ∫c₀dπ₀ + δ + δ'` (`δ' = δ`, resp. `0` one-sided), the
marginal identity `∫(c₀ − f − g)dπ₁ = ∫c₀dπ₁ − ∫f dμ − ∫g dν = ∫c₀dπ₁ − ∫c₀dπ₀`, and the gap bound give
`β∫‖v − Q₀u‖²dπ₁ ≤ δ + δ'`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.OTFD.Wave16b

open TauCeti (IsCoupling)

section
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

lemma coupling_ae_mem {μ : Measure U} {ν : Measure V} {γ : Measure (U × V)} (hγ : IsCoupling γ μ ν)
    {Su : Set U} {Sv : Set V} (hSu : MeasurableSet Su) (hSv : MeasurableSet Sv) (hμ : μ Suᶜ = 0)
    (hν : ν Svᶜ = 0) : ∀ᵐ z ∂γ, z.1 ∈ Su ∧ z.2 ∈ Sv := by
  have h1 : γ (Prod.fst ⁻¹' Suᶜ) = 0 := by
    rw [← Measure.fst_apply hSu.compl, hγ.fst_eq, hμ]
  have h2 : γ (Prod.snd ⁻¹' Svᶜ) = 0 := by
    rw [← Measure.snd_apply hSv.compl, hγ.snd_eq, hν]
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) (measure_union_null h1 h2)
  simp only [mem_setOf_eq, not_and_or] at hz
  rcases hz with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma coupling_prob {μ : Measure U} {ν : Measure V} [IsProbabilityMeasure μ] {γ : Measure (U × V)}
    (hγ : IsCoupling γ μ ν) : IsProbabilityMeasure γ := by
  constructor
  rw [← Measure.fst_univ, hγ.fst_eq, measure_univ]

lemma integral_fst {μ : Measure U} {ν : Measure V} {γ : Measure (U × V)} (hγ : IsCoupling γ μ ν)
    {f : U → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    Integrable (fun z : U × V => f z.1) γ ∧ ∫ z, f z.1 ∂γ = ∫ u, f u ∂μ := by
  have hmap : γ.map Prod.fst = μ := hγ.fst_eq
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hfi
    exact (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 hfi
  · rw [← hmap, integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

lemma integral_snd {μ : Measure U} {ν : Measure V} {γ : Measure (U × V)} (hγ : IsCoupling γ μ ν)
    {g : V → ℝ} (hg : Measurable g) (hgi : Integrable g ν) :
    Integrable (fun z : U × V => g z.2) γ ∧ ∫ z, g z.2 ∂γ = ∫ v, g v ∂ν := by
  have hmap : γ.map Prod.snd = ν := hγ.snd_eq
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hgi
    exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).1 hgi
  · rw [← hmap, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]

/-- Shared core: `c₀ ≤ c₁ + δ` and `c₁ ≤ c₀ + δ'` on the supports give `∫ D dπ₁ ≤ (δ + δ')/β`. -/
lemma dualmap_core [NormedAddCommGroup V] (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ]
    (c₀ c₁ : U × V → ℝ) (f : U → ℝ) (g : V → ℝ) (Q₀ : U → V) (π₀ π₁ : Measure (U × V)) (Su : Set U) (Sv : Set V)
    (β δ δ' : ℝ) (hc0 : Measurable c₀) (hc1 : Measurable c₁) (hf : Measurable f) (hg : Measurable g)
    (hD : Measurable (fun z : U × V => ‖z.2 - Q₀ z.1‖)) (hSu : MeasurableSet Su) (hSv : MeasurableSet Sv)
    (hμS : μ Suᶜ = 0) (hνS : ν Svᶜ = 0) (hopt0 : IsOptimalFor c₀ μ ν π₀) (hfi : Integrable f μ)
    (hgi : Integrable g ν) (hdual : ∫ u, f u ∂μ + ∫ v, g v ∂ν = ∫ z, c₀ z ∂π₀) (hβ : 0 < β)
    (hgap : ∀ u ∈ Su, ∀ v ∈ Sv, β * ‖v - Q₀ u‖ ^ 2 ≤ c₀ (u, v) - f u - g v)
    (hup : ∀ u ∈ Su, ∀ v ∈ Sv, c₀ (u, v) ≤ c₁ (u, v) + δ)
    (hdn : ∀ u ∈ Su, ∀ v ∈ Sv, c₁ (u, v) ≤ c₀ (u, v) + δ')
    (hopt1 : IsOptimalFor c₁ μ ν π₁) :
    Integrable (fun z : U × V => ‖z.2 - Q₀ z.1‖ ^ 2) π₁ ∧
      ∫ z, ‖z.2 - Q₀ z.1‖ ^ 2 ∂π₁ ≤ (δ + δ') / β := by
  obtain ⟨hπ₀, hi00, -⟩ := hopt0
  obtain ⟨hπ₁, hi11, hmin⟩ := hopt1
  haveI := coupling_prob hπ₀
  haveI := coupling_prob hπ₁
  have ae0 := coupling_ae_mem hπ₀ hSu hSv hμS hνS
  have ae1 := coupling_ae_mem hπ₁ hSu hSv hμS hνS
  -- integrability transfers
  have hi01 : Integrable c₀ π₁ := by
    refine ((hi11.norm.add (integrable_const (|δ| + |δ'|)))).mono' hc0.aestronglyMeasurable ?_
    filter_upwards [ae1] with z hz
    have a := hup z.1 hz.1 z.2 hz.2
    have b := hdn z.1 hz.1 z.2 hz.2
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor <;> cases abs_cases (c₁ z) <;> cases abs_cases δ <;> cases abs_cases δ' <;> linarith
  have hi10 : Integrable c₁ π₀ := by
    refine ((hi00.norm.add (integrable_const (|δ| + |δ'|)))).mono' hc1.aestronglyMeasurable ?_
    filter_upwards [ae0] with z hz
    have a := hup z.1 hz.1 z.2 hz.2
    have b := hdn z.1 hz.1 z.2 hz.2
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor <;> cases abs_cases (c₀ z) <;> cases abs_cases δ <;> cases abs_cases δ' <;> linarith
  -- the chain
  have I1 : ∫ z, c₀ z ∂π₁ ≤ ∫ z, c₁ z ∂π₁ + δ := by
    have := integral_mono_ae (g := fun z => c₁ z + δ) hi01 (hi11.add (integrable_const δ)) (by
      filter_upwards [ae1] with z hz
      exact hup z.1 hz.1 z.2 hz.2)
    have e : ∫ z, (c₁ z + δ) ∂π₁ = ∫ z, c₁ z ∂π₁ + δ := by
      rw [integral_add hi11 (integrable_const δ)]; simp
    rwa [e] at this
  have I2 : ∫ z, c₁ z ∂π₁ ≤ ∫ z, c₁ z ∂π₀ := hmin π₀ hπ₀ hi10
  have I3 : ∫ z, c₁ z ∂π₀ ≤ ∫ z, c₀ z ∂π₀ + δ' := by
    have := integral_mono_ae (g := fun z => c₀ z + δ') hi10 (hi00.add (integrable_const δ')) (by
      filter_upwards [ae0] with z hz
      exact hdn z.1 hz.1 z.2 hz.2)
    have e : ∫ z, (c₀ z + δ') ∂π₀ = ∫ z, c₀ z ∂π₀ + δ' := by
      rw [integral_add hi00 (integrable_const δ')]; simp
    rwa [e] at this
  -- the gap under π₁
  obtain ⟨hfi1, hfint⟩ := integral_fst hπ₁ hf hfi
  obtain ⟨hgi1, hgint⟩ := integral_snd hπ₁ hg hgi
  set G : U × V → ℝ := fun z => c₀ z - f z.1 - g z.2 with hG
  have hGi : Integrable G π₁ := (hi01.sub hfi1).sub hgi1
  have hGint : ∫ z, G z ∂π₁ = ∫ z, c₀ z ∂π₁ - ∫ z, c₀ z ∂π₀ := by
    simp only [hG]
    rw [integral_sub (f := fun z => c₀ z - f z.1) (g := fun z => g z.2) (hi01.sub hfi1) hgi1,
      integral_sub (f := c₀) (g := fun z => f z.1) hi01 hfi1, hfint, hgint, ← hdual]
    ring
  have hDm : Measurable (fun z : U × V => ‖z.2 - Q₀ z.1‖ ^ 2) := hD.pow_const 2
  have hDle : ∀ᵐ z ∂π₁, ‖z.2 - Q₀ z.1‖ ^ 2 ≤ G z / β := by
    filter_upwards [ae1] with z hz
    rw [le_div_iff₀ hβ, mul_comm]
    exact hgap z.1 hz.1 z.2 hz.2
  have hDi : Integrable (fun z : U × V => ‖z.2 - Q₀ z.1‖ ^ 2) π₁ := by
    refine (hGi.div_const β).mono' hDm.aestronglyMeasurable ?_
    filter_upwards [hDle] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  refine ⟨hDi, ?_⟩
  calc ∫ z, ‖z.2 - Q₀ z.1‖ ^ 2 ∂π₁ ≤ ∫ z, G z / β ∂π₁ := integral_mono_ae hDi (hGi.div_const β) hDle
    _ = (∫ z, G z ∂π₁) / β := integral_div β _
    _ ≤ (δ + δ') / β := by
        rw [hGint]
        exact div_le_div_of_nonneg_right (by linarith) hβ.le

end

theorem dualmap : Claims.dualmap := by
  intro U V _ _ _ μ ν _ c₀ c₁ f g Q₀ π₀ π₁ Su Sv β δ hc0 hc1 hf hg hD hSu hSv hμS hνS hopt0 hfi hgi hdual hβ hgap
    hpert hopt1
  have := dualmap_core μ ν c₀ c₁ f g Q₀ π₀ π₁ Su Sv β δ δ hc0 hc1 hf hg hD hSu hSv hμS hνS hopt0 hfi hgi hdual hβ
    hgap (fun u hu v hv => by have := hpert u hu v hv; rw [abs_le] at this; linarith)
    (fun u hu v hv => by have := hpert u hu v hv; rw [abs_le] at this; linarith) hopt1
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

theorem dualmap_one_sided : Claims.dualmap_one_sided := by
  intro U V _ _ _ μ ν _ c₀ c₁ f g Q₀ π₀ π₁ Su Sv β δ hc0 hc1 hf hg hD hSu hSv hμS hνS hopt0 hfi hgi hdual hβ hgap
    hpert hopt1
  have := dualmap_core μ ν c₀ c₁ f g Q₀ π₀ π₁ Su Sv β δ 0 hc0 hc1 hf hg hD hSu hSv hμS hνS hopt0 hfi hgi hdual hβ
    hgap (fun u hu v hv => by have := hpert u hu v hv; linarith)
    (fun u hu v hv => by have := hpert u hu v hv; linarith) hopt1
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

end StatFormal.OTFD.Wave16b
