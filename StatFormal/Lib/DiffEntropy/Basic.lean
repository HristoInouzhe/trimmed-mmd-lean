import Mathlib

/-!
# Relative (differential) entropy against a reference measure, and the chain rule for products

For a σ-finite reference `λ` and a probability measure `ρ ≪ λ`, `relEnt ρ λ = −∫ log (dρ/dλ) dρ`
(`= −∫ llr ρ λ dρ`; with `λ = Leb` this is the differential entropy). `FiniteEnt ρ λ` is `ρ ≪ λ` with
`log (dρ/dλ) ∈ L¹(ρ)`: the Bochner integral is then not a junk value.

* `ac_prod_of_ac`: `π ≪ λ₁ ⊗ λ₂` and marginals `μ ≪ λ₁`, `ν ≪ λ₂` force `π ≪ μ ⊗ ν`.
* `llr_prod_ae`: `π`-a.e. `log dπ/d(λ₁⊗λ₂) = log dπ/d(μ⊗ν) + log dμ/dλ₁ (x) + log dν/dλ₂ (y)`.
* `klDiv_prod_eq`: with all three entropies finite, `KL(π ‖ μ ⊗ ν) = −Ent(π) + Ent(μ) + Ent(ν)` (finite).
* `finiteEnt_of_klDiv`: conversely `KL(π ‖ μ ⊗ ν) < ∞` with `Ent μ`, `Ent ν` finite gives `Ent π` finite.
* `gibbs_negPart`, `gibbs_le`: for a positive `g` with `∫ g dλ ≤ 1` and `log g ∈ L¹(ρ)`, the negative part of
  `log dρ/dλ` is `ρ`-integrable, and `Ent(ρ) ≤ −∫ log g dρ` (Gibbs' inequality).
* `finiteEnt_marginals`: if `Ent(π) > −∞` (positive part integrable) and the negative parts of the marginal log
  densities and of `log dπ/dΛ` are integrable, all three entropies are finite (subadditivity in integrability form).
-/

noncomputable section
open MeasureTheory Set InformationTheory Filter
open scoped ENNReal

set_option linter.style.longLine false

namespace StatFormal.DiffEntropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `Ent_λ(ρ) = −∫ log (dρ/dλ) dρ`. -/
def relEnt (ρ lam : Measure α) : ℝ := -∫ x, llr ρ lam x ∂ρ

/-- `ρ ≪ λ` and `log (dρ/dλ) ∈ L¹(ρ)`. -/
def FiniteEnt (ρ lam : Measure α) : Prop := ρ ≪ lam ∧ Integrable (llr ρ lam) ρ

/-! ### Elementary integrability helpers -/

lemma integrable_of_two_sided {μ : Measure α} {f G H : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hG : Integrable G μ) (hH : Integrable H μ) (h1 : ∀ᵐ x ∂μ, f x ≤ G x) (h2 : ∀ᵐ x ∂μ, -f x ≤ H x) :
    Integrable f μ := by
  refine Integrable.mono' (hG.abs.add hH.abs) hf ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  rcases le_total 0 (f x) with h | h
  · rw [abs_of_nonneg h]; linarith [le_abs_self (G x), abs_nonneg (H x)]
  · rw [abs_of_nonpos h]; linarith [le_abs_self (H x), abs_nonneg (G x)]

lemma integrable_of_pos_neg {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hp : Integrable (fun x => max (f x) 0) μ) (hn : Integrable (fun x => max (-f x) 0) μ) :
    Integrable f μ :=
  integrable_of_two_sided hf hp hn (Eventually.of_forall fun x => le_max_left _ _)
    (Eventually.of_forall fun x => le_max_left _ _)

lemma integrable_comp_fst {π : Measure (α × β)} {μ : Measure α} (h : π.map Prod.fst = μ) {f : α → ℝ}
    (hf : Integrable f μ) : Integrable (fun z => f z.1) π := by
  rw [← h] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 hf

lemma integrable_comp_snd {π : Measure (α × β)} {ν : Measure β} (h : π.map Prod.snd = ν) {f : β → ℝ}
    (hf : Integrable f ν) : Integrable (fun z => f z.2) π := by
  rw [← h] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).1 hf

lemma integral_comp_fst {π : Measure (α × β)} {μ : Measure α} (h : π.map Prod.fst = μ) {f : α → ℝ}
    (hf : Integrable f μ) : ∫ z, f z.1 ∂π = ∫ x, f x ∂μ := by
  rw [← h] at hf ⊢
  exact (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm

lemma integral_comp_snd {π : Measure (α × β)} {ν : Measure β} (h : π.map Prod.snd = ν) {f : β → ℝ}
    (hf : Integrable f ν) : ∫ z, f z.2 ∂π = ∫ y, f y ∂ν := by
  rw [← h] at hf ⊢
  exact (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm

lemma integrable_of_comp_fst {π : Measure (α × β)} {μ : Measure α} (h : π.map Prod.fst = μ) {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : Integrable (fun z => f z.1) π) : Integrable f μ := by
  rw [← h] at hfm ⊢
  exact (integrable_map_measure hfm measurable_fst.aemeasurable).2 hf

lemma integrable_of_comp_snd {π : Measure (α × β)} {ν : Measure β} (h : π.map Prod.snd = ν) {f : β → ℝ}
    (hfm : AEStronglyMeasurable f ν) (hf : Integrable (fun z => f z.2) π) : Integrable f ν := by
  rw [← h] at hfm ⊢
  exact (integrable_map_measure hfm measurable_snd.aemeasurable).2 hf

lemma ae_comp_fst {π : Measure (α × β)} {μ : Measure α} (h : π.map Prod.fst = μ) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂π, p z.1 := by
  rw [← h] at hp
  exact ae_of_ae_map measurable_fst.aemeasurable hp

lemma ae_comp_snd {π : Measure (α × β)} {ν : Measure β} (h : π.map Prod.snd = ν) {p : β → Prop}
    (hp : ∀ᵐ y ∂ν, p y) : ∀ᵐ z ∂π, p z.2 := by
  rw [← h] at hp
  exact ae_of_ae_map measurable_snd.aemeasurable hp

/-! ### Absolute continuity -/

variable {l₁ : Measure α} {l₂ : Measure β} [SigmaFinite l₁] [SigmaFinite l₂]

/-- The marginal of a measure `≪ λ₁ ⊗ λ₂` is `≪ λ₁`. -/
lemma ac_fst_of_ac {π : Measure (α × β)} (hπ : π ≪ l₁.prod l₂) : π.map Prod.fst ≪ l₁ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [Measure.map_apply measurable_fst hs]
  apply hπ
  rw [show Prod.fst ⁻¹' s = s ×ˢ (univ : Set β) by ext; simp, Measure.prod_prod, h0, zero_mul]

lemma ac_snd_of_ac {π : Measure (α × β)} (hπ : π ≪ l₁.prod l₂) : π.map Prod.snd ≪ l₂ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [Measure.map_apply measurable_snd hs]
  apply hπ
  rw [show Prod.snd ⁻¹' s = (univ : Set α) ×ˢ s by ext; simp, Measure.prod_prod, h0, mul_zero]

/-- `μ ⊗ ν = (λ₁ ⊗ λ₂).withDensity (m ⊗ n)`. -/
lemma prod_eq_withDensity {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν] (hμ : μ ≪ l₁)
    (hν : ν ≪ l₂) :
    μ.prod ν = (l₁.prod l₂).withDensity (fun z => μ.rnDeriv l₁ z.1 * ν.rnDeriv l₂ z.2) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ l₁ hμ, ← Measure.withDensity_rnDeriv_eq ν l₂ hν]
  exact prod_withDensity (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _)

/-- `π ≪ λ₁ ⊗ λ₂` with marginals `μ ≪ λ₁`, `ν ≪ λ₂` implies `π ≪ μ ⊗ ν`. -/
theorem ac_prod_of_ac {π : Measure (α × β)} {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (hπ : π ≪ l₁.prod l₂) (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hμ : μ ≪ l₁) (hν : ν ≪ l₂) :
    π ≪ μ.prod ν := by
  set f : α × β → ℝ≥0∞ := fun z => μ.rnDeriv l₁ z.1 * ν.rnDeriv l₂ z.2 with hf_def
  have hfm : Measurable f :=
    ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul ((Measure.measurable_rnDeriv _ _).comp measurable_snd)
  have hpos : ∀ᵐ z ∂π, f z ≠ 0 := by
    filter_upwards [ae_comp_fst h1 (Measure.rnDeriv_pos hμ), ae_comp_snd h2 (Measure.rnDeriv_pos hν)] with z h1 h2
    exact mul_ne_zero h1.ne' h2.ne'
  rw [prod_eq_withDensity hμ hν]
  intro s hs
  set t := toMeasurable ((l₁.prod l₂).withDensity f) s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have ht0 : ((l₁.prod l₂).withDensity f) t = 0 := by rw [measure_toMeasurable]; exact hs
  rw [withDensity_apply _ ht, lintegral_eq_zero_iff hfm] at ht0
  have h3 : ∀ᵐ z ∂π, z ∈ t → f z = 0 := by
    have := (ae_restrict_iff' ht).1 ht0
    exact hπ.ae_le this
  have h4 : ∀ᵐ z ∂π, z ∉ t := by
    filter_upwards [h3, hpos] with z h3 h4 hz using h4 (h3 hz)
  have : π t = 0 := measure_eq_zero_iff_ae_notMem.2 h4
  exact measure_mono_null (subset_toMeasurable _ _) this

/-! ### The a.e. chain rule -/

/-- `π`-a.e., `log dπ/d(λ₁⊗λ₂) = log dπ/d(μ⊗ν) + log dμ/dλ₁ + log dν/dλ₂`. -/
theorem llr_prod_ae {π : Measure (α × β)} {μ : Measure α} {ν : Measure β} [SigmaFinite π] [SigmaFinite μ]
    [SigmaFinite ν] (hπ : π ≪ μ.prod ν) (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hμ : μ ≪ l₁)
    (hν : ν ≪ l₂) :
    ∀ᵐ z ∂π, llr π (l₁.prod l₂) z = llr π (μ.prod ν) z + llr μ l₁ z.1 + llr ν l₂ z.2 := by
  have hπΛ : π ≪ l₁.prod l₂ := hπ.trans (hμ.prod hν)
  have hfm : Measurable (fun z : α × β => μ.rnDeriv l₁ z.1 * ν.rnDeriv l₂ z.2) :=
    ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul ((Measure.measurable_rnDeriv _ _).comp measurable_snd)
  have hc := Measure.rnDeriv_mul_rnDeriv (κ := l₁.prod l₂) hπ
  have hd : (μ.prod ν).rnDeriv (l₁.prod l₂) =ᵐ[l₁.prod l₂] fun z => μ.rnDeriv l₁ z.1 * ν.rnDeriv l₂ z.2 := by
    rw [prod_eq_withDensity hμ hν]
    exact Measure.rnDeriv_withDensity _ hfm
  filter_upwards [hπΛ.ae_le hc, hπΛ.ae_le hd, Measure.rnDeriv_pos hπ, hπ.ae_le (Measure.rnDeriv_lt_top π (μ.prod ν)),
    ae_comp_fst h1 (Measure.rnDeriv_pos hμ), ae_comp_fst h1 (hμ.ae_le (Measure.rnDeriv_lt_top μ l₁)),
    ae_comp_snd h2 (Measure.rnDeriv_pos hν), ae_comp_snd h2 (hν.ae_le (Measure.rnDeriv_lt_top ν l₂))]
    with z hc hd hr0 hr1 hm0 hm1 hn0 hn1
  simp only [llr_def]
  rw [← hc, Pi.mul_apply, hd, ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_assoc,
    Real.log_mul (mul_pos (ENNReal.toReal_pos hr0.ne' hr1.ne) (ENNReal.toReal_pos hm0.ne' hm1.ne)).ne'
      (ENNReal.toReal_pos hn0.ne' hn1.ne).ne',
    Real.log_mul (ENNReal.toReal_pos hr0.ne' hr1.ne).ne' (ENNReal.toReal_pos hm0.ne' hm1.ne).ne']

/-! ### `KL(π ‖ μ ⊗ ν) = −Ent(π) + Ent(μ) + Ent(ν)` -/

/-- Chain rule: if `π`, its marginals `μ`, `ν` have finite entropies relative to `λ₁ ⊗ λ₂`, `λ₁`, `λ₂`, then
`KL(π ‖ μ ⊗ ν)` is finite and equals `−Ent(π) + Ent(μ) + Ent(ν)`. -/
theorem klDiv_prod_eq {π : Measure (α × β)} [IsProbabilityMeasure π] {μ : Measure α} {ν : Measure β}
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hπ : FiniteEnt π (l₁.prod l₂)) (hμ : FiniteEnt μ l₁)
    (hν : FiniteEnt ν l₂) :
    klDiv π (μ.prod ν) ≠ ∞ ∧
      (klDiv π (μ.prod ν)).toReal = -relEnt π (l₁.prod l₂) + relEnt μ l₁ + relEnt ν l₂ := by
  have : IsProbabilityMeasure μ := by rw [← h1]; infer_instance
  have : IsProbabilityMeasure ν := by rw [← h2]; infer_instance
  have hac : π ≪ μ.prod ν := ac_prod_of_ac hπ.1 h1 h2 hμ.1 hν.1
  have hae := llr_prod_ae hac h1 h2 hμ.1 hν.1
  have hfst := integrable_comp_fst h1 hμ.2
  have hsnd := integrable_comp_snd h2 hν.2
  have heq : llr π (μ.prod ν) =ᵐ[π] fun z => llr π (l₁.prod l₂) z - llr μ l₁ z.1 - llr ν l₂ z.2 := by
    filter_upwards [hae] with z hz
    rw [hz]; ring
  have hint : Integrable (llr π (μ.prod ν)) π :=
    ((hπ.2.sub hfst).sub hsnd).congr heq.symm
  refine ⟨klDiv_ne_top hac hint, ?_⟩
  have e1 : ∫ z, (llr π (l₁.prod l₂) z - llr μ l₁ z.1 - llr ν l₂ z.2) ∂π =
      ∫ z, (llr π (l₁.prod l₂) z - llr μ l₁ z.1) ∂π - ∫ z, llr ν l₂ z.2 ∂π := integral_sub (hπ.2.sub hfst) hsnd
  have e2 : ∫ z, (llr π (l₁.prod l₂) z - llr μ l₁ z.1) ∂π =
      ∫ z, llr π (l₁.prod l₂) z ∂π - ∫ z, llr μ l₁ z.1 ∂π := integral_sub hπ.2 hfst
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_congr_ae heq, e1, e2, integral_comp_fst h1 hμ.2,
    integral_comp_snd h2 hν.2]
  simp only [relEnt]
  ring

/-- Conversely, `KL(π ‖ μ ⊗ ν) < ∞` with finite marginal entropies forces `Ent(π)` finite. -/
theorem finiteEnt_of_klDiv {π : Measure (α × β)} [IsProbabilityMeasure π] {μ : Measure α} {ν : Measure β}
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hkl : klDiv π (μ.prod ν) ≠ ∞) (hμ : FiniteEnt μ l₁)
    (hν : FiniteEnt ν l₂) : FiniteEnt π (l₁.prod l₂) := by
  have : IsProbabilityMeasure μ := by rw [← h1]; infer_instance
  have : IsProbabilityMeasure ν := by rw [← h2]; infer_instance
  rw [klDiv_ne_top_iff] at hkl
  have hae := llr_prod_ae hkl.1 h1 h2 hμ.1 hν.1
  refine ⟨hkl.1.trans (hμ.1.prod hν.1), ?_⟩
  exact ((hkl.2.add (integrable_comp_fst h1 hμ.2)).add (integrable_comp_snd h2 hν.2)).congr
    (by filter_upwards [hae] with z hz; rw [hz]; rfl)

/-- Subadditivity: `Ent(π) ≤ Ent(μ) + Ent(ν)` when all three are finite. -/
theorem relEnt_le_add {π : Measure (α × β)} [IsProbabilityMeasure π] {μ : Measure α} {ν : Measure β}
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hπ : FiniteEnt π (l₁.prod l₂)) (hμ : FiniteEnt μ l₁)
    (hν : FiniteEnt ν l₂) : relEnt π (l₁.prod l₂) ≤ relEnt μ l₁ + relEnt ν l₂ := by
  have := (klDiv_prod_eq h1 h2 hπ hμ hν).2
  have h0 : 0 ≤ (klDiv π (μ.prod ν)).toReal := ENNReal.toReal_nonneg
  linarith

/-! ### Gibbs' inequality -/

variable {lam : Measure α} [SigmaFinite lam]

/-- Pointwise Gibbs bound: `−log M ≤ −log g + g/M − 1` for `M, g > 0`. -/
lemma neg_log_le (M g : ℝ) (hM : 0 < M) (hg : 0 < g) : -Real.log M ≤ -Real.log g + g / M - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hg hM)
  rw [Real.log_div hg.ne' hM.ne'] at this
  linarith

lemma lintegral_ratio_le {ρ : Measure α} [SigmaFinite ρ] (hρ : ρ ≪ lam) {g : α → ℝ} (hgm : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x, ENNReal.ofReal (g x / (ρ.rnDeriv lam x).toReal) ∂ρ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂lam := by
  rw [← lintegral_rnDeriv_mul hρ (by fun_prop)]
  refine lintegral_mono fun x => ?_
  rcases eq_or_ne (ρ.rnDeriv lam x) 0 with h | h
  · simp [h]
  rcases eq_or_ne (ρ.rnDeriv lam x) ∞ with h' | h'
  · simp [h']
  have hpos : 0 < (ρ.rnDeriv lam x).toReal := ENNReal.toReal_pos h h'
  calc ρ.rnDeriv lam x * ENNReal.ofReal (g x / (ρ.rnDeriv lam x).toReal)
      = ENNReal.ofReal (ρ.rnDeriv lam x).toReal * ENNReal.ofReal (g x / (ρ.rnDeriv lam x).toReal) := by
        rw [ENNReal.ofReal_toReal h']
    _ = ENNReal.ofReal (g x) := by rw [← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne']
    _ ≤ _ := le_rfl

/-- Integrability of `g / (dρ/dλ)` against `ρ` when `∫ g dλ < ∞`. -/
lemma integrable_ratio {ρ : Measure α} [SigmaFinite ρ] (hρ : ρ ≪ lam) {g : α → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∫⁻ x, ENNReal.ofReal (g x) ∂lam ≤ 1) :
    Integrable (fun x => g x / (ρ.rnDeriv lam x).toReal) ρ ∧
      ∫ x, g x / (ρ.rnDeriv lam x).toReal ∂ρ ≤ 1 := by
  have hm : Measurable fun x => g x / (ρ.rnDeriv lam x).toReal :=
    hgm.div (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hnn : ∀ x, 0 ≤ g x / (ρ.rnDeriv lam x).toReal := fun x => div_nonneg (hg0 x) ENNReal.toReal_nonneg
  have hle := (lintegral_ratio_le hρ hgm hg0).trans hg1
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).2
    (hle.trans_lt ENNReal.one_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)

/-- Gibbs, negative part: for measurable `g > 0` with `∫ g dλ ≤ 1` and `log g ∈ L¹(ρ)`, the negative part of
`log dρ/dλ` is `ρ`-integrable (so `Ent_λ(ρ) < +∞` in the extended sense). -/
theorem gibbs_negPart {ρ : Measure α} [IsProbabilityMeasure ρ] (hρ : ρ ≪ lam) {g : α → ℝ} (hgm : Measurable g)
    (hg0 : ∀ x, 0 < g x) (hg1 : ∫⁻ x, ENNReal.ofReal (g x) ∂lam ≤ 1)
    (hlog : Integrable (fun x => Real.log (g x)) ρ) :
    Integrable (fun x => max (-llr ρ lam x) 0) ρ := by
  obtain ⟨hr, -⟩ := integrable_ratio hρ hgm (fun x => (hg0 x).le) hg1
  refine Integrable.mono' ((hlog.abs.add hr).add (integrable_const (1 : ℝ)))
    ((measurable_llr ρ lam).neg.max measurable_const).aestronglyMeasurable ?_
  filter_upwards [Measure.rnDeriv_pos hρ, hρ.ae_le (Measure.rnDeriv_lt_top ρ lam)] with x h0 h1
  have hM := ENNReal.toReal_pos h0.ne' h1.ne
  have key := neg_log_le _ _ hM (hg0 x)
  have hr0 : 0 ≤ g x / (ρ.rnDeriv lam x).toReal := div_nonneg (hg0 x).le hM.le
  simp only [llr_def, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by positivity)
  linarith [neg_le_abs (Real.log (g x))]

/-- Gibbs' inequality: `Ent_λ(ρ) ≤ −∫ log g dρ` for measurable `g > 0` with `∫ g dλ ≤ 1`. -/
theorem gibbs_le {ρ : Measure α} [IsProbabilityMeasure ρ] (hρ : FiniteEnt ρ lam) {g : α → ℝ} (hgm : Measurable g)
    (hg0 : ∀ x, 0 < g x) (hg1 : ∫⁻ x, ENNReal.ofReal (g x) ∂lam ≤ 1)
    (hlog : Integrable (fun x => Real.log (g x)) ρ) :
    relEnt ρ lam ≤ -∫ x, Real.log (g x) ∂ρ := by
  obtain ⟨hr, hr1⟩ := integrable_ratio hρ.1 hgm (fun x => (hg0 x).le) hg1
  have hmono : ∫ x, -llr ρ lam x ∂ρ ≤ ∫ x, (-Real.log (g x) + g x / (ρ.rnDeriv lam x).toReal - 1) ∂ρ := by
    refine integral_mono_ae hρ.2.neg ((hlog.neg.add hr).sub (integrable_const _)) ?_
    filter_upwards [Measure.rnDeriv_pos hρ.1, hρ.1.ae_le (Measure.rnDeriv_lt_top ρ lam)] with x h0 h1
    exact neg_log_le _ _ (ENNReal.toReal_pos h0.ne' h1.ne) (hg0 x)
  have e1 : ∫ x, (-Real.log (g x) + g x / (ρ.rnDeriv lam x).toReal - 1) ∂ρ =
      ∫ x, (-Real.log (g x) + g x / (ρ.rnDeriv lam x).toReal) ∂ρ - ∫ _x, (1 : ℝ) ∂ρ :=
    integral_sub (hlog.neg.add hr) (integrable_const _)
  have e2 : ∫ x, (-Real.log (g x) + g x / (ρ.rnDeriv lam x).toReal) ∂ρ =
      ∫ x, -Real.log (g x) ∂ρ + ∫ x, g x / (ρ.rnDeriv lam x).toReal ∂ρ := integral_add hlog.neg hr
  rw [e1, e2, integral_neg, integral_neg] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  simp only [relEnt]
  linarith

/-- Negative part of `log dπ/d(μ⊗ν)` is integrable (Gibbs with `g ≡ 1` against the probability `μ ⊗ ν`). -/
lemma negPart_llr_integrable {ρ σ : Measure α} [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] (h : ρ ≪ σ) :
    Integrable (fun x => max (-llr ρ σ x) 0) ρ :=
  gibbs_negPart h measurable_const (fun _ => one_pos) (by simp) (by simp)

/-! ### Finiteness of the marginal entropies -/

/-- If `Ent(π) > −∞` (positive part of `log dπ/dΛ` integrable) and the negative parts of `log dπ/dΛ`,
`log dμ/dλ₁`, `log dν/dλ₂` are integrable, then all three entropies are finite. -/
theorem finiteEnt_marginals {π : Measure (α × β)} [IsProbabilityMeasure π] {μ : Measure α} {ν : Measure β}
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) (hπ : π ≪ l₁.prod l₂)
    (hpos : Integrable (fun z => max (llr π (l₁.prod l₂) z) 0) π)
    (hneg : Integrable (fun z => max (-llr π (l₁.prod l₂) z) 0) π)
    (hμn : Integrable (fun x => max (-llr μ l₁ x) 0) μ) (hνn : Integrable (fun y => max (-llr ν l₂ y) 0) ν) :
    FiniteEnt π (l₁.prod l₂) ∧ FiniteEnt μ l₁ ∧ FiniteEnt ν l₂ := by
  have : IsProbabilityMeasure μ := by rw [← h1]; infer_instance
  have : IsProbabilityMeasure ν := by rw [← h2]; infer_instance
  have hμ : μ ≪ l₁ := h1 ▸ ac_fst_of_ac hπ
  have hν : ν ≪ l₂ := h2 ▸ ac_snd_of_ac hπ
  have hπi : Integrable (llr π (l₁.prod l₂)) π :=
    integrable_of_pos_neg (measurable_llr _ _).aestronglyMeasurable hpos hneg
  have hac : π ≪ μ.prod ν := ac_prod_of_ac hπ h1 h2 hμ hν
  have hae := llr_prod_ae hac h1 h2 hμ hν
  have hr := negPart_llr_integrable hac
  have hμf := integrable_comp_fst h1 hμn
  have hνf := integrable_comp_snd h2 hνn
  -- `log m(x) = log p − log r − log n(y) ≤ |log p| + r⁻ + n⁻(y)`
  have hm : Integrable (fun z => llr μ l₁ z.1) π := by
    refine integrable_of_two_sided ((measurable_llr _ _).comp measurable_fst).aestronglyMeasurable
      ((hπi.abs.add hr).add hνf) hμf ?_ (Eventually.of_forall fun z => le_max_left _ _)
    filter_upwards [hae] with z hz
    simp only [Pi.add_apply]
    have : llr μ l₁ z.1 = llr π (l₁.prod l₂) z - llr π (μ.prod ν) z - llr ν l₂ z.2 := by rw [hz]; ring
    rw [this]
    linarith [le_abs_self (llr π (l₁.prod l₂) z), le_max_left (-llr π (μ.prod ν) z) 0,
      le_max_left (-llr ν l₂ z.2) 0]
  have hn : Integrable (fun z => llr ν l₂ z.2) π := by
    refine integrable_of_two_sided ((measurable_llr _ _).comp measurable_snd).aestronglyMeasurable
      ((hπi.abs.add hr).add hμf) hνf ?_ (Eventually.of_forall fun z => le_max_left _ _)
    filter_upwards [hae] with z hz
    simp only [Pi.add_apply]
    have : llr ν l₂ z.2 = llr π (l₁.prod l₂) z - llr π (μ.prod ν) z - llr μ l₁ z.1 := by rw [hz]; ring
    rw [this]
    linarith [le_abs_self (llr π (l₁.prod l₂) z), le_max_left (-llr π (μ.prod ν) z) 0,
      le_max_left (-llr μ l₁ z.1) 0]
  exact ⟨⟨hπ, hπi⟩, ⟨hμ, integrable_of_comp_fst h1 (measurable_llr _ _).aestronglyMeasurable hm⟩,
    ⟨hν, integrable_of_comp_snd h2 (measurable_llr _ _).aestronglyMeasurable hn⟩⟩

end StatFormal.DiffEntropy
