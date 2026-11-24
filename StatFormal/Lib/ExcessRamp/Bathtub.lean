import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The bathtub for sub-measures and the excess identity of a ramp

Library component (trimmed-mmd, Lemmas S4.17–S4.18 `lem:excessbathtub`, `lem:excessid`). Untrusted library code.

Setting: a finite measure `μ` (the law), a finite measure `μ'` (a part of it, for example a closest part `(1−α)g·P`), a
bounded measurable `f` and a cut `t`, with the two *bathtub conditions*
`μ' = μ` on `{f < t}` (as restrictions) and `μ'({f > t}) = 0`. No signed measure is used: every comparison goes through the
hinges `(t − f)_+` and `(f − t)_+`.

## Main results

* `integral_hinge_eq_of_restrict`, `integral_hinge_eq_zero_of_null`: the hinge `(t − f)_+` has the same integral under `μ'` and
  `μ`, and `(f − t)_+` integrates to `0` under `μ'`;
* `bathtub_le` / `bathtub_ge`: every measure `ν ≤ μ` has `∫ f dν ≥ ∫ f dμ' + t (ν(Ω) − μ'(Ω))` (and the mirror at a lower cut);
* `integral_min_eq` / `integral_max_eq`: `∫ min(f, t) dμ = (μ(Ω) − μ'(Ω)) t + ∫ f dμ'` for a probability `μ` (and the mirror);
* `ramp_excess_eq`: the excess identity of the ramp `(min(max(f,u),t) − u)/(t − u)` between two parts of equal mass.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.ExcessRamp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable real function is integrable for a finite measure. -/
lemma integrable_of_abs_le {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_mem_Icc (-C) C hf.aemeasurable (ae_of_all _ fun x => abs_le.1 (hC x))

/-- The hinge `(t − f)_+` is the indicator of `{f < t}` times `t − f`. -/
lemma integral_hinge_eq_setIntegral (ν : Measure Ω) {f : Ω → ℝ} (hf : Measurable f) (t : ℝ) :
    ∫ x, max (t - f x) 0 ∂ν = ∫ x in {x | f x < t}, (t - f x) ∂ν := by
  rw [← integral_indicator (measurableSet_lt hf measurable_const)]
  congr 1
  funext x
  by_cases h : f x < t
  · rw [indicator_of_mem (show x ∈ {x | f x < t} from h), max_eq_left (by linarith)]
  · rw [indicator_of_notMem (show x ∉ {x | f x < t} from h), max_eq_right (by linarith [not_lt.1 h])]

/-- Under `μ' = μ` on `{f < t}`, the hinge `(t − f)_+` has the same integral under `μ'` and `μ`. -/
lemma integral_hinge_eq_of_restrict {μ μ' : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) {t : ℝ}
    (hres : μ'.restrict {x | f x < t} = μ.restrict {x | f x < t}) :
    ∫ x, max (t - f x) 0 ∂μ' = ∫ x, max (t - f x) 0 ∂μ := by
  rw [integral_hinge_eq_setIntegral μ' hf, integral_hinge_eq_setIntegral μ hf, hres]

/-- Under `μ'({f > t}) = 0`, the hinge `(f − t)_+` integrates to `0` under `μ'`. -/
lemma integral_hinge_eq_zero_of_null {μ' : Measure Ω} {f : Ω → ℝ} {t : ℝ} (h0 : μ' {x | t < f x} = 0) :
    ∫ x, max (f x - t) 0 ∂μ' = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  simp only [not_lt] at hx
  simp only [Pi.zero_apply]
  exact max_eq_right (by linarith)

/-- `∫ f dν = t ν(Ω) + ∫ (f − t)_+ dν − ∫ (t − f)_+ dν` for a bounded measurable `f` and a finite `ν`. -/
lemma integral_eq_hinges (ν : Measure Ω) [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (t : ℝ) :
    ∫ x, f x ∂ν = t * ν.real univ + (∫ x, max (f x - t) 0 ∂ν) - ∫ x, max (t - f x) 0 ∂ν := by
  have hC' : ∀ x, |f x - t| ≤ C + |t| := fun x => (abs_sub _ _).trans (by linarith [hC x])
  have hp : Integrable (fun x => max (f x - t) 0) ν :=
    integrable_of_abs_le ((hf.sub measurable_const).max measurable_const) (C := C + |t|) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact (max_le (le_abs_self _) (abs_nonneg _)).trans (hC' x)
  have hn : Integrable (fun x => max (t - f x) 0) ν :=
    integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := C + |t|) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine (max_le (le_abs_self _) (abs_nonneg _)).trans ?_
      rw [abs_sub_comm]; exact hC' x
  have hpt : ∀ x, f x = t + max (f x - t) 0 - max (t - f x) 0 := fun x => by
    rcases le_total (f x) t with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  calc ∫ x, f x ∂ν = ∫ x, (t + max (f x - t) 0 - max (t - f x) 0) ∂ν := by
        congr 1; funext x; exact hpt x
    _ = t * ν.real univ + (∫ x, max (f x - t) 0 ∂ν) - ∫ x, max (t - f x) 0 ∂ν := by
        have h1 : Integrable (fun x => t + max (f x - t) 0) ν := (integrable_const t).add hp
        rw [integral_sub h1 hn, integral_add (integrable_const t) hp, integral_const, smul_eq_mul, mul_comm]

/-- **Bathtub for sub-measures** (Lemma S4.17 (a), first half). If `μ' = μ` on `{f < t}` and `μ'({f > t}) = 0`, every measure
`ν ≤ μ` has `∫ f dμ' + t (ν(Ω) − μ'(Ω)) ≤ ∫ f dν`. -/
theorem bathtub_le {μ μ' : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure μ'] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {t : ℝ} (hres : μ'.restrict {x | f x < t} = μ.restrict {x | f x < t})
    (h0 : μ' {x | t < f x} = 0) (ν : Measure Ω) (hν : ν ≤ μ) :
    (∫ x, f x ∂μ') + t * (ν.real univ - μ'.real univ) ≤ ∫ x, f x ∂ν := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hν
  have h1 := integral_eq_hinges μ' hf hC t
  have h2 := integral_eq_hinges ν hf hC t
  rw [integral_hinge_eq_zero_of_null h0, integral_hinge_eq_of_restrict hf hres] at h1
  have h3 : 0 ≤ ∫ x, max (f x - t) 0 ∂ν := integral_nonneg fun x => le_max_right _ _
  have hn : Integrable (fun x => max (t - f x) 0) μ := by
    refine integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := C + |t|) fun x => ?_
    rw [abs_of_nonneg (le_max_right _ _)]
    refine (max_le (le_abs_self _) (abs_nonneg _)).trans ?_
    exact (abs_sub _ _).trans (by linarith [hC x])
  have h4 : ∫ x, max (t - f x) 0 ∂ν ≤ ∫ x, max (t - f x) 0 ∂μ :=
    integral_mono_measure hν (ae_of_all _ fun x => le_max_right _ _) hn
  rw [h1, h2]
  linarith

/-- **Bathtub for sub-measures, lower cut** (Lemma S4.17 (a), second half). If `μ' = μ` on `{f > u}` and `μ'({f < u}) = 0`,
every measure `ν ≤ μ` has `∫ f dν ≤ ∫ f dμ' + u (ν(Ω) − μ'(Ω))`. -/
theorem bathtub_ge {μ μ' : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure μ'] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {u : ℝ} (hres : μ'.restrict {x | u < f x} = μ.restrict {x | u < f x})
    (h0 : μ' {x | f x < u} = 0) (ν : Measure Ω) (hν : ν ≤ μ) :
    ∫ x, f x ∂ν ≤ (∫ x, f x ∂μ') + u * (ν.real univ - μ'.real univ) := by
  have e1 : {x | -f x < -u} = {x | u < f x} := by ext x; simp only [mem_ofPred_eq, neg_lt_neg_iff]
  have e2 : {x | -u < -f x} = {x | f x < u} := by ext x; simp only [mem_ofPred_eq, neg_lt_neg_iff]
  have h := bathtub_le (μ := μ) (μ' := μ') (f := fun x => -f x) hf.neg (C := C) (fun x => by rw [abs_neg]; exact hC x)
    (t := -u) (by rw [e1]; exact hres) (by rw [e2]; exact h0) ν hν
  rw [integral_neg, integral_neg] at h
  linarith

/-- Under the bathtub conditions at `t`, `∫ min(f, t) dμ = (1 − μ'(Ω)) t + ∫ f dμ'` for a probability measure `μ`. -/
theorem integral_min_eq {μ μ' : Measure Ω} [IsProbabilityMeasure μ] [IsFiniteMeasure μ'] {f : Ω → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {t : ℝ} (hres : μ'.restrict {x | f x < t} = μ.restrict {x | f x < t})
    (h0 : μ' {x | t < f x} = 0) :
    ∫ x, min (f x) t ∂μ = (1 - μ'.real univ) * t + ∫ x, f x ∂μ' := by
  have h1 := integral_eq_hinges μ' hf hC t
  rw [integral_hinge_eq_zero_of_null h0, integral_hinge_eq_of_restrict hf hres] at h1
  have hn : Integrable (fun x => max (t - f x) 0) μ := by
    refine integrable_of_abs_le ((measurable_const.sub hf).max measurable_const) (C := C + |t|) fun x => ?_
    rw [abs_of_nonneg (le_max_right _ _)]
    refine (max_le (le_abs_self _) (abs_nonneg _)).trans ?_
    exact (abs_sub _ _).trans (by linarith [hC x])
  have hpt : ∀ x, min (f x) t = t - max (t - f x) 0 := fun x => by
    rcases le_total (f x) t with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  have h2 : ∫ x, min (f x) t ∂μ = t - ∫ x, max (t - f x) 0 ∂μ := by
    simp_rw [hpt]
    rw [integral_sub (integrable_const t) hn, integral_const, probReal_univ, one_smul]
  rw [h2]
  linarith

/-- Under the bathtub conditions at a lower cut `u`, `∫ max(f, u) dμ = (1 − μ'(Ω)) u + ∫ f dμ'` for a probability measure `μ`. -/
theorem integral_max_eq {μ μ' : Measure Ω} [IsProbabilityMeasure μ] [IsFiniteMeasure μ'] {f : Ω → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {u : ℝ} (hres : μ'.restrict {x | u < f x} = μ.restrict {x | u < f x})
    (h0 : μ' {x | f x < u} = 0) :
    ∫ x, max (f x) u ∂μ = (1 - μ'.real univ) * u + ∫ x, f x ∂μ' := by
  have e1 : {x | -f x < -u} = {x | u < f x} := by ext x; simp only [mem_ofPred_eq, neg_lt_neg_iff]
  have e2 : {x | -u < -f x} = {x | f x < u} := by ext x; simp only [mem_ofPred_eq, neg_lt_neg_iff]
  have h := integral_min_eq (μ := μ) (μ' := μ') (f := fun x => -f x) hf.neg (C := C)
    (fun x => by rw [abs_neg]; exact hC x) (t := -u) (by rw [e1]; exact hres) (by rw [e2]; exact h0)
  have hpt : ∀ x, min (-f x) (-u) = -max (f x) u := fun x => by rw [min_neg_neg]
  simp_rw [hpt] at h
  rw [integral_neg, integral_neg] at h
  linarith

/-- The clipped value as a sum: `min(max(a,u),t) = min(a,t) + (u − a)_+` for `u ≤ t`. -/
lemma clip_eq_min_add {a u t : ℝ} (hut : u ≤ t) : min (max a u) t = min a t + max (u - a) 0 := by
  rcases le_total a u with h | h
  · rw [max_eq_right h, min_eq_left hut, min_eq_left (h.trans hut), max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), add_zero]

/-- The clipped value as a difference: `min(max(a,u),t) = max(a,u) − (a − t)_+` for `u ≤ t`. -/
lemma clip_eq_max_sub {a u t : ℝ} (hut : u ≤ t) : min (max a u) t = max a u - max (a - t) 0 := by
  rcases le_total a t with h | h
  · rw [min_eq_left (max_le h hut), max_eq_right (show a - t ≤ 0 by linarith), sub_zero]
  · rw [max_eq_left (hut.trans h), min_eq_right h, max_eq_left (by linarith)]; ring

/-- **The excess identity of a ramp** (Lemma S4.18, general form). Let `μ, ν` be probability measures with parts `μ', ν'` of
equal mass `m`, satisfying the bathtub conditions at `t` (for `μ'`) and at `u < t` (for `ν'`). Then the ramp
`ψ = (min(max(f,u),t) − u)/(t − u)` has
`E_μ ψ − E_ν ψ − (1 − m) = (∫ f dμ' − ∫ f dν' + ∫ (u − f)_+ dμ + ∫ (f − t)_+ dν)/(t − u)`. -/
theorem ramp_excess_eq {μ ν μ' ν' : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {t u : ℝ} (hut : u < t)
    (hresμ : μ'.restrict {x | f x < t} = μ.restrict {x | f x < t}) (h0μ : μ' {x | t < f x} = 0)
    (hresν : ν'.restrict {x | u < f x} = ν.restrict {x | u < f x}) (h0ν : ν' {x | f x < u} = 0)
    (hmass : ν'.real univ = μ'.real univ) :
    (∫ x, (min (max (f x) u) t - u) / (t - u) ∂μ) - (∫ x, (min (max (f x) u) t - u) / (t - u) ∂ν) - (1 - μ'.real univ) =
      ((∫ x, f x ∂μ') - (∫ x, f x ∂ν') + (∫ x, max (u - f x) 0 ∂μ) + ∫ x, max (f x - t) 0 ∂ν) / (t - u) := by
  have htu : 0 < t - u := sub_pos.2 hut
  have hbd : ∀ {g : Ω → ℝ}, Measurable g → (∀ x, |g x| ≤ C + |t| + |u|) → ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ],
      Integrable g ρ := fun hg hb ρ _ => integrable_of_abs_le hg hb
  have hmin : Measurable fun x => min (f x) t := hf.min measurable_const
  have hmax : Measurable fun x => max (f x) u := hf.max measurable_const
  have hm1 : Measurable fun x => max (u - f x) 0 := (measurable_const.sub hf).max measurable_const
  have hm2 : Measurable fun x => max (f x - t) 0 := (hf.sub measurable_const).max measurable_const
  have hb_min : ∀ x, |min (f x) t| ≤ C + |t| + |u| := fun x => by
    have := hC x
    rcases le_total (f x) t with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg t, abs_nonneg u]
    · rw [min_eq_right h]; linarith [abs_nonneg t, abs_nonneg u, abs_nonneg (f x)]
  have hb_max : ∀ x, |max (f x) u| ≤ C + |t| + |u| := fun x => by
    have := hC x
    rcases le_total (f x) u with h | h
    · rw [max_eq_right h]; linarith [abs_nonneg t, abs_nonneg u, abs_nonneg (f x)]
    · rw [max_eq_left h]; linarith [abs_nonneg t, abs_nonneg u]
  have hb1 : ∀ x, |max (u - f x) 0| ≤ C + |t| + |u| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by linarith [abs_nonneg (f x), hC x, abs_nonneg t, abs_nonneg u])
    linarith [neg_abs_le (f x), hC x, le_abs_self u, abs_nonneg t]
  have hb2 : ∀ x, |max (f x - t) 0| ≤ C + |t| + |u| := fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by linarith [abs_nonneg (f x), hC x, abs_nonneg t, abs_nonneg u])
    linarith [le_abs_self (f x), hC x, neg_abs_le t, abs_nonneg u]
  -- the clipped integrals
  have hclipμ : ∫ x, min (max (f x) u) t ∂μ =
      (1 - μ'.real univ) * t + (∫ x, f x ∂μ') + ∫ x, max (u - f x) 0 ∂μ := by
    simp_rw [clip_eq_min_add hut.le]
    rw [integral_add (hbd hmin hb_min μ) (hbd hm1 hb1 μ), integral_min_eq hf hC hresμ h0μ]
  have hclipν : ∫ x, min (max (f x) u) t ∂ν =
      (1 - μ'.real univ) * u + (∫ x, f x ∂ν') - ∫ x, max (f x - t) 0 ∂ν := by
    simp_rw [clip_eq_max_sub hut.le]
    rw [integral_sub (hbd hmax hb_max ν) (hbd hm2 hb2 ν), integral_max_eq hf hC hresν h0ν, hmass]
  have hclipm : Measurable fun x => min (max (f x) u) t := hmax.min measurable_const
  have hbclip : ∀ x, |min (max (f x) u) t| ≤ C + |t| + |u| := fun x => by
    rw [clip_eq_max_sub hut.le]
    have := hb_max x; have := hb2 x
    rcases le_total (f x) t with h | h
    · rw [max_eq_right (by linarith : f x - t ≤ 0), sub_zero]; exact hb_max x
    · rw [max_eq_left (by linarith : 0 ≤ f x - t), max_eq_left (by linarith [hut] : u ≤ f x)]
      simp only [sub_sub_cancel]; linarith [abs_nonneg u, abs_nonneg (f x), hC x]
  have hrμ : ∫ x, (min (max (f x) u) t - u) / (t - u) ∂μ = ((∫ x, min (max (f x) u) t ∂μ) - u) / (t - u) := by
    rw [integral_div, integral_sub (hbd hclipm hbclip μ) (integrable_const u), integral_const, probReal_univ, one_smul]
  have hrν : ∫ x, (min (max (f x) u) t - u) / (t - u) ∂ν = ((∫ x, min (max (f x) u) t ∂ν) - u) / (t - u) := by
    rw [integral_div, integral_sub (hbd hclipm hbclip ν) (integrable_const u), integral_const, probReal_univ, one_smul]
  rw [hrμ, hrν, hclipμ, hclipν]
  field_simp
  ring

end StatFormal.ExcessRamp
