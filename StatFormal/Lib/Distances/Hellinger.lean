import StatFormal.Lib.Distances.TV
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Bhattacharyya affinity, Hellinger distance and total variation

Library component F.H (part 4). Untrusted library code: no `Statements.lean` is involved.

## Conventions

For measures `μ, ν` we use the reference measure `μ + ν` and the real densities
`p = (dμ/d(μ+ν)).toReal`, `q = (dν/d(μ+ν)).toReal`.

* `bhatt μ ν := ∫ √(p q) d(μ + ν)` — the **Bhattacharyya affinity** (Hellinger affinity);
* `hellSq μ ν := 1 − bhatt μ ν` — the **squared Hellinger distance** in the normalisation
  `H² = ½ ∫ (√p − √q)²`, with values in `[0, 1]` for probability measures.

`tvDist` is the usual total variation `sup_A |μ A − ν A|` of
`StatFormal/Foundations/Distances/TV.lean`.

## Main results

* `bhatt_nonneg`, `bhatt_comm`, `bhatt_self` (`= μ(univ)`), `bhatt_le_one`;
* `bhatt_eq_integral_rnDeriv`: **independence of the reference** — any σ-finite `ρ` dominating
  both measures gives the same value (chain rule for Radon–Nikodym derivatives);
* `bhatt_eq_integral_of_withDensity`: the value for any density representation
  `μ = ρ.withDensity f`;
* `tvDist_eq_integral_max_sub`, `integral_abs_sub_eq_two_mul_tvDist`,
  `tvDist_eq_one_sub_integral_min`: `TV = ∫ (p − q)₊ dρ = ½ ∫ |p − q| dρ = 1 − ∫ min(p, q) dρ`
  for every σ-finite reference `ρ` (Hahn set `{q < p}`);
* `one_sub_bhatt_le_tvDist`: `1 − BC(μ, ν) ≤ TV(μ, ν)`;
* `tvDist_sq_le_one_sub_bhatt_sq`, `tvDist_le_sqrt_one_sub_bhatt_sq`:
  `TV(μ, ν) ≤ √(1 − BC(μ, ν)²)` (Cauchy–Schwarz on `|p − q| = |√p − √q| (√p + √q)`);
* `hellSq_eq_half_integral_sq`, `hellSq_nonneg`, `hellSq_le_one`, `hellSq_self`, `hellSq_comm`,
  `hellSq_le_tvDist`, `tvDist_le_sqrt_hellSq`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Distances

variable {α : Type*} [MeasurableSpace α]

/-- The **Bhattacharyya affinity** `∫ √(p q) d(μ + ν)`, with `p, q` the densities of `μ, ν` with
respect to `μ + ν`. -/
def bhatt (μ ν : Measure α) : ℝ :=
  ∫ x, √((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν)

/-- The **squared Hellinger distance** `1 − BC(μ, ν)` (equal to `½ ∫ (√p − √q)²` for
probability measures, see `hellSq_eq_half_integral_sq`). -/
def hellSq (μ ν : Measure α) : ℝ := 1 - bhatt μ ν

variable {μ ν : Measure α}

theorem bhatt_nonneg (μ ν : Measure α) : 0 ≤ bhatt μ ν :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

theorem bhatt_comm (μ ν : Measure α) : bhatt μ ν = bhatt ν μ := by
  unfold bhatt
  rw [add_comm μ ν]
  congr 1
  ext x
  rw [mul_comm]

/-! ### Pointwise inequalities -/

private theorem sqrt_mul_le_half_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    √(p * q) ≤ (p + q) / 2 := by
  rw [Real.sqrt_mul hp]
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  nlinarith [sq_nonneg (√p - √q)]

private theorem min_le_sqrt_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    min p q ≤ √(p * q) := by
  have hm : 0 ≤ min p q := le_min hp hq
  rw [← Real.sqrt_mul_self hm]
  exact Real.sqrt_le_sqrt (mul_le_mul (min_le_left p q) (min_le_right p q) hm hp)

private theorem max_sub_zero_eq (a b : ℝ) : max (a - b) 0 = a - min a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.2 h), min_eq_left h, sub_self]
  · rw [max_eq_left (sub_nonneg.2 h), min_eq_right h]

private theorem abs_eq_max_add_max (a b : ℝ) : |a - b| = max (a - b) 0 + max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h), max_eq_right (sub_nonpos.2 h),
      max_eq_left (sub_nonneg.2 h)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.2 h), max_eq_left (sub_nonneg.2 h),
      max_eq_right (sub_nonpos.2 h)]
    ring

/-! ### Densities with respect to a reference measure -/

section Reference

variable (ρ : Measure α) [SigmaFinite ρ]

omit [SigmaFinite ρ] in
private theorem measurable_dens (μ : Measure α) :
    Measurable fun x => (μ.rnDeriv ρ x).toReal :=
  (Measure.measurable_rnDeriv μ ρ).ennreal_toReal

omit [SigmaFinite ρ] in
private theorem integrable_dominated {p q f : α → ℝ} (hp : Integrable p ρ) (hq : Integrable q ρ)
    (hf : Measurable f) (h : ∀ x, |f x| ≤ 2 * (p x + q x)) : Integrable f ρ :=
  ((hp.add hq).const_mul 2).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x)

/-- **Independence of the reference measure**: for any σ-finite `ρ` dominating `μ` and `ν`, the
Bhattacharyya integral computed with the densities relative to `ρ` equals `bhatt μ ν`. -/
theorem bhatt_eq_integral_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≪ ρ)
    (hν : ν ≪ ρ) :
    bhatt μ ν = ∫ x, √((μ.rnDeriv ρ x).toReal * (ν.rnDeriv ρ x).toReal) ∂ρ := by
  have hac : μ + ν ≪ ρ := hμ.add_left hν
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ρ =ᵐ[ρ] μ.rnDeriv ρ :=
    Measure.rnDeriv_mul_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right ν)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ :=
    Measure.rnDeriv_mul_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' μ)
  rw [bhatt, ← integral_toReal_rnDeriv_mul hac]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx1, ← hx2]
  simp only [Pi.mul_apply, ENNReal.toReal_mul]
  have hr : 0 ≤ ((μ + ν).rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
  rw [show (μ.rnDeriv (μ + ν) x).toReal * ((μ + ν).rnDeriv ρ x).toReal *
      ((ν.rnDeriv (μ + ν) x).toReal * ((μ + ν).rnDeriv ρ x).toReal) =
      ((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal) *
      (((μ + ν).rnDeriv ρ x).toReal * ((μ + ν).rnDeriv ρ x).toReal) by ring,
    Real.sqrt_mul' _ (mul_self_nonneg _), Real.sqrt_mul_self hr, mul_comm]

/-- The Bhattacharyya affinity computed from any density representation. -/
theorem bhatt_eq_integral_of_withDensity [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hμ : μ = ρ.withDensity f)
    (hν : ν = ρ.withDensity g) :
    bhatt μ ν = ∫ x, √((f x).toReal * (g x).toReal) ∂ρ := by
  have hμρ : μ ≪ ρ := by rw [hμ]; exact withDensity_absolutelyContinuous ρ f
  have hνρ : ν ≪ ρ := by rw [hν]; exact withDensity_absolutelyContinuous ρ g
  rw [bhatt_eq_integral_rnDeriv ρ hμρ hνρ]
  have h1 : μ.rnDeriv ρ =ᵐ[ρ] f := by rw [hμ]; exact Measure.rnDeriv_withDensity ρ hf
  have h2 : ν.rnDeriv ρ =ᵐ[ρ] g := by rw [hν]; exact Measure.rnDeriv_withDensity ρ hg
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- **TV as the integral of the positive part**: `TV(μ, ν) = ∫ (p − q)₊ dρ` for probability
measures and any σ-finite reference `ρ` dominating both (Hahn set `{q < p}`). -/
theorem tvDist_eq_integral_max_sub [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    tvDist μ ν =
      ∫ x, max ((μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal) 0 ∂ρ := by
  set p : α → ℝ := fun x => (μ.rnDeriv ρ x).toReal with hp_def
  set q : α → ℝ := fun x => (ν.rnDeriv ρ x).toReal with hq_def
  have hpm : Measurable p := measurable_dens ρ μ
  have hqm : Measurable q := measurable_dens ρ ν
  have hpi : Integrable p ρ := Measure.integrable_toReal_rnDeriv
  have hqi : Integrable q ρ := Measure.integrable_toReal_rnDeriv
  have hp0 : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hq0 : ∀ x, 0 ≤ q x := fun _ => ENNReal.toReal_nonneg
  have hpA : ∀ A, ∫ x in A, p x ∂ρ = μ.real A := fun A => Measure.setIntegral_toReal_rnDeriv hμ A
  have hqA : ∀ A, ∫ x in A, q x ∂ρ = ν.real A := fun A => Measure.setIntegral_toReal_rnDeriv hν A
  have hp1 : ∫ x, p x ∂ρ = 1 := by
    rw [Measure.integral_toReal_rnDeriv hμ, probReal_univ]
  have hq1 : ∫ x, q x ∂ρ = 1 := by
    rw [Measure.integral_toReal_rnDeriv hν, probReal_univ]
  have hgi : Integrable (fun x => max (p x - q x) 0) ρ :=
    integrable_dominated ρ hpi hqi ((hpm.sub hqm).max measurable_const) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      have := hp0 x; have := hq0 x
      exact max_le (by linarith) (by linarith)
  have hgi' : Integrable (fun x => max (q x - p x) 0) ρ :=
    integrable_dominated ρ hpi hqi ((hqm.sub hpm).max measurable_const) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      have := hp0 x; have := hq0 x
      exact max_le (by linarith) (by linarith)
  have hgg : ∫ x, max (q x - p x) 0 ∂ρ = ∫ x, max (p x - q x) 0 ∂ρ := by
    have hdiff : ∫ x, (max (p x - q x) 0 - max (q x - p x) 0) ∂ρ = ∫ x, (p x - q x) ∂ρ := by
      congr 1; ext x
      rcases le_total (p x) (q x) with h | h
      · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring
      · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]; ring
    rw [integral_sub hgi hgi', integral_sub hpi hqi, hp1, hq1] at hdiff
    linarith
  -- the one-sided bound on a measurable set
  have hone : ∀ (u v : α → ℝ), Integrable u ρ → Integrable v ρ →
      Integrable (fun x => max (u x - v x) 0) ρ → ∀ A,
      ∫ x in A, u x ∂ρ - ∫ x in A, v x ∂ρ ≤ ∫ x, max (u x - v x) 0 ∂ρ := by
    intro u v hu hv hg A
    rw [← integral_sub hu.integrableOn hv.integrableOn]
    calc ∫ x in A, (u x - v x) ∂ρ ≤ ∫ x in A, max (u x - v x) 0 ∂ρ :=
          integral_mono (hu.sub hv).integrableOn hg.integrableOn
            fun x => le_max_left _ _
      _ ≤ ∫ x, max (u x - v x) 0 ∂ρ :=
          setIntegral_le_integral hg (ae_of_all _ fun x => le_max_right _ _)
  apply le_antisymm
  · refine tvDist_le_of_forall fun A _ => ?_
    have h1 := hone p q hpi hqi hgi A
    have h2 := hone q p hqi hpi hgi' A
    rw [hpA, hqA] at h1 h2
    rw [hgg] at h2
    rw [abs_le]; constructor <;> linarith
  · set s := {x | q x < p x} with hs_def
    have hs : MeasurableSet s := measurableSet_lt hqm hpm
    have h1 : ∫ x in s, max (p x - q x) 0 ∂ρ = ∫ x, max (p x - q x) 0 ∂ρ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hx' : p x ≤ q x := not_lt.1 hx
        exact max_eq_right (sub_nonpos.2 hx')
    have h2 : ∫ x in s, max (p x - q x) 0 ∂ρ = ∫ x in s, (p x - q x) ∂ρ :=
      setIntegral_congr_fun hs fun x hx => max_eq_left (sub_nonneg.2 (le_of_lt hx))
    rw [← h1, h2, integral_sub hpi.integrableOn hqi.integrableOn, hpA, hqA]
    exact (le_abs_self _).trans (abs_measureReal_sub_le_tvDist hs)

/-- `∫ |p − q| dρ = 2 · TV(μ, ν)`. -/
theorem integral_abs_sub_eq_two_mul_tvDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    ∫ x, |(μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal| ∂ρ = 2 * tvDist μ ν := by
  have h1 := tvDist_eq_integral_max_sub ρ hμ hν
  have h2 := tvDist_eq_integral_max_sub ρ hν hμ
  rw [tvDist_comm] at h2
  have hpi : Integrable (fun x => (μ.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hqi : Integrable (fun x => (ν.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hpm := measurable_dens ρ μ
  have hqm := measurable_dens ρ ν
  have hgi : Integrable (fun x => max ((μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal) 0) ρ :=
    integrable_dominated ρ hpi hqi ((hpm.sub hqm).max measurable_const) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      have : 0 ≤ (μ.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      have : 0 ≤ (ν.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      exact max_le (by linarith) (by linarith)
  have hgi' : Integrable (fun x => max ((ν.rnDeriv ρ x).toReal - (μ.rnDeriv ρ x).toReal) 0) ρ :=
    integrable_dominated ρ hpi hqi ((hqm.sub hpm).max measurable_const) fun x => by
      rw [abs_of_nonneg (le_max_right _ _)]
      have : 0 ≤ (μ.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      have : 0 ≤ (ν.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      exact max_le (by linarith) (by linarith)
  simp_rw [abs_eq_max_add_max]
  rw [integral_add hgi hgi', ← h1, ← h2]
  ring

/-- `TV(μ, ν) = 1 − ∫ min(p, q) dρ`. -/
theorem tvDist_eq_one_sub_integral_min [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    tvDist μ ν = 1 - ∫ x, min (μ.rnDeriv ρ x).toReal (ν.rnDeriv ρ x).toReal ∂ρ := by
  have hpi : Integrable (fun x => (μ.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hqi : Integrable (fun x => (ν.rnDeriv ρ x).toReal) ρ := Measure.integrable_toReal_rnDeriv
  have hmi : Integrable (fun x => min (μ.rnDeriv ρ x).toReal (ν.rnDeriv ρ x).toReal) ρ :=
    integrable_dominated ρ hpi hqi ((measurable_dens ρ μ).min (measurable_dens ρ ν)) fun x => by
      have h1 : 0 ≤ (μ.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      have h2 : 0 ≤ (ν.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
      rw [abs_of_nonneg (le_min h1 h2)]
      have := min_le_left (μ.rnDeriv ρ x).toReal (ν.rnDeriv ρ x).toReal
      linarith
  rw [tvDist_eq_integral_max_sub ρ hμ hν]
  simp_rw [max_sub_zero_eq]
  rw [integral_sub hpi hmi, Measure.integral_toReal_rnDeriv hμ, probReal_univ]

end Reference

/-! ### Basic properties of the affinity -/

/-- `BC(μ, μ) = μ(univ)`. -/
theorem bhatt_self (μ : Measure α) [IsFiniteMeasure μ] : bhatt μ μ = μ.real univ := by
  unfold bhatt
  have hac : μ ≪ μ + μ := Measure.AbsolutelyContinuous.rfl.add_right μ
  rw [← Measure.integral_toReal_rnDeriv hac]
  congr 1
  ext x
  exact Real.sqrt_mul_self ENNReal.toReal_nonneg

theorem bhatt_self_of_prob (μ : Measure α) [IsProbabilityMeasure μ] : bhatt μ μ = 1 := by
  rw [bhatt_self, probReal_univ]

/-- Notation-free facts about the densities relative to `μ + ν`. -/
private theorem dens_facts (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ ≪ μ + ν ∧ ν ≪ μ + ν ∧
    Integrable (fun x => (μ.rnDeriv (μ + ν) x).toReal) (μ + ν) ∧
    Integrable (fun x => (ν.rnDeriv (μ + ν) x).toReal) (μ + ν) ∧
    ∫ x, (μ.rnDeriv (μ + ν) x).toReal ∂(μ + ν) = 1 ∧
    ∫ x, (ν.rnDeriv (μ + ν) x).toReal ∂(μ + ν) = 1 ∧
    Integrable (fun x => √((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal))
      (μ + ν) := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hpi : Integrable (fun x => (μ.rnDeriv (μ + ν) x).toReal) (μ + ν) :=
    Measure.integrable_toReal_rnDeriv
  have hqi : Integrable (fun x => (ν.rnDeriv (μ + ν) x).toReal) (μ + ν) :=
    Measure.integrable_toReal_rnDeriv
  refine ⟨hμ, hν, hpi, hqi, ?_, ?_, ?_⟩
  · rw [Measure.integral_toReal_rnDeriv hμ, probReal_univ]
  · rw [Measure.integral_toReal_rnDeriv hν, probReal_univ]
  · refine integrable_dominated (μ + ν) hpi hqi
      ((measurable_dens _ μ).mul (measurable_dens _ ν)).sqrt fun x => ?_
    have h1 : 0 ≤ (μ.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ (ν.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have := sqrt_mul_le_half_add h1 h2
    linarith

/-- `BC(μ, ν) ≤ 1` for probability measures (AM–GM `√(pq) ≤ (p + q)/2`). -/
theorem bhatt_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    bhatt μ ν ≤ 1 := by
  obtain ⟨-, -, hpi, hqi, hp1, hq1, hsi⟩ := dens_facts μ ν
  unfold bhatt
  calc ∫ x, √((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν)
      ≤ ∫ x, ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) / 2 ∂(μ + ν) :=
        integral_mono hsi ((hpi.add hqi).div_const 2) fun x =>
          sqrt_mul_le_half_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = 1 := by
        rw [integral_div, integral_add hpi hqi, hp1, hq1]; norm_num

/-- **Lower TV bound**: `1 − BC(μ, ν) ≤ TV(μ, ν)` (from `min(p, q) ≤ √(pq)`). -/
theorem one_sub_bhatt_le_tvDist (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : 1 - bhatt μ ν ≤ tvDist μ ν := by
  obtain ⟨hμ, hν, hpi, hqi, -, -, hsi⟩ := dens_facts μ ν
  rw [tvDist_eq_one_sub_integral_min (μ + ν) hμ hν]
  have hmi : Integrable (fun x => min (μ.rnDeriv (μ + ν) x).toReal
      (ν.rnDeriv (μ + ν) x).toReal) (μ + ν) :=
    integrable_dominated _ hpi hqi ((measurable_dens _ μ).min (measurable_dens _ ν)) fun x => by
      have h1 : 0 ≤ (μ.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
      have h2 : 0 ≤ (ν.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
      rw [abs_of_nonneg (le_min h1 h2)]
      have := min_le_left (μ.rnDeriv (μ + ν) x).toReal (ν.rnDeriv (μ + ν) x).toReal
      linarith
  have : ∫ x, min (μ.rnDeriv (μ + ν) x).toReal (ν.rnDeriv (μ + ν) x).toReal ∂(μ + ν) ≤
      bhatt μ ν :=
    integral_mono hmi hsi fun x => min_le_sqrt_mul ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  linarith

/-- `∫ (√p − √q)² d(μ + ν) = 2 − 2 BC(μ, ν)` for probability measures. -/
theorem integral_sqrt_sub_sq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∫ x, (√(μ.rnDeriv (μ + ν) x).toReal - √(ν.rnDeriv (μ + ν) x).toReal) ^ 2 ∂(μ + ν) =
      2 - 2 * bhatt μ ν := by
  obtain ⟨-, -, hpi, hqi, hp1, hq1, hsi⟩ := dens_facts μ ν
  have hpt : ∀ x, (√(μ.rnDeriv (μ + ν) x).toReal - √(ν.rnDeriv (μ + ν) x).toReal) ^ 2 =
      ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) -
        2 * √((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal) := fun x => by
    have h1 : 0 ≤ (μ.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ (ν.rnDeriv (μ + ν) x).toReal := ENNReal.toReal_nonneg
    rw [Real.sqrt_mul h1]
    have e1 := Real.sq_sqrt h1
    have e2 := Real.sq_sqrt h2
    linear_combination e1 + e2
  simp_rw [hpt]
  have hpq : Integrable (fun x => (μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal)
      (μ + ν) := hpi.add hqi
  have hs2 : Integrable (fun x => 2 * √((μ.rnDeriv (μ + ν) x).toReal *
      (ν.rnDeriv (μ + ν) x).toReal)) (μ + ν) := hsi.const_mul 2
  rw [integral_sub hpq hs2, integral_add hpi hqi, integral_const_mul, hp1, hq1, bhatt]
  norm_num

/-- **Cauchy–Schwarz step**: `TV(μ, ν)² ≤ 1 − BC(μ, ν)²` for probability measures. -/
theorem tvDist_sq_le_one_sub_bhatt_sq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : tvDist μ ν ^ 2 ≤ 1 - bhatt μ ν ^ 2 := by
  obtain ⟨hμ, hν, hpi, hqi, hp1, hq1, hsi⟩ := dens_facts μ ν
  set B := bhatt μ ν with hB
  set T := tvDist μ ν with hT
  have hX := integral_abs_sub_eq_two_mul_tvDist (μ + ν) hμ hν
  set p : α → ℝ := fun x => (μ.rnDeriv (μ + ν) x).toReal with hp_def
  set q : α → ℝ := fun x => (ν.rnDeriv (μ + ν) x).toReal with hq_def
  have hp0 : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hq0 : ∀ x, 0 ≤ q x := fun _ => ENNReal.toReal_nonneg
  have hBdef : ∫ x, √(p x * q x) ∂(μ + ν) = B := rfl
  have hai : Integrable (fun x => |p x - q x|) (μ + ν) := (hpi.sub hqi).abs
  set C : ℝ := 2 + 2 * B with hC
  set X : ℝ := 2 * T with hXdef
  have hB0 : 0 ≤ B := bhatt_nonneg μ ν
  have hCpos : 0 < C := by rw [hC]; linarith
  -- pointwise identity
  have hpt : ∀ x, (C * |√(p x) - √(q x)| - X * (√(p x) + √(q x))) ^ 2 =
      (C ^ 2 + X ^ 2) * (p x + q x) + (2 * X ^ 2 - 2 * C ^ 2) * √(p x * q x) -
        2 * C * X * |p x - q x| := fun x => by
    have h1 := hp0 x
    have h2 := hq0 x
    rw [Real.sqrt_mul h1]
    have e1 := Real.sq_sqrt h1
    have e2 := Real.sq_sqrt h2
    have hab : |√(p x) - √(q x)| * (√(p x) + √(q x)) = |p x - q x| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (p x)) (Real.sqrt_nonneg (q x))),
        ← abs_mul]
      congr 1
      linear_combination e1 - e2
    have ha2 : |√(p x) - √(q x)| ^ 2 = (√(p x) - √(q x)) ^ 2 := sq_abs _
    linear_combination C ^ 2 * ha2 - 2 * C * X * hab + (C ^ 2 + X ^ 2) * (e1 + e2)
  have hnn : 0 ≤ ∫ x, (C * |√(p x) - √(q x)| - X * (√(p x) + √(q x))) ^ 2 ∂(μ + ν) :=
    integral_nonneg fun x => sq_nonneg _
  simp_rw [hpt] at hnn
  have i1 : Integrable (fun x => (C ^ 2 + X ^ 2) * (p x + q x)) (μ + ν) :=
    (hpi.add hqi).const_mul _
  have i2 : Integrable (fun x => (2 * X ^ 2 - 2 * C ^ 2) * √(p x * q x)) (μ + ν) :=
    hsi.const_mul _
  have i3 : Integrable (fun x => 2 * C * X * |p x - q x|) (μ + ν) := hai.const_mul _
  have i12 : Integrable (fun x => (C ^ 2 + X ^ 2) * (p x + q x) +
      (2 * X ^ 2 - 2 * C ^ 2) * √(p x * q x)) (μ + ν) := i1.add i2
  have hX' : ∫ x, |p x - q x| ∂(μ + ν) = X := hX
  rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add hpi hqi, hp1, hq1, hBdef, hX'] at hnn
  -- `0 ≤ C (C (2 − 2B) − X²)`
  have key : 0 ≤ C * (C * (2 - 2 * B) - X ^ 2) := by
    have : (C ^ 2 + X ^ 2) * (1 + 1) + (2 * X ^ 2 - 2 * C ^ 2) * B - 2 * C * X * X =
        C * (C * (2 - 2 * B) - X ^ 2) := by rw [hC]; ring
    rw [← this]; rw [hXdef] at hnn ⊢; linarith
  have h2 : X ^ 2 ≤ C * (2 - 2 * B) := by
    have := (mul_nonneg_iff_of_pos_left hCpos).1 key
    linarith
  rw [hXdef, hC] at h2
  nlinarith

/-- **Upper TV bound**: `TV(μ, ν) ≤ √(1 − BC(μ, ν)²)` for probability measures. -/
theorem tvDist_le_sqrt_one_sub_bhatt_sq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : tvDist μ ν ≤ √(1 - bhatt μ ν ^ 2) := by
  have h := Real.abs_le_sqrt (tvDist_sq_le_one_sub_bhatt_sq μ ν)
  rwa [abs_of_nonneg (tvDist_nonneg μ ν)] at h

/-! ### Squared Hellinger distance -/

theorem hellSq_eq_half_integral_sq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    hellSq μ ν =
      (∫ x, (√(μ.rnDeriv (μ + ν) x).toReal - √(ν.rnDeriv (μ + ν) x).toReal) ^ 2 ∂(μ + ν)) / 2 := by
  rw [integral_sqrt_sub_sq, hellSq]; ring

theorem hellSq_comm (μ ν : Measure α) : hellSq μ ν = hellSq ν μ := by
  rw [hellSq, hellSq, bhatt_comm]

theorem hellSq_self (μ : Measure α) [IsProbabilityMeasure μ] : hellSq μ μ = 0 := by
  rw [hellSq, bhatt_self_of_prob, sub_self]

theorem hellSq_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ hellSq μ ν :=
  sub_nonneg.2 (bhatt_le_one μ ν)

theorem hellSq_le_one (μ ν : Measure α) : hellSq μ ν ≤ 1 :=
  sub_le_self _ (bhatt_nonneg μ ν)

/-- `H²(μ, ν) ≤ TV(μ, ν)`. -/
theorem hellSq_le_tvDist (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    hellSq μ ν ≤ tvDist μ ν :=
  one_sub_bhatt_le_tvDist μ ν

/-- `TV(μ, ν) ≤ √(H² (2 − H²))`. -/
theorem tvDist_le_sqrt_hellSq (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : tvDist μ ν ≤ √(hellSq μ ν * (2 - hellSq μ ν)) := by
  have h := tvDist_le_sqrt_one_sub_bhatt_sq μ ν
  rwa [show 1 - bhatt μ ν ^ 2 = hellSq μ ν * (2 - hellSq μ ν) by rw [hellSq]; ring] at h

end StatFormal.Distances
