import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31to.Proofs
import StatFormal.Lib.BandLimited.Density
import StatFormal.Lib.TVMeasure.Basic

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y6 `lap_err` (S4 :1048-1056, `eq:laperr`)

For Lebesgue densities `p, q` of `P, Q` and a bounded measurable `f` with `osc(f) ≤ 1`, with `M = sup f`, `m = inf f`,
`err(f) = α⋆(1 − (M − m)) + ∫(M − f)(p − q)₊ + ∫(f − m)(q − p)₊`, the three terms are nonnegative, `0 ≤ err(f) ≤ 2`, and `err` is
the frozen `errFn` on `[0,1]`-valued `f`.

Route (printed): `α⋆ = ∫(p − q)₊ = ∫(q − p)₊` (31tq Q1 `tv_density`, both orders), `∫ f dP − ∫ f dQ = ∫ f(p − q)₊ − ∫ f(q − p)₊`;
the last conjunct is the certified `Wave31to.newapprox_err`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances

/-- Y6 `lap_err`. -/
theorem lap_err_route : Claims.lap_err := by
  intro P Q _ _ p q f hpm hqm hp0 hq0 hP hQ hfm hfb hosc
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨hpi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hpm hp0 hP
  obtain ⟨hqi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hqm hq0 hQ
  have htvPQ : tvDist P Q = ∫ x, max (p x - q x) 0 :=
    (StatFormal.Wave31tq.tv_density.2 ℝ P Q p q hpm hqm hp0 hq0 hP hQ).2.2.2.1
  have htvQP : tvDist P Q = ∫ x, max (q x - p x) 0 := by
    rw [tvDist_comm]; exact (StatFormal.Wave31tq.tv_density.2 ℝ Q P q p hqm hpm hq0 hp0 hQ hP).2.2.2.1
  have hbdA : BddAbove (range f) := ⟨C, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (hC x)).2⟩
  have hbdB : BddBelow (range f) := ⟨-C, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (hC x)).1⟩
  set M := ⨆ z, f z with hM
  set m := ⨅ z, f z with hm
  have hfM : ∀ x, f x ≤ M := fun x => le_ciSup hbdA x
  have hfm' : ∀ x, m ≤ f x := fun x => ciInf_le hbdB x
  have hosc' : Wave31to.oscFn f = M - m := rfl
  -- integrability
  have hfae : AEStronglyMeasurable f volume := hfm.aestronglyMeasurable
  have hfbd : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ C := ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x
  have hai : Integrable (fun x => max (p x - q x) 0) := by
    refine hpi.mono' ((hpm.sub hqm).max measurable_const).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hq0 x]) (hp0 x)
  have hbi : Integrable (fun x => max (q x - p x) 0) := by
    refine hqi.mono' ((hqm.sub hpm).max measurable_const).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hp0 x]) (hq0 x)
  have hfai : Integrable (fun x => f x * max (p x - q x) 0) := hai.bdd_mul hfae hfbd
  have hfbi : Integrable (fun x => f x * max (q x - p x) 0) := hbi.bdd_mul hfae hfbd
  have hIP : ∫ x, f x ∂P = ∫ x, f x * p x := by
    rw [hP]; exact StatFormal.TVMeasure.integral_withDensity_ofReal hpm hp0 f
  have hIQ : ∫ x, f x ∂Q = ∫ x, f x * q x := by
    rw [hQ]; exact StatFormal.TVMeasure.integral_withDensity_ofReal hqm hq0 f
  have hfpi : Integrable (fun x => f x * p x) := hpi.bdd_mul hfae hfbd
  have hfqi : Integrable (fun x => f x * q x) := hqi.bdd_mul hfae hfbd
  have hL : linL P Q f = (∫ x, f x * max (p x - q x) 0) - ∫ x, f x * max (q x - p x) 0 := by
    unfold linL
    rw [hIP, hIQ, ← integral_sub hfpi hfqi, ← integral_sub hfai hfbi]
    congr 1; ext x
    rcases le_total (q x) (p x) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hT1 : ∫ x, (M - f x) * max (p x - q x) 0 = M * tvDist P Q - ∫ x, f x * max (p x - q x) 0 := by
    simp_rw [sub_mul]
    rw [integral_sub (hai.const_mul M) hfai, integral_const_mul, htvPQ]
  have hT2 : ∫ x, (f x - m) * max (q x - p x) 0 = (∫ x, f x * max (q x - p x) 0) - m * tvDist P Q := by
    simp_rw [sub_mul]
    rw [integral_sub hfbi (hbi.const_mul m), integral_const_mul, htvQP]
  have hT1nn : 0 ≤ ∫ x, (M - f x) * max (p x - q x) 0 :=
    integral_nonneg fun x => mul_nonneg (sub_nonneg.mpr (hfM x)) (le_max_right _ _)
  have hT2nn : 0 ≤ ∫ x, (f x - m) * max (q x - p x) 0 :=
    integral_nonneg fun x => mul_nonneg (sub_nonneg.mpr (hfm' x)) (le_max_right _ _)
  have hα0 : 0 ≤ tvDist P Q := tvDist_nonneg P Q
  have hα1 : tvDist P Q ≤ 1 := tvDist_le_one
  have hid : errL P Q f = tvDist P Q * (1 - Wave31to.oscFn f) + (∫ x, (M - f x) * max (p x - q x) 0) +
      ∫ x, (f x - m) * max (q x - p x) 0 := by
    rw [errL, hL, hT1, hT2, hosc']; ring
  have hT0 : 0 ≤ tvDist P Q * (1 - Wave31to.oscFn f) := mul_nonneg hα0 (by linarith)
  -- `L(f) ≥ m − M ≥ −1`
  have hfPi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hfQi : Integrable f Q := Integrable.of_bound hfm.aestronglyMeasurable C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hPm : m ≤ ∫ x, f x ∂P := by
    have h := integral_mono (integrable_const m) hfPi hfm'
    simpa using h
  have hQM : ∫ x, f x ∂Q ≤ M := by
    have h := integral_mono hfQi (integrable_const M) hfM
    simpa using h
  have herr2 : errL P Q f ≤ 2 := by
    rw [errL, linL]; rw [hosc'] at hosc; linarith
  refine ⟨hid, hT0, hT1nn, hT2nn, by rw [hid]; linarith, herr2, fun h01 => ?_⟩
  rw [(StatFormal.Wave31to.newapprox_err ℝ P Q f hfm h01).1, errL, linL]

end StatFormal.Wave31tu.RouteP
