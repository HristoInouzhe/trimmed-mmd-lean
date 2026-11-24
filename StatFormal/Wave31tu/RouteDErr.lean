import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tq.RouteM21
import StatFormal.Lib.BandLimited.Density
import StatFormal.Lib.MomentTrim.Crossing
import StatFormal.Lib.LaplaceDev.OneSample

set_option linter.style.longLine false

/-!
# Wave31tu, chunk D: the error is positive (first step of Lemma S4.25 (b), S4 :1252-1255)

`errL_pos`: under `IsCross P Q p q x₀ ℓ₀`, `p(x₀) > 0` and `Claims.lap_err` (Y6, eq:laperr), every continuous `f` with `|f| ≤ 1` and
`osc(f) ≤ 1` has `err(f) > 0`. Printed route: if `osc f < 1` then `err ≥ α⋆(1 − osc f) > 0` (`α⋆ > 0`, 31tq `RouteM.cross_tv`);
otherwise `err = 0` forces `f = M` a.e. on `{p > q}` and `f = m` a.e. on `{q > p}`, which contain punctured neighbourhoods of `x₀`
on the right and on the left (`(p − q)′(x₀) = ℓ₀ > 0`, `MomentTrim.exists_linear_lower`); an open null set is empty, so by continuity
`M = f(x₀) = m`, against `osc f = 1`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave31tu.RouteD

open StatFormal StatFormal.Wave31tq

/-- A continuous `f` equal to `c` a.e. on `(a, b)` (`a < b`), in the form `g · (f − c) = 0` a.e. with `g > 0` on `(a, b)`, equals `c`
at both endpoints' closure, in particular at `a` and `b`. -/
theorem eq_on_closure_of_ae {f g : ℝ → ℝ} (hfc : Continuous f) {a b c : ℝ} (hab : a < b) (hg : ∀ x ∈ Ioo a b, g x ≠ 0)
    (hae : ∀ᵐ x ∂volume, g x * (f x - c) = 0) : ∀ x ∈ Icc a b, f x = c := by
  have hnull : volume (Ioo a b ∩ {x | f x ≠ c}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x ⟨hx, hne⟩
    change ¬ (g x * (f x - c) = 0)
    exact mul_ne_zero (hg x hx) (sub_ne_zero.2 hne)
  have hopen : IsOpen (Ioo a b ∩ {x | f x ≠ c}) := isOpen_Ioo.inter (isOpen_ne_fun hfc continuous_const)
  have hempty := (hopen.measure_eq_zero_iff volume).1 hnull
  have hIoo : Ioo a b ⊆ {x | f x = c} := fun x hx => by
    by_contra hne
    exact Set.notMem_empty x (hempty.subset ⟨hx, hne⟩)
  have hcl := closure_minimal hIoo (isClosed_eq hfc continuous_const)
  rw [closure_Ioo hab.ne] at hcl
  exact fun x hx => hcl hx

/-- The first step of Lemma S4.25 (b): `err(f) > 0` for continuous `f` with `|f| ≤ 1`, `osc f ≤ 1`, under `IsCross` and `p(x₀) > 0`. -/
theorem errL_pos (h6 : Claims.lap_err) {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀)
    {f : ℝ → ℝ} (hfc : Continuous f) (hf1 : ∀ z, |f z| ≤ 1) (hosc : Wave31to.oscFn f ≤ 1) :
    0 < errL P Q f := by
  have hpq0 := RouteM.cross_zero hc
  obtain ⟨htv0, -⟩ := RouteM.cross_tv StatFormal.Wave31tq.tv_density hc hpx
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -, -, -, hd, hℓ⟩ := hc
  obtain ⟨hid, hT0, hAnn, hBnn, -, -, -⟩ := h6 P Q p q f hpm hqm hp0 hq0 hP hQ hfc.measurable ⟨1, hf1⟩ hosc
  obtain ⟨hmf, hfM, -, -, hMm1⟩ := LaplaceDev.bdd_facts hf1 hosc
  obtain ⟨hpi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hpm hp0 hP
  obtain ⟨hqi, -⟩ := StatFormal.BandLimited.integrable_and_integral_of_density hqm hq0 hQ
  by_contra hneg
  rw [not_lt] at hneg
  have hA0 : ∫ x, ((⨆ z, f z) - f x) * max (p x - q x) 0 = 0 := by linarith
  have hB0 : ∫ x, (f x - ⨅ z, f z) * max (q x - p x) 0 = 0 := by linarith
  have hC0 : Distances.tvDist P Q * (1 - Wave31to.oscFn f) = 0 := by linarith
  have hgA : Integrable fun x => ((⨆ z, f z) - f x) * max (p x - q x) 0 :=
    (hpi.sub hqi).pos_part.bdd_mul (continuous_const.sub hfc).aestronglyMeasurable
      (ae_of_all _ fun z => by
        show ‖(⨆ z, f z) - f z‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hfM z))]; linarith [hmf z])
  have hgB : Integrable fun x => (f x - ⨅ z, f z) * max (q x - p x) 0 :=
    (hqi.sub hpi).pos_part.bdd_mul (hfc.sub continuous_const).aestronglyMeasurable
      (ae_of_all _ fun z => by
        show ‖f z - ⨅ z, f z‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hmf z))]; linarith [hfM z])
  have hAe := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sub_nonneg.2 (hfM x)) (le_max_right _ _)) hgA).1 hA0
  have hBe := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sub_nonneg.2 (hmf x)) (le_max_right _ _)) hgB).1 hB0
  obtain ⟨δ, hδ, hRl, hLl⟩ := StatFormal.MomentTrim.exists_linear_lower hd (sub_eq_zero.2 hpq0) hℓ
  -- `f = M` near `x₀` on the right
  have hR := eq_on_closure_of_ae (g := fun x => -max (p x - q x) 0) hfc (by linarith : x₀ < x₀ + δ)
    (fun x hx => by
      have h1 : ℓ₀ / 2 * (x - x₀) ≤ p x - q x := hRl x hx
      have h2 : 0 < p x - q x := by have := mul_pos (half_pos hℓ) (sub_pos.2 hx.1); linarith
      show -max (p x - q x) 0 ≠ 0
      rw [max_eq_left h2.le]; exact neg_ne_zero.2 h2.ne')
    (hAe.mono fun x hx => by
      have h : ((⨆ z, f z) - f x) * max (p x - q x) 0 = 0 := hx
      show -max (p x - q x) 0 * (f x - ⨆ z, f z) = 0
      linear_combination h)
  have hL := eq_on_closure_of_ae (g := fun x => max (q x - p x) 0) hfc (by linarith : x₀ - δ < x₀)
    (fun x hx => by
      have h1 : ℓ₀ / 2 * (x₀ - x) ≤ -(p x - q x) := hLl x hx
      have h2 : 0 < q x - p x := by have := mul_pos (half_pos hℓ) (sub_pos.2 hx.2); linarith
      show max (q x - p x) 0 ≠ 0
      rw [max_eq_left h2.le]; exact h2.ne')
    (hBe.mono fun x hx => by
      have h : (f x - ⨅ z, f z) * max (q x - p x) 0 = 0 := hx
      show max (q x - p x) 0 * (f x - ⨅ z, f z) = 0
      linear_combination h)
  have hM : f x₀ = ⨆ z, f z := hR x₀ ⟨le_rfl, by linarith⟩
  have hm : f x₀ = ⨅ z, f z := hL x₀ ⟨by linarith, le_rfl⟩
  have hosc0 : Wave31to.oscFn f = 0 := by
    show (⨆ z, f z) - (⨅ z, f z) = 0
    rw [← hM, ← hm, sub_self]
  rw [hosc0, sub_zero, mul_one] at hC0
  linarith

end StatFormal.Wave31tu.RouteD
