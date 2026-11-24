import StatFormal.Lib.IntervalDev.Separated
import StatFormal.Lib.Indicatrix.Banach
import StatFormal.Lib.Indicatrix.LayerCake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.Bornology

set_option linter.style.longLine false

/-!
# Localized deviation for functions of bounded variation

Let `μ, ν` be finite measures on `ℝ` whose deviation on every interval `C` is bounded as
`|ν(C) − μ(C)| ≤ √(α μ(C)) + β` (on the event of `lem:lapintervals` this holds for `ν` the empirical law and `μ`
the law of the sample, with `α = 2x/n`, `β = c_x/n`). For a bounded interval `I` and `h : ℝ → [0,1]` continuous on
the closure of `I` with variation at most `V` there,
`|∫_I h dν − ∫_I h dμ| ≤ √((V+1) α ∫_I h dμ) + (V+1) β` (trimmed-mmd S4, Lemma S4.24, `lem:lapbv`).

## Route (printed)

* layer cake (`Indicatrix.integral_eq_intervalIntegral_meas_lt`) for `μ` and `ν` restricted to `I`:
  `∫_I h d(ν − μ) = ∫_0^1 (ν − μ)(A_s) ds` with `A_s = {z ∈ I : h z > s}`;
* `A_s` is separated by the level set `{z ∈ [a,b] : h z = s}` (intermediate value theorem), so it is a union of at
  most `N(s) + 1` intervals (`abs_measureReal_sub_le_of_separated`), `N` Banach's indicatrix on `[a,b] = closure I`;
* `N(s) < ∞` for a.e. `s` and `∫ (N + 1) ≤ V + 1` (`Indicatrix.lintegral_bcount_le`);
* Cauchy–Schwarz in `s`, in the elementary form `√(KW) ≤ (t/2)K + W/(2t)` for every `t > 0`, then optimized in `t`
  (`le_sqrt_mul_add_of_forall`).

## Main results

* `two_sqrt_mul_le`, `le_sqrt_mul_add_of_forall`: the arithmetic–geometric mean step and its optimization;
* `abs_setIntegral_sub_le_of_bv`: the localized deviation bound.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.IntervalDev

open StatFormal.Indicatrix

/-- AM–GM: `2√(KW) ≤ tK + W/t` for `K > 0`, `W ≥ 0`, `t > 0`. -/
theorem two_sqrt_mul_le {K W t : ℝ} (hK : 0 < K) (hW : 0 ≤ W) (ht : 0 < t) :
    2 * √(K * W) ≤ t * K + W / t := by
  have hp : √(K * W) ^ 2 = K * W := Real.sq_sqrt (by positivity)
  have e : K * (t ^ 2 * K + W - 2 * √(K * W) * t) = (t * K - √(K * W)) ^ 2 := by
    linear_combination (-1) * hp
  have h1 : 0 ≤ t ^ 2 * K + W - 2 * √(K * W) * t := by
    have h2 := sq_nonneg (t * K - √(K * W))
    rw [← e] at h2
    by_contra hneg
    have : K * (t ^ 2 * K + W - 2 * √(K * W) * t) < 0 := mul_neg_of_pos_of_neg hK (not_le.1 hneg)
    linarith
  have e2 : t * K + W / t - 2 * √(K * W) = (t ^ 2 * K + W - 2 * √(K * W) * t) / t := by
    field_simp
  have : 0 ≤ t * K + W / t - 2 * √(K * W) := by rw [e2]; positivity
  linarith

/-- Optimization of the AM–GM bound: if `X ≤ (t/2)K + W/(2t) + c` for every `t > 0`, `K > 0`, `W ≥ 0`, then
`X ≤ √(KW) + c`. -/
theorem le_sqrt_mul_add_of_forall {X K W c : ℝ} (hK : 0 < K) (hW : 0 ≤ W)
    (h : ∀ t : ℝ, 0 < t → X ≤ t / 2 * K + W / (2 * t) + c) : X ≤ √(K * W) + c := by
  rcases hW.eq_or_lt with hW0 | hWpos
  · rw [← hW0, mul_zero, Real.sqrt_zero, zero_add]
    by_contra hlt
    push Not at hlt
    have ht : 0 < (X - c) / K := div_pos (by linarith) hK
    have := h _ ht
    have e : (X - c) / K / 2 * K + W / (2 * ((X - c) / K)) = (X - c) / 2 := by
      rw [← hW0, zero_div, add_zero]
      field_simp
    rw [e] at this
    linarith
  · have hsK := Real.sqrt_pos.2 hK
    have hsW := Real.sqrt_pos.2 hWpos
    have hKK : √K * √K = K := Real.mul_self_sqrt hK.le
    have hWW : √W * √W = W := Real.mul_self_sqrt hW
    have := h (√W / √K) (div_pos hsW hsK)
    have e1 : √W / √K / 2 * K = √K * √W / 2 := by
      calc √W / √K / 2 * K = √W / √K / 2 * (√K * √K) := by rw [hKK]
        _ = √K * √W / 2 := by field_simp
    have e2 : W / (2 * (√W / √K)) = √K * √W / 2 := by
      calc W / (2 * (√W / √K)) = (√W * √W) / (2 * (√W / √K)) := by rw [hWW]
        _ = √K * √W / 2 := by field_simp
    have e : √W / √K / 2 * K + W / (2 * (√W / √K)) = √K * √W := by
      rw [e1, e2]; ring
    rw [e] at this
    rw [Real.sqrt_mul hK.le]
    linarith

/-- **Localized deviation for functions of bounded variation** (`lem:lapbv`). If every interval `C` has
`|ν(C) − μ(C)| ≤ √(α μ(C)) + β`, then for every bounded interval `I` and every `h` with values in `[0,1]`,
continuous on `closure I` with `V_{closure I}(h) ≤ V`:
`|∫_I h dν − ∫_I h dμ| ≤ √((V+1) α ∫_I h dμ) + (V+1) β`. -/
theorem abs_setIntegral_sub_le_of_bv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hev : ∀ C : Set ℝ, C.OrdConnected → |ν.real C - μ.real C| ≤ √(α * μ.real C) + β)
    {I : Set ℝ} (hI : I.OrdConnected) (hIb : Bornology.IsBounded I) {h : ℝ → ℝ}
    (h01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1) (hc : ContinuousOn h (closure I)) {V : ℝ} (hV : 0 ≤ V)
    (hvar : eVariationOn h (closure I) ≤ ENNReal.ofReal V) :
    |∫ z in I, h z ∂ν - ∫ z in I, h z ∂μ| ≤ √((V + 1) * α * ∫ z in I, h z ∂μ) + (V + 1) * β := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [Measure.restrict_empty, integral_zero_measure, sub_zero, abs_zero]
    positivity
  set a := sInf I with ha
  set b := sSup I with hb
  have hbb : BddBelow I := hIb.bddBelow
  have hba : BddAbove I := hIb.bddAbove
  have hab : a ≤ b := csInf_le_csSup hne hbb hba
  have hIab : I ⊆ Icc a b := fun x hx => ⟨csInf_le hbb hx, le_csSup hba hx⟩
  have habI : Icc a b ⊆ closure I := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h1 | h1
    · rw [← h1]; exact csInf_mem_closure hne hbb
    rcases eq_or_lt_of_le hx.2 with h2 | h2
    · rw [h2]; exact csSup_mem_closure hne hba
    · apply subset_closure
      obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne h1
      obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hne h2
      exact hI.out hy hz ⟨hyx.le, hxz.le⟩
  have hcab : ContinuousOn h (Icc a b) := hc.mono habI
  have hvab : eVariationOn h (Icc a b) ≤ ENNReal.ofReal V := (eVariationOn.mono h habI).trans hvar
  have hIm : MeasurableSet I := hI.measurableSet
  have hcI : ContinuousOn h I := hc.mono subset_closure
  -- the layer cake
  set A : ℝ → Set ℝ := fun s => {z | s < h z} ∩ I with hA
  have hLC : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      ∫ z in I, h z ∂ρ = ∫ s in (0 : ℝ)..1, ρ.real (A s) := by
    intro ρ _
    rw [integral_eq_intervalIntegral_meas_lt (ρ.restrict I) (hcI.aemeasurable hIm)
      (fun z => (h01 z).1) (fun z => (h01 z).2)]
    congr 1
    ext s
    rw [measureReal_restrict_apply' hIm]
  have hint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      IntervalIntegrable (fun s => ρ.real (A s)) volume 0 1 := fun ρ _ =>
    Antitone.intervalIntegrable fun s s' hss' =>
      measureReal_mono fun z hz => ⟨lt_of_le_of_lt hss' hz.1, hz.2⟩
  have hU0 : 0 ≤ ∫ z in I, h z ∂μ := setIntegral_nonneg hIm fun z _ => (h01 z).1
  have hUeq := hLC μ
  conv_lhs => rw [hLC ν, hLC μ, ← intervalIntegral.integral_sub (hint ν) (hint μ)]
  -- Banach's indicatrix
  have hBm := measurable_bcount hab hcab
  have hBl : ∫⁻ s, bcount h a b s ≤ ENNReal.ofReal V := (lintegral_bcount_le hab hcab).trans hvab
  have hBne : ∫⁻ s, bcount h a b s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBl
  have hBfin : ∀ᵐ s, bcount h a b s < ⊤ := ae_lt_top hBm hBne
  set K : ℝ → ℝ := fun s => (bcount h a b s).toReal + 1 with hKdef
  have hK1 : ∀ s, 1 ≤ K s := fun s => by
    simp only [hKdef]; linarith [ENNReal.toReal_nonneg (a := bcount h a b s)]
  have hBint : Integrable (fun s => (bcount h a b s).toReal) :=
    integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hBne
  have hKint : IntervalIntegrable K volume 0 1 :=
    hBint.intervalIntegrable.add intervalIntegrable_const
  have hKle : ∫ s in (0 : ℝ)..1, K s ≤ V + 1 := by
    rw [intervalIntegral.integral_add hBint.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul]
    have h1 : ∫ s in (0 : ℝ)..1, (bcount h a b s).toReal ≤ ∫ s, (bcount h a b s).toReal := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact setIntegral_le_integral hBint (ae_of_all _ fun s => ENNReal.toReal_nonneg)
    have h2 : ∫ s, (bcount h a b s).toReal ≤ V := by
      rw [integral_toReal hBm.aemeasurable hBfin]
      exact ENNReal.toReal_le_of_le_ofReal hV hBl
    linarith
  -- the pointwise bound on the upper level sets
  have hpt : ∀ s, bcount h a b s < ⊤ →
      |ν.real (A s) - μ.real (A s)| ≤ √(K s * α * μ.real (A s)) + K s * β := by
    intro s hs
    set Zs : Set ℝ := {x | x ∈ Icc a b ∧ h x = s} with hZs
    have hfin : Zs.Finite := by
      rw [← Set.encard_lt_top_iff]
      have : ENat.toENNReal Zs.encard < ⊤ := hs
      exact ENat.toENNReal_lt_top.1 this
    have hK : K s = (hfin.toFinset.card : ℝ) + 1 := by
      simp only [hKdef, bcount]
      rw [← hZs, hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe, ENNReal.toReal_natCast]
    rw [hK]
    refine abs_measureReal_sub_le_of_separated μ ν hα hev hfin.toFinset I (A s) hI
      inter_subset_right ?_
    intro x hx y hy hxy hxor
    have hcxy : ContinuousOn h (Icc x y) := hcI.mono (hI.out hx hy)
    have hsv : s ∈ h '' Icc x y := by
      by_cases hxA : x ∈ A s
      · have hyA : y ∉ A s := hxor.1 hxA
        have h1 : s < h x := hxA.1
        have h2 : h y ≤ s := by
          by_contra hlt; exact hyA ⟨not_le.1 hlt, hy⟩
        exact intermediate_value_Icc' hxy.le hcxy ⟨h2, h1.le⟩
      · have hyA : y ∈ A s := by
          by_contra hyA; exact hxA (hxor.2 hyA)
        have h1 : h x ≤ s := by
          by_contra hlt; exact hxA ⟨not_le.1 hlt, hx⟩
        exact intermediate_value_Icc hxy.le hcxy ⟨h1, hyA.1.le⟩
    obtain ⟨z, hz, hzs⟩ := hsv
    exact ⟨z, hfin.mem_toFinset.2 ⟨hIab (hI.out hx hy hz), hzs⟩, hz.1, hz.2⟩
  -- integrate and optimize
  rw [mul_assoc]
  refine le_sqrt_mul_add_of_forall (by linarith) (mul_nonneg hα hU0) fun t ht => ?_
  set g : ℝ → ℝ := fun s => (t / 2 + β) * K s + α / (2 * t) * μ.real (A s) with hg
  have hgint : IntervalIntegrable g volume 0 1 :=
    (hKint.const_mul _).add ((hint μ).const_mul _)
  have hDle : ∀ᵐ s, |ν.real (A s) - μ.real (A s)| ≤ g s := by
    filter_upwards [hBfin] with s hs
    have h1 := hpt s hs
    have hW : 0 ≤ α * μ.real (A s) := mul_nonneg hα measureReal_nonneg
    have h2 := two_sqrt_mul_le (lt_of_lt_of_le one_pos (hK1 s)) hW ht
    rw [← mul_assoc] at h2
    have e : α * μ.real (A s) / t = 2 * (α / (2 * t) * μ.real (A s)) := by
      field_simp
    rw [e] at h2
    simp only [hg]
    nlinarith
  calc |∫ s in (0 : ℝ)..1, (ν.real (A s) - μ.real (A s))|
      ≤ ∫ s in (0 : ℝ)..1, |ν.real (A s) - μ.real (A s)| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, g s :=
        intervalIntegral.integral_mono_ae zero_le_one ((hint ν).sub (hint μ)).abs hgint hDle
    _ = (t / 2 + β) * (∫ s in (0 : ℝ)..1, K s) + α / (2 * t) * ∫ z in I, h z ∂μ := by
        rw [intervalIntegral.integral_add (hKint.const_mul _) ((hint μ).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hUeq]
    _ ≤ (t / 2 + β) * (V + 1) + α / (2 * t) * ∫ z in I, h z ∂μ := by
        have h0 : 0 ≤ t / 2 + β := by positivity
        linarith [mul_le_mul_of_nonneg_left hKle h0]
    _ = t / 2 * (V + 1) + α * (∫ z in I, h z ∂μ) / (2 * t) + (V + 1) * β := by
        ring

end StatFormal.IntervalDev
