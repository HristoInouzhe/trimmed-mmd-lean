import StatFormal.Lib.Bernstein.Pointwise
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Bernstein's inequality for bounded i.i.d. variables

Library component F.B (part 2). Untrusted library code: no `Statements.lean` is involved.

## Setting

`Z_i = g(ω i)`, `i : Fin n`, under `Measure.pi fun _ : Fin n => ν` (i.i.d. with law `g_* ν`),
`g` measurable with values in `[0, 1]`. `popMean ν g = ∫ g dν`, `popVar ν g = ∫ (g − E g)² dν`,
`sampleMean g ω = (1/n) Σ g(ω i)`.

## Main results

* `integral_exp_mul_le_of_abs_le_one`: for a centred `X` with `|X| ≤ 1` and `0 ≤ λ < 3`,
  `E exp(λX) ≤ exp(λ² E X² / (2 (1 − λ/3)))` (sub-gamma MGF bound with scale `1/3`);
* `integral_exp_mul_sum_eq`: `E exp(λ Σ X(ω i)) = (E exp(λ X))ⁿ` under the product measure;
* `bernstein`: **one-sided Bernstein inequality** (Maurer–Pontil 2009, Thm 3):
  `P(√(2σ² log(1/δ)/n) + log(1/δ)/(3n) ≤ E Z − Z̄) ≤ δ` for `0 < δ ≤ 1`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set

namespace StatFormal.Bernstein

variable {β : Type*} [MeasurableSpace β]

/-- Population mean `∫ g dν`. -/
def popMean (ν : Measure β) (g : β → ℝ) : ℝ := ∫ x, g x ∂ν

/-- Population variance `∫ (g − E g)² dν`. -/
def popVar (ν : Measure β) (g : β → ℝ) : ℝ := ∫ x, (g x - popMean ν g) ^ 2 ∂ν

/-- Sample mean `(1/n) Σᵢ g(ω i)`. -/
def sampleMean {n : ℕ} (g : β → ℝ) (ω : Fin n → β) : ℝ := (∑ i, g (ω i)) / n

theorem popVar_nonneg (ν : Measure β) (g : β → ℝ) : 0 ≤ popVar ν g :=
  integral_nonneg fun _ => sq_nonneg _

theorem popMean_mem_Icc (ν : Measure β) [IsProbabilityMeasure ν] {g : β → ℝ}
    (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) : popMean ν g ∈ Icc (0 : ℝ) 1 := by
  have hi : Integrable g ν := Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ hg01)
  refine ⟨integral_nonneg fun x => (hg01 x).1, ?_⟩
  calc popMean ν g = ∫ x, g x ∂ν := rfl
    _ ≤ ∫ _x, (1 : ℝ) ∂ν := integral_mono hi (integrable_const _) fun x => (hg01 x).2
    _ = 1 := by simp

/-- **Sub-gamma MGF bound**: for measurable centred `X` with `|X| ≤ 1` and `0 ≤ λ < 3`,
`E exp(λX) ≤ exp(λ² E X² / (2 (1 − λ/3)))`. -/
theorem integral_exp_mul_le_of_abs_le_one (ν : Measure β) [IsProbabilityMeasure ν]
    {X : β → ℝ} (hX : Measurable X) (hX1 : ∀ x, |X x| ≤ 1) (hX0 : ∫ x, X x ∂ν = 0)
    {l : ℝ} (hl0 : 0 ≤ l) (hl3 : l < 3) :
    ∫ x, exp (l * X x) ∂ν ≤ exp (l ^ 2 / (2 * (1 - l / 3)) * ∫ x, X x ^ 2 ∂ν) := by
  set C := l ^ 2 / (2 * (1 - l / 3)) with hC
  have hmem : ∀ x, X x ∈ Icc (-1 : ℝ) 1 := fun x => abs_le.1 (hX1 x)
  have hi : Integrable X ν := Integrable.of_mem_Icc (-1) 1 hX.aemeasurable (ae_of_all _ hmem)
  have hi2 : Integrable (fun x => X x ^ 2) ν :=
    Integrable.of_mem_Icc 0 1 (hX.pow_const 2).aemeasurable (ae_of_all _ fun x => by
      have := hmem x
      exact ⟨sq_nonneg _, by nlinarith [this.1, this.2]⟩)
  have hie : Integrable (fun x => exp (l * X x)) ν :=
    Integrable.of_mem_Icc 0 (exp l) (measurable_exp.comp (hX.const_mul l)).aemeasurable
      (ae_of_all _ fun x => ⟨(exp_pos _).le, exp_le_exp.2 (by nlinarith [(hmem x).2])⟩)
  calc ∫ x, exp (l * X x) ∂ν ≤ ∫ x, (1 + l * X x + C * X x ^ 2) ∂ν := by
        refine integral_mono hie (((integrable_const 1).add (hi.const_mul l)).add
          (hi2.const_mul C)) fun x => ?_
        have := exp_mul_le_bernstein hl0 hl3 (hmem x).2
        rw [hC]
        calc exp (l * X x) ≤ 1 + l * X x + l ^ 2 * X x ^ 2 / (2 * (1 - l / 3)) := this
          _ = _ := by ring
    _ = 1 + C * ∫ x, X x ^ 2 ∂ν := by
        have j1 : Integrable (fun x => 1 + l * X x) ν := (integrable_const 1).add (hi.const_mul l)
        have j2 : Integrable (fun x => C * X x ^ 2) ν := hi2.const_mul C
        have j3 : Integrable (fun x => l * X x) ν := hi.const_mul l
        rw [integral_add j1 j2, integral_add (integrable_const 1) j3, integral_const_mul,
          integral_const_mul, hX0]
        simp
    _ ≤ exp (C * ∫ x, X x ^ 2 ∂ν) := by
        have := add_one_le_exp (C * ∫ x, X x ^ 2 ∂ν)
        linarith

/-- MGF of a sum of i.i.d. copies under the product measure. -/
theorem integral_exp_mul_sum_eq (ν : Measure β) [IsProbabilityMeasure ν] (X : β → ℝ) (n : ℕ)
    (l : ℝ) :
    ∫ ω, exp (l * ∑ i, X (ω i)) ∂(Measure.pi fun _ : Fin n => ν) =
      (∫ x, exp (l * X x) ∂ν) ^ n := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) x => exp (l * X x))]
  simp

/-- **One-sided Bernstein inequality** (Maurer–Pontil 2009, Thm 3): for i.i.d. `Z_i ∈ [0,1]` with
variance `σ²`, `n ≥ 1` and `0 < δ ≤ 1`,
`P(√(2σ² log(1/δ)/n) + log(1/δ)/(3n) ≤ E Z − Z̄) ≤ δ`. -/
theorem bernstein (ν : Measure β) [IsProbabilityMeasure ν] {g : β → ℝ} (hg : Measurable g)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * popVar ν g * log (1 / δ) / n) + log (1 / δ) / (3 * n) ≤
        popMean ν g - sampleMean g ω} ≤ δ := by
  set P := Measure.pi fun _ : Fin n => ν with hP
  set μ := popMean ν g with hμ
  set σ2 := popVar ν g with hσ2
  set L := log (1 / δ) with hL
  have hL0 : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hexpL : exp (-L) = δ := by rw [hL, log_div one_ne_zero hδ0.ne', log_one, zero_sub,
    neg_neg, exp_log hδ0]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hμ01 : μ ∈ Icc (0 : ℝ) 1 := popMean_mem_Icc ν hg hg01
  -- the centred variable
  set X : β → ℝ := fun x => μ - g x with hXdef
  have hXm : Measurable X := measurable_const.sub hg
  have hX1 : ∀ x, |X x| ≤ 1 := fun x => by
    have h1 := hg01 x
    rw [abs_le]
    exact ⟨by change -1 ≤ μ - g x; linarith [h1.1, h1.2, hμ01.1, hμ01.2],
      by change μ - g x ≤ 1; linarith [h1.1, h1.2, hμ01.1, hμ01.2]⟩
  have hgi : Integrable g ν := Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ hg01)
  have hX0 : ∫ x, X x ∂ν = 0 := by
    simp only [hXdef]
    rw [integral_sub (integrable_const _) hgi, integral_const]
    simp [hμ, popMean]
  have hX2 : ∫ x, X x ^ 2 ∂ν = σ2 := by
    simp only [hXdef, hσ2, popVar, ← hμ]
    congr 1; ext x; ring
  -- the sum and the event
  set S : (Fin n → β) → ℝ := fun ω => ∑ i, X (ω i) with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun i _ => hXm.comp (measurable_pi_apply i)
  have hSb : ∀ ω, S ω ≤ n := fun ω => by
    calc S ω ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (abs_le.1 (hX1 (ω i))).2
      _ = n := by simp
  have hSb' : ∀ ω, -(n : ℝ) ≤ S ω := fun ω => by
    calc -(n : ℝ) = ∑ _i : Fin n, (-1 : ℝ) := by simp
      _ ≤ S ω := Finset.sum_le_sum fun i _ => (abs_le.1 (hX1 (ω i))).1
  have hSeq : ∀ ω, S ω = n * (μ - sampleMean g ω) := fun ω => by
    simp only [hS, hXdef, sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  set u := √(2 * σ2 * L / n) + L / (3 * n) with hu
  have hsub : {ω | u ≤ μ - sampleMean g ω} ⊆ {ω | n * u ≤ S ω} := fun ω hω => by
    change (n : ℝ) * u ≤ S ω
    rw [hSeq]; exact mul_le_mul_of_nonneg_left hω hnR.le
  have hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω => exp (t * S ω)) P := fun t ht =>
    Integrable.of_mem_Icc 0 (exp (t * n)) (measurable_exp.comp (hSm.const_mul t)).aemeasurable
      (ae_of_all _ fun ω => ⟨(exp_pos _).le, exp_le_exp.2 (mul_le_mul_of_nonneg_left (hSb ω) ht)⟩)
  have hchern : ∀ t : ℝ, 0 ≤ t →
      P.real {ω | u ≤ μ - sampleMean g ω} ≤ exp (-t * (n * u)) * (∫ x, exp (t * X x) ∂ν) ^ n :=
    fun t ht => by
      refine (measureReal_mono hsub).trans ?_
      have := measure_ge_le_exp_mul_mgf (μ := P) (X := S) (n * u) ht (hint t ht)
      rwa [mgf, hS, hP, integral_exp_mul_sum_eq] at this
  have hσ0 : 0 ≤ σ2 := popVar_nonneg ν g
  rcases hσ0.eq_or_lt with h0 | hpos
  · -- zero variance: `X = 0` a.e., take `λ = 3`
    have hXae : X =ᵐ[ν] 0 := by
      have hi2 : Integrable (fun x => X x ^ 2) ν :=
        Integrable.of_mem_Icc 0 1 (hXm.pow_const 2).aemeasurable (ae_of_all _ fun x => by
          have := abs_le.1 (hX1 x)
          exact ⟨sq_nonneg _, by nlinarith [this.1, this.2]⟩)
      have h := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (X x)) hi2).1
        (by rw [hX2, ← h0])
      filter_upwards [h] with x hx
      simpa using hx
    have hmgf : ∫ x, exp (3 * X x) ∂ν = 1 := by
      rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by filter_upwards [hXae] with x hx; simp [hx])]
      simp
    have := hchern 3 (by norm_num)
    rw [hmgf, one_pow, mul_one] at this
    refine this.trans (le_of_eq ?_)
    rw [← hexpL, hu, ← h0]
    congr 1
    simp only [mul_zero, zero_mul, zero_div, Real.sqrt_zero, zero_add]
    field_simp
  · -- positive variance: optimise `λ`
    set v : ℝ := n * σ2 with hv
    have hv0 : 0 < v := mul_pos hnR hpos
    set a : ℝ := n * √(2 * σ2 * L / n) with ha
    have ha0 : 0 ≤ a := mul_nonneg hnR.le (Real.sqrt_nonneg _)
    have ha2 : a ^ 2 = 2 * v * L := by
      rw [ha, mul_pow, Real.sq_sqrt (by positivity), hv]
      field_simp
    set s : ℝ := a / v with hs
    have hs0 : 0 ≤ s := div_nonneg ha0 hv0.le
    have hsv : a = s * v := by rw [hs]; field_simp
    have hLs : L = v * s ^ 2 / 2 := by
      have h1 : (s * v) ^ 2 = 2 * v * L := hsv ▸ ha2
      have h2 : v * (v * s ^ 2 - 2 * L) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · linarith
    set w : ℝ := 1 + s / 3 with hw
    have hw0 : 0 < w := by rw [hw]; linarith
    set l : ℝ := s / w with hl
    have hl0 : 0 ≤ l := div_nonneg hs0 hw0.le
    have hl3 : l < 3 := by
      rw [hl, div_lt_iff₀ hw0, hw]; linarith
    have hden : 1 - l / 3 = 1 / w := by
      rw [hl]; field_simp; rw [hw]; ring
    have hmgf := integral_exp_mul_le_of_abs_le_one ν hXm hX1 hX0 hl0 hl3
    rw [hX2] at hmgf
    have hnu : n * u = a + L / 3 := by
      rw [hu, ha, mul_add]; congr 1; field_simp
    have := hchern l hl0
    refine this.trans ?_
    calc exp (-l * (n * u)) * (∫ x, exp (l * X x) ∂ν) ^ n
        ≤ exp (-l * (n * u)) * exp (l ^ 2 / (2 * (1 - l / 3)) * σ2) ^ n := by
          gcongr
      _ = exp (-l * (n * u) + n * (l ^ 2 / (2 * (1 - l / 3)) * σ2)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = δ := by
          rw [← hexpL]
          congr 1
          rw [hnu, hden, hsv, hLs, hl]
          have hw0' : (1 + s / 3) ≠ 0 := by linarith
          simp only [hv, hw]
          field_simp
          ring

end StatFormal.Bernstein
