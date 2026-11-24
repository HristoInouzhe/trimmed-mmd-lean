import StatFormal.Archive.Wave29d.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Refutation of the attainment clause of `lem:lindsay` for bounded measurable rules (`lindsay_attain_refuted`)

Untrusted proof file. `K = L = [−1, 1]`, `κ = δ`, one anchor `x₀ = 0`, `λ = ε = 1`, `m̂ = δ₀` and
`h(y) = if y = 0 then 0 else √(y² + 1 − |y|)`. Then `φ(y) = 1 − |y|` off `0`, `φ(0) = 0`, and `D_{m̂}(y) = e^{φ(y)}`.
For every `y` there is `y'` with `D(y) < D(y')` (`y' = ½` if `y = 0`, `y' = y/2` otherwise), and `D(y') = ∫ D dδ_{y'}`
is in the set whose supremum is taken; if that set is unbounded its `sSup` is `0 < D(y)`. Either way no `y` attains it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace StatFormal.Wave29d

namespace LindsayRefute

abbrev I := Icc (-1 : ℝ) 1

def x0 : I := ⟨0, by norm_num⟩

def hBad (y : I) : ℝ := if (y : ℝ) = 0 then 0 else √((y : ℝ) ^ 2 + 1 - |(y : ℝ)|)

lemma hBad_meas : Measurable hBad := by
  unfold hBad
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun measurable_subtype_coe measurable_const
  · fun_prop

lemma hBad_bdd : ∃ H, ∀ x, |hBad x| ≤ H := by
  refine ⟨2, fun x => ?_⟩
  have h1 := x.2.1
  have h2 := x.2.2
  unfold hBad
  split_ifs
  · norm_num
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_le_left (by norm_num)]
    have : |(x : ℝ)| ≤ 1 := abs_le.2 ⟨h1, h2⟩
    have : (x : ℝ) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (x : ℝ), sq_abs (x : ℝ)]
    nlinarith [abs_nonneg (x : ℝ)]

lemma phi_eq (y : I) :
    phiRule hBad 1 1 (fun _ : Fin 1 => x0) 0 y = if (y : ℝ) = 0 then 0 else 1 - |(y : ℝ)| := by
  have hx0 : hBad x0 = 0 := by simp [hBad, x0]
  simp only [phiRule, hx0, sub_zero, one_mul, mul_one, div_one]
  have hx0' : ((x0 : I) : ℝ) = 0 := rfl
  rw [hx0']
  unfold hBad
  split_ifs with h
  · simp [h]
  · have hy : |(y : ℝ)| ≤ 1 := abs_le.2 ⟨y.2.1, y.2.2⟩
    have hnn : 0 ≤ (y : ℝ) ^ 2 + 1 - |(y : ℝ)| := by nlinarith [sq_nonneg (y : ℝ)]
    rw [Real.sq_sqrt hnn]
    ring

lemma D_eq (y : I) :
    lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y =
      Real.exp (if (y : ℝ) = 0 then 0 else 1 - |(y : ℝ)|) := by
  have hpsi : ∀ z, psiK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) 0 z =
      Real.exp (if (z : ℝ) = 0 then 0 else 1 - |(z : ℝ)|) := by
    intro z
    simp only [psiK, Kernel.id_apply, integral_dirac]
    rw [phi_eq]
  simp only [lindsayDK, Fin.sum_univ_one, Nat.cast_one, div_one, one_mul, integral_dirac]
  rw [hpsi, hpsi]
  simp [x0]

end LindsayRefute

open LindsayRefute in
theorem lindsay_attain_refuted : Claims.lindsay_attain_refuted := by
  intro H
  obtain ⟨y, hy⟩ := H hBad 1 1 (Measure.dirac x0) hBad_meas hBad_bdd one_pos one_pos inferInstance
  change lindsaySupK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) {m | IsProbabilityMeasure m} (Measure.dirac x0) =
    lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y at hy
  set S := {v | ∃ m ∈ {m : Measure I | IsProbabilityMeasure m},
    v = ∫ z, lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) z ∂m}
  have hmem : ∀ y' : I,
      lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y' ∈ S := fun y' =>
    ⟨Measure.dirac y', (inferInstance : IsProbabilityMeasure (Measure.dirac y')), by rw [integral_dirac]⟩
  -- a strictly better point
  obtain ⟨y', hlt⟩ : ∃ y' : I,
      lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y <
        lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y' := by
    rw [D_eq]
    by_cases h0 : (y : ℝ) = 0
    · refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
      rw [D_eq]
      simp only [h0, if_true]
      norm_num
    · have hy1 := y.2.1
      have hy2 := y.2.2
      refine ⟨⟨(y : ℝ) / 2, by linarith, by linarith⟩, ?_⟩
      rw [D_eq]
      have h2 : (y : ℝ) / 2 ≠ 0 := by simpa using h0
      simp only [h0, h2, if_false]
      apply Real.exp_lt_exp.2
      rw [abs_div, abs_two]
      have : 0 < |(y : ℝ)| := abs_pos.2 h0
      linarith
  have hpos : 0 < lindsayDK Kernel.id (phiRule hBad 1 1 fun _ : Fin 1 => x0) (Measure.dirac x0) y := by
    rw [D_eq]; exact Real.exp_pos _
  unfold lindsaySupK at hy
  by_cases hb : BddAbove S
  · have := le_csSup hb (hmem y')
    change sSup S = _ at hy
    linarith
  · change sSup S = _ at hy
    rw [Real.sSup_of_not_bddAbove hb] at hy
    linarith

end StatFormal.Wave29d
