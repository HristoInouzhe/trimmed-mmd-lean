import StatFormal.Lib.CrossLaws.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Gaussian densities on the line: derivative, comparison, mixtures, exponential tails (library, untrusted)

Facts about the unit-variance Gaussian density `φ_m(x) = (2π)^{−1/2}e^{−(x−m)²/2}` (Mathlib's `gaussianPDFReal m 1`) and its law
`N(m, 1)` (`gaussianReal m 1`), used to check that the simulated pairs of the trimmed-mmd paper (the shift `N(±a, 1)` and the
mixtures `0.8N(0,1) + 0.2N(±μ,1)`) satisfy the laws of Propositions 5.5 and 5.6.

* `gpdf_eq`, `continuous_gpdf`, `hasDerivAt_gpdf` (`φ_m′(x) = −(x − m)φ_m(x)`), `gpdf_le_of_sq_le` (`φ_b(x) ≤ φ_a(x)` when
  `(x − a)² ≤ (x − b)²`), `gauss_withDensity`;
* `mix_withDensity`: `c·(f·Leb) + d·(g·Leb) = (cf + dg)·Leb` for `c, d ∈ ℝ≥0`;
* `TailExp μ A` (`μ({|x| > t}) ≤ Ae^{−t}` for `t > 0`): `tailExp_gauss` (Chernoff bounds through the moment generating function at
  `±1`), `tailExp_smul`, `tailExp_add`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.CrossLaws

/-- `φ_m(x) = (2π)^{−1/2} e^{−(x−m)²/2}`. -/
theorem gpdf_eq (m x : ℝ) : gaussianPDFReal m 1 x = (√(2 * Real.pi))⁻¹ * Real.exp (-(x - m) ^ 2 / 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]

/-- `φ_m` is continuous. -/
theorem continuous_gpdf (m : ℝ) : Continuous (gaussianPDFReal m 1) := by
  rw [funext (gpdf_eq m)]
  fun_prop

/-- `φ_m′(x) = −(x − m)φ_m(x)`. -/
theorem hasDerivAt_gpdf (m x : ℝ) : HasDerivAt (gaussianPDFReal m 1) (-(x - m) * gaussianPDFReal m 1 x) x := by
  rw [funext (gpdf_eq m)]
  have h1 : HasDerivAt (fun y : ℝ => -(y - m) ^ 2 / 2) (-(x - m)) x := by
    have h := (((hasDerivAt_id' x).sub_const m).pow 2).neg.div_const 2
    convert h using 1
    push_cast
    ring
  convert h1.exp.const_mul (√(2 * Real.pi))⁻¹ using 1
  ring

/-- `φ_b(x) ≤ φ_a(x)` when `(x − a)² ≤ (x − b)²`. -/
theorem gpdf_le_of_sq_le {a b x : ℝ} (h : (x - a) ^ 2 ≤ (x - b) ^ 2) : gaussianPDFReal b 1 x ≤ gaussianPDFReal a 1 x := by
  rw [gpdf_eq, gpdf_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith

/-- `N(m, 1) = φ_m · Leb`. -/
theorem gauss_withDensity (m : ℝ) :
    gaussianReal m 1 = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal m 1 x)) :=
  gaussianReal_of_var_ne_zero m one_ne_zero

/-- `c·(f·Leb) + d·(g·Leb) = (cf + dg)·Leb` for `c, d ∈ ℝ≥0` and measurable `f, g ≥ 0`. -/
theorem mix_withDensity (c d : ℝ≥0) {f g : ℝ → ℝ} (hf : Measurable f) (_hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) :
    c • volume.withDensity (fun x => ENNReal.ofReal (f x)) + d • volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      volume.withDensity (fun x => ENNReal.ofReal ((c : ℝ) * f x + (d : ℝ) * g x)) := by
  rw [ENNReal.smul_def, ENNReal.smul_def, ← withDensity_smul' _ _ ENNReal.coe_ne_top,
    ← withDensity_smul' _ _ ENNReal.coe_ne_top, ← withDensity_add_left ((hf.ennreal_ofReal).const_smul _)]
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_add (mul_nonneg (NNReal.coe_nonneg c) (hf0 x)) (mul_nonneg (NNReal.coe_nonneg d) (hg0 x)), ENNReal.ofReal_mul (NNReal.coe_nonneg c),
    ENNReal.ofReal_mul (NNReal.coe_nonneg d), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

/-- `μ({|x| > t}) ≤ Ae^{−t}` for every `t > 0`. -/
def TailExp (μ : Measure ℝ) (A : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → μ {x | t < |x|} ≤ ENNReal.ofReal (A * Real.exp (-t))

/-- **Gaussian tails** (Chernoff at `±1`): `N(m, 1)({|x| > t}) ≤ (M(1) + M(−1))e^{−t}`, `M` the moment generating function. -/
theorem tailExp_gauss (m : ℝ) :
    TailExp (gaussianReal m 1) (mgf (fun x => x) (gaussianReal m 1) 1 + mgf (fun x => x) (gaussianReal m 1) (-1)) := by
  intro t ht
  set G := gaussianReal m 1 with hG
  have hsub : {x : ℝ | t < |x|} ⊆ {x | t ≤ x} ∪ {x | x ≤ -t} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    rcases le_or_gt 0 x with h | h
    · left; rw [abs_of_nonneg h] at hx; exact hx.le
    · right; rw [abs_of_neg h] at hx; show x ≤ -t; linarith
  have h1 : G.real {x | t ≤ x} ≤ Real.exp (-1 * t) * mgf (fun x => x) G 1 :=
    measure_ge_le_exp_mul_mgf (X := fun x => x) t zero_le_one (integrable_exp_mul_gaussianReal 1)
  have h2 : G.real {x | x ≤ -t} ≤ Real.exp (-(-1) * -t) * mgf (fun x => x) G (-1) :=
    measure_le_le_exp_mul_mgf (X := fun x => x) (-t) (by norm_num) (integrable_exp_mul_gaussianReal (-1))
  have e1 : Real.exp (-1 * t) = Real.exp (-t) := by ring_nf
  have e2 : Real.exp (-(-1) * -t) = Real.exp (-t) := by ring_nf
  rw [e1] at h1
  rw [e2] at h2
  have hm1 : 0 ≤ mgf (fun x => x) G 1 := mgf_nonneg
  have hm2 : 0 ≤ mgf (fun x => x) G (-1) := mgf_nonneg
  calc G {x | t < |x|} ≤ G ({x | t ≤ x} ∪ {x | x ≤ -t}) := measure_mono hsub
    _ ≤ G {x | t ≤ x} + G {x | x ≤ -t} := measure_union_le _ _
    _ = ENNReal.ofReal (G.real {x | t ≤ x}) + ENNReal.ofReal (G.real {x | x ≤ -t}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-t) * mgf (fun x => x) G 1) + ENNReal.ofReal (Real.exp (-t) * mgf (fun x => x) G (-1)) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal ((mgf (fun x => x) G 1 + mgf (fun x => x) G (-1)) * Real.exp (-t)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- `TailExp` under a nonnegative scalar. -/
theorem tailExp_smul {μ : Measure ℝ} {A : ℝ} (c : ℝ≥0) (h : TailExp μ A) : TailExp (c • μ) ((c : ℝ) * A) := by
  intro t ht
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc (c : ℝ≥0∞) * μ {x | t < |x|} ≤ (c : ℝ≥0∞) * ENNReal.ofReal (A * Real.exp (-t)) := by gcongr; exact h t ht
    _ = ENNReal.ofReal ((c : ℝ) * A * Real.exp (-t)) := by
        rw [mul_assoc, ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_coe_nnreal]

/-- `TailExp` of a sum. -/
theorem tailExp_add {μ ν : Measure ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hμ : TailExp μ A) (hν : TailExp ν B) :
    TailExp (μ + ν) (A + B) := by
  intro t ht
  rw [Measure.add_apply]
  calc μ {x | t < |x|} + ν {x | t < |x|} ≤ ENNReal.ofReal (A * Real.exp (-t)) + ENNReal.ofReal (B * Real.exp (-t)) :=
        add_le_add (hμ t ht) (hν t ht)
    _ = ENNReal.ofReal ((A + B) * Real.exp (-t)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The moment generating functions in `tailExp_gauss` are nonnegative. -/
theorem gauss_tail_const_nonneg (m : ℝ) :
    0 ≤ mgf (fun x => x) (gaussianReal m 1) 1 + mgf (fun x => x) (gaussianReal m 1) (-1) :=
  add_nonneg mgf_nonneg mgf_nonneg

end StatFormal.CrossLaws
