import StatFormal.Wave31tq.RouteM21
import StatFormal.Lib.CrossLaws.Gauss

/-!
# Wave 31tq, route M (Q28): the simulated pairs of S6.4 and Figure 2 satisfy the laws of Propositions 5.5 and 5.6 (untrusted)

`simulated_pairs_route : Claims.simulated_pairs` (no cross-chunk hypotheses). With `φ_m = gaussianPDFReal m 1`:
* the shift `N(±a, 1)`: `p − q = φ_a − φ_{−a}` has the sign of `x` (`(x − a)² ≤ (x + a)²` iff `x ≥ 0`), derivative
  `φ_a′(0) − φ_{−a}′(0) = aφ_a(0) + aφ_{−a}(0) = 2aφ_0(a)`;
* the mixtures `0.8N(0,1) + 0.2N(±μ,1)`: densities `0.8φ_0 + 0.2φ_{±μ}` (`CrossLaws.mix_withDensity`), `p − q = 0.2(φ_μ − φ_{−μ})`,
  derivative `0.2(μφ_μ(0) + μφ_{−μ}(0)) = 0.4μφ_0(μ)`, total mass `0.8 + 0.2 = 1`;
* tails: `|P − Q| ≤ P + Q` and the Chernoff bounds `N(m,1)({|x| > t}) ≤ (M(1) + M(−1))e^{−t}` (`CrossLaws.tailExp_gauss`), so
  `|P − Q|({|x| > t}) ≤ C′e^{−t/C′}` with `C′ = 1 + A + B` (`expTail_of_tailExp`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.CrossLaws

/-- `ExpTail` at `0` from `TailExp` bounds of the two laws. -/
theorem expTail_of_tailExp {P Q : Measure ℝ} [IsFiniteMeasure P] [IsFiniteMeasure Q] {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : TailExp P A) (hQ : TailExp Q B) : ExpTail P Q 0 := by
  refine ⟨1 + A + B, by linarith, fun t ht => ?_⟩
  have hset : {x : ℝ | t < |x - 0|} = {x | t < |x|} := by simp only [sub_zero]
  rw [hset]
  calc absPQ P Q {x | t < |x|} ≤ P {x | t < |x|} + Q {x | t < |x|} := absPQ_le_add P Q _
    _ ≤ ENNReal.ofReal (A * Real.exp (-t)) + ENNReal.ofReal (B * Real.exp (-t)) := add_le_add (hP t ht) (hQ t ht)
    _ = ENNReal.ofReal ((A + B) * Real.exp (-t)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ ≤ ENNReal.ofReal ((1 + A + B) * Real.exp (-t / (1 + A + B))) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : Real.exp (-t) ≤ Real.exp (-t / (1 + A + B)) := Real.exp_le_exp.mpr (by
          rw [neg_div, neg_le_neg_iff]; exact div_le_self ht.le (by linarith))
        exact mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by linarith)

/-- `φ_m(0) = φ_0(m)` and `φ_{−m}(0) = φ_0(m)`. -/
theorem gpdf_zero_eq (m : ℝ) : gaussianPDFReal m 1 0 = gaussianPDFReal 0 1 m ∧ gaussianPDFReal (-m) 1 0 = gaussianPDFReal 0 1 m := by
  simp only [gpdf_eq]
  constructor <;> ring_nf

/-- The shift pair `N(±a, 1)` (Q28 (a)). -/
theorem shift_pair {a : ℝ} (ha : 0 < a) :
    IsCross (gaussianReal a 1) (gaussianReal (-a) 1) (gaussianPDFReal a 1) (gaussianPDFReal (-a) 1) 0
        (2 * a * gaussianPDFReal 0 1 a) ∧
      0 < gaussianPDFReal a 1 0 ∧ ExpTail (gaussianReal a 1) (gaussianReal (-a) 1) 0 := by
  obtain ⟨e1, e2⟩ := gpdf_zero_eq a
  have hd : HasDerivAt (fun x => gaussianPDFReal a 1 x - gaussianPDFReal (-a) 1 x) (2 * a * gaussianPDFReal 0 1 a) 0 := by
    convert (hasDerivAt_gpdf a 0).sub (hasDerivAt_gpdf (-a) 0) using 1
    rw [e1, e2]; ring
  refine ⟨⟨measurable_gaussianPDFReal a 1, measurable_gaussianPDFReal (-a) 1, gaussianPDFReal_nonneg a 1,
    gaussianPDFReal_nonneg (-a) 1, gauss_withDensity a, gauss_withDensity (-a),
    ⟨1, one_pos, (continuous_gpdf a).continuousOn, (continuous_gpdf (-a)).continuousOn⟩,
    ae_of_all _ fun x hx => gpdf_le_of_sq_le (by nlinarith), ae_of_all _ fun x hx => gpdf_le_of_sq_le (by nlinarith),
    hd, mul_pos (by positivity) (gaussianPDFReal_pos 0 1 a one_ne_zero)⟩,
    gaussianPDFReal_pos a 1 0 one_ne_zero,
    expTail_of_tailExp (gauss_tail_const_nonneg a) (gauss_tail_const_nonneg (-a)) (tailExp_gauss a) (tailExp_gauss (-a))⟩

/-- The mixture `0.8N(0,1) + 0.2N(m,1)` is a probability measure. -/
theorem mix_prob (m : ℝ) :
    IsProbabilityMeasure ((0.8 : ℝ≥0) • gaussianReal 0 1 + (0.2 : ℝ≥0) • gaussianReal m 1) := by
  constructor
  simp [Measure.add_apply, Measure.smul_apply]
  rw [← ENNReal.coe_add]
  norm_num

/-- The mixture `0.8N(0,1) + 0.2N(m,1)` has the density `0.8φ_0 + 0.2φ_m`. -/
theorem mix_density (m : ℝ) :
    (0.8 : ℝ≥0) • gaussianReal 0 1 + (0.2 : ℝ≥0) • gaussianReal m 1 =
      volume.withDensity (fun x => ENNReal.ofReal (0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal m 1 x)) := by
  have c8 : ((0.8 : ℝ≥0) : ℝ) = 0.8 := by norm_num
  have c2 : ((0.2 : ℝ≥0) : ℝ) = 0.2 := by norm_num
  rw [gauss_withDensity 0, gauss_withDensity m,
    mix_withDensity _ _ (measurable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _) (gaussianPDFReal_nonneg _ _)
      (gaussianPDFReal_nonneg _ _), c8, c2]

/-- The mixture `0.8N(0,1) + 0.2N(m,1)` has `TailExp`. -/
theorem mix_tail (m : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ TailExp ((0.8 : ℝ≥0) • gaussianReal 0 1 + (0.2 : ℝ≥0) • gaussianReal m 1) A :=
  ⟨_, add_nonneg (mul_nonneg (NNReal.coe_nonneg _) (gauss_tail_const_nonneg 0))
      (mul_nonneg (NNReal.coe_nonneg _) (gauss_tail_const_nonneg m)),
    tailExp_add (mul_nonneg (NNReal.coe_nonneg _) (gauss_tail_const_nonneg 0))
      (mul_nonneg (NNReal.coe_nonneg _) (gauss_tail_const_nonneg m))
      (tailExp_smul _ (tailExp_gauss 0)) (tailExp_smul _ (tailExp_gauss m))⟩

/-- Q28 `simulated_pairs` (S6 :157-168; main :264-265). -/
theorem simulated_pairs_route : Claims.simulated_pairs := by
  refine ⟨fun a ha => shift_pair ha, fun μ hμ => ?_⟩
  obtain ⟨e1, e2⟩ := gpdf_zero_eq μ
  have hd : HasDerivAt (fun x => (0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal μ 1 x) -
      (0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal (-μ) 1 x)) (0.4 * μ * gaussianPDFReal 0 1 μ) 0 := by
    convert (((hasDerivAt_gpdf 0 0).const_mul 0.8).add ((hasDerivAt_gpdf μ 0).const_mul 0.2)).sub
      (((hasDerivAt_gpdf 0 0).const_mul 0.8).add ((hasDerivAt_gpdf (-μ) 0).const_mul 0.2)) using 1
    rw [e1, e2]; ring
  obtain ⟨A, hA, hPA⟩ := mix_tail μ
  obtain ⟨B, hB, hQB⟩ := mix_tail (-μ)
  have h0 := gaussianPDFReal_pos 0 1 0 one_ne_zero
  have hμ0 := gaussianPDFReal_pos μ 1 0 one_ne_zero
  refine ⟨mix_prob μ, mix_prob (-μ), ⟨?_, ?_, fun x => ?_, fun x => ?_, mix_density μ, mix_density (-μ), ?_, ?_, ?_, hd, ?_⟩,
    by positivity, expTail_of_tailExp hA hB hPA hQB⟩
  · exact (measurable_const.mul (measurable_gaussianPDFReal 0 1)).add (measurable_const.mul (measurable_gaussianPDFReal μ 1))
  · exact (measurable_const.mul (measurable_gaussianPDFReal 0 1)).add
      (measurable_const.mul (measurable_gaussianPDFReal (-μ) 1))
  · have := gaussianPDFReal_nonneg 0 1 x; have := gaussianPDFReal_nonneg μ 1 x; positivity
  · have := gaussianPDFReal_nonneg 0 1 x; have := gaussianPDFReal_nonneg (-μ) 1 x; positivity
  · exact ⟨1, one_pos, ((continuous_const.mul (continuous_gpdf 0)).add (continuous_const.mul (continuous_gpdf μ))).continuousOn,
      ((continuous_const.mul (continuous_gpdf 0)).add (continuous_const.mul (continuous_gpdf (-μ)))).continuousOn⟩
  · refine ae_of_all _ fun x hx => ?_
    have h := gpdf_le_of_sq_le (a := μ) (b := -μ) (x := x) (by nlinarith)
    show 0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal (-μ) 1 x ≤ 0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal μ 1 x
    linarith
  · refine ae_of_all _ fun x hx => ?_
    have h := gpdf_le_of_sq_le (a := -μ) (b := μ) (x := x) (by nlinarith)
    show 0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal μ 1 x ≤ 0.8 * gaussianPDFReal 0 1 x + 0.2 * gaussianPDFReal (-μ) 1 x
    linarith
  · exact mul_pos (by positivity) (gaussianPDFReal_pos 0 1 μ one_ne_zero)

end StatFormal.Wave31tq.RouteM
