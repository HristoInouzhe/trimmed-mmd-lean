import StatFormal.Lib.KernelRun.Median
import StatFormal.Lib.PaperRunThm.EmpVar


/-!
# Wave 31tr, chunk A3, T49 (b): the printed bandwidth rules and kernel profiles (untrusted route)

* `median_bandwidth_route` (T49 (b) (i)): the median heuristic `medianBw ρ` is measurable and positive (library
  `Lib/KernelRun/Median.lean`: order statistics at the measurable rank `zeroCount + ⌊(k² − zeroCount)/2⌋ (+1)`).
* `kernel_profiles_route` (T49 (b) (ii)–(iii)): the Laplace and Gaussian profiles are jointly measurable in `(θ, x, y)` and valued in
  `[0,1]` (the exponent is `≤ 0`: a nonnegative distance divided by `|σ| ≥ 0`, resp. by `2σ² ≥ 0`, junk `/0 = 0` included); the
  scaled distance is measurable, nonnegative, symmetric and zero on the diagonal; the batch-0 scales are measurable (an `if` on the
  measurable event `{empVar = 0}`, `empVar` continuous) and positive (`1`, or the square root of a positive variance).
-/

set_option linter.style.longLine false


noncomputable section
open MeasureTheory

namespace StatFormal.Wave31tr.RouteKernel

open StatFormal.KernelRun StatFormal.PaperRunThm

/-- **T49 (b) (i)**: the median heuristic is a measurable, positive function of the points. -/
theorem median_bandwidth_route : Claims.median_bandwidth := by
  intro E _ ρ k hρ hρ0 _ _
  exact ⟨measurable_medianBw hρ k, medianBw_pos hρ0⟩

/-- The scaled distance is jointly measurable in the scales and the two points. -/
theorem measurable_scaledDist_joint (d : ℕ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => scaledDist p.1 p.2.1 p.2.2 := by
  unfold scaledDist
  fun_prop

theorem scaledDist_nonneg {d : ℕ} (s x y : Fin d → ℝ) : 0 ≤ scaledDist s x y := Real.sqrt_nonneg _

theorem measurable_empVar_coord (k d : ℕ) (i : Fin d) : Measurable fun z : Fin k → Fin d → ℝ => empVar fun l => z l i := by
  have h := (measurable_popVar k).comp (Measurable.of_eval fun l => (measurable_pi_apply i).comp (measurable_pi_apply l) :
    Measurable fun z : Fin k → Fin d → ℝ => fun l => z l i)
  exact h

theorem measurable_lapK_joint (d : ℕ) :
    Measurable fun p : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) × (Fin d → ℝ) => lapK p.1 p.2.1 p.2.2 := by
  unfold lapK scaledDist
  fun_prop

theorem measurable_gaussK_joint (d : ℕ) :
    Measurable fun p : (ℝ × (Fin d → ℝ)) × (Fin d → ℝ) × (Fin d → ℝ) => gaussK p.1 p.2.1 p.2.2 := by
  unfold gaussK scaledDist
  fun_prop

theorem measurable_scaledDist (d : ℕ) (s : Fin d → ℝ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => scaledDist s p.1 p.2 := by
  unfold scaledDist
  fun_prop

theorem lapK_le_one {d : ℕ} (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ) : lapK θ x y ≤ 1 := by
  unfold lapK
  rw [Real.exp_le_one_iff, neg_div]
  exact neg_nonpos.mpr (div_nonneg (scaledDist_nonneg _ _ _) (abs_nonneg _))

theorem gaussK_le_one {d : ℕ} (θ : ℝ × (Fin d → ℝ)) (x y : Fin d → ℝ) : gaussK θ x y ≤ 1 := by
  unfold gaussK
  rw [Real.exp_le_one_iff, neg_div]
  have h2 : (0 : ℝ) ≤ 2 * θ.1 ^ 2 := mul_nonneg zero_le_two (sq_nonneg _)
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) h2)

theorem scaledDist_symm {d : ℕ} (s a b : Fin d → ℝ) : scaledDist s a b = scaledDist s b a := by
  unfold scaledDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← neg_sub (b i), neg_div, neg_sq]

theorem scaledDist_self {d : ℕ} (s a : Fin d → ℝ) : scaledDist s a a = 0 := by
  unfold scaledDist
  simp only [sub_self, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    Real.sqrt_zero]

theorem measurable_b0Scale (k d : ℕ) : Measurable fun z : Fin k → Fin d → ℝ => b0Scale z := by
  refine Measurable.of_eval fun i => ?_
  unfold b0Scale
  exact Measurable.ite (measurableSet_eq_fun (measurable_empVar_coord k d i) measurable_const) measurable_const
    (measurable_empVar_coord k d i).sqrt

theorem b0Scale_pos {k d : ℕ} (z : Fin k → Fin d → ℝ) (i : Fin d) : 0 < b0Scale z i := by
  unfold b0Scale
  split_ifs with h
  · exact one_pos
  · have h0 : 0 ≤ empVar fun l => z l i := popVar_nonneg _
    exact Real.sqrt_pos.mpr (lt_of_le_of_ne h0 (Ne.symm h))

/-- **T49 (b) (ii)–(iii)**: the Laplace and Gaussian profiles, the scaled distance and the batch-0 scales. -/
theorem kernel_profiles_route : Claims.kernel_profiles := by
  intro d
  refine ⟨measurable_lapK_joint d, measurable_gaussK_joint d, fun θ x y => ⟨(Real.exp_pos _).le, lapK_le_one θ x y⟩,
    fun θ x y => ⟨(Real.exp_pos _).le, gaussK_le_one θ x y⟩, measurable_scaledDist d,
    fun s a b => ⟨scaledDist_nonneg s a b, scaledDist_symm s a b, scaledDist_self s a⟩,
    fun k => ⟨measurable_b0Scale k d, b0Scale_pos⟩⟩

end StatFormal.Wave31tr.RouteKernel
