import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Elementary bounds for `H¹` functions of the line (library, untrusted)

* `integral_abs_le_sqrt`: Cauchy–Schwarz on an interval, `∫_a^b |h| ≤ √((b − a) ∫_ℝ h²)` for `h ∈ L²(ℝ)`;
* `eVariationOn_le_of_ac`: the variation of an absolutely continuous `f` on `[a, b]` is at most `∫_a^b |f′|` (each increment is
  `|∫_{u_i}^{u_{i+1}} f′| ≤ ∫_{u_i}^{u_{i+1}} |f′|`, by the fundamental theorem of calculus for absolutely continuous functions), hence
  at most any bound `B` of that integral;
* `abs_le_one_of_osc`: a bounded function tending to `0` at `+∞` has `inf f ≤ 0 ≤ sup f`, so `sup f − inf f ≤ 1` forces `|f| ≤ 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.LaplaceH1

/-- **Cauchy–Schwarz on an interval**: `∫_a^b |h| ≤ √((b − a) ∫_ℝ h²)` for `h ∈ L²(ℝ)` and `a ≤ b`. -/
theorem integral_abs_le_sqrt {h : ℝ → ℝ} (hh : MemLp h 2 volume) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, |h x| ≤ √((b - a) * ∫ x, h x ^ 2) := by
  rw [intervalIntegral.integral_of_le hab]
  have : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hhμ : MemLp h 2 (volume.restrict (Ioc a b)) := hh.restrict _
  have habs : MemLp (fun x => |h x|) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := by
    rw [ENNReal.ofReal_ofNat]
    simpa [Real.norm_eq_abs] using hhμ.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := memLp_const 1
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc a b)) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => abs_nonneg (h x)) (Eventually.of_forall fun _ => zero_le_one) habs hone
  simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul] at hCS
  have h2 : ∀ x, |h x| ^ (2 : ℝ) = h x ^ 2 := fun x => by rw [Real.rpow_two, sq_abs]
  simp only [h2] at hCS
  have hvol : (volume.restrict (Ioc a b)).real univ = b - a := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hab]
  rw [hvol] at hCS
  have hsub : ∫ x in Ioc a b, h x ^ 2 ≤ ∫ x, h x ^ 2 :=
    setIntegral_le_integral hh.integrable_sq (Eventually.of_forall fun x => sq_nonneg _)
  refine hCS.trans ?_
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_comm, ← Real.sqrt_mul (by linarith)]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsub (by linarith))

/-- **The variation of an absolutely continuous function** on `[a, b]` is at most `∫_a^b |f′|`; hence any bound on that
integral bounds the variation. -/
theorem eVariationOn_le_of_ac {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) {B : ℝ}
    (hB : ∫ x in a..b, |deriv f x| ≤ B) : eVariationOn f (Icc a b) ≤ ENNReal.ofReal B := by
  have hint : IntervalIntegrable (fun x => |deriv f x|) volume a b := hf.intervalIntegrable_deriv.abs
  have hsub : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → uIcc x y ⊆ uIcc a b := fun x y hx hy =>
    uIcc_subset_uIcc (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])
  have key : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x ≤ y → |f y - f x| ≤ ∫ t in x..y, |deriv f t| := by
    intro x y hx hy hxy
    rw [← (hf.mono (hsub x y hx hy)).integral_deriv_eq_sub]
    exact intervalIntegral.abs_integral_le_integral_abs hxy
  refine iSup_le fun ⟨n, ⟨u, hu, hus⟩⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), |deriv f t|) := by
        gcongr with i hi
        rw [edist_dist, Real.dist_eq]
        exact ENNReal.ofReal_le_ofReal (key _ _ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), |deriv f t|) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ =>
          intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) fun _ _ => abs_nonneg _).symm
    _ = ENNReal.ofReal (∫ t in u 0..u n, |deriv f t|) := by
        rw [intervalIntegral.sum_integral_adjacent_intervals]
        intro k _
        exact hint.mono_set (hsub _ _ (hus k) (hus (k + 1)))
    _ ≤ ENNReal.ofReal B := by
        refine ENNReal.ofReal_le_ofReal (le_trans ?_ hB)
        exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
          (Eventually.of_forall fun _ => abs_nonneg _) hint

/-- A bounded function tending to `0` at `+∞` with `sup f − inf f ≤ 1` has `|f| ≤ 1` (`inf f ≤ 0 ≤ sup f`). -/
theorem abs_le_one_of_osc {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (htop : Tendsto f atTop (𝓝 0))
    (hosc : (⨆ x, f x) - (⨅ x, f x) ≤ 1) (x : ℝ) : |f x| ≤ 1 := by
  have hba : BddAbove (range f) := ⟨C, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (hC y)⟩
  have hbb : BddBelow (range f) := ⟨-C, by rintro _ ⟨y, rfl⟩; exact (neg_le_neg (hC y)).trans (neg_abs_le _)⟩
  have hS : 0 ≤ ⨆ x, f x := le_of_tendsto htop (Eventually.of_forall fun y => le_ciSup hba y)
  have hI : ⨅ x, f x ≤ 0 := ge_of_tendsto htop (Eventually.of_forall fun y => ciInf_le hbb y)
  have h1 : f x ≤ ⨆ x, f x := le_ciSup hba x
  have h2 : ⨅ x, f x ≤ f x := ciInf_le hbb x
  rw [abs_le]; constructor <;> linarith

end StatFormal.LaplaceH1
