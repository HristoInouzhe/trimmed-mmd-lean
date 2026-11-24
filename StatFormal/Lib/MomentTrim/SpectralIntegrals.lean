import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The spectral integrals of the explicit-trimming bounds (library, untrusted)

The integrals `I_{N,s} = ∫ min(1, v^{2N}/N!²) |v|^{−2s} dv` of Proposition S4.15 (finite when `2N − 2s > −1` and `2s > 1`) and
`∫ min(1, ξ²W²) |ξ|^{−2s} dξ = W^{2s−1} (2/(3−2s) + 2/(2s−1))` of Proposition S4.14 (`1/2 < s < 3/2`), and the substitution
`v = Wξ`: `∫ min(1, (Wξ)^{2N}/N!²) |ξ|^{−2s} dξ = W^{2s−1} I_{N,s}`.

* `integrable_comp_abs_of_integrableOn_Ioi`: an even function integrable on `(0, ∞)` is integrable;
* `integrable_minPow`: `v ↦ min(1, v^{2N}/c) |v|^{−2s}` is integrable (`c > 0`, `1/2 < s < N + 1/2`);
* `integral_minPow_scale`: the substitution `v = Wξ`;
* `integral_minSq`: `∫ min(1, v²) |v|^{−2s} dv = 2/(3−2s) + 2/(2s−1)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real

namespace StatFormal.MomentTrim

/-- An even function `x ↦ f |x|` is integrable as soon as `f` is integrable on `(0, ∞)`. -/
theorem integrable_comp_abs_of_integrableOn_Ioi {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have h := int_Iic.union hf'
  rwa [Iic_union_Ioi, integrableOn_univ] at h

/-- The integrand `min(1, v^{2N}/c) |v|^{−2s}` as a function of `|v|`. -/
lemma minPow_eq_comp_abs (N : ℕ) (c s v : ℝ) :
    min 1 (v ^ (2 * N) / c) * |v| ^ (-2 * s) = (fun u : ℝ => min 1 (u ^ (2 * N) / c) * u ^ (-2 * s)) |v| := by
  simp only
  rw [pow_mul, pow_mul, sq_abs]

/-- **`I_{N,s}` is finite.** For `c > 0` and `1/2 < s < N + 1/2`, `v ↦ min(1, v^{2N}/c) |v|^{−2s}` is integrable. -/
theorem integrable_minPow (N : ℕ) {c s : ℝ} (hc : 0 < c) (hs : 1 / 2 < s) (hsN : s - 1 / 2 < N) :
    Integrable (fun v : ℝ => min 1 (v ^ (2 * N) / c) * |v| ^ (-2 * s)) := by
  set G : ℝ → ℝ := fun u => min 1 (u ^ (2 * N) / c) * u ^ (-2 * s) with hGdef
  have e : (fun v : ℝ => min 1 (v ^ (2 * N) / c) * |v| ^ (-2 * s)) = fun v => G |v| := by
    funext v; exact minPow_eq_comp_abs N c s v
  rw [e]
  refine integrable_comp_abs_of_integrableOn_Ioi (f := G) ?_
  have hmeas : Measurable fun u : ℝ => min 1 (u ^ (2 * N) / c) * u ^ (-2 * s) := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- near `0`: at most `u^{2N}/c · u^{−2s} = u^{2N−2s}/c`, and `2N − 2s > −1`
    have hr : -1 < (2 * N : ℝ) - 2 * s := by linarith
    have hI : IntegrableOn (fun u : ℝ => c⁻¹ * u ^ ((2 * N : ℝ) - 2 * s)) (Ioc 0 1) := by
      refine Integrable.const_mul ?_ _
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (intervalIntegral.intervalIntegrable_rpow' hr)
    refine hI.mono' hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu => ?_))
    have hu0 : 0 < u := hu.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min zero_le_one (div_nonneg (by positivity) hc.le))
      (rpow_nonneg hu0.le _))]
    have h1 : min 1 (u ^ (2 * N) / c) ≤ u ^ (2 * N) / c := min_le_right _ _
    have h2 : u ^ (2 * N) / c * u ^ (-2 * s) = c⁻¹ * u ^ ((2 * N : ℝ) - 2 * s) := by
      rw [sub_eq_add_neg, rpow_add hu0, ← rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
      ring_nf
    calc min 1 (u ^ (2 * N) / c) * u ^ (-2 * s) ≤ u ^ (2 * N) / c * u ^ (-2 * s) :=
          mul_le_mul_of_nonneg_right h1 (rpow_nonneg hu0.le _)
      _ = c⁻¹ * u ^ ((2 * N : ℝ) - 2 * s) := h2
  · -- at infinity: at most `u^{−2s}`, and `−2s < −1`
    have hI : IntegrableOn (fun u : ℝ => u ^ (-2 * s)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hI.mono' hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
    have hu0 : 0 < u := lt_trans one_pos hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min zero_le_one (div_nonneg (by positivity) hc.le))
      (rpow_nonneg hu0.le _))]
    exact mul_le_of_le_one_left (rpow_nonneg hu0.le _) (min_le_left _ _)

/-- **The substitution `v = Wξ`.** For `W > 0`,
`∫ min(1, (Wξ)^{2N}/c) |ξ|^{−2s} dξ = W^{2s−1} ∫ min(1, v^{2N}/c) |v|^{−2s} dv`. -/
theorem integral_minPow_scale (N : ℕ) (c s : ℝ) {W : ℝ} (hW : 0 < W) :
    ∫ ξ : ℝ, min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s) =
      W ^ (2 * s - 1) * ∫ v : ℝ, min 1 (v ^ (2 * N) / c) * |v| ^ (-2 * s) := by
  set F : ℝ → ℝ := fun v => min 1 (v ^ (2 * N) / c) * |v| ^ (-2 * s)
  have e : ∀ ξ : ℝ, min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s) = W ^ (2 * s) * F (W * ξ) := by
    intro ξ
    simp only [F]
    rw [abs_mul, abs_of_pos hW, mul_rpow hW.le (abs_nonneg ξ)]
    have : W ^ (2 * s) * W ^ (-2 * s) = 1 := by
      rw [← rpow_add hW]; simp
    calc min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s)
        = (W ^ (2 * s) * W ^ (-2 * s)) * (min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s)) := by rw [this, one_mul]
      _ = _ := by ring
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_mul_left F W, abs_of_pos (inv_pos.mpr hW), smul_eq_mul, ← mul_assoc,
    ← rpow_neg_one, ← rpow_add hW]
  ring_nf

/-- **The integral of Proposition S4.14.** For `1/2 < s < 3/2`, `∫ min(1, v²) |v|^{−2s} dv = 2/(3−2s) + 2/(2s−1)`. -/
theorem integral_minSq {s : ℝ} (hs : 1 / 2 < s) (hs3 : s < 3 / 2) :
    ∫ v : ℝ, min 1 (v ^ 2) * |v| ^ (-2 * s) = 2 / (3 - 2 * s) + 2 / (2 * s - 1) := by
  set G : ℝ → ℝ := fun u => min 1 (u ^ 2) * u ^ (-2 * s)
  have e : ∀ v : ℝ, min 1 (v ^ 2) * |v| ^ (-2 * s) = G |v| := fun v => by simp only [G, sq_abs]
  simp_rw [e]
  rw [integral_comp_abs]
  have hG1 : ∀ u ∈ Ioc (0 : ℝ) 1, G u = u ^ (2 - 2 * s) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hsq : u ^ 2 ≤ 1 := by nlinarith [hu.2]
    simp only [G]
    rw [min_eq_right hsq, sub_eq_add_neg, rpow_add hu0, ← rpow_natCast]
    norm_num
  have hG2 : ∀ u ∈ Ioi (1 : ℝ), G u = u ^ (-2 * s) := by
    intro u hu
    have hsq : 1 ≤ u ^ 2 := by nlinarith [mem_Ioi.mp hu]
    simp only [G]
    rw [min_eq_left hsq, one_mul]
  have hr : -1 < 2 - 2 * s := by linarith
  have hI1 : IntegrableOn G (Ioc 0 1) := by
    refine IntegrableOn.congr_fun ?_ (fun u hu => (hG1 u hu).symm) measurableSet_Ioc
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (intervalIntegral.intervalIntegrable_rpow' hr)
  have hI2 : IntegrableOn G (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).congr_fun (fun u hu => (hG2 u hu).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2,
    setIntegral_congr_fun measurableSet_Ioc hG1, setIntegral_congr_fun measurableSet_Ioi hG2,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr),
    integral_Ioi_rpow_of_lt (by linarith) one_pos]
  have h3 : (2 - 2 * s) + 1 = 3 - 2 * s := by ring
  have h4 : (-2 * s) + 1 = -(2 * s - 1) := by ring
  rw [h3, h4, one_rpow, one_rpow, zero_rpow (by linarith : (3 - 2 * s) ≠ 0)]
  have h5 : (3 - 2 * s) ≠ 0 := by linarith
  have h6 : (2 * s - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- The scaled integrand `min(1, (Wξ)^{2N}/c) |ξ|^{−2s}` is `W^{2s}` times the integrand at `Wξ` (`W > 0`). -/
lemma minPow_scale_eq (N : ℕ) (c s : ℝ) {W : ℝ} (hW : 0 < W) (ξ : ℝ) :
    min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s) =
      W ^ (2 * s) * (min 1 ((W * ξ) ^ (2 * N) / c) * |W * ξ| ^ (-2 * s)) := by
  rw [abs_mul, abs_of_pos hW, mul_rpow hW.le (abs_nonneg ξ)]
  have : W ^ (2 * s) * W ^ (-2 * s) = 1 := by
    rw [← rpow_add hW]; simp
  calc min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s)
      = (W ^ (2 * s) * W ^ (-2 * s)) * (min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s)) := by rw [this, one_mul]
    _ = _ := by ring

/-- The scaled integrand is integrable (`W > 0`, `c > 0`, `1/2 < s < N + 1/2`). -/
theorem integrable_minPow_scale (N : ℕ) {c s W : ℝ} (hc : 0 < c) (hs : 1 / 2 < s) (hsN : s - 1 / 2 < N) (hW : 0 < W) :
    Integrable (fun ξ : ℝ => min 1 ((W * ξ) ^ (2 * N) / c) * |ξ| ^ (-2 * s)) := by
  simp_rw [minPow_scale_eq N c s hW]
  exact ((integrable_minPow N hc hs hsN).comp_mul_left' hW.ne').const_mul _

end StatFormal.MomentTrim
