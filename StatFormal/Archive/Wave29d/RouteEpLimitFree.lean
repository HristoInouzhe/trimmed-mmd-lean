import StatFormal.Archive.Wave29d.RouteLocLower

/-!
# Route — robust equality JASA `thm:ep-limit0` (i), free class `≤ ε log n` (untrusted)

`OT_ε(P̂, P̂) = max_f J_{P̂}(f)` (frozen strong duality) and, dropping all but the `j`-th exponential in
`g_f(x_j) = −ε log n⁻¹ Σ_i e^{(f_i − c_i(x_j))/ε}`, `g_f(x_j) ≤ ε log n − f_j`, so `J_{P̂}(f) ≤ ε log n` for every `f`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave29d

open StatFormal.RobustEquality.Semidual (gsoft muDisc)
open StatFormal.RobustEquality.SemidualStrong (OTdisc Jdual Setting)

theorem eplimit_free_logn : Claims.eplimit_free_logn := by
  intro K _ n ε x c hn hε hcm hcB hcx
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set a : Fin n → ℝ := fun _ => 1 / (n : ℝ)
  have hset : Setting ε a c := ⟨hε, fun _ => by positivity, by simp [a, Finset.card_univ]; field_simp, hcm, hcB⟩
  set Q := ∑ j, ENNReal.ofReal (1 / (n : ℝ)) • Measure.dirac (x j) with hQ
  have hQp : IsProbabilityMeasure Q := by
    constructor
    simp only [hQ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (n : ℝ) * (1 / n) = 1 by field_simp]; simp
  have hJ : ∀ f, Jdual ε a c Q f ≤ ε * Real.log n := by
    intro f
    have hgm := StatFormal.RobustEquality.Semidual.measurable_gsoft ε a f c hcm
    have hint : ∫ y, gsoft ε a f c y ∂Q = ∑ j, 1 / (n : ℝ) * gsoft ε a f c (x j) := by
      rw [hQ, integral_finset_sum_measure (fun j _ =>
        ((LocLower.gsoft_integrable hset f (Measure.dirac (x j))).smul_measure ENNReal.ofReal_ne_top))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_smul_measure, integral_dirac' _ _ hgm.stronglyMeasurable, ENNReal.toReal_ofReal (by positivity),
        smul_eq_mul]
    have hg : ∀ j, gsoft ε a f c (x j) ≤ ε * Real.log n - f j := by
      intro j
      unfold gsoft
      have hpos : 0 < a j * Real.exp ((f j - c j (x j)) / ε) := by positivity
      have hle : a j * Real.exp ((f j - c j (x j)) / ε) ≤ ∑ i, a i * Real.exp ((f i - c i (x j)) / ε) :=
        Finset.single_le_sum (f := fun i => a i * Real.exp ((f i - c i (x j)) / ε)) (fun i _ => by positivity)
          (Finset.mem_univ j)
      have hlog := Real.log_le_log hpos hle
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, hcx, sub_zero] at hlog
      have haj : Real.log (a j) = -Real.log n := by simp only [a, one_div, Real.log_inv]
      rw [haj] at hlog
      have : ε * (f j / ε) = f j := by field_simp
      have h3 := mul_le_mul_of_nonneg_left hlog hε.le
      rw [mul_add, this] at h3
      linarith
    unfold Jdual
    rw [hint]
    have : ∑ j, 1 / (n : ℝ) * gsoft ε a f c (x j) ≤ ∑ j, 1 / (n : ℝ) * (ε * Real.log n - f j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hg j) (by positivity)
    have h2 : ∑ j : Fin n, 1 / (n : ℝ) * (ε * Real.log n - f j) = ε * Real.log n - ∑ i, a i * f i := by
      simp only [a, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    linarith
  obtain ⟨fs, -, hval, -⟩ := StatFormal.RobustEquality.SemidualStrong.strong_duality _ n ε a c Q hset
  have h1 : OTdisc ε a c Q ≤ ((ε * Real.log n : ℝ) : EReal) := by
    rw [hval, EReal.coe_le_coe_iff]; exact hJ fs
  exact ⟨h1, (iInf₂_le Q hQp).trans h1⟩

end StatFormal.Wave29d
