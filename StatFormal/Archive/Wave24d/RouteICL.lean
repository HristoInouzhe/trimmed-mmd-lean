import StatFormal.Archive.Wave24d.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Route — ICL `cor:consistency`: the vanishing deviation and the consistency chain (untrusted)

`√(2M log n/m) → 0`, `log(2n)/m = (log 2 + log n)/m → 0`, `log m/(2m) → 0` (`log x/x → 0`). Chain: on the oracle event
`R(μ_ŵ) − R⋆ ≤ (A_j − R⋆) + r_j`, eventually `< ε`, so `P(R(μ_ŵ) − R⋆ ≥ ε) ≤ P(Sᶜ) ≤ 1/m → 0`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave24d

lemma tendsto_sqrt_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) : Tendsto (fun j => √(f j)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp hf
  simpa [Function.comp_def] using this

theorem icl_dev_vanishes : Claims.icl_dev_vanishes := by
  intro BL lcov Kmin Kmax M n m hn hm hlog
  have h1 : Tendsto (fun j => 2 * M * Real.log (n j) / m j) atTop (𝓝 0) := by
    have := hlog.const_mul (2 * (M : ℝ))
    simp only [mul_zero] at this
    refine this.congr fun j => ?_
    ring
  have hinv : Tendsto (fun j => (1 : ℝ) / m j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hm
  have h2 : Tendsto (fun j => 2 * Real.log (2 * n j) / m j) atTop (𝓝 0) := by
    have hsum := ((hinv.const_mul (2 * Real.log 2)).add (hlog.const_mul 2))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    rw [Real.log_mul (by norm_num) hj.ne']
    ring
  have h3 : Tendsto (fun j => Real.log (1 / (1 / (m j : ℝ))) / (2 * m j)) atTop (𝓝 0) := by
    have hl := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 two_ne_zero).comp hm
    refine hl.congr fun j => ?_
    simp only [Function.comp_apply, pow_one, add_zero, one_div, inv_inv]
  have := ((tendsto_sqrt_zero h1).const_mul (4 * BL)).add ((tendsto_sqrt_zero h2).const_mul (4 * lcov * (Kmax / Kmin)))
    |>.add ((tendsto_sqrt_zero h3).const_mul (BL + lcov * Real.log (Kmax / Kmin)))
  simp only [mul_zero, add_zero] at this
  refine this.congr fun j => ?_
  unfold devBound; ring

theorem icl_consistency : Claims.icl_consistency := by
  intro Ω _ P _ Rhat A Rstar lamKL eps n m BL lcov Kmin Kmax M hge hev happ hn hm hlog hkl heps
  have hdev := icl_dev_vanishes BL lcov Kmin Kmax M n m hn hm hlog
  have hr : Tendsto (fun j => lamKL j * Real.log (n j) + eps j +
      2 * devBound BL lcov Kmin Kmax M (n j) (m j) (1 / m j)) atTop (𝓝 0) := by
    have := (hkl.add heps).add (hdev.const_mul 2)
    simpa using this
  have hinv : Tendsto (fun j => ENNReal.ofReal (1 / m j)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop hm : Tendsto (fun j => (1 : ℝ) / m j) atTop (𝓝 0))
    simpa using this
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv (Eventually.of_forall fun _ => zero_le)
    ?_
  filter_upwards [hev, happ (ε / 2) (by linarith), hr.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)),
    hm.eventually (eventually_ge_atTop 1)] with j hevj hA hrj hmj
  obtain ⟨S, hSm, hPS, hS⟩ := hevj
  have hsub : {ω | ε ≤ dist (Rhat j ω) Rstar} ⊆ Sᶜ := by
    intro ω hω hωS
    have h1 := hS ω hωS
    have h2 := hge j ω
    simp only [mem_setOf_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h2)] at hω
    linarith
  refine (measure_mono hsub).trans ?_
  rw [prob_compl_eq_one_sub hSm]
  have hx0 : 0 ≤ 1 / (m j : ℝ) := by positivity
  have hx1 : 1 / (m j : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hmj
  have hsplit : (1 : ℝ≥0∞) = ENNReal.ofReal (1 - 1 / m j) + ENNReal.ofReal (1 / m j) := by
    rw [← ENNReal.ofReal_add (by linarith) hx0]; simp
  calc 1 - P S ≤ 1 - ENNReal.ofReal (1 - 1 / m j) := tsub_le_tsub_left hPS _
    _ = ENNReal.ofReal (1 / m j) := by
        rw [hsplit, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]

end StatFormal.Wave24d
