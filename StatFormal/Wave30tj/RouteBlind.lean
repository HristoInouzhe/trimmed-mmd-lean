import StatFormal.Wave30tj.Statements
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Route (wave 30tj): the kernel-blindness construction (untrusted)

* `rl_continuous`: for continuous `g`, `∫₀¹ s(Nx) g(x) dx → 0`: on each cell `[k/N, (k+1)/N]` the integral of `s(N·)` is
  `N⁻¹ ∫_k^{k+1} s = 0` (periodicity, mean zero), so the cell contributes at most `N⁻¹ · osc(g, 1/N)`;
* `riemann_lebesgue_periodic`: approximate `f ∈ L¹([0,1])` by a continuous compactly supported `g` (Mathlib
  `Integrable.exists_hasCompactSupport_integral_sub_le`), `|s| ≤ 1`;
* the construction: `TV(P₀, Q_N) = ½` (`∫_A s(N·) ∈ [−½, ½]` since `(1 ± s(N·))/2 ≥ 0` integrate to `½`, attained on
  `{s(N·) > 0}`), `D_α ≤ MMD` (`g ≡ 1` is a trimming density), `μ_{Q_N} − μ_{P₀} = ∫₀¹ s(Nx) φ(x) dx`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace StatFormal.Wave30tj

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal

open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.Unconditional (Dpop setDist)

/-! ### Cells -/

lemma cell_integral_zero {s : ℝ → ℝ} (hp : Function.Periodic s 1) (h0 : ∫ x in (0 : ℝ)..1, s x = 0)
    {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∫ x in ((k : ℕ) / N : ℝ)..(((k + 1 : ℕ) : ℝ) / N), s (N * x) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [integral_comp_mul_left (fun x => s x) hN']
  have e1 : (N : ℝ) * ((k : ℝ) / N) = k := by field_simp
  have e2 : (N : ℝ) * (((k + 1 : ℕ) : ℝ) / N) = k + 1 := by push_cast; field_simp
  rw [e1, e2, hp.intervalIntegral_add_eq (k : ℝ) 0, zero_add, h0, smul_zero]

lemma intervalIntegrable_sN_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℝ → ℝ}
    (hs : Measurable s) (hb : ∀ x, |s x| ≤ 1) (N : ℕ) {h : ℝ → E} {u v : ℝ}
    (hh : IntervalIntegrable h volume u v) : IntervalIntegrable (fun x => s (N * x) • h x) volume u v := by
  have hsN : Measurable fun x : ℝ => s (N * x) := hs.comp (measurable_const_mul _)
  rw [intervalIntegrable_iff] at hh ⊢
  exact hh.bdd_smul 1 hsN.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb _)

lemma intervalIntegral_sN_zero {s : ℝ → ℝ} (hs : Measurable s) (hp : Function.Periodic s 1) (hb : ∀ x, |s x| ≤ 1)
    (h0 : ∫ x in (0 : ℝ)..1, s x = 0) {N : ℕ} (hN : 0 < N) : ∫ x in (0 : ℝ)..1, s (N * x) = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := sum_integral_adjacent_intervals (μ := volume) (f := fun x => s (N * x))
    (a := fun k : ℕ => (k : ℝ) / N) (n := N) (fun k _ => by
      have := intervalIntegrable_sN_smul (E := ℝ) hs hb N (h := fun _ => (1 : ℝ)) (u := (k : ℝ) / N)
        (v := ((k + 1 : ℕ) : ℝ) / N) intervalIntegrable_const
      simpa using this)
  simp only [Nat.cast_zero, zero_div, div_self hN'.ne'] at hsum
  rw [← hsum]
  exact Finset.sum_eq_zero fun k _ => cell_integral_zero hp h0 hN k

/-! ### Riemann–Lebesgue -/

section RL
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma rl_continuous {g : ℝ → E} (hg : Continuous g) {s : ℝ → ℝ} (hs : Measurable s) (hp : Function.Periodic s 1)
    (hb : ∀ x, |s x| ≤ 1) (h0 : ∫ x in (0 : ℝ)..1, s x = 0) :
    Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..1, s (N * x) • g x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn g (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNδ : 1 / (N : ℝ) < δ := by
    have h1 : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN']
    have := (div_lt_iff₀ hδ).1 hN0
    nlinarith
  rw [dist_zero_right]
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have hsum := sum_integral_adjacent_intervals (μ := volume) (f := fun x => s (N * x) • g x) (a := a) (n := N)
    (fun k _ => intervalIntegrable_sN_smul hs hb N (hg.intervalIntegrable _ _))
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a N = 1 := by simp [a, div_self hN'.ne']
  rw [ha0, haN] at hsum
  rw [← hsum]
  have hcell : ∀ k ∈ Finset.range N, ‖∫ x in a k..a (k + 1), s (N * x) • g x‖ ≤ ε / 2 * (1 / N) := by
    intro k hk
    have hk' : k < N := Finset.mem_range.1 hk
    have hak : a k ≤ a (k + 1) := by
      simp only [a]; gcongr; simp
    have hlen0 : a (k + 1) - a k = 1 / N := by
      simp only [a]; push_cast; field_simp; ring
    have hlen : |a (k + 1) - a k| = 1 / N := by
      rw [hlen0, abs_of_nonneg (by positivity)]
    have hI1 : IntervalIntegrable (fun x => s (N * x) • (g x - g (a k))) volume (a k) (a (k + 1)) :=
      intervalIntegrable_sN_smul hs hb N ((hg.sub continuous_const).intervalIntegrable _ _)
    have hI2 : IntervalIntegrable (fun x => s (N * x) • g (a k)) volume (a k) (a (k + 1)) :=
      intervalIntegrable_sN_smul hs hb N intervalIntegrable_const
    have hsplit : ∫ x in a k..a (k + 1), s (N * x) • g x =
        (∫ x in a k..a (k + 1), s (N * x) • (g x - g (a k))) + ∫ x in a k..a (k + 1), s (N * x) • g (a k) := by
      rw [← integral_add hI1 hI2]
      congr 1; ext x; rw [← smul_add, sub_add_cancel]
    rw [hsplit, intervalIntegral.integral_smul_const, cell_integral_zero hp h0 hNpos k, zero_smul, add_zero]
    have hak0 : 0 ≤ a k := by simp only [a]; positivity
    have hak1 : a (k + 1) ≤ 1 := by
      simp only [a]; rw [div_le_one hN']; exact_mod_cast hk'
    calc ‖∫ x in a k..a (k + 1), s (N * x) • (g x - g (a k))‖ ≤ ε / 2 * |a (k + 1) - a k| := by
          refine norm_integral_le_of_norm_le_const fun x hx => ?_
          rw [uIoc_of_le hak] at hx
          rw [norm_smul, Real.norm_eq_abs]
          have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have hakI : a k ∈ Icc (0 : ℝ) 1 := ⟨hak0, by linarith [hx.1, hx.2]⟩
          have hd : dist x (a k) < δ := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
            have : x - a k ≤ a (k + 1) - a k := by linarith [hx.2]
            linarith
          have := hδg x hxI (a k) hakI hd
          rw [dist_eq_norm] at this
          calc |s (N * x)| * ‖g x - g (a k)‖ ≤ 1 * (ε / 2) :=
                mul_le_mul (hb _) this.le (norm_nonneg _) zero_le_one
            _ = ε / 2 := one_mul _
      _ = ε / 2 * (1 / N) := by rw [hlen]
  calc ‖∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), s (N * x) • g x‖
      ≤ ∑ k ∈ Finset.range N, ‖∫ x in a k..a (k + 1), s (N * x) • g x‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, ε / 2 * (1 / N) := Finset.sum_le_sum hcell
    _ = ε / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by linarith

lemma setIntegral_Icc01 (F : ℝ → E) : ∫ x in Icc (0 : ℝ) 1, F x = ∫ x in (0 : ℝ)..1, F x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem riemann_lebesgue_periodic : Claims.riemann_lebesgue_periodic := by
  intro E _ _ _ f s hf hs hp hb h0
  have hsN : ∀ N : ℕ, Measurable fun x : ℝ => s (N * x) := fun N => hs.comp (measurable_const_mul _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfi : Integrable (indicator (Icc (0 : ℝ) 1) f) volume := (integrable_indicator_iff measurableSet_Icc).2 hf
  obtain ⟨g, -, hfg, hgc, hgi⟩ := hfi.exists_hasCompactSupport_integral_sub_le (ε := ε / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (rl_continuous hgc hs hp hb h0) (ε / 2) (by linarith)
  refine ⟨N0, fun N hN => ?_⟩
  have h1 := hN0 N hN
  rw [dist_zero_right] at h1 ⊢
  rw [← setIntegral_Icc01] at h1
  have hgI : IntegrableOn g (Icc (0 : ℝ) 1) := hgi.integrableOn
  have hfI : Integrable (fun x => s (N * x) • f x) (volume.restrict (Icc (0 : ℝ) 1)) :=
    hf.bdd_smul 1 (hsN N).aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb _)
  have hgI' : Integrable (fun x => s (N * x) • g x) (volume.restrict (Icc (0 : ℝ) 1)) :=
    hgI.bdd_smul 1 (hsN N).aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb _)
  have hdiff : ‖(∫ x in Icc (0 : ℝ) 1, s (N * x) • f x) - ∫ x in Icc (0 : ℝ) 1, s (N * x) • g x‖ ≤ ε / 2 := by
    rw [← integral_sub hfI hgI']
    have hn : Integrable (fun x => ‖f x - g x‖) (volume.restrict (Icc (0 : ℝ) 1)) := (hf.sub hgI).norm
    calc ‖∫ x in Icc (0 : ℝ) 1, (s (N * x) • f x - s (N * x) • g x)‖
        ≤ ∫ x in Icc (0 : ℝ) 1, ‖f x - g x‖ := by
          refine norm_integral_le_of_norm_le hn (ae_of_all _ fun x => ?_)
          rw [← smul_sub, norm_smul, Real.norm_eq_abs]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hb _))
      _ = ∫ x in Icc (0 : ℝ) 1, ‖indicator (Icc (0 : ℝ) 1) f x - g x‖ := by
          refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
          simp only [indicator_of_mem hx]
      _ ≤ ∫ x, ‖indicator (Icc (0 : ℝ) 1) f x - g x‖ :=
          setIntegral_le_integral (hfi.sub hgi).norm (ae_of_all _ fun _ => norm_nonneg _)
      _ ≤ ε / 2 := hfg
  calc ‖∫ x in Icc (0 : ℝ) 1, s (N * x) • f x‖
      ≤ ‖(∫ x in Icc (0 : ℝ) 1, s (N * x) • f x) - ∫ x in Icc (0 : ℝ) 1, s (N * x) • g x‖ +
          ‖∫ x in Icc (0 : ℝ) 1, s (N * x) • g x‖ := norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end RL

end StatFormal.Wave30tj
