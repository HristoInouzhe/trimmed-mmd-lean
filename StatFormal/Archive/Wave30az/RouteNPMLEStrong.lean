import StatFormal.Archive.Wave30az.RouteNPMLE

/-!
# Route — paper 2 `thm:npmle`, `sup = min` for bounded measurable rules

The moment set `Ψ = {(∫ψ_i dm)_i : m ∈ 𝒫(L)} ⊆ ℝⁿ` is convex and lies in a box `[c, C]ⁿ` with `c > 0` (the Feller
condition makes `y ↦ κ(y,K)` continuous, hence bounded below on the compact `L`). `G(p) = n⁻¹Σ log p_i` attains its
maximum on the compact convex `closure Ψ` at some `p*`; the first-order condition there (`foc_of_log_le`) at the
Dirac points `ψ(y) ∈ Ψ` is dual feasibility of `v = 1/p*`, and `sup_Ψ G = G(p*)` by continuity. Weak duality
(`npmle_weak`) gives the rest. No maximiser over `𝒫(L)` is needed.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave30az

open StatFormal.Wave29d (psiK npmleK lambdaK MixSettingK)
open StatFormal.Wave29d.LindsayGen

theorem npmle_gen_strong : Claims.npmle_gen_strong := by
  intro K L _ _ _ _ _ _ _ n κ φ hS hF
  have hn : (0 : ℝ) < n := by exact_mod_cast hS.1
  haveI := isFiniteKernel hS
  obtain ⟨B, hB⟩ := hS.2.2.2
  -- a uniform lower bound for `κ(y, K)`
  have hκc : Continuous fun y => (κ y).real univ := by
    have := hF (fun _ => (1 : ℝ)) continuous_const
    simpa [integral_const] using this
  obtain ⟨y0⟩ := (inferInstance : Nonempty L)
  obtain ⟨y1, -, hy1⟩ := isCompact_univ.exists_isMinOn univ_nonempty hκc.continuousOn
  set c0 := (κ y1).real univ with hc0def
  have hc0 : 0 < c0 := by
    rw [hc0def, measureReal_def]
    exact ENNReal.toReal_pos (hS.2.1 y1).1.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (hS.2.1 y1).2)
  set c := Real.exp (-B) * c0 with hcdef
  have hc : 0 < c := mul_pos (Real.exp_pos _) hc0
  have hψlow : ∀ i y, c ≤ psiK κ φ i y := by
    intro i y
    unfold psiK
    calc c ≤ (κ y).real univ * Real.exp (-B) := by
          rw [hcdef, mul_comm]
          exact mul_le_mul_of_nonneg_right (isMinOn_iff.1 hy1 y (mem_univ _)) (Real.exp_pos _).le
      _ = ∫ _x, Real.exp (-B) ∂(κ y) := by rw [integral_const, smul_eq_mul]
      _ ≤ ∫ x, Real.exp (φ i x) ∂(κ y) :=
          integral_mono (integrable_const _) (exp_integrable hS i y)
            (fun x => Real.exp_le_exp.2 (by linarith [(abs_le.1 (hB i x)).1]))
  obtain ⟨C, -, hC⟩ := psi_le hS
  -- the moment map and the moment set
  set A : Measure L → Fin n → ℝ := fun m i => ∫ y, psiK κ φ i y ∂m with hAdef
  set P : Set (Measure L) := {m | IsProbabilityMeasure m} with hP
  set Ψ := A '' P with hΨ
  set box : Set (Fin n → ℝ) := Icc (fun _ => c) (fun _ => C) with hbox
  have hΨbox : Ψ ⊆ box := by
    rintro _ ⟨m, hm, rfl⟩
    haveI : IsProbabilityMeasure m := hm
    refine ⟨fun i => ?_, fun i => A_le hS hC i⟩
    calc c = ∫ _y, c ∂m := by simp
      _ ≤ ∫ y, psiK κ φ i y ∂m := integral_mono (integrable_const _) (psi_integrable hS i) (hψlow i)
  set S := closure Ψ with hSdef
  have hSbox : S ⊆ box := closure_minimal hΨbox isClosed_Icc
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_Icc _ _).subset hSbox)
  have hΨconv : Convex ℝ Ψ := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
    haveI : IsProbabilityMeasure m := hm
    haveI : IsProbabilityMeasure m' := hm'
    have hb' : b = 1 - a := by linarith
    refine ⟨ENNReal.ofReal a • m + ENNReal.ofReal (1 - a) • m', measConvex_prob m hm m' hm' a ha (by linarith), ?_⟩
    funext i
    simp only [hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add_measure ((psi_integrable hS i).smul_measure ENNReal.ofReal_ne_top)
        ((psi_integrable hS i).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul, hb']
  have hSconv : Convex ℝ S := hΨconv.closure
  have hSpos : ∀ p ∈ S, ∀ i, 0 < p i := fun p hp i => lt_of_lt_of_le hc ((hSbox hp).1 i)
  set G : (Fin n → ℝ) → ℝ := fun p => (1 / n : ℝ) * ∑ i, Real.log (p i) with hG
  have hGc : ContinuousOn G S := by
    refine continuousOn_const.mul (continuousOn_finset_sum _ fun i _ => ?_)
    exact ContinuousOn.log (continuous_apply i).continuousOn fun p hp => (hSpos p hp i).ne'
  have hdirac : ∀ y, (fun i => psiK κ φ i y) ∈ Ψ := fun y =>
    ⟨Measure.dirac y, (inferInstance : IsProbabilityMeasure (Measure.dirac y)), by
      funext i; simp [hAdef, integral_dirac]⟩
  have hSne : S.Nonempty := ⟨_, subset_closure (hdirac y0)⟩
  obtain ⟨ps, hpsS, hpsmax⟩ := hScomp.exists_isMaxOn hSne hGc
  have hps : ∀ i, 0 < ps i := hSpos ps hpsS
  -- the first-order condition at `p*`
  have hfoc : ∀ p ∈ S, ∑ i, p i / ps i ≤ n := by
    intro p hp
    refine StatFormal.Foundations.Lindsay.foc_of_log_le p ps (hSpos p hp) hps fun t ht0 ht1 => ?_
    have hmem : (1 - t) • ps + t • p ∈ S := hSconv hpsS hp (by linarith) ht0.le (by ring)
    have h := isMaxOn_iff.1 hpsmax _ hmem
    simp only [hG, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have hfeas : ∀ y, (1 / n : ℝ) * ∑ i, (1 / ps i) * psiK κ φ i y ≤ 1 := by
    intro y
    have h := hfoc _ (subset_closure (hdirac y))
    calc (1 / n : ℝ) * ∑ i, (1 / ps i) * psiK κ φ i y = (1 / n : ℝ) * ∑ i, psiK κ φ i y / ps i := by
          congr 1; exact Finset.sum_congr rfl fun i _ => one_div_mul_eq_div _ _
      _ ≤ (1 / n : ℝ) * n := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1 := by field_simp
  -- the primal value is `G(p*)`
  rw [lambdaK_eq hS (M := P) (fun m hm => hm)]
  set T := {v | ∃ m ∈ P, v = npmleK κ φ m} with hT
  have hTG : T ⊆ G '' Ψ := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨A m, ⟨m, hm, rfl⟩, rfl⟩
  have hGT : G '' Ψ ⊆ T := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  have hTne : T.Nonempty := ⟨_, Measure.dirac y0, (inferInstance : IsProbabilityMeasure (Measure.dirac y0)), rfl⟩
  have hTle : ∀ v ∈ T, v ≤ G ps := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := hTG hv
    exact isMaxOn_iff.1 hpsmax p (subset_closure hp)
  have hsup : sSup T = G ps := by
    refine le_antisymm (csSup_le hTne hTle) ?_
    have h1 : G ps ∈ closure (G '' Ψ) := hGc.image_closure ⟨ps, hpsS, rfl⟩
    have h2 : closure (G '' Ψ) ⊆ Iic (sSup T) :=
      closure_minimal (fun v hv => le_csSup ⟨G ps, hTle⟩ (hGT hv)) isClosed_Iic
    exact h2 h1
  refine ⟨⟨fun i => 1 / ps i, fun i => one_div_pos.2 (hps i), hfeas, ?_⟩, ?_⟩
  · rw [hsup]
    simp only [hG, one_div, Real.log_inv, Finset.sum_neg_distrib]
    ring
  · rintro D ⟨v, hv, hvf, rfl⟩
    refine csSup_le hTne ?_
    rintro _ ⟨m, hm, rfl⟩
    exact npmle_weak K L n κ φ m v hS hm hv hvf

end StatFormal.Wave30az
