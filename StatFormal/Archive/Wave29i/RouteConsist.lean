import StatFormal.Archive.Wave29i.RouteConsistReduction
import StatFormal.Archive.Wave29i.RouteConsistApprox

/-!
# Route — ICL `cor:consistency`, first claim (untrusted)

`consist_check`: the frozen conditional chain `Wave24d.icl_consistency`, fed with
* `R̂_j = max(R⋆, R(μ_ŵ))` (equal to `R(μ_ŵ)` for all large `j`, since `ŵ ∈ Δ^(M)` makes `μ_ŵ` admissible on the
  pool event), `A_j = inf_{Δ^(M)} R(μ_w)` (a nonempty set bounded below by `R⋆` for large `j`);
* premise (1) from `consist_reduction` (the oracle event at every large `j`);
* premise (2) from `consist_approx`;
gives `R̂_j → R⋆` in probability, hence `R(μ_ŵ) → R⋆`. `R⋆` exists as `sInf` of a nonempty (`P₀`, atomless, is
admissible) set bounded below (`−λ_cov log K_max`). `consist_risk` is `consist_check` applied to the three proofs.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29i

open StatFormal.Wave11b (distinctSet ctxLaw Admissible jSwor collision)
open StatFormal.Wave26b (poolLaw riskIid)
open StatFormal.ICL (InDeltaM)
open StatFormal.Foundations.SworLaw
open ConsistR

/-- Route check (not a target): the frozen conditional chain with its two premises discharged. -/
theorem consist_check : StatFormal.Wave24d.Claims.icl_consistency → Claims.consist_reduction →
    Claims.consist_approx → Claims.consist_risk := by
  intro hicl hred happr
  intro Z Ω₀ _ _ _ _ _ P₀ _ Q _ Zs M L Kk BL Kmin Kmax lcov hM hat hL hLb hsym hK hKmin hKb hlcov hZm hZi hZl
  have hP₀adm : Admissible P₀ M P₀ := ⟨inferInstance, P₀.measure_compl_support, by
    rw [distinctSet_eq, pi_injective_eq_one P₀ hat]; exact one_pos⟩
  have hne : (consistClass L Kk lcov P₀).Nonempty := ⟨_, P₀, hP₀adm, rfl⟩
  have hbdd : BddBelow (consistClass L Kk lcov P₀) := by
    refine ⟨-(lcov * Real.log Kmax), ?_⟩
    rintro _ ⟨μ, ⟨hμ, -, hpos⟩, rfl⟩
    haveI := hμ
    exact consistRisk_ge hM hLb hK hKmin hKb hlcov P₀ μ hpos
  set Rstar := sInf (consistClass L Kk lcov P₀) with hRstar
  have hglb : IsGLB (consistClass L Kk lcov P₀) Rstar := isGLB_csInf hne hbdd
  refine ⟨Rstar, hglb, ?_⟩
  filter_upwards [hred Z Ω₀ P₀ Q Zs M L Kk BL Kmin Kmax lcov hM hat hL hLb hsym hK hKmin hKb hlcov hZm hZi hZl,
    happr Z Ω₀ P₀ Q Zs M L Kk BL Kmin Kmax lcov Rstar hM hat hL hLb hsym hK hKmin hKb hlcov hZm hZi hZl hglb]
    with ω₀ hR hA
  intro Ω _ P _ n m X wh lamKL eps hXm hXi hXl hopt hn hm hlog hkl heps
  set R : (j : ℕ) → Ω → ℝ := fun j ω =>
    consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) (wh j ω)) with hRdef
  set A : ℕ → ℝ := fun j =>
    sInf ((fun w => consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) w)) '' {w | InDeltaM w M})
    with hAdef
  have hlow : ∀ j (w : Fin (n j) → ℝ), InDeltaM w M →
      Rstar ≤ consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) w) :=
    fun j w hw => hglb.1 ⟨_, ((hR (n j)).1 w hw).1, rfl⟩
  have hReq : ∀ᶠ j in atTop, ∀ ω, max Rstar (R j ω) = R j ω := by
    filter_upwards [hopt] with j hj ω
    exact max_eq_right (hlow j _ (hj.2 ω).1)
  have hn2 : ∀ᶠ j in atTop, 2 ≤ n j := by
    filter_upwards [hn.eventually (eventually_ge_atTop (2 : ℝ))] with j hj
    exact_mod_cast hj
  have hm2 : ∀ᶠ j in atTop, 2 ≤ m j := by
    filter_upwards [hm.eventually (eventually_ge_atTop (2 : ℝ))] with j hj
    exact_mod_cast hj
  have hconv := hicl Ω P (fun j ω => max Rstar (R j ω)) A Rstar lamKL eps n m BL lcov Kmin Kmax M
    (fun j ω => le_max_left _ _) ?_ ?_ hn hm hlog hkl heps
  · intro ε hε
    refine (hconv ε hε).congr' ?_
    filter_upwards [hReq] with j hj
    simp_rw [hj]
  · -- premise (1): the oracle event, for all large `j`
    filter_upwards [hopt, hn2, hm2] with j hj hnj hmj
    obtain ⟨S, hSm, hSP, hS⟩ := (hR (n j)).2 Ω P (m j) (X j) (wh j) (lamKL j) (eps j) hnj hmj hj.1 (hXm j)
      (hXi j) (hXl j) (fun ω => (hj.2 ω).1) (fun ω w hw => (hj.2 ω).2 w hw)
    refine ⟨S, hSm, hSP, fun ω hω => ?_⟩
    rw [max_eq_right (hlow j _ (hj.2 ω).1)]
    have hle : R j ω - (lamKL j * Real.log (n j) + eps j +
        2 * StatFormal.Wave24d.devBound BL lcov Kmin Kmax M (n j) (m j) (1 / m j)) ≤ A j := by
      refine le_csInf ⟨_, ⟨wh j ω, (hj.2 ω).1, rfl⟩⟩ ?_
      rintro _ ⟨w, hw, rfl⟩
      have := hS ω hω w hw
      simp only [hRdef]
      linarith
    linarith
  · -- premise (2): the approximation step
    intro ε hε
    obtain ⟨N, hN⟩ := hA ε hε
    filter_upwards [hn.eventually (eventually_ge_atTop (N : ℝ))] with j hj
    obtain ⟨w, hw, hle⟩ := hN (n j) (by exact_mod_cast hj)
    have hbddj : BddBelow ((fun w => consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) w)) ''
        {w | InDeltaM w M}) := ⟨Rstar, by rintro _ ⟨w', hw', rfl⟩; exact hlow j w' hw'⟩
    exact (csInf_le hbddj ⟨w, hw, rfl⟩).trans hle

theorem consist_risk : Claims.consist_risk :=
  consist_check StatFormal.Wave24d.icl_consistency consist_reduction consist_approx

end StatFormal.Wave29i
