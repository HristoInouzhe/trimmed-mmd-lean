import StatFormal.Archive.Wave26b.RouteICLTop

/-!
# Route — ICL `cor:iid-consistency` (untrusted)

On the almost-sure pool event (pool in `supp P₀`, eventually dense): `R^iid(μ_w) ≥ R^{iid⋆}` for every pool weight;
the oracle event (`thm:joint` + `cor:oracle` + the reduction) holds for all large `j`; and the quantisations of the
minimiser `μ⋆` give `inf_w R^iid(μ_w) ≤ R^{iid⋆} + ε` for all large pools (weak continuity of `R^iid`; nested pools).
The frozen consistency chain (`Wave24d` `icl_consistency`) concludes.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave26b

open StatFormal.ICL.Joint (ProbVec)

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

lemma poolLaw_carried {n : ℕ} {S : Set Z} (z : Fin n → Z) (hz : ∀ i, z i ∈ S) (w : Fin n → ℝ) :
    poolLaw z w Sᶜ = 0 := by
  classical
  simp only [poolLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hz j), mul_zero]

/-- The approximation step: on a dense pool, for every `ε > 0`, all large pools carry a weight `w` with
`R^iid(μ_w) ≤ R^iid(μ⋆) + ε`. -/
lemma approx_pool {M : ℕ} {L : Z → (Fin M → Z) → ℝ} {Kk : Z → Z → ℝ} {BL Kmin Kmax : ℝ} (lcov : ℝ)
    (hL : Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2)) (hLb : ∀ z t, 0 ≤ L z t ∧ L z t ≤ BL)
    (hK : Continuous (Function.uncurry Kk)) (hKmin : 0 < Kmin) (hKb : ∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax)
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (μs : ProbabilityMeasure Z) (hμs : (μs : Measure Z) P₀.supportᶜ = 0)
    (z : ℕ → Z) (hdense : ∀ δ > 0, ∃ N, ∀ x ∈ P₀.support, ∃ i < N, dist x (z i) < δ) :
    ∀ ε > 0, ∃ N₀, ∀ n ≥ N₀, ∃ w : Fin n → ℝ, ProbVec w ∧
      riskIid L Kk lcov P₀ (poolLaw (fun i : Fin n => z i) w) ≤ riskIid L Kk lcov P₀ (μs : Measure Z) + ε := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hRc := continuous_riskIid lcov hL hLb hK hKmin hKb P₀
  -- for each `k`, a bad pool size `n_k ≥ N_k` and the quantisation weights at `δ_k = 1/(k+1)`
  have hk : ∀ k : ℕ, ∃ n : ℕ, ∃ w : Fin n → ℝ, ProbVec w ∧
      riskIid L Kk lcov P₀ (μs : Measure Z) + ε < riskIid L Kk lcov P₀ (poolLaw (fun i : Fin n => z i) w) ∧
      ∀ f : Z → ℝ, Continuous f → ∀ η : ℝ, (∀ x y, dist x y < 1 / (k + 1) → |f x - f y| ≤ η) →
        |∫ x, f x ∂(poolLaw (fun i : Fin n => z i) w) - ∫ x, f x ∂(μs : Measure Z)| ≤ η := by
    intro k
    obtain ⟨N, hN⟩ := hdense (1 / (k + 1)) (by positivity)
    obtain ⟨n, hnN, hbad⟩ := hcon N
    have hcov : ∀ x ∈ P₀.support, ∃ i : Fin n, dist x (z i) < 1 / (k + 1) := by
      intro x hx
      obtain ⟨i, hi, hd⟩ := hN x hx
      exact ⟨⟨i, by omega⟩, hd⟩
    obtain ⟨w, hw, hint⟩ := exists_pool_weights (μs : Measure Z) hμs (fun i : Fin n => z i) hcov
    exact ⟨n, w, hw, hbad w hw, hint⟩
  choose n w hw hbad hint using hk
  set ν : ℕ → ProbabilityMeasure Z := fun k => ⟨poolLaw (fun i : Fin (n k) => z i) (w k), poolLaw_isProb _ (hw k)⟩
  have hν : Tendsto ν atTop (𝓝 μs) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (η / 2) (by positivity)
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
    refine ⟨K, fun k hkK => ?_⟩
    have hkδ : 1 / ((k : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hK
      have : (K : ℝ) ≤ k := by exact_mod_cast hkK
      nlinarith
    have := hint k f f.continuous (η / 2) fun x y hxy => by
      have := hfδ (lt_of_lt_of_le hxy hkδ)
      rw [Real.dist_eq] at this
      exact this.le
    rw [Real.dist_eq]
    exact lt_of_le_of_lt this (by linarith)
  have hlim := (hRc.tendsto μs).comp hν
  have hev := (hlim.eventually (gt_mem_nhds (show riskIid L Kk lcov P₀ (μs : Measure Z) <
    riskIid L Kk lcov P₀ (μs : Measure Z) + ε by linarith)))
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd (hbad k) (not_lt.2 hk.le)

theorem iid_consistency : Claims.iid_consistency := by
  intro Z Ω₀ _ _ _ _ _ P₀ _ Q _ Zs M L Kk BL Kmin Kmax lcov hM hL hLb hK hKmin hKb hlcov hZm hZi hZl
  obtain ⟨μs, hμsS, hleast⟩ := exists_minimiser lcov hL hLb hK hKmin hKb P₀
  refine ⟨riskIid L Kk lcov P₀ (μs : Measure Z), hleast, ?_⟩
  filter_upwards [ae_pool_dense hZm hZi hZl] with ω₀ hω₀
  obtain ⟨hin, hdense⟩ := hω₀
  intro Ω _ P _ n m X wh lamKL eps hXm hXi hXl hwh hlKL hopt hn hm hlog hkl heps
  set Rstar := riskIid L Kk lcov P₀ (μs : Measure Z) with hRstar
  set z : ℕ → Z := fun i => Zs i ω₀ with hz
  -- lower bound: every pool law is carried by `supp P₀`
  have hlow : ∀ j (w : Fin (n j) → ℝ), ProbVec w → Rstar ≤ riskIid L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => z i) w) := by
    intro j w hw
    haveI := poolLaw_isProb (fun i : Fin (n j) => z i) hw
    exact hleast.2 ⟨_, inferInstance, poolLaw_carried _ (fun i => hin i) w, rfl⟩
  set A : ℕ → ℝ := fun j =>
    sInf ((fun w => riskIid L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => z i) w)) '' {w | ProbVec w}) with hA
  refine StatFormal.Wave24d.icl_consistency Ω P
    (fun j ω => riskIid L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) (wh j ω))) A Rstar lamKL eps n m
    BL lcov Kmin Kmax M (fun j ω => hlow j _ (hwh j ω)) ?_ ?_ hn hm hlog hkl heps
  · -- the oracle event, for all large `j`
    have hn2 : ∀ᶠ j in atTop, 2 ≤ n j := by
      filter_upwards [hn.eventually (eventually_ge_atTop (2 : ℝ))] with j hj
      exact_mod_cast hj
    have hm2 : ∀ᶠ j in atTop, 2 ≤ m j := by
      filter_upwards [hm.eventually (eventually_ge_atTop (2 : ℝ))] with j hj
      exact_mod_cast hj
    filter_upwards [hn2, hm2] with j hnj hmj
    exact oracle_event P hnj hmj hM hL hLb hK hKmin hKb hlcov (hlKL j) P₀ (fun i : Fin (n j) => Zs i ω₀)
      (X j) (hXm j) (hXi j) (hXl j) (wh j) (hwh j) (hopt j)
  · -- the approximation step
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := approx_pool lcov hL hLb hK hKmin hKb P₀ μs hμsS z hdense ε hε
    filter_upwards [hn.eventually (eventually_ge_atTop (N₀ : ℝ))] with j hj
    have hjN : N₀ ≤ n j := by exact_mod_cast hj
    obtain ⟨w, hw, hwle⟩ := hN₀ (n j) hjN
    have hbdd : BddBelow ((fun w => riskIid L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => z i) w)) '' {w | ProbVec w}) :=
      ⟨Rstar, by rintro _ ⟨w', hw', rfl⟩; exact hlow j w' hw'⟩
    exact (csInf_le hbdd ⟨w, hw, rfl⟩).trans hwle

end StatFormal.Wave26b
