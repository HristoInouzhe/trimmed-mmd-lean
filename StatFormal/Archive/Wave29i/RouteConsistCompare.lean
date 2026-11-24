import StatFormal.Archive.Wave29i.RouteConsistBasic

/-!
# Route — ICL `cor:consistency`, second claim `R⋆ ≤ R^{iid⋆}` (untrusted)

* For atomless `ν`, `ν^{⊗M}(D_M) = 1`, so `Π_ν = ν^{⊗M}`, `Π̄_ν = ν` and `R(ν) = R^iid(ν)`; atomless laws on
  `supp P₀` are admissible.
* Atomless laws on `supp P₀` are weakly dense in `𝒫(supp P₀)`: quantise `μ` on a finite `δ`-net `x_i ∈ supp P₀`
  (Wave 26b cells, weights `w_i`) and replace `δ_{x_i}` by `P₀(· | B(x_i, δ))` (atomless, carried by `supp P₀`,
  positive mass since `x_i ∈ supp P₀`); `|∫ f dν − ∫ f dμ| ≤ 2η` when `f` oscillates by `≤ η` on `δ`-balls.
* `R^iid` is weakly continuous (Wave 26b), so `R⋆ ≤ R(ν_k) = R^iid(ν_k) → R^iid(μ)` for every `μ ∈ 𝒫(supp P₀)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave29i

open StatFormal.Wave11b (distinctSet ctxLaw Admissible)
open StatFormal.Wave26b (poolLaw riskIid gIid)
open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.Foundations.SworLaw

variable {Z : Type} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

namespace ConsistR

lemma ctxLaw_of_atomless {M : ℕ} (ν : Measure Z) [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} = 0) :
    ctxLaw ν M = Measure.pi fun _ : Fin M => ν := by
  rw [ctxLaw_eq]
  unfold ProbabilityTheory.cond
  rw [pi_injective_eq_one ν hν, inv_one, one_smul]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact pi_not_injective_eq_zero ν hν)

lemma consistMarg_of_atomless {M : ℕ} (hM : 1 ≤ M) (ν : Measure Z) [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} = 0) :
    consistMarg ν M = ν := by
  unfold consistMarg
  rw [ctxLaw_of_atomless ν hν]
  have h : ∀ s : Fin M, (Measure.pi fun _ : Fin M => ν).map (fun t => t s) = ν := fun s =>
    (measurePreserving_eval (fun _ : Fin M => ν) s).map_eq
  simp_rw [h]
  ext s hs
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [Measure.smul_apply, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (show M ≠ 0 by omega))
      (ENNReal.natCast_ne_top M), one_mul]

lemma consistRisk_of_atomless {M : ℕ} (hM : 1 ≤ M) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov : ℝ)
    (P₀ : Measure Z) (ν : Measure Z) [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} = 0) :
    consistRisk L Kk lcov P₀ ν = riskIid L Kk lcov P₀ ν := by
  unfold consistRisk riskIid consistG gIid
  rw [ctxLaw_of_atomless ν hν, consistMarg_of_atomless hM ν hν]

/-- Atomless approximation of a law carried by `supp P₀` (`P₀` atomless). -/
lemma exists_atomless_approx (P₀ : Measure Z) [IsProbabilityMeasure P₀] (hat : ∀ x, P₀ {x} = 0)
    (μ : Measure Z) [IsProbabilityMeasure μ] (hμS : μ P₀.supportᶜ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ν : Measure Z, IsProbabilityMeasure ν ∧ (∀ x, ν {x} = 0) ∧ ν P₀.supportᶜ = 0 ∧
      ∀ f : Z → ℝ, Continuous f → ∀ η : ℝ, (∀ x y, dist x y < δ → |f x - f y| ≤ η) →
        |∫ x, f x ∂ν - ∫ x, f x ∂μ| ≤ 2 * η := by
  classical
  set S := P₀.support with hS
  have hSk : IsCompact S := Measure.isClosed_support.isCompact
  obtain ⟨t, htS, htf, htcov⟩ := finite_cover_balls_of_compact hSk hδ
  set s := htf.toFinset with hs
  set z : Fin s.card → Z := fun i => (s.equivFin.symm i : Z) with hz
  have hzS : ∀ i, z i ∈ S := fun i => htS (htf.mem_toFinset.1 (s.equivFin.symm i).2)
  have hcov : ∀ x ∈ S, ∃ i, dist x (z i) < δ := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (htcov hx)
    refine ⟨s.equivFin ⟨c, htf.mem_toFinset.2 hc⟩, ?_⟩
    simp only [hz, Equiv.symm_apply_apply]
    exact Metric.mem_ball.1 hxc
  obtain ⟨w, hw, hint⟩ := StatFormal.Wave26b.exists_pool_weights μ hμS z hcov
  set B : Fin s.card → Set Z := fun i => Metric.ball (z i) δ with hB
  have hBpos : ∀ i, P₀ (B i) ≠ 0 := fun i =>
    ((Measure.mem_support_iff_forall (z i)).1 (hzS i) _ (Metric.ball_mem_nhds (z i) hδ)).ne'
  have hcp : ∀ i, IsProbabilityMeasure (P₀[|B i]) := fun i => cond_isProbabilityMeasure (hBpos i)
  set ν : Measure Z := ∑ i, ENNReal.ofReal (w i) • P₀[|B i] with hν
  have hνp : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simp only [hν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw.1 i), hw.2, ENNReal.ofReal_one]
  have hcondnull : ∀ i (A : Set Z), P₀ A = 0 → P₀[|B i] A = 0 := by
    intro i A hA
    rw [cond_apply measurableSet_ball, measure_mono_null inter_subset_right hA, mul_zero]
  refine ⟨ν, hνp, fun x => ?_, ?_, fun f hf η hη => ?_⟩
  · simp only [hν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => by rw [hcondnull i _ (hat x), mul_zero]
  · simp only [hν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => by rw [hcondnull i _ P₀.measure_compl_support, mul_zero]
  · have hfi : ∀ (ρ : Measure Z) [IsFiniteMeasure ρ], Integrable f ρ := fun ρ _ =>
      StatFormal.Wave26b.integrable_of_continuous_bdd ρ hf
    have hνint : ∫ x, f x ∂ν = ∑ i, w i * ∫ x, f x ∂(P₀[|B i]) := by
      rw [hν, integral_finsetSum_measure (fun i _ => (hfi _).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul_measure, ENNReal.toReal_ofReal (hw.1 i), smul_eq_mul]
    have hcell : ∀ i, |∫ x, f x ∂(P₀[|B i]) - f (z i)| ≤ η := by
      intro i
      have hae : ∀ᵐ y ∂(P₀[|B i]), y ∈ B i := by
        rw [ae_iff]
        exact cond_compl_eq_zero P₀ measurableSet_ball
      have h1 : ∫ x, f x ∂(P₀[|B i]) - f (z i) = ∫ x, (f x - f (z i)) ∂(P₀[|B i]) := by
        rw [integral_sub (hfi _) (integrable_const _), integral_const, probReal_univ, one_smul]
      rw [h1]
      have := norm_integral_le_of_norm_le_const (μ := P₀[|B i]) (f := fun x => f x - f (z i)) (C := η) (by
        filter_upwards [hae] with y hy
        rw [Real.norm_eq_abs]
        exact hη y (z i) (Metric.mem_ball.1 hy))
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact this
    have hpool : ∫ x, f x ∂(poolLaw z w) = ∑ i, w i * f (z i) :=
      StatFormal.Wave26b.integral_poolLaw z hw.1 hf.measurable
    have h2 := hint f hf η hη
    rw [hpool] at h2
    have h3 : |∑ i, w i * ∫ x, f x ∂(P₀[|B i]) - ∑ i, w i * f (z i)| ≤ η := by
      rw [← Finset.sum_sub_distrib]
      calc |∑ i, (w i * ∫ x, f x ∂(P₀[|B i]) - w i * f (z i))|
          ≤ ∑ i, |w i * ∫ x, f x ∂(P₀[|B i]) - w i * f (z i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, w i * η := Finset.sum_le_sum fun i _ => by
            rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 i)]
            exact mul_le_mul_of_nonneg_left (hcell i) (hw.1 i)
        _ = η := by rw [← Finset.sum_mul, hw.2, one_mul]
    rw [hνint]
    calc |∑ i, w i * ∫ x, f x ∂(P₀[|B i]) - ∫ x, f x ∂μ|
        ≤ |∑ i, w i * ∫ x, f x ∂(P₀[|B i]) - ∑ i, w i * f (z i)| + |∑ i, w i * f (z i) - ∫ x, f x ∂μ| :=
          abs_sub_le _ _ _
      _ ≤ 2 * η := by linarith

/-- Approximants with `|∫ f dν_k − ∫ f dμ| ≤ 2η` on `1/(k+1)`-oscillation `η` converge weakly. -/
lemma tendsto_of_approx (νs : ℕ → ProbabilityMeasure Z) (μs : ProbabilityMeasure Z)
    (hνf : ∀ (k : ℕ) (f : Z → ℝ), Continuous f → ∀ η : ℝ, (∀ x y, dist x y < 1 / ((k : ℝ) + 1) → |f x - f y| ≤ η) →
        |∫ x, f x ∂(νs k : Measure Z) - ∫ x, f x ∂(μs : Measure Z)| ≤ 2 * η) :
    Tendsto νs atTop (𝓝 μs) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (η / 4) (by positivity)
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
    refine ⟨K, fun k hkK => ?_⟩
    have hkδ : 1 / ((k : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hK
      have : (K : ℝ) ≤ k := by exact_mod_cast hkK
      nlinarith
    have := hνf k f f.continuous (η / 4) fun x y hxy => by
      have := hfδ (lt_of_lt_of_le hxy hkδ)
      rw [Real.dist_eq] at this
      exact this.le
    rw [Real.dist_eq]
    exact lt_of_le_of_lt this (by linarith)

end ConsistR

open ConsistR

theorem consist_compare : Claims.consist_compare := by
  intro Z _ _ _ _ P₀ _ M L Kk BL Kmin Kmax lcov Rstar Riid hM hat hL hLb hK hKmin hKb hglb hglbIid
  refine hglbIid.2 ?_
  rintro _ ⟨μ, hμ, hμS, rfl⟩
  haveI := hμ
  have hk : ∀ k : ℕ, ∃ ν : Measure Z, IsProbabilityMeasure ν ∧ (∀ x, ν {x} = 0) ∧ ν P₀.supportᶜ = 0 ∧
      ∀ f : Z → ℝ, Continuous f → ∀ η : ℝ, (∀ x y, dist x y < 1 / ((k : ℝ) + 1) → |f x - f y| ≤ η) →
        |∫ x, f x ∂ν - ∫ x, f x ∂μ| ≤ 2 * η := fun k =>
    exists_atomless_approx P₀ hat μ hμS (by positivity)
  choose ν hνp hνa hνS hνf using hk
  set νs : ℕ → ProbabilityMeasure Z := fun k => ⟨ν k, hνp k⟩ with hνs
  set μs : ProbabilityMeasure Z := ⟨μ, hμ⟩ with hμs
  have hconv : Tendsto νs atTop (𝓝 μs) := tendsto_of_approx νs μs hνf
  have hlim := ((StatFormal.Wave26b.continuous_riskIid lcov hL hLb hK hKmin hKb P₀).tendsto μs).comp hconv
  refine ge_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  show Rstar ≤ riskIid L Kk lcov P₀ (ν k)
  haveI := hνp k
  rw [← consistRisk_of_atomless hM L Kk lcov P₀ (ν k) (hνa k)]
  exact hglb.1 ⟨ν k, ⟨hνp k, hνS k, by rw [distinctSet_eq, pi_injective_eq_one _ (hνa k)]; exact one_pos⟩, rfl⟩

end StatFormal.Wave29i
