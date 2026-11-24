import StatFormal.Archive.Wave18b.Statements
import StatFormal.Archive.Wave11b.RouteFlow

/-!
# Route: SB `prop:excess` (untrusted)

* Minkowski in `L²(P)` (`eLpNorm_add_le`), `(∫⁻ edist²)^{1/2} = ‖·‖_{L²}`.
* `C^flow`: split `∫⁻` over the fibres `{S = s}`, `∫⁻_{S=s} f = P(S=s) ∫⁻ f dP[·|S=s]`, then the certified
  `Wave11b.flow_cost` on each fibre.
* `C^sto`: Tonelli on `π ⊗ N(0,v)`; for fixed `(x₀,x₁)`, `E(t(x₀ − x₁) − Z)² = t²(x₀ − x₁)² + v`.
* `C^flow ≤ C^sto`: certified `Wave9b.pareto_weak` with the coupling `stoPlan` of `R_s` and its second marginal.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave18b

open StatFormal.Wave9b

lemma lintegral_edist_sq_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    (∫⁻ ω, edist (f ω) (g ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) = eLpNorm (f - g) 2 P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    ((hf.sub hg).aestronglyMeasurable)]
  simp only [Pi.sub_apply, edist_eq_enorm_sub, ENNReal.toReal_ofNat]

theorem excess_minkowski : Claims.excess_minkowski := by
  intro Ω _ P U Ut Y hU hUt hY
  have e1 := lintegral_edist_sq_eq hUt hY
  have e2 := lintegral_edist_sq_eq hU hY
  have e3 := lintegral_edist_sq_eq hUt hU
  have h1 : (Ut - Y) = (Ut - U) + (U - Y) := by ring
  have h2 : (U - Y) = -(Ut - U) + (Ut - Y) := by ring
  have m1 : eLpNorm (Ut - Y) 2 P ≤ eLpNorm (U - Y) 2 P + eLpNorm (Ut - U) 2 P := by
    rw [h1, add_comm (eLpNorm (U - Y) 2 P)]
    exact eLpNorm_add_le (by norm_num)
  have m2 : eLpNorm (U - Y) 2 P ≤ eLpNorm (Ut - Y) 2 P + eLpNorm (Ut - U) 2 P := by
    rw [h2, add_comm (eLpNorm (Ut - Y) 2 P), ← eLpNorm_neg (Ut - U)]
    exact eLpNorm_add_le (by norm_num)
  refine ⟨by rw [e1, e2, e3]; exact m1, by rw [e1, e2, e3]; exact m2, ?_⟩
  set R := ∫⁻ ω, edist (Ut ω) (Y ω) ^ (2 : ℝ) ∂P
  have hR : R = (R ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [hR]
  exact ENNReal.rpow_le_rpow (by rw [e1, e2, e3]; exact m1) (by norm_num)

lemma measurable_flowMap' (R μ : Measure ℝ) : Measurable (flowMap R μ) := measurable_flowMap R μ

theorem excess_flow_cost : Claims.excess_flow_cost := by
  intro Ω _ P _ S U μ hS hU hs hμ hR
  set G : Fin 2 → Ω → ℝ≥0∞ := fun s ω =>
    edist (flowMap ((P[|S ⁻¹' {s}]).map U) (μ s) (U ω)) (U ω) ^ (2 : ℝ) with hG
  have hGm : ∀ s, Measurable (G s) := fun s =>
    (((measurable_flowMap' _ _).comp hU).edist hU).pow_const _
  have hsplit : ∀ ω, edist (flowMap ((P[|S ⁻¹' {S ω}]).map U) (μ (S ω)) (U ω)) (U ω) ^ (2 : ℝ) =
      ∑ s, (S ⁻¹' {s}).indicator (G s) ω := by
    intro ω
    rw [Finset.sum_eq_single (S ω)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro b _ hb
      rw [Set.indicator_of_notMem (by simpa [eq_comm] using hb)]
    · simp
  simp_rw [hsplit]
  rw [lintegral_finset_sum _ (fun s _ => (hGm s).indicator (hS (measurableSet_singleton s)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lintegral_indicator (hS (measurableSet_singleton s))]
  have hfc := Wave11b.flow_cost Ω P S U s (μ s) inferInstance hS hU (hs s) (hμ s) (hR s)
  have hcond : ∫⁻ ω, G s ω ∂(P[|S ⁻¹' {s}]) = (P (S ⁻¹' {s}))⁻¹ * ∫⁻ ω in S ⁻¹' {s}, G s ω ∂P := by
    rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  have hfin : P (S ⁻¹' {s}) ≠ ⊤ := measure_ne_top _ _
  calc ∫⁻ ω in S ⁻¹' {s}, G s ω ∂P
      = P (S ⁻¹' {s}) * ((P (S ⁻¹' {s}))⁻¹ * ∫⁻ ω in S ⁻¹' {s}, G s ω ∂P) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (hs s) hfin, one_mul]
    _ = P (S ⁻¹' {s}) * wassersteinEDist 2 ((P[|S ⁻¹' {s}]).map U) (μ s) ^ (2 : ℝ) := by
        rw [← hcond]
        exact congrArg _ hfc

/-- `E(A − Z)² = A² + v` for `Z ∼ N(0,v)`, as a lintegral. -/
lemma lintegral_sq_gauss (A : ℝ) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal ((A - z) ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (A ^ 2 + v) := by
  have hm2 : MemLp id 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have hint1 : Integrable (fun z : ℝ => z) (gaussianReal 0 v) := (memLp_id_gaussianReal 1).integrable le_rfl
  have hint2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := hm2.integrable_sq
  have hI : Integrable (fun z : ℝ => (A - z) ^ 2) (gaussianReal 0 v) := by
    have : (fun z : ℝ => (A - z) ^ 2) = fun z => A ^ 2 - 2 * A * z + z ^ 2 := by funext z; ring
    rw [this]
    exact ((integrable_const _).sub (hint1.const_mul _)).add hint2
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun z => sq_nonneg _)]
  congr 1
  have hvar : ∫ z, z ^ 2 ∂(gaussianReal 0 v) = v := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    simpa using h
  have : (fun z : ℝ => (A - z) ^ 2) = fun z => A ^ 2 - 2 * A * z + z ^ 2 := by funext z; ring
  have hJ : Integrable (fun z : ℝ => A ^ 2 - 2 * A * z) (gaussianReal 0 v) :=
    (integrable_const _).sub (hint1.const_mul _)
  have hK : Integrable (fun z : ℝ => 2 * A * z) (gaussianReal 0 v) := hint1.const_mul _
  rw [this, integral_add hJ hint2, integral_sub (integrable_const _) hK, integral_const_mul, hvar,
    integral_id_gaussianReal, integral_const, probReal_univ, smul_eq_mul]
  ring

theorem excess_sto_cost : Claims.excess_sto_cost := by
  intro ε t π _ hε ht
  have hv : ((ε * t * (1 - t)).toNNReal : ℝ) = ε * t * (1 - t) :=
    Real.coe_toNNReal _ (mul_nonneg (mul_nonneg hε ht.1) (by linarith [ht.2]))
  unfold qcost stoPlan
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  rw [lintegral_prod _ (by fun_prop)]
  have hinner : ∀ x : ℝ × ℝ,
      ∫⁻ z, edist ((x, z).1.1, (1 - t) * (x, z).1.1 + t * (x, z).1.2 + (x, z).2).1
          ((x, z).1.1, (1 - t) * (x, z).1.1 + t * (x, z).1.2 + (x, z).2).2 ^ (2 : ℝ)
          ∂(gaussianReal 0 (ε * t * (1 - t)).toNNReal) =
        ENNReal.ofReal (t ^ 2) * edist x.1 x.2 ^ (2 : ℝ) + ENNReal.ofReal (ε * t * (1 - t)) := by
    intro x
    simp only [edist_rpow_two]
    have : ∀ z : ℝ, (x.1 - ((1 - t) * x.1 + t * x.2 + z)) ^ 2 = (t * (x.1 - x.2) - z) ^ 2 := by
      intro z; ring
    simp_rw [this]
    rw [lintegral_sq_gauss, hv, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg (mul_nonneg hε ht.1) (by linarith [ht.2]))]
    congr 1; ring
  simp_rw [hinner]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (by fun_prop)]

theorem excess_flow_le_sto : Claims.excess_flow_le_sto := by
  intro ε t p R ν π hε ht hπ hcpl
  refine Finset.sum_le_sum fun s _ => ?_
  gcongr
  haveI := hπ s
  have hc := stoPlan_coupling (ε := ε) (t := t) (hcpl s)
  have hc' : IsCoupling (stoPlan ε t (π s)) (R s) (stoPlan ε t (π s)).snd := ⟨hc.fst_eq, rfl⟩
  exact pareto_weak (R s) _ _ hc'

end StatFormal.Wave18b
