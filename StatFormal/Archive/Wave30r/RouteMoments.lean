import StatFormal.Archive.Wave30r.RouteP2
import Mathlib.Probability.Distributions.Pareto

set_option linter.style.longLine false

/-!
# Wave 30r route: the FAccT `lem:sharp` fails without a moment hypothesis

`μ` = Pareto(1,1) on `ℝ¹` (density `x⁻²` on `[1,∞)`: no atoms, `∫ x² dμ = ∞`), `S(y) = e₁ 1_{y > 2}`, `ν = S_#μ`
(two atoms, both of positive mass, carried by the unit ball, so `ν ∈ 𝒫₂`). Every coupling of `μ` and `ν` has
`∫ ‖x − y‖² = ∞` (`lintegral_sqdist_eq_top`), so the FAccT objective is `+∞` on every coupling and the graph coupling
`(id, S)_#μ` is an `argmin`; by the certified Wave 8a `sharp_iff`, every version of its conditional-mean map pushes `μ`
to `ν` exactly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30r

open StatFormal.Wave8a StatFormal.Foundations.EntropicPlan

namespace Moments

/-- The embedding `ℝ → ℝ¹`. -/
def emb (x : ℝ) : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 x

lemma emb_apply (x : ℝ) (i : Fin 1) : emb x i = x := by
  rw [Fin.fin_one_eq_zero i]
  simp [emb]

lemma enorm_emb (x : ℝ) : ‖emb x‖ₑ = ‖x‖ₑ := by
  simp [emb, enorm_eq_nnnorm]

lemma isometry_emb : Isometry emb := Isometry.of_dist_eq fun a b => by simp [emb]

lemma measurable_emb : Measurable emb := isometry_emb.continuous.measurable

lemma measurable_coord (i : Fin 1) : Measurable fun y : EuclideanSpace ℝ (Fin 1) => y i :=
  (EuclideanSpace.proj i).continuous.measurable

/-- Pareto(1,1). -/
abbrev mu0 : Measure ℝ := paretoMeasure 1 1

instance : IsProbabilityMeasure mu0 := isProbabilityMeasure_paretoMeasure one_pos one_pos

/-- The source law on `ℝ¹`. -/
def muP : Measure (EuclideanSpace ℝ (Fin 1)) := mu0.map emb

instance : IsProbabilityMeasure muP := by unfold muP; infer_instance

lemma mu0_singleton (s : ℝ) : mu0 {s} = 0 := by
  rw [show mu0 = volume.withDensity (paretoPDF 1 1) from rfl, withDensity_apply _ (measurableSet_singleton s), Measure.restrict_singleton]
  simp

lemma marginal_muP (i : Fin 1) : muP.map (fun x => x i) = mu0 := by
  rw [muP, Measure.map_map (measurable_coord i) measurable_emb]
  have : (fun x : EuclideanSpace ℝ (Fin 1) => x i) ∘ emb = id := funext fun x => emb_apply x i
  rw [this, Measure.map_id]

lemma measurable_paretoPDF : Measurable (paretoPDF 1 1) :=
  (measurable_paretoPDFReal 1 1).ennreal_ofReal

lemma lintegral_mu0_sq : ∫⁻ x, ‖x‖ₑ ^ 2 ∂mu0 = ∞ := by
  rw [show mu0 = volume.withDensity (paretoPDF 1 1) from rfl, lintegral_withDensity_eq_lintegral_mul _ measurable_paretoPDF
    (measurable_enorm.pow_const 2)]
  simp only [Pi.mul_apply]
  refine eq_top_iff.2 ?_
  calc (∞ : ℝ≥0∞) = volume (Ici (1 : ℝ)) := Real.volume_Ici.symm
    _ = ∫⁻ _ in Ici (1 : ℝ), 1 := (setLIntegral_one _).symm
    _ ≤ ∫⁻ x in Ici (1 : ℝ), paretoPDF 1 1 x * ‖x‖ₑ ^ 2 := by
        refine setLIntegral_mono' measurableSet_Ici fun x (hx : 1 ≤ x) => le_of_eq ?_
        have hx0 : 0 ≤ x := zero_le_one.trans hx
        rw [paretoPDF_of_le hx, Real.enorm_eq_ofReal hx0, ← ENNReal.ofReal_pow hx0,
          ← ENNReal.ofReal_mul (by positivity)]
        have : (1 : ℝ) * 1 ^ (1 : ℝ) * x ^ (-((1 : ℝ) + 1)) * x ^ 2 = 1 := by
          have hxpos : 0 < x := zero_lt_one.trans_le hx
          rw [Real.one_rpow, one_mul, one_mul, show -((1 : ℝ) + 1) = -2 by norm_num,
            Real.rpow_neg hx0, Real.rpow_two, inv_mul_cancel₀ (pow_pos hxpos 2).ne']
        rw [this, ENNReal.ofReal_one]
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma not_moment_muP : ¬ HasFiniteMoment 2 muP := by
  rw [hasFiniteMoment_two_iff, muP, lintegral_map (measurable_enorm.pow_const 2) measurable_emb]
  simp only [enorm_emb]
  rw [lintegral_mu0_sq]
  simp

lemma mu0_pos {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Icc 1 3) (hvol : volume s ≠ 0) : 0 < mu0 s := by
  rw [show mu0 = volume.withDensity (paretoPDF 1 1) from rfl, withDensity_apply _ hs]
  have hle : ∫⁻ _ in s, ENNReal.ofReal (1 / 9) ≤ ∫⁻ x in s, paretoPDF 1 1 x := by
    refine setLIntegral_mono' hs fun x hx => ?_
    obtain ⟨hx1, hx3⟩ := hsub hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    rw [paretoPDF_of_le hx1]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.one_rpow, one_mul, one_mul, show -((1 : ℝ) + 1) = -2 by norm_num, Real.rpow_neg hx0,
      Real.rpow_two, one_div]
    refine (inv_le_inv₀ (by norm_num) (pow_pos hxpos 2)).2 ?_
    nlinarith
  refine lt_of_lt_of_le ?_ hle
  rw [setLIntegral_const]
  exact ENNReal.mul_pos (by simp) hvol

/-- The threshold map `S(y) = e₁ 1_{y > 2}`. -/
def thr (y : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) := if 2 < y 0 then emb 1 else 0

lemma measurable_thr : Measurable thr :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_coord 0)) measurable_const measurable_const

/-- The target law `S_#μ`. -/
def nuP : Measure (EuclideanSpace ℝ (Fin 1)) := muP.map thr

instance : IsProbabilityMeasure nuP := by unfold nuP; infer_instance

lemma moment_nuP : HasFiniteMoment 2 nuP := by
  refine hasFiniteMoment_of_ball (M := 1) ?_
  rw [nuP, Measure.map_apply measurable_thr Metric.isClosed_closedBall.measurableSet.compl]
  have : thr ⁻¹' (Metric.closedBall 0 1)ᶜ = ∅ := by
    ext y
    simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, mem_empty_iff_false,
      iff_false, not_not, thr]
    split_ifs
    · simp [emb]
    · simp
  rw [this, measure_empty]

lemma emb_one_ne_zero : emb 1 ≠ 0 := by
  intro h
  have := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h
  simp [emb_apply] at this

lemma nuP_apply (s : Set (EuclideanSpace ℝ (Fin 1))) (hs : MeasurableSet s) :
    nuP s = mu0 ((thr ∘ emb) ⁻¹' s) := by
  rw [nuP, Measure.map_apply measurable_thr hs, muP, Measure.map_apply measurable_emb (measurable_thr hs)]
  rfl

lemma not_dirac_nuP : ¬ ∃ y, nuP = Measure.dirac y := by
  rintro ⟨y, hy⟩
  have h0 : 0 < nuP {0} := by
    rw [nuP_apply _ (measurableSet_singleton 0)]
    refine (mu0_pos measurableSet_Icc (Icc_subset_Icc le_rfl (by norm_num)) (by simp)).trans_le
      (measure_mono fun x (hx : x ∈ Icc (1 : ℝ) 2) => ?_)
    have : ¬ (2 : ℝ) < emb x 0 := by rw [emb_apply]; exact not_lt.2 hx.2
    simp [thr, this]
  have h1 : 0 < nuP {emb 1} := by
    rw [nuP_apply _ (measurableSet_singleton _)]
    refine (mu0_pos measurableSet_Ioc (fun x hx => ⟨by linarith [hx.1], hx.2⟩) (by norm_num)).trans_le
      (measure_mono fun x (hx : x ∈ Ioc (2 : ℝ) 3) => ?_)
    have : (2 : ℝ) < emb x 0 := by rw [emb_apply]; exact hx.1
    simp [thr, this]
  rw [hy, Measure.dirac_apply' _ (measurableSet_singleton _)] at h0 h1
  have hy0 : y ∈ ({0} : Set (EuclideanSpace ℝ (Fin 1))) := by
    by_contra h; rw [indicator_of_notMem h] at h0; exact lt_irrefl _ h0
  have hy1 : y ∈ ({emb 1} : Set (EuclideanSpace ℝ (Fin 1))) := by
    by_contra h; rw [indicator_of_notMem h] at h1; exact lt_irrefl _ h1
  rw [mem_singleton_iff] at hy0 hy1
  exact emb_one_ne_zero (hy1.symm.trans hy0)

/-- The graph coupling `(id, S)_#μ`. -/
def piG : Measure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) := muP.map fun x => (x, thr x)

lemma measurable_graph : Measurable fun x : EuclideanSpace ℝ (Fin 1) => (x, thr x) :=
  measurable_id.prodMk measurable_thr

lemma isCoupling_piG : IsCoupling piG muP nuP where
  fst_eq := by
    rw [piG, Measure.fst, Measure.map_map measurable_fst measurable_graph]
    exact Measure.map_id
  snd_eq := by
    rw [piG, Measure.snd, Measure.map_map measurable_snd measurable_graph]
    rfl

lemma lintegral_half_eq_top {π : Measure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))}
    (hπ : IsCoupling π muP nuP) : ∫⁻ z, halfQuadCost z ∂π = ∞ := by
  have h : ∫⁻ z, quadCost z ∂π = ∞ := lintegral_sqdist_eq_top hπ not_moment_muP moment_nuP
  simp only [halfQuadCost, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (by simp), h, ENNReal.top_mul (by simp)]

lemma entropicCost_eq_top (ε : ℝ≥0) : entropicTransportCost halfQuadCost ε muP nuP = ∞ :=
  eq_top_iff.2 (le_entropicTransportCost fun π hπ => by rw [lintegral_half_eq_top hπ, top_add])

lemma isEntropicPlanHalf_piG (ε : ℝ≥0) : IsEntropicPlanHalf ε muP nuP piG :=
  ⟨isCoupling_piG, by rw [lintegral_half_eq_top isCoupling_piG, top_add, entropicCost_eq_top]⟩

end Moments

open Moments in
theorem sharp_facct_moments : Claims.sharp_facct_moments := by
  refine ⟨muP, nuP, inferInstance, inferInstance, fun i s => ?_, not_moment_muP, moment_nuP, not_dirac_nuP,
    fun ε => ⟨piG, isEntropicPlanHalf_piG ε, sharp_bary_exists 1 muP nuP piG isCoupling_piG moment_nuP,
      fun T hT => ?_⟩⟩
  · rw [marginal_muP i]
    exact mu0_singleton s
  · have h := sharp_iff 1 muP nuP piG T isCoupling_piG moment_nuP hT
    exact h.1.2 (h.2.2 ⟨thr, measurable_thr, rfl⟩)

end StatFormal.Wave30r
