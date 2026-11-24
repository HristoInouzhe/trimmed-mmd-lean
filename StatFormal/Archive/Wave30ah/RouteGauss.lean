import StatFormal.Archive.Wave30ah.Statements
import StatFormal.Archive.Wave30z.RouteRay

/-!
# Route — wave 30ah: the half-normal / chi-bar-square shape in `cor:boundary-linear` (a) (untrusted)

Split `G = N(0, σ²)` as `G|_{(−∞,0]} + G|_{(0,∞)}`. On `(−∞, 0]`, `x_+ = 0`, so that part maps to
`G(−∞, 0] δ₀ = ½ δ₀`; on `(0, ∞)`, `x_+ = x`. On `(−∞, 0]`, `|x| = −x`, and `−G = G` (symmetry) maps
`G|_{(−∞,0]}` to `G|_{[0,∞)} = G|_{(0,∞)}` (no atoms), so `law |Z| = 2 G|_{(0,∞)}`. Hence `law Z_+ = ½δ₀ + ½ law|Z|`.
Squares: `law Z_+² = ½δ₀ + ½ law Z²`, and `Z = σN` gives `law Z² = law σ²N²`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace StatFormal.Wave30ah

section Gauss

lemma gauss_split (G : Measure ℝ) : G = G.restrict (Iic 0) + G.restrict (Ioi 0) := by
  rw [← compl_Iic, Measure.restrict_add_restrict_compl measurableSet_Iic]

lemma map_max_restrict_Iic (G : Measure ℝ) :
    (G.restrict (Iic 0)).map (fun x => max x 0) = G (Iic 0) • Measure.dirac 0 := by
  have : (G.restrict (Iic 0)).map (fun x => max x 0) = (G.restrict (Iic 0)).map (fun _ => (0 : ℝ)) :=
    Measure.map_congr (ae_restrict_of_forall_mem measurableSet_Iic fun x hx => max_eq_right hx)
  rw [this, Measure.map_const, Measure.restrict_apply_univ]

lemma map_max_restrict_Ioi (G : Measure ℝ) :
    (G.restrict (Ioi 0)).map (fun x => max x 0) = G.restrict (Ioi 0) := by
  have : (G.restrict (Ioi 0)).map (fun x => max x 0) = (G.restrict (Ioi 0)).map id :=
    Measure.map_congr (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => max_eq_left (le_of_lt hx))
  rw [this, Measure.map_id]

lemma map_abs_restrict_Ioi (G : Measure ℝ) :
    (G.restrict (Ioi 0)).map (fun x => |x|) = G.restrict (Ioi 0) := by
  have : (G.restrict (Ioi 0)).map (fun x => |x|) = (G.restrict (Ioi 0)).map id :=
    Measure.map_congr (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => abs_of_pos hx)
  rw [this, Measure.map_id]

lemma map_abs_gaussian {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun x => |x|) = (2 : ℝ≥0∞) • (gaussianReal 0 v).restrict (Ioi 0) := by
  set G := gaussianReal 0 v
  have hs := nullSingletonClass_gaussianReal (μ := 0) hv
  have hneg : G.map (fun x => -x) = G := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v); rw [neg_zero] at h; exact h
  have hIic : (G.restrict (Iic 0)).map (fun x => |x|) = G.restrict (Ioi 0) := by
    have h1 : (G.restrict (Iic 0)).map (fun x => |x|) = (G.restrict (Iic 0)).map (fun x => -x) :=
      Measure.map_congr (ae_restrict_of_forall_mem measurableSet_Iic fun x hx => abs_of_nonpos hx)
    have h2 : (G.restrict (Iic 0)).map (fun x => -x) = (G.map fun x => -x).restrict (Ici 0) := by
      rw [Measure.restrict_map measurable_neg measurableSet_Ici]
      congr 2; ext x; simp
    rw [h1, h2, hneg, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  conv_lhs => rw [gauss_split G]
  rw [Measure.map_add _ _ (continuous_abs.measurable), hIic, map_abs_restrict_Ioi, two_smul]

lemma map_max_gaussian {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun x => max x 0) =
      (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • (gaussianReal 0 v).map (fun x => |x|) := by
  set G := gaussianReal 0 v
  rw [map_abs_gaussian hv, smul_smul]
  have h2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [h2, one_smul]
  conv_lhs => rw [gauss_split G]
  have hmm : Measurable fun x : ℝ => max x 0 := (continuous_id.max continuous_const).measurable
  rw [Measure.map_add _ _ hmm, map_max_restrict_Iic,
    map_max_restrict_Ioi, StatFormal.Wave30z.gaussianReal_Iic_zero hv]

lemma halfNormal_Iic {σ2 : ℝ} (hσ : 0 < σ2) : halfNormal σ2 (Iic 0) = 0 := by
  have hv : σ2.toNNReal ≠ 0 := by simpa using hσ
  have hs := nullSingletonClass_gaussianReal (μ := 0) hv
  unfold halfNormal
  rw [Measure.map_apply continuous_abs.measurable measurableSet_Iic]
  have : (fun x : ℝ => |x|) ⁻¹' Iic 0 = {0} := by
    ext x; simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h; exact abs_nonpos_iff.1 h
    · intro h; rw [h, abs_zero]
  rw [this, measure_singleton]

lemma map_sq_gaussian {σ2 : ℝ} (hσ : 0 < σ2) :
    (gaussianReal 0 σ2.toNNReal).map (fun x => x ^ 2) = chiSq1.map (fun y => σ2 * y) := by
  have hG : gaussianReal 0 σ2.toNNReal = (gaussianReal 0 1).map (fun x => √σ2 * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext; simp [Real.sq_sqrt hσ.le, hσ.le]
  have hm1 : Measurable fun x : ℝ => √σ2 * x := measurable_const.mul measurable_id
  have hm2 : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hm3 : Measurable fun y : ℝ => σ2 * y := measurable_const.mul measurable_id
  rw [hG, Measure.map_map hm2 hm1, chiSq1, Measure.map_map hm3 hm2]
  congr 1
  funext x
  simp only [Function.comp, mul_pow, Real.sq_sqrt hσ.le]

end Gauss

theorem boundary_ray_shape : Claims.boundary_ray_shape := by
  intro σ2 hσ
  have hv : σ2.toNNReal ≠ 0 := by simpa using hσ
  refine ⟨map_max_gaussian hv, halfNormal_Iic hσ, ?_⟩
  have hmax : Measurable fun x : ℝ => max x 0 := (continuous_id.max continuous_const).measurable
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hm3 : Measurable fun y : ℝ => σ2 * y := measurable_const.mul measurable_id
  have e1 : (gaussianReal 0 σ2.toNNReal).map (fun x => (max x 0) ^ 2) =
      ((gaussianReal 0 σ2.toNNReal).map (fun x => max x 0)).map (fun x => x ^ 2) := by
    rw [Measure.map_map hsq hmax]; rfl
  have e2 : ((gaussianReal 0 σ2.toNNReal).map (fun x => |x|)).map (fun x => x ^ 2) =
      (gaussianReal 0 σ2.toNNReal).map (fun x => x ^ 2) := by
    rw [Measure.map_map hsq continuous_abs.measurable]
    congr 1; funext x; simp only [Function.comp, sq_abs]
  rw [e1, map_max_gaussian hv, Measure.map_add _ _ hsq, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hsq, e2, map_sq_gaussian hσ, chiBarSq, Measure.map_add _ _ hm3, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' hm3]
  · norm_num
  all_goals first | exact hm3.aemeasurable | exact hsq.aemeasurable

theorem boundary_ray_square : Claims.boundary_ray_square := by
  intro 𝒳 E _ _ _ _ φ κ α P Q _ _ Ω _ μ _ ξ η n m r cP cQ Ω' _ μ' _ 𝔾 ν tP sQ hφ hκ hα0 hα1 hS hSc h𝔾 hAB hν
    hray htP hsQ
  intro σ2
  have hR := (StatFormal.Wave30z.boundary_ray 𝒳 E φ κ α P Q Ω μ ξ η n m r cP cQ Ω' μ' 𝔾 ν hφ hκ hα0 hα1 hS hSc h𝔾
    hAB hν hray).2 tP sQ htP hsQ
  have h1 := hR.1.continuous_comp (g := fun x : ℝ => x ^ 2) (continuous_pow 2)
  refine ⟨h1, fun hσ => (boundary_ray_shape σ2 hσ).2.2⟩

end StatFormal.Wave30ah
