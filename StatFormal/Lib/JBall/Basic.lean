import StatFormal.Wave31tp.Statements
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# The ball-averaged cosine `j_d` (library, untrusted)

For `d ≥ 1` let `B` be the open unit ball of `ℝ^d = EuclideanSpace ℝ (Fin d)` and
`j_d(y) = vol(B)⁻¹ ∫_B cos(y v₁) dv` (`Wave31tp.jBall`, `v₁ = v 0`). Classical facts proved here:

* `continuous_jBall`, `jBall_neg`, `jBall_zero`, `abs_jBall_le_one`: `j_d` is continuous and
  even, `j_d(0) = 1`, `|j_d| ≤ 1` (dominated convergence; `|cos| ≤ 1` on a finite-measure set);
* `jBall_lt_one`: `j_d(y) < 1` for `y ≠ 0`, since `1 − cos(y v₁)` is continuous, nonnegative
  and positive on a nonempty open subset of `B`;
* `tendsto_jBall_cocompact`: `j_d(y) → 0` as `|y| → ∞`, the Riemann–Lebesgue lemma
  (`tendsto_integral_exp_inner_smul_cocompact`) for `1_B` at the frequency `−(y/2π) e₁`;
* `exists_jBall_le_lt_one`, `sSup_jBall_Ici_one_lt_one`: `sup_{y ≥ 1} j_d(y) < 1` (outside a
  compact set `j_d < 1/2`; on the compact part the maximum is attained at some `y₀ ≥ 1`);
* `avg_cos_inner`: on every real inner-product space `V` of dimension `d`,
  `vol(B_V(0,r))⁻¹ ∫_{B_V(0,r)} cos⟪h, ξ⟫ dh = j_d(r‖ξ‖)`, via an orthonormal basis of `V` whose
  first vector is `ξ/‖ξ‖` (its coordinate map is a measure-preserving linear isometry onto
  `ℝ^d`) and the substitution `u = r v`.

The closed form `j_d(y) = Γ(d/2+1)(2/y)^{d/2} J_{d/2}(y)` (Stein–Weiss IV.3) is not used.
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped RealInnerProductSpace FourierTransform

set_option linter.style.longLine false

namespace StatFormal.JBall

open StatFormal.Wave31tp (jBall)

local notation "E" d => EuclideanSpace ℝ (Fin d)

section Basic

variable {d : ℕ}

lemma jBall_def [NeZero d] (y : ℝ) :
    jBall d y = (volume (ball (0 : E d) 1)).toReal⁻¹ * ∫ v in ball (0 : E d) 1, Real.cos (y * v 0) := rfl

lemma volume_unitBall_ne_top : volume (ball (0 : E d) 1) ≠ ⊤ := measure_ball_lt_top.ne

/-- The volume of the unit ball of `ℝ^d` is a positive real number. -/
lemma volume_unitBall_toReal_pos : 0 < (volume (ball (0 : E d) 1)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' volume_unitBall_ne_top

/-- A continuous function is integrable on the unit ball (inside the compact closed ball). -/
lemma integrableOn_unitBall {F : Type*} [NormedAddCommGroup F] {f : (E d) → F} (hf : Continuous f) :
    IntegrableOn f (ball (0 : E d) 1) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall

lemma continuous_coord (i : Fin d) : Continuous fun v : E d => v i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

variable [NeZero d]

/-- `y ↦ ∫_B cos(y v₁)` is continuous (dominated by `1` on the finite-measure ball). -/
lemma continuous_integral_cos : Continuous fun y : ℝ => ∫ v in ball (0 : E d) 1, Real.cos (y * v 0) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun y => ?_) (fun y => ?_) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul (continuous_coord 0))).aestronglyMeasurable
  · exact Eventually.of_forall fun v => by simpa using Real.abs_cos_le_one _
  · exact integrableOn_const volume_unitBall_ne_top
  · exact Eventually.of_forall fun v => Real.continuous_cos.comp (continuous_id.mul continuous_const)

/-- `j_d` is continuous. -/
theorem continuous_jBall : Continuous (jBall d) :=
  continuous_const.mul continuous_integral_cos

/-- `j_d` is even. -/
theorem jBall_neg (y : ℝ) : jBall d (-y) = jBall d y := by
  simp only [jBall_def, neg_mul, Real.cos_neg]

/-- `j_d(0) = 1`. -/
theorem jBall_zero : jBall d 0 = 1 := by
  rw [jBall_def]
  simp only [zero_mul, Real.cos_zero, setIntegral_const, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ volume_unitBall_toReal_pos.ne'

/-- `|j_d| ≤ 1`. -/
theorem abs_jBall_le_one (y : ℝ) : |jBall d y| ≤ 1 := by
  have hV := volume_unitBall_toReal_pos (d := d)
  have hI : ‖∫ v in ball (0 : E d) 1, Real.cos (y * v 0)‖ ≤ 1 * volume.real (ball (0 : E d) 1) :=
    norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
      (fun v _ => by simpa using Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, one_mul] at hI
  rw [jBall_def, abs_mul, abs_inv, abs_of_pos hV]
  calc _ ≤ (volume (ball (0 : E d) 1)).toReal⁻¹ * (volume (ball (0 : E d) 1)).toReal := by
        gcongr; exact hI
    _ = 1 := inv_mul_cancel₀ hV.ne'

/-- `∫_B (1 − cos(y v₁)) > 0` for `y ≠ 0`: the integrand is continuous, nonnegative, and positive at
`v = t e₁` with `t = 1/(2(|y|+1))`. -/
lemma integral_one_sub_cos_pos {y : ℝ} (hy : y ≠ 0) :
    0 < ∫ v in ball (0 : E d) 1, (1 - Real.cos (y * v 0)) := by
  have hc : Continuous fun v : E d => 1 - Real.cos (y * v 0) :=
    continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul (continuous_coord 0)))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun v => sub_nonneg.2 (Real.cos_le_one _)) (integrableOn_unitBall hc)]
  have hopen : IsOpen (Function.support (fun v : E d => 1 - Real.cos (y * v 0)) ∩ ball 0 1) :=
    (hc.isOpen_preimage _ isOpen_compl_singleton).inter isOpen_ball
  refine hopen.measure_pos volume ⟨EuclideanSpace.single 0 (1 / (2 * (|y| + 1))), ?_, ?_⟩
  · have hpos : 0 < |y| + 1 := by positivity
    set t := 1 / (2 * (|y| + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hyt : |y * t| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos ht0, ht]
      rw [show |y| * (1 / (2 * (|y| + 1))) = (|y| / (|y| + 1)) / 2 by field_simp]
      have : |y| / (|y| + 1) ≤ 1 := (div_le_one hpos).2 (by linarith)
      linarith
    have hne : y * t ≠ 0 := mul_ne_zero hy ht0.ne'
    simp only [Function.mem_support, PiLp.single_apply, ↓reduceIte]
    intro h
    have h1 : Real.cos (y * t) = 1 := by linarith
    obtain ⟨hl1, hl2⟩ := abs_le.1 hyt
    exact hne ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.two_le_pi])
      (by linarith [Real.two_le_pi])).1 h1)
  · rw [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_lt_one (by positivity)]
    linarith [abs_nonneg y]

/-- `j_d(y) < 1` for `y ≠ 0`. -/
theorem jBall_lt_one {y : ℝ} (hy : y ≠ 0) : jBall d y < 1 := by
  have hV := volume_unitBall_toReal_pos (d := d)
  have hsub : ∫ v in ball (0 : E d) 1, (1 - Real.cos (y * v 0)) =
      (volume (ball (0 : E d) 1)).toReal - ∫ v in ball (0 : E d) 1, Real.cos (y * v 0) := by
    have h1 : IntegrableOn (fun _ : E d => (1 : ℝ)) (ball (0 : E d) 1) := integrableOn_const volume_unitBall_ne_top
    have h2 : IntegrableOn (fun v : E d => Real.cos (y * v 0)) (ball (0 : E d) 1) :=
      integrableOn_unitBall (Real.continuous_cos.comp (continuous_const.mul (continuous_coord 0)))
    rw [integral_sub h1 h2, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hpos := integral_one_sub_cos_pos (d := d) hy
  rw [hsub] at hpos
  rw [jBall_def, inv_mul_lt_iff₀ hV, mul_one]
  linarith

/-- The frequency `w_y = −(y/2π) e₁`, at which `𝐞(−⟪v, w_y⟫) = e^{i y v₁}`. -/
def freq (d : ℕ) [NeZero d] (y : ℝ) : E d := (-(y / (2 * Real.pi))) • EuclideanSpace.single 0 1

lemma tendsto_freq : Tendsto (freq d) (cocompact ℝ) (cocompact (E d)) := by
  rw [← Metric.cobounded_eq_cocompact (α := E d), ← tendsto_norm_atTop_iff_cobounded]
  have h : (fun y => ‖freq d y‖) = fun y => ‖y‖ / (2 * Real.pi) := by
    ext y
    rw [freq, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_neg, norm_div, Real.norm_eq_abs (2 * Real.pi),
      abs_of_pos (by positivity)]
  rw [h]
  exact tendsto_norm_cocompact_atTop.atTop_div_const (by positivity)

/-- `∫_B cos(y v₁) = Re ∫ 𝐞(−⟪v, w_y⟫) 1_B(v) dv`. -/
lemma integral_cos_eq_re (y : ℝ) :
    ∫ v in ball (0 : E d) 1, Real.cos (y * v 0) =
      (∫ v, 𝐞 (-⟪v, freq d y⟫) • (ball (0 : E d) 1).indicator (fun _ => (1 : ℂ)) v).re := by
  have h1 : (fun v : E d => 𝐞 (-⟪v, freq d y⟫) • (ball (0 : E d) 1).indicator (fun _ => (1 : ℂ)) v) =
      (ball (0 : E d) 1).indicator (fun v => ((𝐞 (-⟪v, freq d y⟫) : Circle) : ℂ)) := by
    ext v
    by_cases hv : v ∈ ball (0 : E d) 1
    · simp [indicator_of_mem hv, Circle.smul_def]
    · simp [indicator_of_notMem hv]
  rw [h1, integral_indicator measurableSet_ball]
  have hint : Integrable (fun v : E d => ((𝐞 (-⟪v, freq d y⟫) : Circle) : ℂ)) (volume.restrict (ball 0 1)) := by
    refine integrableOn_unitBall ?_
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine setIntegral_congr_fun measurableSet_ball fun v _ => ?_
  have hin : ⟪v, freq d y⟫ = -(y / (2 * Real.pi)) * v 0 := by
    rw [freq, inner_smul_right, EuclideanSpace.inner_single_right, one_mul]
    simp
  simp only [Real.fourierChar_apply]
  rw [Complex.exp_ofReal_mul_I_re, hin]
  congr 1
  field_simp

/-- **Riemann–Lebesgue**: `j_d(y) → 0` as `|y| → ∞`. -/
theorem tendsto_jBall_cocompact : Tendsto (jBall d) (cocompact ℝ) (𝓝 0) := by
  have hRL := tendsto_integral_exp_inner_smul_cocompact ((ball (0 : E d) 1).indicator fun _ => (1 : ℂ))
  have h2 := ((Complex.continuous_re.tendsto 0).comp (hRL.comp tendsto_freq)).const_mul
    ((volume (ball (0 : E d) 1)).toReal⁻¹)
  rw [Complex.zero_re, mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, jBall_def, integral_cos_eq_re]

/-- `j_d` is bounded above by `1`. -/
theorem bddAbove_jBall (s : Set ℝ) : BddAbove (jBall d '' s) :=
  ⟨1, by rintro _ ⟨y, -, rfl⟩; exact (le_abs_self _).trans (abs_jBall_le_one y)⟩

/-- A uniform bound `j_d(y) ≤ c < 1` on `y ≥ 1`: beyond a compact set `j_d < 1/2`, and on the compact part
the maximum is attained at a point `y₀ ≥ 1`, where `j_d(y₀) < 1`. -/
theorem exists_jBall_le_lt_one : ∃ c < 1, ∀ y ∈ Ici (1 : ℝ), jBall d y ≤ c := by
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.1
    ((tendsto_jBall_cocompact (d := d)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hS : IsCompact (insert (1 : ℝ) (K ∩ Ici 1)) := (hK.inter_right isClosed_Ici).insert 1
  obtain ⟨y₀, hy₀S, hmax⟩ := hS.exists_isMaxOn (insert_nonempty _ _)
    (continuous_jBall (d := d)).continuousOn
  have hy₀ : 1 ≤ y₀ := by
    rcases hy₀S with rfl | ⟨-, h⟩
    exacts [le_rfl, h]
  refine ⟨max (1 / 2) (jBall d y₀), max_lt (by norm_num) (jBall_lt_one (by linarith)), fun y hy => ?_⟩
  by_cases hyK : y ∈ K
  · exact le_max_of_le_right (hmax (mem_insert_of_mem _ ⟨hyK, hy⟩))
  · exact le_max_of_le_left (hKsub hyK).le

/-- `sup_{y ≥ 1} j_d(y) < 1`. -/
theorem sSup_jBall_Ici_one_lt_one : sSup (jBall d '' Ici 1) < 1 := by
  obtain ⟨c, hc1, hc⟩ := exists_jBall_le_lt_one (d := d)
  exact (csSup_le (nonempty_Ici.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hc y hy)).trans_lt hc1

end Basic

section Rotation

variable {d : ℕ} [NeZero d]

/-- In `ℝ^d`, the average of `cos(a v₁)` over the ball of radius `r > 0` is `j_d(r a)` (substitution `u = r v`). -/
theorem avg_cos_coord (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (volume (ball (0 : E d) r)).toReal⁻¹ * ∫ u in ball (0 : E d) r, Real.cos (a * u 0) = jBall d (r * a) := by
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr d
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun u : E d => Real.cos (a * u 0)) (ball 0 1) hr
  rw [smul_unitBall_of_pos hr, finrank_euclideanSpace_fin] at hscale
  have hpt : ∀ x : E d, Real.cos (a * (r • x) 0) = Real.cos ((r * a) * x 0) := fun x => by
    rw [PiLp.smul_apply, smul_eq_mul]; ring_nf
  simp_rw [hpt] at hscale
  have hI : ∫ u in ball (0 : E d) r, Real.cos (a * u 0) =
      r ^ d * ∫ v in ball (0 : E d) 1, Real.cos ((r * a) * v 0) := by
    rw [hscale, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul]
  have hvol : volume (ball (0 : E d) r) = ENNReal.ofReal (r ^ d) * volume (ball (0 : E d) 1) := by
    rw [Measure.addHaar_ball volume 0 hr.le, finrank_euclideanSpace_fin]
  rw [hI, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hrd.le, jBall_def, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hrd.ne', one_mul]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- Every `ξ` is `‖ξ‖ • e` for a unit vector `e` (any unit vector when `ξ = 0`). -/
lemma exists_unit_smul (hd : Module.finrank ℝ V = d) (ξ : V) : ∃ e : V, ‖e‖ = 1 ∧ ξ = ‖ξ‖ • e := by
  by_cases h0 : ξ = 0
  · let b := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
    exact ⟨b 0, b.norm_eq_one 0, by simp [h0]⟩
  · refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]

omit [MeasurableSpace V] [BorelSpace V] in
/-- An orthonormal basis of `V` indexed by `Fin d` whose `0`-th vector is a given unit vector. -/
lemma exists_orthonormalBasis_zero (hd : Module.finrank ℝ V = d) {e : V} (he : ‖e‖ = 1) :
    ∃ b : OrthonormalBasis (Fin d) ℝ V, b 0 = e := by
  have hon : Orthonormal ℝ (({0} : Set (Fin d)).domRestrict fun _ => e) := by
    refine ⟨fun _ => he, fun i j hij => absurd ?_ hij⟩
    exact Subtype.ext (i.2.trans j.2.symm)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (by rw [hd, Fintype.card_fin]) hon
  exact ⟨b, hb 0 rfl⟩

/-- **Rotation and scaling**: on every real inner-product space `V` of dimension `d`, the average of `cos⟪h, ξ⟫` over the
ball `B_V(0, r)`, `r > 0`, is `j_d(r‖ξ‖)`. -/
theorem avg_cos_inner (hd : Module.finrank ℝ V = d) {r : ℝ} (hr : 0 < r) (ξ : V) :
    (volume (ball (0 : V) r)).toReal⁻¹ * ∫ h in ball (0 : V) r, Real.cos ⟪h, ξ⟫ = jBall d (r * ‖ξ‖) := by
  obtain ⟨e, he, hξ⟩ := exists_unit_smul hd ξ
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_zero hd he
  have hL : MeasurePreserving b.repr volume volume := b.measurePreserving_repr
  have hpre : b.repr ⁻¹' ball (0 : E d) r = ball (0 : V) r := by
    ext h
    simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  have hcoord : ∀ h : V, Real.cos ⟪h, ξ⟫ = Real.cos (‖ξ‖ * b.repr h 0) := fun h => by
    rw [b.repr_apply_apply, hb, real_inner_comm h e]
    conv_lhs => rw [hξ, inner_smul_right]
  have hint : ∫ h in ball (0 : V) r, Real.cos ⟪h, ξ⟫ = ∫ u in ball (0 : E d) r, Real.cos (‖ξ‖ * u 0) := by
    simp_rw [hcoord]
    rw [← hpre]
    exact hL.setIntegral_preimage_emb b.repr.toHomeomorph.measurableEmbedding
      (fun u : E d => Real.cos (‖ξ‖ * u 0)) (ball 0 r)
  have hvol : volume (ball (0 : V) r) = volume (ball (0 : E d) r) := by
    rw [← hpre, hL.measure_preimage measurableSet_ball.nullMeasurableSet]
  rw [hint, hvol, avg_cos_coord _ hr]

end Rotation

end StatFormal.JBall
