import StatFormal.Wave31tq.Statements
import StatFormal.Lib.HalfSpace.Volume
import StatFormal.Lib.HalfSpace.Integrals

/-!
# Wave 31tq, route X: the half-space witness in every dimension (Q29) (untrusted proof file)

* `halfspace_geometry_route`: for `G = {a < ⟪x, e⟫}` (`‖e‖ = 1`), `E = G ∩ B(c₀, ρ)`: (G1) `vol(E △ (E + h)) ≤ Π_ρ‖h‖` with
  `Π_ρ = (2ρ)^{d−1} + 2dω_dρ^{d−1}` (`HalfSpace.volume_symmDiff_halfball_le`: a slab inside a box and two ball shells), (G2)
  `vol{x ∈ B(c₀, ρ) : dist(x, ∂G) ≤ t} ≤ 2(2ρ)^{d−1} t` (`HalfSpace.volume_near_hyperplane_le`), and
  `dist(x, ∂G) = |⟪x, e⟫ − a|` (`HalfSpace.infDist_frontier_halfspace`).
* `halfspace_pair_route`: with `⟪c₀, e⟫ = a`, `p, q = vol(B₂)⁻¹ 1_{B₂} ± η(⟪x, e⟫ − a) 1_{B₁}`, `η = (2 vol(B(0,2)))⁻¹`: on `B₁`,
  `|⟪x, e⟫ − a| < 1`, so the perturbation is at most `η = vol(B₂)⁻¹/2` and `p, q ≥ 0`; the perturbation integrates to `0` by the
  reflection through `c₀` (`HalfSpace.integral_indicator_inner_sub_eq_zero`), so `P, Q` are probability measures; `P(A) − Q(A) =
  2∫_A η(⟪x, e⟫ − a)1_{B₁}`, which is positive on the open nonempty `A = G ∩ B₁` (so `α⋆ > 0`) and at most
  `2ηω_d = 2^{−d} ≤ 1/2` in absolute value (so `α⋆ < 1`). No cross-chunk hypothesis is needed.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric Module
open scoped InnerProductSpace RealInnerProductSpace symmDiff ENNReal

namespace StatFormal.Wave31tq.RouteX

open StatFormal.Distances

/-- Q29 `halfspace_geometry`: (G1), (G2) and `dist(x, ∂G) = |⟪x, e⟫ − a|` for the half-space `G` and the ball `B(c₀, ρ)`. -/
theorem halfspace_geometry_route : Claims.halfspace_geometry := by
  intro d _ V _ _ _ _ _ hd e a c₀ ρ he hρ
  subst hd
  exact ⟨fun h => HalfSpace.volume_symmDiff_halfball_le he a c₀ (by linarith) h,
    fun w₀ _ t _ => HalfSpace.volume_near_hyperplane_le he a c₀ (by linarith) t,
    fun x => HalfSpace.infDist_frontier_halfspace he a x⟩

/-- The explicit pair of Q29 (c), with its densities named. -/
theorem pair_facts (d : ℕ) [NeZero d] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (hd : finrank ℝ V = d) (e : V) (a : ℝ) (c₀ : V) (he : ‖e‖ = 1)
    (hc : ⟪c₀, e⟫_ℝ = a) (η : ℝ) (hη : η = (2 * (volume (ball (0 : V) 2)).toReal)⁻¹) (u w : V → ℝ)
    (hu : ∀ x, u x = (volume (ball c₀ 2)).toReal⁻¹ * (ball c₀ 2).indicator (fun _ => (1 : ℝ)) x)
    (hw : ∀ x, w x = η * (⟪x, e⟫_ℝ - a) * (ball c₀ 1).indicator (fun _ => (1 : ℝ)) x) :
    Measurable (fun x => u x + w x) ∧ Measurable (fun x => u x - w x) ∧ (∀ x, 0 ≤ u x + w x) ∧ (∀ x, 0 ≤ u x - w x) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (u x + w x))) univ = 1 ∧
      (volume.withDensity (fun x => ENNReal.ofReal (u x - w x))) univ = 1 ∧
      (∀ x ∈ {x : V | a < ⟪x, e⟫_ℝ}, u x - w x ≤ u x + w x) ∧ (∀ x ∉ {x : V | a < ⟪x, e⟫_ℝ}, u x + w x ≤ u x - w x) ∧
      (∀ x, |(u x + w x) - (u x - w x)| ≤ 2 * η * infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ})) ∧
      (∀ x, x ∉ ball c₀ 1 → w x = 0) ∧
      0 < tvDist (volume.withDensity (fun x => ENNReal.ofReal (u x + w x)))
        (volume.withDensity (fun x => ENNReal.ofReal (u x - w x))) ∧
      tvDist (volume.withDensity (fun x => ENNReal.ofReal (u x + w x)))
        (volume.withDensity (fun x => ENNReal.ofReal (u x - w x))) < 1 := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have : Nontrivial V := ⟨⟨e, 0, he0⟩⟩
  have hee : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  -- volumes of the balls
  set V2 := (volume (ball (0 : V) 2)).toReal with hV2def
  set ω1 := (volume (ball (0 : V) 1)).toReal with hω1def
  have hB2c : (volume (ball c₀ 2)).toReal = V2 := by rw [Measure.addHaar_ball_center]
  have hB1c : (volume (ball c₀ 1)).toReal = ω1 := by rw [Measure.addHaar_ball_center]
  have hω1pos : 0 < ω1 := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hV2 : V2 = 2 ^ d * ω1 := by
    rw [hV2def, Measure.addHaar_ball volume (0 : V) zero_le_two, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hd]
  have hV2pos : 0 < V2 := by rw [hV2]; positivity
  have hηpos : 0 < η := by rw [hη]; positivity
  have h2η : V2⁻¹ = 2 * η := by rw [hη]; field_simp
  -- pointwise facts
  have hin : ∀ x ∈ ball c₀ 1, |⟪x, e⟫_ℝ - a| < 1 := fun x hx => by
    rw [← hc, ← inner_sub_left]
    calc |⟪x - c₀, e⟫_ℝ| ≤ ‖x - c₀‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ < 1 := by rw [he, mul_one, ← dist_eq_norm]; exact hx
  have hw_off : ∀ x, x ∉ ball c₀ 1 → w x = 0 := fun x hx => by rw [hw, indicator_of_notMem hx, mul_zero]
  have hw_on : ∀ x ∈ ball c₀ 1, w x = η * (⟪x, e⟫_ℝ - a) := fun x hx => by rw [hw, indicator_of_mem hx, mul_one]
  have hu_on : ∀ x ∈ ball c₀ 1, u x = V2⁻¹ := fun x hx => by
    rw [hu, indicator_of_mem (ball_subset_ball one_le_two hx), mul_one, hB2c]
  have hu0 : ∀ x, 0 ≤ u x := fun x => by
    rw [hu]; exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (indicator_nonneg (fun _ _ => zero_le_one) x)
  have hwabs : ∀ x, |w x| ≤ η * |⟪x, e⟫_ℝ - a| := fun x => by
    by_cases hx : x ∈ ball c₀ 1
    · rw [hw_on x hx, abs_mul, abs_of_pos hηpos]
    · rw [hw_off x hx, abs_zero]; positivity
  have hwle : ∀ x, |w x| ≤ (ball c₀ 1).indicator (fun _ => η) x := fun x => by
    by_cases hx : x ∈ ball c₀ 1
    · rw [indicator_of_mem hx]
      have h1 := hin x hx
      have h2 := hwabs x
      have h3 : η * |⟪x, e⟫_ℝ - a| ≤ η * 1 := mul_le_mul_of_nonneg_left h1.le hηpos.le
      linarith
    · rw [indicator_of_notMem hx, hw_off x hx, abs_zero]
  have hpos : ∀ x, 0 ≤ u x + w x ∧ 0 ≤ u x - w x := fun x => by
    by_cases hx : x ∈ ball c₀ 1
    · have h1 := hwle x
      rw [indicator_of_mem hx, abs_le] at h1
      rw [hu_on x hx, h2η]
      constructor <;> linarith [h1.1, h1.2]
    · rw [hw_off x hx, add_zero, sub_zero]; exact ⟨hu0 x, hu0 x⟩
  have hwG : ∀ x, a < ⟪x, e⟫_ℝ → 0 ≤ w x := fun x hx => by
    by_cases hb : x ∈ ball c₀ 1
    · rw [hw_on x hb]; exact mul_nonneg hηpos.le (by linarith)
    · rw [hw_off x hb]
  have hwGc : ∀ x, ¬ a < ⟪x, e⟫_ℝ → w x ≤ 0 := fun x hx => by
    push Not at hx
    by_cases hb : x ∈ ball c₀ 1
    · rw [hw_on x hb]; exact mul_nonpos_of_nonneg_of_nonpos hηpos.le (by linarith)
    · rw [hw_off x hb]
  -- measurability and integrability
  have hum : Measurable u := by
    rw [show u = fun x => (volume (ball c₀ 2)).toReal⁻¹ * (ball c₀ 2).indicator (fun _ => (1 : ℝ)) x from funext hu]
    exact measurable_const.mul (measurable_const.indicator measurableSet_ball)
  have hwm : Measurable w := by
    rw [show w = fun x => η * (⟪x, e⟫_ℝ - a) * (ball c₀ 1).indicator (fun _ => (1 : ℝ)) x from funext hw]
    exact (measurable_const.mul ((continuous_id.inner continuous_const).measurable.sub measurable_const)).mul
      (measurable_const.indicator measurableSet_ball)
  have hgi : Integrable ((ball c₀ 1).indicator fun _ => η) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hui : Integrable u := by
    have hu' : u = (ball c₀ 2).indicator (fun _ => (volume (ball c₀ 2)).toReal⁻¹) := funext fun x => by
      rw [hu]; by_cases hx : x ∈ ball c₀ 2 <;> simp [hx]
    rw [hu']
    exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hwi : Integrable w :=
    Integrable.mono' hgi hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hwle x)
  have hint_u : ∫ x, u x = 1 := by
    have hu' : (fun x => u x) = (ball c₀ 2).indicator (fun _ => (volume (ball c₀ 2)).toReal⁻¹) := funext fun x => by
      rw [hu]; by_cases hx : x ∈ ball c₀ 2 <;> simp [hx]
    rw [hu', integral_indicator_const _ measurableSet_ball, smul_eq_mul, measureReal_def, hB2c,
      mul_inv_cancel₀ hV2pos.ne']
  have hint_w : ∫ x, w x = 0 := by
    have hw' : (fun x => w x) = fun x => η * (ball c₀ 1).indicator (fun x => ⟪x, e⟫_ℝ - a) x := funext fun x => by
      by_cases hx : x ∈ ball c₀ 1
      · rw [hw_on x hx, indicator_of_mem hx]
      · rw [hw_off x hx, indicator_of_notMem hx, mul_zero]
    rw [hw', integral_const_mul, HalfSpace.integral_indicator_inner_sub_eq_zero hc, mul_zero]
  -- the two laws
  have hpi : Integrable (fun x => u x + w x) := hui.add hwi
  have hqi : Integrable (fun x => u x - w x) := hui.sub hwi
  have hPu : (volume.withDensity (fun x => ENNReal.ofReal (u x + w x))) univ = 1 := by
    rw [HalfSpace.withDensity_ofReal_univ volume (p := fun x => u x + w x) hpi (fun x => (hpos x).1),
      integral_add hui hwi, hint_u, hint_w, add_zero, ENNReal.ofReal_one]
  have hQu : (volume.withDensity (fun x => ENNReal.ofReal (u x - w x))) univ = 1 := by
    rw [HalfSpace.withDensity_ofReal_univ volume (p := fun x => u x - w x) hqi (fun x => (hpos x).2),
      integral_sub hui hwi, hint_u, hint_w, sub_zero, ENNReal.ofReal_one]
  set P := volume.withDensity (fun x => ENNReal.ofReal (u x + w x)) with hPdef
  set Q := volume.withDensity (fun x => ENNReal.ofReal (u x - w x)) with hQdef
  have : IsFiniteMeasure P := ⟨by rw [hPu]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure Q := ⟨by rw [hQu]; exact ENNReal.one_lt_top⟩
  have hreal : ∀ A, MeasurableSet A → P.real A - Q.real A = 2 * ∫ x in A, w x := fun A hA => by
    rw [hPdef, hQdef, HalfSpace.measureReal_withDensity_ofReal volume (p := fun x => u x + w x) hpi (fun x => (hpos x).1) hA,
      HalfSpace.measureReal_withDensity_ofReal volume (p := fun x => u x - w x) hqi (fun x => (hpos x).2) hA,
      integral_add hui.integrableOn hwi.integrableOn, integral_sub hui.integrableOn hwi.integrableOn]
    ring
  -- α⋆ < 1
  have hupper : tvDist P Q ≤ 1 / 2 := by
    apply tvDist_le_of_forall
    intro A hA
    rw [hreal A hA, abs_mul, abs_two]
    have h1 : |∫ x in A, w x| ≤ ∫ x, |w x| :=
      (abs_integral_le_integral_abs).trans (setIntegral_le_integral hwi.abs (Filter.Eventually.of_forall fun x => abs_nonneg _))
    have h2 : ∫ x, |w x| ≤ ∫ x, (ball c₀ 1).indicator (fun _ => η) x := integral_mono hwi.abs hgi hwle
    have h3 : ∫ x, (ball c₀ 1).indicator (fun _ => η) x = ω1 * η := by
      rw [integral_indicator_const _ measurableSet_ball, smul_eq_mul, measureReal_def, hB1c]
    have h2d : (2 : ℝ) ≤ 2 ^ d := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (NeZero.one_le)
    have h4 : 2 * (ω1 * η) ≤ 1 / 2 := by
      have e1 : 2 * (ω1 * η) = (2 ^ d)⁻¹ := by
        rw [hη, hV2]; field_simp
      rw [e1, one_div]
      exact inv_anti₀ two_pos h2d
    nlinarith
  -- α⋆ > 0
  have hAm : MeasurableSet ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1) :=
    (measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable).inter measurableSet_ball
  have hAo : IsOpen ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1) :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).inter isOpen_ball
  have hAne : ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1).Nonempty := by
    refine ⟨c₀ + (1 / 2 : ℝ) • e, ?_, ?_⟩
    · change a < ⟪c₀ + (1 / 2 : ℝ) • e, e⟫_ℝ
      rw [inner_add_left, real_inner_smul_left, hee, hc]; linarith
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he]; norm_num
  have hwA : 0 < ∫ x in {x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1, w x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem hAm fun x hx => hwG x hx.1) hwi.integrableOn]
    have hsupp : Function.support w ∩ ({x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1) = {x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1 :=
      inter_eq_right.2 fun x hx => by
        have hx1 : a < ⟪x, e⟫_ℝ := hx.1
        rw [Function.mem_support, hw_on x hx.2]
        exact (mul_pos hηpos (by linarith)).ne'
    rw [hsupp]
    exact hAo.measure_pos volume hAne
  have hlower : 0 < tvDist P Q := by
    have h := abs_measureReal_sub_le_tvDist (μ := P) (ν := Q) hAm
    rw [hreal _ hAm] at h
    have : 0 < |2 * ∫ x in {x : V | a < ⟪x, e⟫_ℝ} ∩ ball c₀ 1, w x| := abs_pos.2 (by positivity)
    linarith
  refine ⟨hum.add hwm, hum.sub hwm, fun x => (hpos x).1, fun x => (hpos x).2, hPu, hQu,
    fun x hx => by linarith [hwG x hx], fun x hx => by linarith [hwGc x hx], fun x => ?_, hw_off, hlower,
    by linarith⟩
  rw [HalfSpace.infDist_frontier_halfspace he, show (u x + w x) - (u x - w x) = 2 * w x by ring, abs_mul, abs_two]
  have := hwabs x
  nlinarith

/-- Q29 `halfspace_pair`: the explicit pair crossing on a hyperplane through the centre. -/
theorem halfspace_pair_route : Claims.halfspace_pair := by
  intro d _ V _ _ _ _ _ hd e a c₀ he hc
  exact pair_facts d hd e a c₀ he hc _ rfl _ _ (fun _ => rfl) (fun _ => rfl)

end StatFormal.Wave31tq.RouteX
