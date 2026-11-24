import StatFormal.Wave31tu.Statements
import StatFormal.Lib.LaplaceScale.QP
import StatFormal.Lib.LaplaceScale.Measure

/-!
# Wave 31tu route B: Claim Y17 `lap_rescale`, rescaling the data by `1/σ` (S4 :1038-1039; untrusted proof material)

"Rescaling the data by `1/σ` leaves the witness values, cut points and ramps unchanged and preserves the hypotheses with
rescaled constants, so we take `σ = 1`."  With `φ_σ(u) = φ(σu)`, `P_σ = P∘(·/σ)⁻¹`, `p_σ(u) = σp(σu)`:

* `laplace_feature_scale`: `φ_σ` has the Gram function `e^{−|u−u'|}`;
* `qp_scale`: the sample `x/σ, y/σ` has, with `φ_σ`, the feature vectors of `x, y` with `φ` (`φ_σ(x_i/σ) = φ(x_i)`), so the same
  minimizers, value, witness, witness values (as functions of `z/σ`) and own terms (`Lib/LaplaceScale/QP.lean`);
* `cross_scale`: `IsCross` for `P_σ, Q_σ, p_σ, q_σ` at `x₀/σ` with slope `σ²ℓ₀` (density of the image law,
  `map_div_withDensity`; a.e. signs along `u ↦ σu`, `ae_comp_mul`; the chain rule);
* `tail_scale`: `C′e^{−σt/C′} ≤ M e^{−t/M}` for `M = max(C′, C′/σ)`; the tails of `|P_σ − Q_σ| = |P − Q|∘(·/σ)⁻¹`
  (`absPQ_map_equiv`) and of `P_σ + Q_σ` at `t` are those of `|P − Q|`, `P + Q` at `σt`;
* `condR_scale`, `pbar_scale`: `eq:condR` with `min(1, r⋆/σ)`, `c⋆σ`, and the bound `σp̄` on the shrunken window;
* TV (`tvDist_map_measurableEquiv`), `D_α` (`Dpop_map_equiv`) and the two-sample law (`sampleLaw_map`) under the rescaling.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteB

open StatFormal StatFormal.Wave30tz StatFormal.Wave30tp StatFormal.Wave31tq StatFormal.LaplaceScale

lemma mul_div_scale {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) : σ * (x / σ) = x := by
  field_simp

/-- `φ_σ(u) = φ(σu)` has the Gram function `e^{−|u−u'|}` when `φ` has `e^{−|x−x'|/σ}`. -/
lemma laplace_feature_scale {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {σ : ℝ} {φ : ℝ → H} (hσ : 0 < σ)
    (hφ : IsLaplaceFeature σ φ) : IsLaplaceFeature 1 (fun u => φ (σ * u)) := by
  intro x y
  simp only
  rw [hφ, ← mul_sub, abs_mul, abs_of_pos hσ, div_one, neg_div, mul_div_cancel_left₀ _ hσ.ne']

/-- The quadratic program, its value, witness values and own terms are unchanged by `x ↦ x/σ`, `φ ↦ φ_σ`. -/
lemma qp_scale {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {σ : ℝ} (hσ : σ ≠ 0) (φ : ℝ → H) {n m : ℕ}
    (x : Fin n → ℝ) (y : Fin m → ℝ) (α : ℝ) (w : Fin n → ℝ) (v : Fin m → ℝ) :
    (IsQPMin φ α x y w v ↔ IsQPMin (fun u => φ (σ * u)) α (fun i => x i / σ) (fun j => y j / σ) w v) ∧
      qpVal φ x y w v = qpVal (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v ∧
      (∀ z, fitF φ x y w v z = fitF (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v (z / σ)) ∧
      ownX φ x y w v = ownX (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v ∧
      ownY φ x y w v = ownY (fun u => φ (σ * u)) (fun i => x i / σ) (fun j => y j / σ) w v := by
  have hx : ∀ i, φ (σ * (x i / σ)) = φ (x i) := fun i => by rw [mul_div_scale hσ]
  have hy : ∀ j, φ (σ * (y j / σ)) = φ (y j) := fun j => by rw [mul_div_scale hσ]
  have hw := witness_congr (ψ := fun u => φ (σ * u)) (x' := fun i => x i / σ) (y' := fun j => y j / σ) hx hy w v
  refine ⟨(isQPMin_congr (ψ := fun u => φ (σ * u)) (x' := fun i => x i / σ) (y' := fun j => y j / σ) hx hy α w v).symm,
    (qpVal_congr (ψ := fun u => φ (σ * u)) (x' := fun i => x i / σ) (y' := fun j => y j / σ) hx hy w v).symm,
    fun z => ?_,
    (ownX_congr (ψ := fun u => φ (σ * u)) (x' := fun i => x i / σ) (y' := fun j => y j / σ) hx hy w v).symm,
    (ownY_congr (ψ := fun u => φ (σ * u)) (x' := fun i => x i / σ) (y' := fun j => y j / σ) hx hy w v).symm⟩
  simp only [fitF, hw, mul_div_scale hσ]

/-- The crossing hypotheses of Proposition 5.5 under the rescaling. -/
lemma cross_scale {σ : ℝ} (hσ : 0 < σ) {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (h : IsCross P Q p q x₀ ℓ₀) :
    IsCross (P.map (fun x => x / σ)) (Q.map (fun x => x / σ)) (fun u => σ * p (σ * u)) (fun u => σ * q (σ * u))
      (x₀ / σ) (σ ^ 2 * ℓ₀) := by
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r, hr, hpc, hqc⟩, hpq, hqp, hd, hℓ⟩ := h
  have hmaps : MapsTo (fun u => σ * u) (Ioo (x₀ / σ - r / σ) (x₀ / σ + r / σ)) (Ioo (x₀ - r) (x₀ + r)) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    rw [← sub_div, div_lt_iff₀ hσ] at h1
    rw [← add_div, lt_div_iff₀ hσ] at h2
    exact ⟨by linarith [mul_comm σ u], by linarith [mul_comm σ u]⟩
  refine ⟨(hpm.comp (measurable_const_mul σ)).const_mul σ, (hqm.comp (measurable_const_mul σ)).const_mul σ,
    fun u => mul_nonneg hσ.le (hp0 _), fun u => mul_nonneg hσ.le (hq0 _), ?_, ?_, ?_, ?_, ?_, ?_, by positivity⟩
  · rw [hP]; exact map_div_withDensity hσ p
  · rw [hQ]; exact map_div_withDensity hσ q
  · exact ⟨r / σ, div_pos hr hσ, continuousOn_const.mul (hpc.comp (continuous_const_mul σ).continuousOn hmaps),
      continuousOn_const.mul (hqc.comp (continuous_const_mul σ).continuousOn hmaps)⟩
  · filter_upwards [ae_comp_mul hσ.ne' hpq] with u hu hlt
    have : x₀ < σ * u := by rw [div_lt_iff₀ hσ] at hlt; linarith [mul_comm σ u]
    exact mul_le_mul_of_nonneg_left (hu this) hσ.le
  · filter_upwards [ae_comp_mul hσ.ne' hqp] with u hu hlt
    have : σ * u < x₀ := by rw [lt_div_iff₀ hσ] at hlt; linarith [mul_comm σ u]
    exact mul_le_mul_of_nonneg_left (hu this) hσ.le
  · have hd' : HasDerivAt (fun x => p x - q x) ℓ₀ (σ * (x₀ / σ)) := by rw [mul_div_scale hσ.ne']; exact hd
    have hlin : HasDerivAt (fun u : ℝ => σ * u) σ (x₀ / σ) := by
      simpa using (hasDerivAt_id (x₀ / σ)).const_mul σ
    have h2 := (hd'.comp (x₀ / σ) hlin).const_mul σ
    convert h2 using 1
    · funext u
      simp only [Function.comp_apply]
      ring
    · ring

/-- The tail bound after rescaling: `C′e^{−σt/C′} ≤ M e^{−t/M}`, `M = max(C′, C′/σ)`, for `C′, σ, t > 0`. -/
lemma tail_scale {σ C' t : ℝ} (hσ : 0 < σ) (hC : 0 < C') (ht : 0 < t) :
    C' * Real.exp (-(σ * t) / C') ≤ max C' (C' / σ) * Real.exp (-t / max C' (C' / σ)) := by
  set M := max C' (C' / σ) with hMdef
  have hM : C' ≤ M := le_max_left _ _
  have hM' : C' / σ ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le hC hM
  have hexp : Real.exp (-(σ * t) / C') ≤ Real.exp (-t / M) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ hMpos hC]
    have h1 : C' ≤ M * σ := by rwa [div_le_iff₀ hσ] at hM'
    have h2 : t * C' ≤ t * (M * σ) := mul_le_mul_of_nonneg_left h1 ht.le
    linarith [mul_comm (σ * t) M, mul_assoc t M σ, mul_comm t (M * σ), mul_assoc M σ t]
  exact mul_le_mul hM hexp (Real.exp_pos _).le hMpos.le

/-- The preimage of `{|u − x₀/σ| > t}` under `x ↦ x/σ` is `{|x − x₀| > σt}`. -/
lemma preimage_tail {σ : ℝ} (hσ : 0 < σ) (x₀ t : ℝ) :
    (fun x : ℝ => x / σ) ⁻¹' {x | t < |x - x₀ / σ|} = {x | σ * t < |x - x₀|} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq]
  rw [← sub_div, abs_div, abs_of_pos hσ, lt_div_iff₀ hσ, mul_comm t σ]

lemma measurableSet_tail (c t : ℝ) : MeasurableSet {x : ℝ | t < |x - c|} :=
  measurableSet_lt measurable_const (by fun_prop)

/-- `eq:condR` under the rescaling, with radius `min(1, r⋆/σ)` and constant `c⋆σ` (densities `p, q ≥ 0`). -/
lemma condR_scale {σ : ℝ} (hσ : 0 < σ) {p q : ℝ → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) {x₀ rs cs : ℝ}
    (h : CondR p q x₀ rs cs) :
    CondR (fun u => σ * p (σ * u)) (fun u => σ * q (σ * u)) (x₀ / σ) (min 1 (rs / σ)) (cs * σ) := by
  obtain ⟨hrs0, -, hcs, hae⟩ := h
  refine ⟨lt_min one_pos (div_pos hrs0 hσ), min_le_left _ _, mul_pos hcs hσ, ?_⟩
  filter_upwards [ae_comp_mul hσ.ne' hae] with u hu
  set a := min (min 1 (rs / σ)) |u - x₀ / σ| with hadef
  have ha1 : σ * a ≤ rs := by
    have : a ≤ rs / σ := (min_le_left _ _).trans (min_le_right _ _)
    calc σ * a ≤ σ * (rs / σ) := mul_le_mul_of_nonneg_left this hσ.le
      _ = rs := mul_div_scale hσ.ne' rs
  have ha2 : σ * a ≤ |σ * u - x₀| := by
    have : a ≤ |u - x₀ / σ| := min_le_right _ _
    calc σ * a ≤ σ * |u - x₀ / σ| := mul_le_mul_of_nonneg_left this hσ.le
      _ = |σ * u - x₀| := by rw [← abs_of_pos hσ, ← abs_mul, abs_of_pos hσ, mul_sub, mul_div_scale hσ.ne']
  have hpq0 : 0 ≤ p (σ * u) + q (σ * u) := add_nonneg (hp0 _) (hq0 _)
  have hmin : σ * a ≤ min rs |σ * u - x₀| := le_min ha1 ha2
  calc cs * σ * a * (σ * p (σ * u) + σ * q (σ * u)) = σ * (cs * (σ * a) * (p (σ * u) + q (σ * u))) := by ring
    _ ≤ σ * (cs * min rs |σ * u - x₀| * (p (σ * u) + q (σ * u))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hcs.le) hpq0) hσ.le
    _ ≤ σ * |p (σ * u) - q (σ * u)| := mul_le_mul_of_nonneg_left hu hσ.le
    _ = |σ * p (σ * u) - σ * q (σ * u)| := by rw [← mul_sub, abs_mul, abs_of_pos hσ]

/-- The bound `p + q ≤ p̄` on `[x₀ − r⋆, x₀ + r⋆]` gives `p_σ + q_σ ≤ σp̄` on `[x₀/σ − min(1, r⋆/σ), x₀/σ + min(1, r⋆/σ)]`. -/
lemma pbar_scale {σ : ℝ} (hσ : 0 < σ) {p q : ℝ → ℝ} {x₀ rs pbar : ℝ} (h : ∀ z ∈ Icc (x₀ - rs) (x₀ + rs), p z + q z ≤ pbar) :
    ∀ z ∈ Icc (x₀ / σ - min 1 (rs / σ)) (x₀ / σ + min 1 (rs / σ)), σ * p (σ * z) + σ * q (σ * z) ≤ σ * pbar := by
  intro z hz
  have hm : σ * min 1 (rs / σ) ≤ rs :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hσ.le).trans_eq (mul_div_scale hσ.ne' rs)
  obtain ⟨hz1, hz2⟩ := hz
  have h1 := mul_le_mul_of_nonneg_left hz1 hσ.le
  have h2 := mul_le_mul_of_nonneg_left hz2 hσ.le
  rw [mul_sub, mul_div_scale hσ.ne'] at h1
  rw [mul_add, mul_div_scale hσ.ne'] at h2
  have hz' : σ * z ∈ Icc (x₀ - rs) (x₀ + rs) := ⟨by linarith, by linarith⟩
  calc σ * p (σ * z) + σ * q (σ * z) = σ * (p (σ * z) + q (σ * z)) := by ring
    _ ≤ σ * pbar := mul_le_mul_of_nonneg_left (h _ hz') hσ.le

/-- **Claim Y17** (`lap_rescale`, S4 :1038-1039). -/
theorem lap_rescale_route : Claims.lap_rescale := by
  intro H _ _ σ φ hσ hφ
  refine ⟨laplace_feature_scale hσ hφ, fun n m x y α w v => qp_scale hσ.ne' φ x y α w v, ?_⟩
  intro P Q _ _ p q x₀ ℓ₀ C' rs cs pbar hcross
  have hp0 := hcross.2.2.1
  have hq0 := hcross.2.2.2.1
  have hmeas : Measurable fun x : ℝ => x / σ := measurable_id.div_const σ
  refine ⟨cross_scale hσ hcross, ?_, ?_, ?_, ?_, condR_scale hσ hp0 hq0, pbar_scale hσ, ?_⟩
  · exact Distances.tvDist_map_measurableEquiv (μ := P) (ν := Q) (scaleEquiv σ hσ.ne')
  · intro a
    exact Dpop_map_equiv (scaleEquiv σ hσ.ne') (coe_scaleEquiv σ hσ.ne') (fun x => by simp only [mul_div_scale hσ.ne'])
      P Q a
  · rintro ⟨hC, ht⟩
    refine ⟨lt_max_of_lt_left hC, fun t htpos => ?_⟩
    rw [absPQ_map_equiv P Q (scaleEquiv σ hσ.ne') (coe_scaleEquiv σ hσ.ne'), Measure.map_apply hmeas (measurableSet_tail _ _),
      preimage_tail hσ]
    exact (ht (σ * t) (by positivity)).trans (ENNReal.ofReal_le_ofReal (tail_scale hσ hC htpos))
  · rintro ⟨hC, ht⟩
    refine ⟨lt_max_of_lt_left hC, fun t htpos => ?_⟩
    rw [Measure.add_apply, Measure.map_apply hmeas (measurableSet_tail _ _), Measure.map_apply hmeas (measurableSet_tail _ _),
      preimage_tail hσ, ← Measure.add_apply]
    exact (ht (σ * t) (by positivity)).trans (ENNReal.ofReal_le_ofReal (tail_scale hσ hC htpos))
  · intro n m
    exact sampleLaw_map P Q hmeas n m

end StatFormal.Wave31tu.RouteB
