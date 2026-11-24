import StatFormal.Archive.OTFD.Wave8b.Statements
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Route: A `thm:naive-degenerate`

1. Sphere kit: `sphereUnif K` is a probability measure carried by the unit sphere and invariant under every linear
   isometry (Mathlib's cone formula `toSphere_apply'` plus `LinearIsometryEquiv.measurePreserving`).
2. `E⟨v,θ⟩² = ‖v‖²/K`: invariance and a reflection taking `v` to `w` (`reflection_sub`) make it depend on `‖v‖`
   only; summing over the coordinate vectors gives `1`.
3. `⟨ι_K L^{-1}(rθ), h⟩ = r⟨θ, L^{-⊤}Π_K h⟩` and Fubini (`integral_prod_mul`) with `E R² = 1/3`.
4. Weak topology: a weak neighbourhood of `0` contains `{x : |ℓ(x)| < r, ℓ ∈ s}` (`hasBasis_weakBilin`), then
   Chebyshev and the second-moment bound.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace ENNReal Pointwise

namespace StatFormal.OTFD.Wave8b

variable {K : ℕ}

/-! ### Sphere kit -/

lemma sphereUnif_map_isometry (T : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K)) :
    (sphereUnif K).map T = sphereUnif K := by
  have hT : Measurable T := T.continuous.measurable
  have key : ((volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere.map Subtype.val).map T =
      (volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere.map Subtype.val := by
    ext A hA
    rw [Measure.map_apply hT hA, Measure.map_apply measurable_subtype_coe (hT hA),
      Measure.map_apply measurable_subtype_coe hA,
      Measure.toSphere_apply' _ (measurable_subtype_coe (hT hA)),
      Measure.toSphere_apply' _ (measurable_subtype_coe hA), Subtype.image_preimage_coe,
      Subtype.image_preimage_coe]
    congr 1
    have hset : Ioo (0 : ℝ) 1 • (Metric.sphere (0 : EuclideanSpace ℝ (Fin K)) 1 ∩ T ⁻¹' A) =
        T ⁻¹' (Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ A)) := by
      ext z
      simp only [Set.mem_smul, Set.mem_inter_iff, Metric.mem_sphere, dist_zero_right,
        Set.mem_preimage]
      constructor
      · rintro ⟨a, ha, y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨a, ha, T y, ⟨by rw [T.norm_map]; exact hy1, hy2⟩, by rw [map_smul]⟩
      · rintro ⟨a, ha, y, ⟨hy1, hy2⟩, hz⟩
        refine ⟨a, ha, T.symm y, ⟨by rw [T.symm.norm_map]; exact hy1, by simpa using hy2⟩, ?_⟩
        apply T.injective
        rw [map_smul, LinearIsometryEquiv.apply_symm_apply, hz]
    rw [hset]
    exact (T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding _)
  simp only [sphereUnif]
  rw [Measure.map_smul _ hT.aemeasurable, key]

lemma toSphere_univ_ne (hK : 1 ≤ K) :
    (volume : Measure (EuclideanSpace ℝ (Fin K))).toSphere univ ≠ 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin K)) := by
    have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    infer_instance
  intro h
  exact Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.1 h)

lemma sphereUnif_prob (hK : 1 ≤ K) : IsProbabilityMeasure (sphereUnif K) := by
  constructor
  simp only [sphereUnif, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  exact ENNReal.inv_mul_cancel (toSphere_univ_ne hK) (measure_ne_top _ _)

instance sphereUnif_finite : IsFiniteMeasure (sphereUnif K) := by
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h
    have : (volume : Measure (EuclideanSpace ℝ (Fin 0))).toSphere = 0 :=
      (Measure.toSphere_eq_zero_iff_finrank _).2 (by simp)
    simp only [sphereUnif, this, Measure.map_zero, smul_zero]
    infer_instance
  · have := sphereUnif_prob h; infer_instance

lemma sphereUnif_ae_norm : ∀ᵐ θ ∂(sphereUnif K), ‖θ‖ = 1 := by
  simp only [sphereUnif]
  refine Measure.ae_smul_measure ?_ _
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun measurable_norm measurable_const)).2 (ae_of_all _ fun θ => by simp)

lemma integrable_inner_sq (v : EuclideanSpace ℝ (Fin K)) :
    Integrable (fun θ => ⟪v, θ⟫_ℝ ^ 2) (sphereUnif K) := by
  refine Integrable.of_bound (by fun_prop) (‖v‖ ^ 2) (sphereUnif_ae_norm.mono fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have := abs_real_inner_le_norm v θ
  rw [hθ, mul_one] at this
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma sphere_moment_isometry (T : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K))
    (v : EuclideanSpace ℝ (Fin K)) :
    ∫ θ, ⟪T v, θ⟫_ℝ ^ 2 ∂(sphereUnif K) = ∫ θ, ⟪v, θ⟫_ℝ ^ 2 ∂(sphereUnif K) := by
  conv_lhs => rw [← sphereUnif_map_isometry T]
  rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [LinearIsometryEquiv.inner_map_map]

lemma sphere_moment_unit {v w : EuclideanSpace ℝ (Fin K)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∫ θ, ⟪v, θ⟫_ℝ ^ 2 ∂(sphereUnif K) = ∫ θ, ⟪w, θ⟫_ℝ ^ 2 ∂(sphereUnif K) := by
  have h := Submodule.reflection_sub (hv.trans hw.symm)
  rw [← sphere_moment_isometry (Submodule.reflection (ℝ ∙ (v - w))ᗮ) v, h]

lemma sphere_second_moment (hK : 1 ≤ K) (v : EuclideanSpace ℝ (Fin K)) :
    ∫ θ, ⟪v, θ⟫_ℝ ^ 2 ∂(sphereUnif K) = ‖v‖ ^ 2 / K := by
  have := sphereUnif_prob hK
  set e0 : EuclideanSpace ℝ (Fin K) := EuclideanSpace.single ⟨0, hK⟩ 1 with he0
  have hunit : ∀ k : Fin K, ‖(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin K))‖ = 1 := by
    intro k; simp
  have hsum : ∑ k : Fin K, ∫ θ, ⟪(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin K)), θ⟫_ℝ ^ 2
      ∂(sphereUnif K) = 1 := by
    rw [← integral_finset_sum _ fun k _ => integrable_inner_sq _]
    have : ∀ᵐ θ ∂(sphereUnif K), ∑ k : Fin K,
        ⟪(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin K)), θ⟫_ℝ ^ 2 = 1 := by
      filter_upwards [sphereUnif_ae_norm] with θ hθ
      simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
      rw [← EuclideanSpace.real_norm_sq_eq, hθ, one_pow]
    rw [integral_congr_ae this]
    simp
  have hall : ∀ k : Fin K, ∫ θ, ⟪(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin K)), θ⟫_ℝ ^ 2
      ∂(sphereUnif K) = ∫ θ, ⟪e0, θ⟫_ℝ ^ 2 ∂(sphereUnif K) :=
    fun k => sphere_moment_unit (hunit k) (hunit _)
  simp only [hall, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have g0 : ∫ θ, ⟪e0, θ⟫_ℝ ^ 2 ∂(sphereUnif K) = 1 / K := by
    field_simp; linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  set w := ‖v‖⁻¹ • v with hw
  have hwn : ‖w‖ = 1 := by rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
  have hvw : v = ‖v‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have : ∀ θ, ⟪v, θ⟫_ℝ ^ 2 = ‖v‖ ^ 2 * ⟪w, θ⟫_ℝ ^ 2 := fun θ => by
    conv_lhs => rw [hvw]
    rw [real_inner_smul_left, mul_pow]
  simp_rw [this]
  rw [integral_const_mul, sphere_moment_unit hwn (hunit ⟨0, hK⟩), ← he0, g0]
  field_simp

/-! ### The radius -/

instance unifRadius_prob : IsProbabilityMeasure unifRadius :=
  ⟨by simp [unifRadius]⟩

lemma radius_sq : ∫ r, r ^ 2 ∂unifRadius = 1 / 3 := by
  simp only [unifRadius]
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  norm_num

lemma integrable_radius_sq : Integrable (fun r : ℝ => r ^ 2) unifRadius := by
  simp only [unifRadius]
  exact (continuous_pow 2).integrableOn_Ioc

/-! ### The naive law -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma inner_embed (e : ℕ → H) (z : EuclideanSpace ℝ (Fin K)) (h : H) :
    ⟪embed e K z, h⟫_ℝ = ⟪z, proj e K h⟫_ℝ := by
  simp only [embed, proj, sum_inner, real_inner_smul_left, PiLp.inner_apply, PiLp.toLp_apply,
    RCLike.inner_apply, conj_trivial]
  refine sum_congr rfl fun k _ => by ring

lemma continuous_embed (e : ℕ → H) : Continuous (embed e K) := by
  unfold embed
  fun_prop

lemma measurable_naiveMap (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) :
    Measurable fun p : ℝ × EuclideanSpace ℝ (Fin K) => L.symm (p.1 • p.2) := by
  fun_prop

lemma naive_inner_eq (e : ℕ → H) (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (h : H)
    (p : ℝ × EuclideanSpace ℝ (Fin K)) :
    ⟪embed e K (L.symm (p.1 • p.2)), h⟫_ℝ ^ 2 =
      p.1 ^ 2 * ⟪ContinuousLinearMap.adjoint (L.symm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
        (proj e K h), p.2⟫_ℝ ^ 2 := by
  rw [inner_embed, show L.symm (p.1 • p.2) =
      (L.symm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) (p.1 • p.2) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, real_inner_smul_left, mul_pow, real_inner_comm]

theorem naive_second_moment : Claims.naive_second_moment := by
  intro H _ _ e K L h hK
  have := sphereUnif_prob hK
  have hcont : Continuous fun u : EuclideanSpace ℝ (Fin K) => ⟪embed e K u, h⟫_ℝ ^ 2 :=
    ((continuous_embed e).inner continuous_const).pow 2
  constructor
  · rw [naiveLaw, integrable_map_measure hcont.aestronglyMeasurable
      (measurable_naiveMap L).aemeasurable]
    simp only [Function.comp_def, naive_inner_eq]
    exact integrable_radius_sq.mul_prod (integrable_inner_sq _)
  · rw [naiveLaw, integral_map (measurable_naiveMap L).aemeasurable hcont.aestronglyMeasurable]
    simp only [naive_inner_eq]
    have hp := integral_prod_mul (μ := unifRadius) (ν := sphereUnif K) (fun r : ℝ => r ^ 2)
      (fun θ => ⟪ContinuousLinearMap.adjoint
        (L.symm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) (proj e K h), θ⟫_ℝ ^ 2)
    rw [hp, radius_sq, sphere_second_moment hK]
    field_simp

/-! ### The law, its radius, and `M_K = I` -/

/-- The linear isometry `L' ∘ L⁻¹` when `‖L v‖ = ‖L' v‖`. -/
def isoOfNorm (L L' : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (h : ∀ v, ‖L v‖ = ‖L' v‖) :
    EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K) :=
  { (L.symm.trans L').toLinearEquiv with
    norm_map' := fun w => by
      change ‖L' (L.symm w)‖ = ‖w‖
      rw [← h, ContinuousLinearEquiv.apply_symm_apply] }

theorem naive_law_indep : Claims.naive_law_indep := by
  intro K L L' h
  set O := isoOfNorm L L' h with hO
  have hsymm : ∀ x, L'.symm x = L.symm (O.symm x) := by
    intro x
    change L'.symm x = L.symm (L (L'.symm x))
    simp
  have hOm : Measurable O.symm := O.symm.continuous.measurable
  have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin K) => L'.symm (p.1 • p.2)) =
      (fun p : ℝ × EuclideanSpace ℝ (Fin K) => L.symm (p.1 • p.2)) ∘ Prod.map id O.symm := by
    funext p
    simp [hsymm, map_smul]
  rw [naiveLaw, naiveLaw, hfun, ← Measure.map_map (measurable_naiveMap L) (measurable_id.prodMap hOm),
    ← Measure.map_prod_map _ _ measurable_id hOm, Measure.map_id, sphereUnif_map_isometry]

lemma ae_prod_fst_mem : ∀ᵐ p ∂(unifRadius.prod (sphereUnif K)), p.1 ∈ Ioc (0 : ℝ) 1 :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)

lemma ae_prod_snd_norm : ∀ᵐ p ∂(unifRadius.prod (sphereUnif K)), ‖p.2‖ = 1 :=
  Measure.quasiMeasurePreserving_snd.ae sphereUnif_ae_norm

theorem naive_radial : Claims.naive_radial := by
  intro K L hK
  have := sphereUnif_prob hK
  have hm : Measurable fun u : EuclideanSpace ℝ (Fin K) => ‖L u‖ := by fun_prop
  have hmap : (naiveLaw L).map (fun u => ‖L u‖) = unifRadius := by
    rw [naiveLaw, Measure.map_map hm (measurable_naiveMap L)]
    have hae : (fun u => ‖L u‖) ∘ (fun p : ℝ × EuclideanSpace ℝ (Fin K) => L.symm (p.1 • p.2)) =ᵐ[
        unifRadius.prod (sphereUnif K)] Prod.fst := by
      filter_upwards [ae_prod_fst_mem, ae_prod_snd_norm] with p h1 h2
      simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, norm_smul, h2, mul_one,
        Real.norm_eq_abs, abs_of_pos h1.1]
    rw [Measure.map_congr hae, Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨hmap, fun τ h0 h1 => ?_⟩
  have : naiveLaw L {u | ‖L u‖ ≤ τ} = (naiveLaw L).map (fun u => ‖L u‖) (Iic τ) := by
    rw [Measure.map_apply hm measurableSet_Iic]; rfl
  rw [this, hmap, unifRadius, Measure.restrict_apply measurableSet_Iic]
  have : Iic τ ∩ Ioc (0 : ℝ) 1 = Ioc 0 τ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]; constructor
    · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', h.trans h1⟩
  rw [this, Real.volume_Ioc, sub_zero]

theorem naive_identity_I : Claims.naive_identity_I := by
  intro H _ _ e K h hK
  have hm := naive_second_moment H e K (ContinuousLinearEquiv.refl ℝ _) h hK
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at hm
  refine ⟨?_, hm⟩
  simp [naiveLaw]

/-! ### Spectral bounds -/

lemma adjoint_inv_bound (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2) (p : EuclideanSpace ℝ (Fin K)) :
    ‖ContinuousLinearMap.adjoint (L.symm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) p‖ ^ 2
      ≤ ‖p‖ ^ 2 / c := by
  set A : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) := L.symm.toContinuousLinearMap
    with hA
  set q := ContinuousLinearMap.adjoint A p
  have h1 : ‖q‖ ^ 2 ≤ ‖A q‖ * ‖p‖ := by
    rw [← real_inner_self_eq_norm_sq]
    calc ⟪q, q⟫_ℝ = ⟪A q, p⟫_ℝ := ContinuousLinearMap.adjoint_inner_right A q p
      _ ≤ ‖A q‖ * ‖p‖ := real_inner_le_norm _ _
  have h2 : c * ‖A q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    have := hL (A q)
    simpa [hA] using this
  rw [le_div_iff₀ hc]
  have hp := norm_nonneg p
  have hq := norm_nonneg q
  have hAq := norm_nonneg (A q)
  -- `(c‖q‖²)² ≤ c²‖Aq‖²‖p‖² ≤ c‖q‖²‖p‖²`
  by_cases hq0 : ‖q‖ = 0
  · rw [hq0]; nlinarith [sq_nonneg ‖p‖]
  have hqpos : 0 < ‖q‖ := lt_of_le_of_ne hq (Ne.symm hq0)
  have h3 : (‖q‖ ^ 2) ^ 2 ≤ ‖A q‖ ^ 2 * ‖p‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have h4 : c * (‖q‖ ^ 2) ^ 2 ≤ ‖q‖ ^ 2 * ‖p‖ ^ 2 := by nlinarith
  have h5 : 0 < ‖q‖ ^ 2 := by positivity
  nlinarith

lemma proj_norm_le (e : ℕ → H) (he : Orthonormal ℝ e) (h : H) : ‖proj e K h‖ ≤ ‖h‖ := by
  have hsq : ‖proj e K h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have := he.sum_inner_products_le (s := Finset.range K) (x := h)
    simp only [Real.norm_eq_abs, sq_abs] at this
    simp only [proj, PiLp.toLp_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => ⟪e k, h⟫_ℝ ^ 2)]
    exact this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

theorem naive_second_moment_le : Claims.naive_second_moment_le := by
  intro H _ _ e K L c h hK he hc hL
  rw [(naive_second_moment H e K L h hK).2]
  refine ⟨?_, proj_norm_le e he h⟩
  have := adjoint_inv_bound L hc hL (proj e K h)
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hc] at this
  nlinarith

theorem naive_second_moment_tendsto : Claims.naive_second_moment_tendsto := by
  intro H _ _ e L c h he hc hL
  have hlim : Tendsto (fun K : ℕ => ‖h‖ ^ 2 / (3 * c) / K) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun K => integral_nonneg fun u => by positivity
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have h1 := (naive_second_moment_le H e K (L K) c h hK he hc (hL K)).1
    have h2 := proj_norm_le (K := K) e he h
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    refine h1.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    exact mul_le_mul_of_nonneg_right this (by positivity)

/-! ### Convergence of the embedded laws -/

lemma naiveLaw_prob (hK : 1 ≤ K) (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) :
    IsProbabilityMeasure (naiveLaw L) := by
  have := sphereUnif_prob hK
  unfold naiveLaw; infer_instance

lemma norm_embed (e : ℕ → H) (he : Orthonormal ℝ e) (z : EuclideanSpace ℝ (Fin K)) :
    ‖embed e K z‖ = ‖z‖ := by
  have ho : Orthonormal ℝ (fun k : Fin K => e k) := he.comp _ (fun a b h => Fin.ext h)
  have h1 : ‖embed e K z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, embed, ho.inner_sum, EuclideanSpace.real_norm_sq_eq]
    simp [sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

lemma integral_embLaw [MeasurableSpace H] [BorelSpace H] (e : ℕ → H)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) {f : H → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(embLaw e L) = ∫ u, f (embed e K u) ∂(naiveLaw L) := by
  rw [embLaw, integral_map (continuous_embed e).measurable.aemeasurable hf.aestronglyMeasurable]

lemma weak_nbhd [CompleteSpace H] (f : H → ℝ)
    (hf : Continuous fun y : WeakSpace ℝ H => f ((toWeakSpace ℝ H).symm y)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (StrongDual ℝ H)) (r : ℝ), 0 < r ∧
      ∀ x : H, (∀ ℓ ∈ s, |ℓ x| < r) → |f x - f 0| < ε := by
  set g := fun y : WeakSpace ℝ H => f ((toWeakSpace ℝ H).symm y) with hg
  have hU : g ⁻¹' Metric.ball (g 0) ε ∈ 𝓝 (0 : WeakSpace ℝ H) :=
    hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  obtain ⟨V, hV, hVU⟩ := (LinearMap.hasBasis_weakBilin (topDualPairing ℝ H).flip).mem_iff.1 hU
  simp only [SeminormFamily.basisSets, Set.mem_iUnion, Set.mem_singleton_iff] at hV
  obtain ⟨s, r, hr, rfl⟩ := hV
  refine ⟨s, r, hr, fun x hx => ?_⟩
  have hmem : (s.sup (topDualPairing ℝ H).flip.toSeminormFamily) (toWeakSpace ℝ H x) < r := by
    refine Seminorm.finset_sup_apply_lt hr fun ℓ hℓ => ?_
    change ‖ℓ x‖ < r
    rw [Real.norm_eq_abs]; exact hx ℓ hℓ
  have := Metric.mem_ball.1 (Set.mem_preimage.1 (hVU ((Seminorm.mem_ball_zero _).2 hmem)))
  simpa [hg, Real.dist_eq] using this

lemma cheb_naive (hK : 1 ≤ K) (e : ℕ → H) (he : Orthonormal ℝ e)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2) (h' : H) {r : ℝ} (hr : 0 < r) :
    (naiveLaw L).real {u | r ^ 2 ≤ ⟪embed e K u, h'⟫_ℝ ^ 2} ≤ ‖h'‖ ^ 2 / (3 * c * K) / r ^ 2 := by
  have hint := (naive_second_moment H e K L h' hK).1
  have h1 := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun u => by positivity) hint (r ^ 2)
  have h2 := (naive_second_moment_le H e K L c h' hK he hc hL)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2.2 2
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine h1.trans (h2.1.trans ?_)
  exact div_le_div_of_nonneg_right h3 (by positivity)

theorem naive_weak_tendsto : Claims.naive_weak_tendsto := by
  intro H _ _ _ _ _ e L c he hc hL f hf hBd
  obtain ⟨B, hB⟩ := hBd
  have hfc : Continuous f := by
    have := hf.comp (toWeakSpaceCLM ℝ H).continuous
    exact this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, r, hr, hsr⟩ := weak_nbhd f hf (half_pos hε)
  set hs : StrongDual ℝ H → H := fun ℓ => (InnerProductSpace.toDual ℝ H).symm ℓ with hhs
  have hℓ : ∀ ℓ x, ℓ x = ⟪x, hs ℓ⟫_ℝ := fun ℓ x => by
    rw [real_inner_comm, hhs, InnerProductSpace.toDual_symm_apply]
  set M := 2 * B * ∑ ℓ ∈ s, ‖hs ℓ‖ ^ 2 / (3 * c) / r ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (ε / 2))
  refine ⟨max N 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := le_of_max_le_right hK
  have hKN : (N : ℝ) ≤ K := by exact_mod_cast le_of_max_le_left hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
  have := naiveLaw_prob hK1 (L K)
  rw [Real.dist_eq, integral_embLaw e (L K) hfc]
  set μ := naiveLaw (L K) with hμ
  set g := fun u => f (embed e K u) with hgdef
  have hgc : Continuous g := hfc.comp (continuous_embed e)
  have hgint : Integrable g μ :=
    Integrable.of_bound hgc.aestronglyMeasurable B (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hB _)
  set bad : StrongDual ℝ H → Set (EuclideanSpace ℝ (Fin K)) :=
    fun ℓ => {u | r ^ 2 ≤ ⟪embed e K u, hs ℓ⟫_ℝ ^ 2} with hbad
  have hbadm : ∀ ℓ, MeasurableSet (bad ℓ) := fun ℓ =>
    measurableSet_le measurable_const (((continuous_embed e).inner continuous_const).pow 2).measurable
  have hpt : ∀ u, |g u - f 0| ≤ ε / 2 + 2 * B * ∑ ℓ ∈ s, (bad ℓ).indicator 1 u := by
    intro u
    have hsum0 : 0 ≤ ∑ ℓ ∈ s, (bad ℓ).indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u :=
      sum_nonneg fun ℓ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases hgood : ∀ ℓ ∈ s, |ℓ (embed e K u)| < r
    · exact (hsr _ hgood).le.trans (le_add_of_nonneg_right (by positivity))
    · push_neg at hgood
      obtain ⟨ℓ, hℓs, hℓr⟩ := hgood
      have hin : u ∈ bad ℓ := by
        simp only [hbad, Set.mem_setOf_eq]
        rw [← hℓ]
        calc r ^ 2 ≤ |ℓ (embed e K u)| ^ 2 := pow_le_pow_left₀ hr.le hℓr 2
          _ = (ℓ (embed e K u)) ^ 2 := sq_abs _
      have h1 : (1 : ℝ) ≤ ∑ ℓ ∈ s, (bad ℓ).indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u := by
        have := single_le_sum (f := fun ℓ => (bad ℓ).indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ) u)
          (fun ℓ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hℓs
        simpa [Set.indicator_of_mem hin] using this
      have h2 : |g u - f 0| ≤ 2 * B := by
        have := abs_sub (g u) (f 0)
        linarith [hB (embed e K u), hB 0]
      nlinarith
  have hbadint : ∀ ℓ, Integrable ((bad ℓ).indicator (1 : EuclideanSpace ℝ (Fin K) → ℝ)) μ :=
    fun ℓ => (integrable_const (1 : ℝ)).indicator (hbadm ℓ)
  have hbound_int : Integrable (fun u => ε / 2 + 2 * B * ∑ ℓ ∈ s, (bad ℓ).indicator 1 u) μ :=
    (integrable_const _).add ((integrable_finset_sum _ fun ℓ _ => hbadint ℓ).const_mul _)
  have hcalc : |∫ u, g u ∂μ - f 0| ≤ ε / 2 + 2 * B * ∑ ℓ ∈ s, μ.real (bad ℓ) := by
    have e1 : ∫ u, g u ∂μ - f 0 = ∫ u, (g u - f 0) ∂μ := by
      rw [integral_sub hgint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e1]
    refine (abs_integral_le_integral_abs).trans ((integral_mono (hgint.sub (integrable_const _)).abs
      hbound_int hpt).trans (le_of_eq ?_))
    rw [integral_add (integrable_const _) ((integrable_finset_sum _ fun ℓ _ => hbadint ℓ).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_finset_sum _ fun ℓ _ => hbadint ℓ]
    simp only [integral_indicator_one (hbadm _)]
  have hcheb : ∑ ℓ ∈ s, μ.real (bad ℓ) ≤ ∑ ℓ ∈ s, ‖hs ℓ‖ ^ 2 / (3 * c) / r ^ 2 / K := by
    refine sum_le_sum fun ℓ _ => (cheb_naive hK1 e he (L K) hc (hL K) (hs ℓ) hr).trans (le_of_eq ?_)
    field_simp
  have hMK : 2 * B * ∑ ℓ ∈ s, ‖hs ℓ‖ ^ 2 / (3 * c) / r ^ 2 / K = M / K := by
    rw [hM, ← sum_div, mul_div_assoc]
  have hMlt : M / K < ε / 2 := by
    rw [div_lt_iff₀ hK']
    rw [div_lt_iff₀ (half_pos hε)] at hN
    nlinarith
  calc |∫ u, g u ∂μ - f 0| ≤ ε / 2 + 2 * B * ∑ ℓ ∈ s, μ.real (bad ℓ) := hcalc
    _ ≤ ε / 2 + 2 * B * ∑ ℓ ∈ s, ‖hs ℓ‖ ^ 2 / (3 * c) / r ^ 2 / K := by gcongr
    _ = ε / 2 + M / K := by rw [hMK]
    _ < ε := by linarith

/-! ### The norm topology -/

lemma integral_embLaw_prod [MeasurableSpace H] [BorelSpace H] (e : ℕ → H)
    (L : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) {f : H → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(embLaw e L) =
      ∫ p, f (embed e K (L.symm (p.1 • p.2))) ∂(unifRadius.prod (sphereUnif K)) := by
  rw [integral_embLaw e L hf, naiveLaw]
  exact integral_map (measurable_naiveMap L).aemeasurable
    (hf.comp (continuous_embed e)).aestronglyMeasurable

theorem naive_norm_mass : Claims.naive_norm_mass := by
  intro H _ _ _ _ e K L C a hK he hC hL ha0 ha1
  have := sphereUnif_prob hK
  have hlow : ∀ θ : EuclideanSpace ℝ (Fin K), ‖θ‖ = 1 → 1 / Real.sqrt C ≤ ‖L.symm θ‖ := by
    intro θ hθ
    have h1 := hL (L.symm θ)
    rw [ContinuousLinearEquiv.apply_symm_apply, hθ, one_pow] at h1
    have h2 : 1 / C ≤ ‖L.symm θ‖ ^ 2 := by rw [div_le_iff₀ hC]; linarith
    calc 1 / Real.sqrt C = Real.sqrt (1 / C) := by rw [Real.sqrt_div' _ hC.le, Real.sqrt_one]
      _ ≤ Real.sqrt (‖L.symm θ‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖L.symm θ‖ := Real.sqrt_sq (norm_nonneg _)
  have hmeas : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin K) => embed e K (L.symm (p.1 • p.2)) :=
    (continuous_embed e).measurable.comp (measurable_naiveMap L)
  have hS : MeasurableSet {x : H | a / Real.sqrt C < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  rw [embLaw, naiveLaw, Measure.map_map (continuous_embed e).measurable (measurable_naiveMap L),
    Measure.map_apply (f := embed e K ∘ fun p : ℝ × EuclideanSpace ℝ (Fin K) => L.symm (p.1 • p.2))
      hmeas hS]
  have hsub : (Prod.fst ⁻¹' Ioc a 1 : Set (ℝ × EuclideanSpace ℝ (Fin K))) ≤ᵐ[unifRadius.prod (sphereUnif K)]
      ((fun p : ℝ × EuclideanSpace ℝ (Fin K) => embed e K (L.symm (p.1 • p.2))) ⁻¹'
        {x : H | a / Real.sqrt C < ‖x‖}) := by
    filter_upwards [ae_prod_snd_norm] with p hp hmem
    simp only [Set.mem_preimage, Set.mem_Ioc] at hmem
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply]
    rw [norm_embed e he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (ha0.trans hmem.1)]
    have := hlow p.2 hp
    have hsC := Real.sqrt_pos.2 hC
    calc a / Real.sqrt C < p.1 * (1 / Real.sqrt C) := by
          rw [mul_one_div]; exact div_lt_div_of_pos_right hmem.1 hsC
      _ ≤ p.1 * ‖L.symm p.2‖ := mul_le_mul_of_nonneg_left this (ha0.trans hmem.1).le
  refine le_trans ?_ (measure_mono_ae hsub)
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one, unifRadius,
    Measure.restrict_apply measurableSet_Ioc]
  have : Ioc a 1 ∩ Ioc (0 : ℝ) 1 = Ioc a 1 := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, ha0.trans h.1, h.2⟩
  rw [this, Real.volume_Ioc]

theorem naive_norm_no_weak : Claims.naive_norm_no_weak := by
  intro H _ _ _ _ e L C he hC hL hall
  set f : H → ℝ := fun x => min ‖x‖ 1 with hf
  have hfc : Continuous f := continuous_norm.min continuous_const
  have hfb : ∃ B, ∀ x, |f x| ≤ B := ⟨1, fun x => by
    rw [abs_of_nonneg (le_min (norm_nonneg _) zero_le_one)]; exact min_le_right _ _⟩
  have ht := hall f hfc hfb
  set m := min (1 / 2 / Real.sqrt C) 1 with hm
  have hm0 : 0 < m := lt_min (by have := Real.sqrt_pos.2 hC; positivity) one_pos
  have hlow : ∀ K, 1 ≤ K → m * (1 / 2) ≤ ∫ x, f x ∂(embLaw e (L K)) := by
    intro K hK
    have := naiveLaw_prob hK (L K)
    have : IsProbabilityMeasure (embLaw e (L K)) := by unfold embLaw; infer_instance
    set S := {x : H | 1 / 2 / Real.sqrt C < ‖x‖} with hSdef
    have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
    have hmass := naive_norm_mass H e K (L K) C (1 / 2) hK he hC (hL K) (by norm_num) (by norm_num)
    have hreal : 1 / 2 ≤ (embLaw e (L K)).real S := by
      rw [measureReal_def]
      have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hmass
      norm_num at this ⊢
      exact this
    have hfint : Integrable f (embLaw e (L K)) :=
      Integrable.of_bound hfc.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) zero_le_one)]
        exact min_le_right _ _)
    have hpt : S.indicator (fun _ => m) ≤ f := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact min_le_min (le_of_lt hx) le_rfl
      · rw [Set.indicator_of_notMem hx]; exact le_min (norm_nonneg _) zero_le_one
    have h1 := integral_mono ((integrable_const m).indicator hS) hfint hpt
    rw [integral_indicator_const m hS, smul_eq_mul] at h1
    nlinarith
  have hlim := ge_of_tendsto ht ((eventually_ge_atTop 1).mono fun K hK => hlow K hK)
  simp only [hf, norm_zero, min_eq_left zero_le_one] at hlim
  nlinarith

theorem naive_KI_norm : Claims.naive_KI_norm := by
  intro H _ _ e K L hK he hL r θ hθ
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by exact_mod_cast hK)
  have hsymm : L.symm (r • θ) = (Real.sqrt K)⁻¹ • (r • θ) := by
    apply L.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hL, smul_smul, mul_inv_cancel₀ hsK.ne', one_smul]
  rw [hsymm, norm_embed e he, norm_smul, norm_smul, hθ, mul_one, Real.norm_eq_abs,
    abs_inv, abs_of_pos hsK, Real.norm_eq_abs]
  field_simp

theorem naive_KI_converges : Claims.naive_KI_converges := by
  intro H _ _ _ _ e L he hL
  constructor
  · intro K hK v
    rw [hL, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [sq_nonneg ‖v‖]
  · intro f hfc hBd
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hfc.continuousAt (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ ^ 2)
    refine ⟨max N 1, fun K hK => ?_⟩
    have hK1 : 1 ≤ K := le_of_max_le_right hK
    have hKN : (N : ℝ) ≤ K := by exact_mod_cast le_of_max_le_left hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
    have := sphereUnif_prob hK1
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK'
    have hsmall : 1 / Real.sqrt K < δ := by
      rw [div_lt_iff₀ hsK]
      have h1 : 1 / δ ^ 2 < K := lt_of_lt_of_le hN hKN
      rw [div_lt_iff₀ (by positivity)] at h1
      have h2 : (δ * Real.sqrt K) ^ 2 = δ ^ 2 * K := by rw [mul_pow, Real.sq_sqrt hK'.le]
      have h3 : 1 < (δ * Real.sqrt K) ^ 2 := by rw [h2]; linarith
      by_contra hc
      push_neg at hc
      have := pow_le_one₀ (by positivity) hc (n := 2)
      linarith
    rw [Real.dist_eq, integral_embLaw_prod e (L K) hfc]
    set g := fun p : ℝ × EuclideanSpace ℝ (Fin K) => f (embed e K ((L K).symm (p.1 • p.2))) with hg
    obtain ⟨B, hB⟩ := hBd
    have hgc : Continuous g := hfc.comp ((continuous_embed e).comp
      ((L K).symm.continuous.comp (continuous_fst.smul continuous_snd)))
    have hgint : Integrable g (unifRadius.prod (sphereUnif K)) :=
      Integrable.of_bound hgc.aestronglyMeasurable B (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]; exact hB _)
    have hae : ∀ᵐ p ∂(unifRadius.prod (sphereUnif K)), ‖g p - f 0‖ ≤ ε / 2 := by
      filter_upwards [ae_prod_fst_mem, ae_prod_snd_norm] with p h1 h2
      have hnorm := naive_KI_norm H e K (L K) hK1 he (hL K) p.1 p.2 h2
      have hd : dist (embed e K ((L K).symm (p.1 • p.2))) 0 < δ := by
        rw [dist_zero_right, hnorm, abs_of_pos h1.1]
        calc p.1 / Real.sqrt K ≤ 1 / Real.sqrt K := div_le_div_of_nonneg_right h1.2 hsK.le
          _ < δ := hsmall
      have := hδf hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
    have e1 : ∫ p, g p ∂(unifRadius.prod (sphereUnif K)) - f 0 =
        ∫ p, (g p - f 0) ∂(unifRadius.prod (sphereUnif K)) := by
      rw [integral_sub hgint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e1]
    have := norm_integral_le_of_norm_le_const hae
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    linarith

end StatFormal.OTFD.Wave8b
