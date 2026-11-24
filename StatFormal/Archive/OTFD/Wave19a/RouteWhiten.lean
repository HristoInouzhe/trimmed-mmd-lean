import StatFormal.Archive.OTFD.Wave19a.Statements
import StatFormal.Archive.OTFD.Wave8c.RouteTransfer
import StatFormal.Archive.OTFD.Wave8c.RouteNaive
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Route: B `prop:ext-whitening` (untrusted)

`W = L·` (`LᵀL = M`, `L` invertible) is a linear homeomorphism and a measurable equivalence of `ℝ^K`.
* (a) `‖z − u‖_M = ‖Lz − Lu‖` (`mnorm_eq_norm`); couplings correspond under `W × W` (Tau Ceti
  `isCoupling_map_prodMap_iff`), with equal costs, so `W_{2,M}(α, β) = W₂(W#α, W#β)`; scores and weights coincide,
  so the out-of-sample maps conjugate.
* (b) supports, sublevel regions, absolute continuity, convexity, compactness and interiors transfer through `W`.
* (c) set identities `⟨v, L⁻¹y⟩ = ⟨L⁻ᵀv, y⟩`.
* (d) `My ∈ ∂φ(x) ⇔ Ly ∈ ∂(φ ∘ L⁻¹)(Lx)`; uniqueness of Brenier maps (`Wave8c.gradMap_ae_eq`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal RealInnerProductSpace

namespace StatFormal.OTFD.Wave19a

open StatFormal.OTFD.Wave8c (mvec mnorm IsGradMap measurable_mvec continuous_mvec mvec_mul mvec_add mvec_sub
  mvec_smul mvec_one mvec_inv_mul mvec_mul_inv inner_mvec mnorm_eq_norm det_L_ne_zero gradMap_ae_eq)

section Whiten
variable {K : ℕ}

local notation "ℝK" => EuclideanSpace ℝ (Fin K)

/-- `W = L·` as a measurable equivalence. -/
def wEquiv {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) : ℝK ≃ᵐ ℝK where
  toFun := mvec L
  invFun := mvec L⁻¹
  left_inv := mvec_inv_mul hd
  right_inv := mvec_mul_inv hd
  measurable_toFun := measurable_mvec L
  measurable_invFun := measurable_mvec L⁻¹

lemma wEquiv_apply {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (x : ℝK) : wEquiv hd x = mvec L x := rfl

lemma wEquiv_symm_apply {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (x : ℝK) :
    (wEquiv hd).symm x = mvec L⁻¹ x := rfl

/-- `W = L·` as a homeomorphism. -/
def wHomeo {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) : ℝK ≃ₜ ℝK where
  toEquiv := (wEquiv hd).toEquiv
  continuous_toFun := continuous_mvec L
  continuous_invFun := continuous_mvec L⁻¹

lemma wHomeo_apply {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (x : ℝK) : wHomeo hd x = mvec L x := rfl

lemma inner_mvec_transpose (A : Matrix (Fin K) (Fin K) ℝ) (x y : ℝK) : ⟪mvec A x, y⟫ = ⟪x, mvec Aᵀ y⟫ := by
  rw [real_inner_comm, inner_mvec, inner_mvec, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

lemma inner_whiten {M L : Matrix (Fin K) (Fin K) ℝ} (hL : Lᵀ * L = M) (x y : ℝK) :
    ⟪x, mvec M y⟫ = ⟪mvec L x, mvec L y⟫ := by
  rw [← hL, mvec_mul, ← inner_mvec_transpose]

lemma mem_image_mvec_iff {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) {S : Set ℝK} {z : ℝK} :
    z ∈ mvec L '' S ↔ mvec L⁻¹ z ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩; rwa [mvec_inv_mul hd]
  · intro h; exact ⟨_, h, mvec_mul_inv hd z⟩

lemma mvec_sum (A : Matrix (Fin K) (Fin K) ℝ) {n : ℕ} (f : Fin n → ℝK) :
    mvec A (∑ j, f j) = ∑ j, mvec A (f j) := map_sum (Matrix.toEuclideanLin A) _ _

/-- Supports under a measurable homeomorphism. -/
lemma support_map_equiv {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (ν : Measure ℝK) :
    (ν.map (mvec L)).support = mvec L '' ν.support := by
  have hmap : ∀ U, (ν.map (mvec L)) U = ν (mvec L ⁻¹' U) := fun U => by
    exact (wEquiv hd).map_apply U
  ext z
  rw [mem_image_mvec_iff hd]
  rw [Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
  constructor
  · intro h V hV
    have hU : mvec L⁻¹ ⁻¹' V ∈ 𝓝 z := (continuous_mvec L⁻¹).continuousAt.preimage_mem_nhds hV
    have := h _ hU
    rwa [hmap, ← preimage_comp, show mvec L⁻¹ ∘ mvec L = id from funext (mvec_inv_mul hd), preimage_id]
      at this
  · intro h U hU
    have hV : mvec L ⁻¹' U ∈ 𝓝 (mvec L⁻¹ z) := by
      refine (continuous_mvec L).continuousAt.preimage_mem_nhds ?_
      rwa [mvec_mul_inv hd]
    rw [hmap]; exact h _ hV

lemma ac_map_mvec {A : Matrix (Fin K) (Fin K) ℝ} (hA : A.det ≠ 0) {ν : Measure ℝK} (h : ν ≪ volume) :
    ν.map (mvec A) ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [Measure.map_apply (measurable_mvec A) hs]
  apply h
  change volume ((Matrix.toEuclideanLin A) ⁻¹' s) = 0
  rw [Measure.addHaar_preimage_linearMap volume (by simpa using hA), h0, mul_zero]

lemma memLp_map_mvec {ν : Measure ℝK} [IsFiniteMeasure ν] (h2 : MemLp id 2 ν) (A : Matrix (Fin K) (Fin K) ℝ) :
    MemLp id 2 (ν.map (mvec A)) := by
  have := StatFormal.OTFD.Wave8c.memLp_map_affine h2 A 0
  simpa using this

/-- Subgradients whiten: `My ∈ ∂φ(x) ⇔ Ly ∈ ∂(φ ∘ L⁻¹)(Lx)`. -/
lemma subdiff_whiten {M L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (hL : Lᵀ * L = M) (φ : ℝK → EReal)
    (x y : ℝK) :
    mvec M y ∈ TauCeti.subdifferential (innerₗ ℝK) φ x ↔
      mvec L y ∈ TauCeti.subdifferential (innerₗ ℝK) (fun w => φ (mvec L⁻¹ w)) (mvec L x) := by
  have hid : ∀ a b : ℝK, ⟪a - b, mvec M y⟫ = ⟪mvec L a - mvec L b, mvec L y⟫ := fun a b => by
    rw [inner_whiten hL, mvec_sub]
  simp only [TauCeti.mem_subdifferential_iff, innerₗ_apply_apply, mvec_inv_mul hd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x' => ?_⟩
    have := h3 (mvec L⁻¹ x')
    rwa [hid, mvec_mul_inv hd] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x' => ?_⟩
    have := h3 (mvec L x')
    rwa [mvec_inv_mul hd, ← hid] at this

end Whiten

/-! ### Claims -/

theorem whiten_cost : Claims.whiten_cost := by
  intro K M L hL z u
  rw [mnorm_eq_norm hL, mvec_sub]

theorem whiten_scores : Claims.whiten_scores := by
  intro K n M L hL f Z u j
  unfold oosScore
  have h1 : (1 : Matrix (Fin K) (Fin K) ℝ)ᵀ * 1 = 1 := by simp
  show f j - mnorm M (Z j) ^ 2 + ⟪(2 : ℝ) • mvec M (Z j), u⟫ =
    f j - mnorm 1 (mvec L (Z j)) ^ 2 + ⟪(2 : ℝ) • mvec 1 (mvec L (Z j)), mvec L u⟫
  rw [mnorm_eq_norm hL, mnorm_eq_norm h1, mvec_one, inner_smul_left, inner_smul_left,
    real_inner_comm, inner_whiten hL, real_inner_comm]

theorem whiten_oos : Claims.whiten_oos := by
  intro K n M L hM hL G lam f Z u
  have hd := det_L_ne_zero hM hL
  have h1 : (1 : Matrix (Fin K) (Fin K) ℝ)ᵀ * 1 = 1 := by simp
  have hw : (fun i => (f i - mnorm 1 (mvec L u - mvec L (Z i)) ^ 2) / lam) =
      fun i => (f i - mnorm M (u - Z i) ^ 2) / lam := by
    funext i; rw [mnorm_eq_norm h1, mvec_one, mnorm_eq_norm hL, mvec_sub]
  unfold oosMap
  rw [hw, mvec_sum]
  refine (Finset.sum_congr rfl fun j _ => ?_)
  rw [mvec_smul, mvec_inv_mul hd]

theorem whiten_calib : Claims.whiten_calib := by
  intro K M L hM hL μ g hg τ
  have hd := det_L_ne_zero hM hL
  rw [Measure.map_apply (measurable_mvec L) (show MeasurableSet {w | g (mvec L⁻¹ w) ≤ τ} from
    measurableSet_le (hg.comp (measurable_mvec L⁻¹)) measurable_const)]
  congr 1
  ext u; simp [mvec_inv_mul hd]

theorem whiten_support : Claims.whiten_support := by
  intro K M L hM hL μ g τ
  have hd := det_L_ne_zero hM hL
  refine ⟨support_map_equiv hd μ, ?_⟩
  rw [support_map_equiv hd μ]
  ext w
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hg⟩
    exact ⟨u, ⟨hu, by rwa [mvec_inv_mul hd] at hg⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hg⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, by rwa [mvec_inv_mul hd]⟩

lemma det_inv_ne_zero {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) : (L⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hd

lemma map_inv_map {L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (μ : Measure (EuclideanSpace ℝ (Fin K))) :
    (μ.map (mvec L)).map (mvec L⁻¹) = μ := by
  rw [Measure.map_map (measurable_mvec _) (measurable_mvec _),
    show mvec L⁻¹ ∘ mvec L = id from funext (mvec_inv_mul hd), Measure.map_id]

theorem whiten_ac : Claims.whiten_ac := by
  intro K M L hM hL μ
  have hd := det_L_ne_zero hM hL
  refine ⟨fun h => ?_, fun h => ac_map_mvec hd h⟩
  have := ac_map_mvec (det_inv_ne_zero hd) h
  rwa [map_inv_map hd] at this

theorem whiten_geom : Claims.whiten_geom := by
  intro K M L hM hL A
  have hd := det_L_ne_zero hM hL
  have hback : mvec L⁻¹ '' (mvec L '' A) = A := by
    rw [image_image]; simp [mvec_inv_mul hd]
  refine ⟨⟨fun h => ?_, fun h => h.linear_image (Matrix.toEuclideanLin L)⟩,
    ⟨fun h => ?_, fun h => h.image (continuous_mvec L)⟩, ?_⟩
  · have := h.linear_image (Matrix.toEuclideanLin L⁻¹); rwa [hback] at this
  · have := h.image (continuous_mvec L⁻¹); rwa [hback] at this
  · exact ((wHomeo hd).image_interior A).symm

lemma inner_inv_transpose {L : Matrix (Fin K) (Fin K) ℝ} (v y : EuclideanSpace ℝ (Fin K)) :
    ⟪v, mvec L⁻¹ y⟫ = ⟪mvec L⁻¹ᵀ v, y⟫ := by
  rw [inner_mvec_transpose, transpose_transpose]

theorem whiten_band : Claims.whiten_band := by
  intro K M L hM hL Q Q' hQ
  have hd := det_L_ne_zero hM hL
  refine ⟨fun A v => ?_, fun c0 e u => ?_, fun e z => ?_⟩
  · rw [image_image]
    refine image_congr fun u _ => ?_
    rw [hQ, inner_inv_transpose]
  · rw [hQ, inner_inv_transpose]
  · rw [← inner_inv_transpose, mvec_inv_mul hd]

theorem whiten_gaps : Claims.whiten_gaps := by
  intro K n M L hM hL f Z A j
  rw [image_image]
  refine image_congr fun u _ => ?_
  simp only [whiten_scores K n M L hL f Z u]

theorem whiten_subdiff : Claims.whiten_subdiff := by
  intro K M L hM hL φ u
  have hd := det_L_ne_zero hM hL
  ext y
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro h
    exact ⟨mvec L y, (subdiff_whiten hd hL φ u y).1 h, mvec_inv_mul hd y⟩
  · rintro ⟨w, hw, rfl⟩
    rw [subdiff_whiten hd hL, mvec_mul_inv hd]; exact hw

theorem whiten_population : Claims.whiten_population := by
  intro K M L hM hL μ P _ Q hQ
  have hd := det_L_ne_zero hM hL
  have hemb : MeasurableEmbedding (mvec L) := (wEquiv hd).measurableEmbedding
  obtain ⟨hQm, hQmap, φ, hφ⟩ := hQ
  haveI : IsProbabilityMeasure P := by rw [← hQmap]; infer_instance
  set Qw : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun w => mvec L (Q (mvec L⁻¹ w)) with hQwdef
  have hQwm : Measurable Qw := (measurable_mvec L).comp (hQm.comp (measurable_mvec L⁻¹))
  have hQw : IsGradMap (μ.map (mvec L)) (P.map (mvec L)) Qw := by
    refine ⟨hQwm, ?_, fun w => φ (mvec L⁻¹ w), ?_⟩
    · rw [Measure.map_map hQwm (measurable_mvec L), ← hQmap, Measure.map_map (measurable_mvec L) hQm]
      congr 1; funext u; simp [Qw, Function.comp, mvec_inv_mul hd]
    · rw [hemb.ae_map_iff]
      filter_upwards [hφ] with x hx
      simp only [Qw, mvec_inv_mul hd]
      exact (subdiff_whiten hd hL φ x (Q x)).1 hx
  refine ⟨hQw, fun hμ h2μ h2P Q' hQ' => ?_⟩
  have hae := gradMap_ae_eq (ρ := volume) (ac_map_mvec hd hμ) (memLp_map_mvec h2μ L) (memLp_map_mvec h2P L)
    hQw hQ'
  have hae' : ∀ᵐ x ∂(μ.map (mvec L)), Qw x = Q' x := hae
  rw [hemb.ae_map_iff] at hae'
  filter_upwards [hae'] with u hu
  simp only [Qw, mvec_inv_mul hd] at hu
  rw [← hu, mvec_inv_mul hd]

theorem whiten_essrange : Claims.whiten_essrange := by
  intro K M L hM hL μ Q Q' A hQm hQ'm hA hae
  have hd := det_L_ne_zero hM hL
  have hemb : MeasurableEmbedding (mvec L) := (wEquiv hd).measurableEmbedding
  have hres : (μ.map (mvec L)).restrict (mvec L '' A) = (μ.restrict A).map (mvec L) := by
    rw [hemb.restrict_map, preimage_image_eq _ hemb.injective]
  have hmap : ((μ.map (mvec L)).restrict (mvec L '' A)).map Q' = ((μ.restrict A).map Q).map (mvec L) := by
    rw [hres, Measure.map_map hQ'm (measurable_mvec L), Measure.map_map (measurable_mvec L) hQm]
    refine Measure.map_congr ?_
    filter_upwards [ae_restrict_of_ae hae] with u hu
    simp only [Function.comp, hu, mvec_mul_inv hd]
  have hsupp : (((μ.map (mvec L)).restrict (mvec L '' A)).map Q').support =
      mvec L '' ((μ.restrict A).map Q).support := by
    rw [hmap, support_map_equiv hd]
  refine ⟨hsupp, ?_, fun v => ?_⟩
  · rw [hsupp, ← (Matrix.toEuclideanLin L).image_convexHull]
    exact ((wHomeo hd).image_closure _).symm
  · rw [hsupp, image_image]
    refine image_congr fun y _ => ?_
    rw [← inner_inv_transpose, mvec_inv_mul hd]

theorem whiten_wasserstein : Claims.whiten_wasserstein := by
  intro K M L hM hL α β
  have hd := det_L_ne_zero hM hL
  set W := wEquiv hd
  have hcost : ∀ z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K),
      edist (W z.1) (W z.2) = ENNReal.ofReal (mnorm M (z.1 - z.2)) := fun z => by
    rw [edist_dist, dist_eq_norm, wEquiv_apply, wEquiv_apply, ← mvec_sub, mnorm_eq_norm hL]
  have hmeas : Measurable fun z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => edist z.1 z.2 :=
    continuous_edist.measurable
  have heL : ∀ π : Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)),
      eLpNorm (fun z => edist z.1 z.2) 2 (π.map (Prod.map W W)) =
        eLpNorm (fun z => ENNReal.ofReal (mnorm M (z.1 - z.2))) 2 π := by
    intro π
    rw [eLpNorm_map_measure hmeas.aestronglyMeasurable (W.measurable.prodMap W.measurable).aemeasurable]
    congr 1
    funext z; exact hcost z
  unfold w2M TauCeti.wassersteinEDist
  apply le_antisymm
  · refine le_iInf₂ fun π' hπ' => ?_
    set π := π'.map (Prod.map W.symm W.symm)
    have hπ : TauCeti.IsCoupling π α β := by
      have := (TauCeti.isCoupling_map_prodMap_iff (π := π') W.symm W.symm).2 hπ'
      rwa [show ⇑W.symm = mvec L⁻¹ from rfl, map_inv_map hd, map_inv_map hd] at this
    have hback : π.map (Prod.map W W) = π' := by
      rw [Measure.map_map (W.measurable.prodMap W.measurable) (W.symm.measurable.prodMap W.symm.measurable),
        Prod.map_comp_map, W.self_comp_symm, Prod.map_id, Measure.map_id]
    calc ⨅ (π : Measure _) (_ : TauCeti.IsCoupling π α β), eLpNorm (fun z => ENNReal.ofReal (mnorm M (z.1 - z.2))) 2 π
        ≤ eLpNorm (fun z => ENNReal.ofReal (mnorm M (z.1 - z.2))) 2 π := iInf₂_le π hπ
      _ = _ := by rw [← heL, hback]
  · refine le_iInf₂ fun π hπ => ?_
    have hπ' : TauCeti.IsCoupling (π.map (Prod.map W W)) (α.map W) (β.map W) :=
      (TauCeti.isCoupling_map_prodMap_iff W W).2 hπ
    exact (iInf₂_le (π.map (Prod.map W W)) hπ').trans_eq (heL π)

end StatFormal.OTFD.Wave19a
