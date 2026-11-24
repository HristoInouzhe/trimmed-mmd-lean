import StatFormal.Archive.OTFD.Wave19a.RouteWhiten
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Route: B `prop:rk-transfer` (i) consequence, (iii), (iv) (untrusted)

(i)–(ii) themselves are the certified `Wave8c.Claims.transfer_push_rank`, `transfer_unique` (identical statements).
* `M`-monotone maps: `T` is `M`-monotone from `α` to `β` iff `M∘T` is a subgradient selection pushing `α` to
  `M#β`; uniqueness then follows from Tau Ceti's Brenier uniqueness (`Wave8c.gradMap_ae_eq`).
* (iii), (iv): the candidate maps are `M`-monotone (`subdiff_affine_scale`, `affine_mem_subdiff` for the symmetric
  PSD `M S_A`); a.e. inverse algebra as in `Wave8c`.
* Optimality: whitening with `L = √M` (`CFC.sqrt`, symmetric) turns `M`-optimality into Euclidean optimality
  (couplings correspond under `L × L`); the whitened map has linear part `N = L S_B S_A⁻¹ L⁻¹ = L⁻¹(M S_B S_A⁻¹)L⁻¹`;
  `Wave8c.symm_of_optimal` (needs an open set in the support: convex support of `μ`) and
  `Wave8c.affine_symm_posdef` (for the converse) close the equivalence.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace StatFormal.OTFD.Wave19a

open StatFormal.OTFD.Wave8c (mvec mnorm IsGradMap IsRankPair quadCost measurable_mvec continuous_mvec mvec_mul
  mvec_add mvec_sub mvec_smul mvec_one mvec_inv_mul mvec_mul_inv inner_mvec mnorm_eq_norm det_L_ne_zero
  gradMap_ae_eq rankPair_ae_FQ subdiff_affine_scale affine_mem_subdiff det_ne_zero_of_posDef memLp_map_affine
  measurable_quadCost symm_of_optimal interior_support_nonempty isGradMap_affine affine_symm_posdef)

section MGrad
variable {K : ℕ}

lemma mgrad_to_grad {M : Matrix (Fin K) (Fin K) ℝ} {α β : Measure (EuclideanSpace ℝ (Fin K))}
    {T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)} (hT : IsMGradMap M α β T) :
    IsGradMap α (β.map (mvec M)) (fun x => mvec M (T x)) := by
  obtain ⟨hTm, hTmap, φ, hφ⟩ := hT
  exact ⟨(measurable_mvec M).comp hTm, by rw [← hTmap, Measure.map_map (measurable_mvec M) hTm]; rfl, φ, hφ⟩

/-- Uniqueness of `M`-monotone maps from an absolutely continuous law (finite second moments). -/
lemma mgrad_unique {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) {α β : Measure (EuclideanSpace ℝ (Fin K))}
    [IsProbabilityMeasure α] (hα : α ≪ volume) (h2α : MemLp id 2 α) (h2β : MemLp id 2 β)
    {T S : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)} (hT : IsMGradMap M α β T)
    (hS : IsMGradMap M α β S) : T =ᵐ[α] S := by
  haveI : IsFiniteMeasure β := by rw [← hT.2.1]; infer_instance
  have h := gradMap_ae_eq (ρ := volume) hα h2α (memLp_map_mvec h2β M) (mgrad_to_grad hT) (mgrad_to_grad hS)
  filter_upwards [h] with x hx
  have := congrArg (mvec M⁻¹) hx
  simpa [mvec_inv_mul (det_ne_zero_of_posDef hM)] using this

lemma det_SA_ne_zero {M SA : Matrix (Fin K) (Fin K) ℝ} (h : (M * SA).PosDef) : SA.det ≠ 0 := by
  have := det_ne_zero_of_posDef h
  rw [det_mul] at this
  exact right_ne_zero_of_mul this

/-- The affine map `u ↦ m + S u` is `M`-monotone when `MS` is symmetric positive semidefinite. -/
lemma isMGradMap_affine {M S : Matrix (Fin K) (Fin K) ℝ} (hMS : (M * S).PosSemidef) (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (m : EuclideanSpace ℝ (Fin K)) :
    IsMGradMap M μ (μ.map fun u => m + mvec S u) (fun u => m + mvec S u) := by
  refine ⟨measurable_const.add (measurable_mvec S), rfl,
    fun z => ((⟪z, mvec (M * S) z⟫ / 2 + ⟪mvec M m, z⟫ : ℝ) : EReal), Eventually.of_forall fun u => ?_⟩
  have := affine_mem_subdiff hMS (mvec M m) u
  rwa [show mvec M (m + mvec S u) = mvec (M * S) u + mvec M m by rw [mvec_add, mvec_mul, add_comm]]

lemma memLp_map_affine' {μ : Measure (EuclideanSpace ℝ (Fin K))} [IsFiniteMeasure μ] (h2 : MemLp id 2 μ)
    (S : Matrix (Fin K) (Fin K) ℝ) (m : EuclideanSpace ℝ (Fin K)) : MemLp id 2 (μ.map fun u => m + mvec S u) := by
  have := memLp_map_affine h2 S m
  rwa [show (fun z => mvec S z + m) = fun u => m + mvec S u by funext u; rw [add_comm]] at this

end MGrad

theorem rk_transfer_rank_functions : Claims.rk_transfer_rank_functions := by
  intro K μ PA PB FA QA FB QB α φ hA hB
  filter_upwards [rankPair_ae_FQ hB hA.1.aemeasurable hA.2.2.2.1] with z hz
  rw [hz]

theorem rk_transfer_scalar_affine : Claims.rk_transfer_scalar_affine := by
  intro K M μ PA _ FA QA QB b c hM hμ h2μ h2PA hc hRP hQA hQB
  haveI : IsProbabilityMeasure PA := by rw [← hQA.2.1]; infer_instance
  set Q1 : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun u => b + c • QA u with hQ1def
  have hQ1 : IsMGradMap M μ (PA.map fun z => b + c • z) Q1 := by
    obtain ⟨hQm, hQmap, φ, hφ⟩ := hQA
    refine ⟨measurable_const.add (hQm.const_smul c), ?_,
      fun x => (c : EReal) * φ x + ((⟪mvec M b, x⟫ : ℝ) : EReal), hφ.mono fun u hu => ?_⟩
    · rw [← hQmap, Measure.map_map (by fun_prop) hQm]; rfl
    · have := subdiff_affine_scale hu hc (mvec M b)
      rwa [show mvec M (Q1 u) = c • mvec M (QA u) + mvec M b by
        simp only [Q1, mvec_add, mvec_smul]; rw [add_comm]]
  have h2P' : MemLp id 2 (PA.map fun z => b + c • z) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    exact (memLp_const b).add (h2PA.const_smul c)
  have hae : QB =ᵐ[μ] Q1 := mgrad_unique hM hμ h2μ h2P' hQB hQ1
  rw [← hRP.2.2.2.1] at hae
  filter_upwards [ae_of_ae_map hRP.1.aemeasurable hae, hRP.2.2.2.2.2] with z h1 h2
  rw [h1]; simp only [Q1, h2]

theorem rk_transfer_affine : Claims.rk_transfer_affine := by
  intro K M SA SB mA mB μ _ FA QA QB hM hMA hMB hμ h2μ hRP hQA hQB
  have hdA := det_SA_ne_zero hMA
  have hQAe : QA =ᵐ[μ] fun u => mA + mvec SA u :=
    mgrad_unique hM hμ h2μ (memLp_map_affine' h2μ SA mA) hQA (isMGradMap_affine hMA.posSemidef μ mA)
  have hQBe : QB =ᵐ[μ] fun u => mB + mvec SB u :=
    mgrad_unique hM hμ h2μ (memLp_map_affine' h2μ SB mB) hQB (isMGradMap_affine hMB.posSemidef μ mB)
  have hFmap := hRP.2.2.2.1
  have h1 : ∀ᵐ z ∂(μ.map fun u => mA + mvec SA u), QA (FA z) = mA + mvec SA (FA z) :=
    ae_of_ae_map hRP.1.aemeasurable (by rw [hFmap]; exact hQAe)
  have h2 : ∀ᵐ z ∂(μ.map fun u => mA + mvec SA u), QB (FA z) = mB + mvec SB (FA z) :=
    ae_of_ae_map hRP.1.aemeasurable (by rw [hFmap]; exact hQBe)
  have hF : FA =ᵐ[μ.map fun u => mA + mvec SA u] fun z => mvec SA⁻¹ (z - mA) := by
    filter_upwards [h1, hRP.2.2.2.2.2] with z hz hQF
    rw [hQF] at hz
    have : mvec SA (FA z) = z - mA := by rw [eq_sub_iff_add_eq, add_comm]; exact hz.symm
    rw [← this, mvec_inv_mul hdA]
  refine ⟨hQAe, hF, ?_⟩
  filter_upwards [h2, hF] with z hz hFz
  rw [hz, hFz, mvec_mul]

/-! ### Optimality -/

section Opt
variable {K : ℕ}

/-- Whitening of optimality: `T` is `M`-optimal iff `L T L⁻¹` is Euclidean-optimal between the whitened laws. -/
lemma opt_whiten {M L : Matrix (Fin K) (Fin K) ℝ} (hd : L.det ≠ 0) (hL : Lᵀ * L = M)
    (α β : Measure (EuclideanSpace ℝ (Fin K))) {T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)}
    (hT : Measurable T) :
    TauCeti.IsKantorovichOptimalTransportMap (mCost M) α β T ↔
      TauCeti.IsKantorovichOptimalTransportMap quadCost (α.map (mvec L)) (β.map (mvec L))
        (fun w => mvec L (T (mvec L⁻¹ w))) := by
  set W := wEquiv hd
  set Tw : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun w => mvec L (T (mvec L⁻¹ w))
  have hTw : Measurable Tw := (measurable_mvec L).comp (hT.comp (measurable_mvec L⁻¹))
  have hc : ∀ x y : EuclideanSpace ℝ (Fin K), quadCost (mvec L x, mvec L y) = mCost M (x, y) := by
    intro x y
    simp only [quadCost, mCost]
    rw [whiten_cost K M L hL x y]
  have hprod : Measurable (Prod.map (mvec L) (mvec L) : _ → EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) :=
    (measurable_mvec L).prodMap (measurable_mvec L)
  have hplan : ∀ π : Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)),
      ∫⁻ z, quadCost z ∂(π.map (Prod.map (mvec L) (mvec L))) = ∫⁻ z, mCost M z ∂π := by
    intro π
    rw [lintegral_map measurable_quadCost hprod]
    exact lintegral_congr fun z => hc z.1 z.2
  have hcost : TauCeti.transportCost quadCost (α.map (mvec L)) (β.map (mvec L)) =
      TauCeti.transportCost (mCost M) α β := by
    unfold TauCeti.transportCost
    apply le_antisymm
    · refine le_iInf₂ fun π hπ => ?_
      have hπ' : TauCeti.IsCoupling (π.map (Prod.map W W)) (α.map W) (β.map W) :=
        (TauCeti.isCoupling_map_prodMap_iff W W).2 hπ
      exact (iInf₂_le (π.map (Prod.map W W)) hπ').trans_eq (hplan π)
    · refine le_iInf₂ fun π' hπ' => ?_
      set π := π'.map (Prod.map W.symm W.symm)
      have hπ : TauCeti.IsCoupling π α β := by
        have := (TauCeti.isCoupling_map_prodMap_iff (π := π') W.symm W.symm).2 hπ'
        rwa [show ⇑W.symm = mvec L⁻¹ from rfl, map_inv_map hd, map_inv_map hd] at this
      have hback : π.map (Prod.map W W) = π' := by
        rw [Measure.map_map (W.measurable.prodMap W.measurable) (W.symm.measurable.prodMap W.symm.measurable),
          Prod.map_comp_map, W.self_comp_symm, Prod.map_id, Measure.map_id]
      calc ⨅ (π : Measure _) (_ : TauCeti.IsCoupling π α β), ∫⁻ z, mCost M z ∂π ≤ ∫⁻ z, mCost M z ∂π :=
            iInf₂_le π hπ
        _ = _ := by rw [← hplan π]; exact congrArg (fun ν => ∫⁻ z, quadCost z ∂ν) hback
  have hmapcost : TauCeti.transportMapCost quadCost (α.map (mvec L)) Tw = TauCeti.transportMapCost (mCost M) α T := by
    rw [TauCeti.transportMapCost_def, TauCeti.transportMapCost_def,
      lintegral_map (f := fun w => quadCost (w, Tw w)) (measurable_quadCost.comp (measurable_id.prodMk hTw))
        (measurable_mvec L)]
    refine lintegral_congr fun x => ?_
    simp only [Tw, mvec_inv_mul hd]
    exact hc x (T x)
  have hlaw : (α.map (mvec L)).map Tw = (α.map T).map (mvec L) := by
    rw [Measure.map_map hTw (measurable_mvec L), Measure.map_map (measurable_mvec L) hT]
    congr 1; funext x; simp [Tw, Function.comp, mvec_inv_mul hd]
  constructor
  · intro h
    refine ⟨⟨hTw.aemeasurable, by rw [hlaw, h.map_eq]⟩, ?_⟩
    rw [hmapcost, hcost]; exact h.transportMapCost_eq
  · intro h
    refine ⟨⟨hT.aemeasurable, ?_⟩, ?_⟩
    · have h1 := h.map_eq
      rw [hlaw] at h1
      have := congrArg (fun ν => ν.map (mvec L⁻¹)) h1
      simpa only [map_inv_map hd] using this
    · rw [← hmapcost, ← hcost]; exact h.transportMapCost_eq

/-- A symmetric square root `L` of `M` (`LᵀL = M`, `Lᵀ = L`). -/
lemma exists_sqrt {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) : ∃ L : Matrix (Fin K) (Fin K) ℝ, Lᵀ * L = M ∧ Lᵀ = L := by
  refine ⟨CFC.sqrt M, ?_, ?_⟩
  · have hT : (CFC.sqrt M)ᵀ = CFC.sqrt M := by
      have := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg M)).isHermitian.eq
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    rw [hT]; exact CFC.sqrt_mul_sqrt_self M (nonneg_iff_posSemidef.2 hM.posSemidef)
  · have := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg M)).isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

end Opt

theorem rk_transfer_affine_optimal_iff : Claims.rk_transfer_affine_optimal_iff := by
  intro K M SA SB mA mB μ _ FA QA QB hM hMA hMB hμ h2μ hconv hRP hQA hQB
  obtain ⟨L, hL, hLs⟩ := exists_sqrt hM
  have hd := det_L_ne_zero hM hL
  have hdA := det_SA_ne_zero hMA
  have hLinv : L⁻¹ * L = 1 := nonsing_inv_mul L (isUnit_iff_ne_zero.2 hd)
  obtain ⟨-, -, hT⟩ := rk_transfer_affine K M SA SB mA mB μ FA QA QB hM hMA hMB hμ h2μ hRP hQA hQB
  set PA := μ.map fun u => mA + mvec SA u with hPA
  set PB := μ.map fun u => mB + mvec SB u with hPB
  set T0 : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun z => mB + mvec (SB * SA⁻¹) (z - mA)
    with hT0def
  have hT0m : Measurable T0 := measurable_const.add ((measurable_mvec _).comp (measurable_id.sub_const _))
  -- the push-forward `T0#P_A = P_B`
  have hpush0 : PA.map T0 = PB :=
    calc PA.map T0 = PA.map (fun z => QB (FA z)) := (Measure.map_congr hT).symm
      _ = (PA.map FA).map QB := (Measure.map_map hQB.1 hRP.1).symm
      _ = PB := by rw [hRP.2.2.2.1, hQB.2.1]
  have hiff1 : TauCeti.IsKantorovichOptimalTransportMap (mCost M) PA PB (fun z => QB (FA z)) ↔
      TauCeti.IsKantorovichOptimalTransportMap (mCost M) PA PB T0 :=
    ⟨fun h => h.congr hT.symm, fun h => h.congr hT⟩
  rw [hiff1, opt_whiten hd hL PA PB hT0m]
  set N := L * SB * SA⁻¹ * L⁻¹ with hNdef
  set e := mvec L mB - mvec (L * SB * SA⁻¹) mA with hedef
  have hTw : (fun w => mvec L (T0 (mvec L⁻¹ w))) = fun w => mvec N w + e := by
    funext w
    simp only [T0, N, e, mvec_add, mvec_sub, mvec_mul, mvec_mul_inv hd]
    abel
  have hpushW : (PA.map (mvec L)).map (fun w => mvec N w + e) = PB.map (mvec L) :=
    calc (PA.map (mvec L)).map (fun w => mvec N w + e)
        = (PA.map (mvec L)).map (fun w => mvec L (T0 (mvec L⁻¹ w))) := by rw [hTw]
      _ = PA.map (fun z => mvec L (T0 (mvec L⁻¹ (mvec L z)))) :=
          Measure.map_map ((measurable_mvec L).comp (hT0m.comp (measurable_mvec L⁻¹))) (measurable_mvec L)
      _ = PA.map (fun z => mvec L (T0 z)) := by simp_rw [mvec_inv_mul hd]
      _ = (PA.map T0).map (mvec L) := (Measure.map_map (measurable_mvec L) hT0m).symm
      _ = PB.map (mvec L) := by rw [hpush0]
  rw [hTw]
  have h2A : MemLp id 2 (PA.map (mvec L)) := memLp_map_mvec (memLp_map_affine' h2μ SA mA) L
  have h2B : MemLp id 2 (PB.map (mvec L)) := memLp_map_mvec (memLp_map_affine' h2μ SB mB) L
  have hNM : M * SB * SA⁻¹ = Lᵀ * N * L := by
    calc M * SB * SA⁻¹ = Lᵀ * L * SB * SA⁻¹ * (L⁻¹ * L) := by rw [hLinv, Matrix.mul_one, hL]
      _ = Lᵀ * N * L := by simp only [N, Matrix.mul_assoc]
  have hN' : N = L⁻¹ * (M * SB * SA⁻¹) * L⁻¹ := by
    rw [← hL, hLs]
    calc N = (L⁻¹ * L) * L * SB * SA⁻¹ * L⁻¹ := by rw [hLinv, Matrix.one_mul]
      _ = L⁻¹ * (L * L * SB * SA⁻¹) * L⁻¹ := by simp only [Matrix.mul_assoc]
  constructor
  · intro hopt
    obtain ⟨u0, hu0⟩ := interior_support_nonempty hμ hconv
    have hdLA : (L * SA).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hd hdA
    set g : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) := fun u => mvec (L * SA) u + mvec L mA with hgdef
    have hc : Continuous g := (continuous_mvec _).add continuous_const
    have hPAg : PA.map (mvec L) = μ.map g :=
      calc PA.map (mvec L) = μ.map (fun u => mvec L (mA + mvec SA u)) :=
            Measure.map_map (measurable_mvec L) (measurable_const.add (measurable_mvec SA))
        _ = μ.map g := by congr 1; funext u; simp only [g, mvec_add, mvec_mul]; rw [add_comm]
    set O := (fun w => mvec (L * SA)⁻¹ (w - mvec L mA)) ⁻¹' interior μ.support with hOdef
    have hOo : IsOpen O :=
      isOpen_interior.preimage ((continuous_mvec _).comp (continuous_id.sub continuous_const))
    have hOne : O.Nonempty := ⟨g u0, by simp [O, g, mvec_inv_mul hdLA, hu0]⟩
    have hOs : O ⊆ (PA.map (mvec L)).support := by
      rw [hPAg]
      intro w hw
      rw [Measure.mem_support_iff_forall]
      intro W' hW'
      obtain ⟨W'', hW''W, hW''o, hwW''⟩ := mem_nhds_iff.1 hW'
      refine lt_of_lt_of_le ?_ (measure_mono hW''W)
      rw [Measure.map_apply hc.measurable hW''o.measurableSet]
      have hgu : g (mvec (L * SA)⁻¹ (w - mvec L mA)) = w := by
        rw [hgdef]; simp only [mvec_mul_inv hdLA, sub_add_cancel]
      refine (Measure.mem_support_iff_forall _).1 (interior_subset hw) _ ((hW''o.preimage hc).mem_nhds ?_)
      simp only [mem_preimage, hgu]; exact hwW''
    have hsym := symm_of_optimal h2A h2B hOo hOne hOs N e hopt
    rw [hNM]
    simp only [transpose_mul, transpose_transpose, hsym, Matrix.mul_assoc]
  · intro hsym
    have hNsym : Nᵀ = N := by
      rw [hN', transpose_mul, transpose_mul, hsym, transpose_nonsing_inv, hLs]
      simp only [Matrix.mul_assoc]
    have hconj : ∀ S : Matrix (Fin K) (Fin K) ℝ, L * S * L⁻¹ = (L⁻¹)ᴴ * (M * S) * L⁻¹ := by
      intro S
      rw [conjTranspose_eq_transpose_of_trivial, transpose_nonsing_inv, hLs, ← hL, hLs]
      calc L * S * L⁻¹ = (L⁻¹ * L) * L * S * L⁻¹ := by rw [hLinv, Matrix.one_mul]
        _ = L⁻¹ * (L * L * S) * L⁻¹ := by simp only [Matrix.mul_assoc]
    have hinj := mulVec_injective_of_det_ne_zero (det_inv_ne_zero hd)
    have hApd : (L * SA * L⁻¹).PosDef := by rw [hconj]; exact hMA.conjTranspose_mul_mul_same hinj
    have hA'pd : (L * SB * L⁻¹).PosDef := by rw [hconj]; exact hMB.conjTranspose_mul_mul_same hinj
    have hAA : (L * SB * L⁻¹) * (L * SA * L⁻¹)⁻¹ = N := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv L (isUnit_iff_ne_zero.2 hd)]
      calc L * SB * L⁻¹ * (L * (SA⁻¹ * L⁻¹)) = L * SB * (L⁻¹ * L) * SA⁻¹ * L⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = N := by rw [hLinv, Matrix.mul_one]
    have hNpd := affine_symm_posdef K (L * SA * L⁻¹) (L * SB * L⁻¹) hApd hA'pd (by rw [hAA]; exact hNsym)
    rw [hAA] at hNpd
    have hg := isGradMap_affine (PA.map (mvec L)) hNpd.posSemidef e
    rw [hpushW] at hg
    exact hg.isOptimal h2A h2B

end StatFormal.OTFD.Wave19a
