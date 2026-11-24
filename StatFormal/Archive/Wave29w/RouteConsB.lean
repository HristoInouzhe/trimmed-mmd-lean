import StatFormal.Archive.Wave29w.Statements
import StatFormal.Archive.Wave29p.RouteConsA
import StatFormal.Archive.Wave29b.RouteConsM
import StatFormal.Archive.OTFD.WaveL9.RouteGrad
import StatFormal.Archive.OTFD.Wave19a.RouteTransfer

/-!
# Route — B `thm:consistency`, general `M_K`, under the printed homeomorphism hypothesis (untrusted)

The Wave 29p `consA_homeo` argument (`M_K = I`) transferred through the change of variables `u ↦ M_K u` on the
reference side (as in Wave 29b `cons_general_M`):

1. `μ_K(int S) = 1` (convex frontier Lebesgue-null), so `P_K(int 𝒴) = 1`; `G' = 1_{int 𝒴} G` pushes `P_K` to `μ_K`.
2. `M_K`-optimality of `Q` (`IsMGradMap`: `M_K Q(u) ∈ ∂φ(u)` `μ_K`-a.e., `φ` finite there) makes
   `{(u, M_K Q u)}` cyclically monotone (telescoping); its swap `{(M_K Q u, u)}` is cyclically monotone (WaveL3
   `cycMon_swap`), and so is its image under `(a, b) ↦ (M_K⁻¹ a, M_K b)` (`M_K` symmetric), i.e. `{(Q u, M_K u)}`; this
   set contains the graph of `M_K G'` over `int 𝒴 ∩ G'⁻¹(good ∩ int S)`, so `M_K G'` is `P_K`-a.e. cyclically
   monotone. `M_K F` is too (`M_K F ∈ ∂ψ` a.e.).
3. Both push `P_K` to `M_K#μ_K`, carried by `B̄(0, L')`; the certified WaveL7 `brenierUniq_of_bdd_target`
   (`P_K ≪ Leb`) gives `M_K F = M_K G'` a.e., so `F = G'` `P_K`-a.e. (`M_K` invertible).
4. `M_K G(y) ∈ ∂ψ(y)` at every `y ∈ int 𝒴` (Wave 29p `subgrad_of_ae`: a.e. points are dense, `M_K G` continuous),
   and `ψ` is differentiable there with gradient `M_K G(y)` (Wave 29p `hasGradientAt_of_subgrad`).
5. The certified Wave 29b `cons_general_M` with the rank map `G'`; on `𝒦 ⊆ int 𝒴`, `G' = G`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29w

open StatFormal.OTFD.WaveL1 (Euc IsCMMapAE CycMon Graph)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open StatFormal.OTFD.Wave8c (mvec measurable_mvec continuous_mvec mvec_inv_mul det_ne_zero_of_posDef inner_mvec_symm
  mvec_sub)

section Lemmas

variable {K : ℕ}

/-- Cyclical monotonicity is preserved by `(a, b) ↦ (M⁻¹ a, M b)` for symmetric positive definite `M`. -/
lemma cycMon_image_mvec {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.PosDef) {Γ : Set (Euc K × Euc K)} (hΓ : CycMon Γ) :
    CycMon ((fun p : Euc K × Euc K => (mvec M⁻¹ p.1, mvec M p.2)) '' Γ) := by
  intro m z hz
  choose w hw hwz using hz
  have hHi : (M⁻¹).IsHermitian := hM.isHermitian.inv
  have hdet := det_ne_zero_of_posDef hM
  have key : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ = ⟪(w i).2, (w (finRotate m i)).1 - (w i).1⟫ := by
    intro i
    rw [← hwz i, ← hwz (finRotate m i)]
    simp only
    rw [← mvec_sub, inner_mvec_symm hHi, mvec_inv_mul hdet]
  simp_rw [key]
  exact hΓ m w hw

/-- An a.e. selection of the (finite-valued) subdifferential of an extended-real function has a cyclically monotone
graph over the good set. -/
lemma cycMon_of_subdiff {φ : Euc K → EReal} {T : Euc K → Euc K} {S : Set (Euc K)}
    (hS : ∀ u ∈ S, T u ∈ TauCeti.subdifferential (innerₗ (Euc K)) φ u) :
    CycMon {z : Euc K × Euc K | z.1 ∈ S ∧ z.2 = T z.1} := by
  refine StatFormal.OTFD.WaveL3.cycMon_mono
    (StatFormal.OTFD.WaveL9.cycMon_subgradGraphDom S (fun u => (φ u).toReal)) ?_
  rintro z ⟨hz1, hz2⟩
  refine ⟨hz1, fun w hw => ?_⟩
  have h := StatFormal.OTFD.Wave8c.subdiff_toReal (hS z.1 hz1) (hS w hw).2.1
  rw [hz2, real_inner_comm]
  exact h

/-- A countable compact exhaustion of an open subset of `ℝ^K`: every compact subset lies in one of its members. -/
lemma exists_exhaustion {Y : Set (Euc K)} (hY : IsOpen Y) :
    ∃ C : ℕ → Set (Euc K), (∀ j, IsCompact (C j) ∧ C j ⊆ Y) ∧
      ∀ 𝒦 : Set (Euc K), IsCompact 𝒦 → 𝒦 ⊆ Y → ∃ j, 𝒦 ⊆ C j := by
  haveI : LocallyCompactSpace Y := hY.locallyCompactSpace
  let E := CompactExhaustion.choice Y
  refine ⟨fun j => ((↑) : Y → Euc K) '' E j, fun j => ⟨(E.isCompact j).image continuous_subtype_val, ?_⟩,
    fun 𝒦 h𝒦 hsub => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · have hs : IsCompact (((↑) : Y → Euc K) ⁻¹' 𝒦) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hsub]
      exact h𝒦
    obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact hs
    exact ⟨j, fun x hx => ⟨⟨x, hsub hx⟩, hj hx, rfl⟩⟩

end Lemmas

theorem consB_homeo : Claims.consB_homeo := by
  classical
  intro K Ω H _ Pr _ Z P μ MK ψ F R L L' ψh γ Fh 𝒦 PiK g cK c' S Q G hMK hind hlaw hPac hμR hML' hμac hSc hS0
    hψc hψL hFm hFmap hFsub hQopt hQc hGc hQmaps hGmaps hGQ hQG h𝒦c h𝒦i hfst hsnd hsupp hψhL hFh hgsub hgsym hgc
    hcK hg1
  have hdet := det_ne_zero_of_posDef hMK
  set Y := interior (P : Measure (Euc K)).support with hY
  set G' : Euc K → Euc K := Y.piecewise G (fun _ => 0) with hG'
  have hG'm : Measurable G' := hGc.measurable_piecewise continuousOn_const isOpen_interior.measurableSet
  have hG'eq : ∀ y ∈ Y, G' y = G y := fun y hy => by simp [hG', hy]
  obtain ⟨hQm, hQmap, φ, hφ⟩ := hQopt
  -- 1. full mass of the interiors; `G'` pushes `P` to `μ`
  have hμS : (μ : Measure (Euc K)) (interior S)ᶜ = 0 := StatFormal.Wave29p.ae_interior_of_convex hμac hSc hS0
  have hPY : (P : Measure (Euc K)) Yᶜ = 0 := by
    rw [← hQmap, Measure.map_apply hQm isOpen_interior.measurableSet.compl]
    refine measure_mono_null (fun u hu => ?_) hμS
    intro huS; exact hu (hQmaps huS)
  have hG'map : (P : Measure (Euc K)).map G' = μ := by
    rw [← hQmap, Measure.map_map hG'm hQm]
    have hae : G' ∘ Q =ᵐ[(μ : Measure (Euc K))] id := by
      filter_upwards [mem_ae_iff.2 hμS] with u hu
      simp only [Function.comp_apply, id]
      rw [hG'eq _ (hQmaps hu), hGQ u hu]
    rw [Measure.map_congr hae, Measure.map_id]
  -- the `M`-images
  have hMm := measurable_mvec MK
  set μ' : Measure (Euc K) := (μ : Measure (Euc K)).map (mvec MK) with hμ'
  have hμ'R : μ' (Metric.closedBall 0 L')ᶜ = 0 := by
    rw [hμ', Measure.map_apply hMm Metric.isClosed_closedBall.measurableSet.compl]
    refine measure_mono_null (fun u hu => ?_) hμR
    intro huR; exact hu (mem_closedBall_zero_iff.2 (hML' u huR))
  have hMG'm : Measurable fun y => mvec MK (G' y) := hMm.comp hG'm
  have hMFm : Measurable fun y => mvec MK (F y) := hMm.comp hFm
  have hMG'map : (P : Measure (Euc K)).map (fun y => mvec MK (G' y)) = μ' := by
    rw [hμ', ← hG'map, Measure.map_map hMm hG'm]; rfl
  have hMFmap : (P : Measure (Euc K)).map (fun y => mvec MK (F y)) = μ' := by
    rw [hμ', ← hFmap, Measure.map_map hMm hFm]; rfl
  -- 2. `M G'` is `P`-a.e. cyclically monotone
  set good : Set (Euc K) := toMeasurable (μ : Measure (Euc K))
    {u | mvec MK (Q u) ∈ TauCeti.subdifferential (innerₗ (Euc K)) φ u}ᶜ
  have hgoodm : MeasurableSet goodᶜ := (measurableSet_toMeasurable _ _).compl
  have hgood0 : (μ : Measure (Euc K)) goodᶜᶜ = 0 := by
    rw [compl_compl, measure_toMeasurable]; exact hφ
  have hgoodS : ∀ u ∈ goodᶜ, mvec MK (Q u) ∈ TauCeti.subdifferential (innerₗ (Euc K)) φ u := fun u hu => by
    by_contra hc
    exact hu (subset_toMeasurable _ _ hc)
  have hΓ0 := cycMon_of_subdiff hgoodS
  have hΓ1 := cycMon_image_mvec hMK (StatFormal.OTFD.WaveL3.cycMon_swap hΓ0)
  have hMG'cm : IsCMMapAE (P : Measure (Euc K)) (fun y => mvec MK (G' y)) := by
    refine ⟨Y ∩ G' ⁻¹' (goodᶜ ∩ interior S), isOpen_interior.measurableSet.inter
      (hG'm (hgoodm.inter isOpen_interior.measurableSet)), ?_, ?_⟩
    · rw [compl_inter]
      refine measure_union_null hPY ?_
      rw [← preimage_compl, ← Measure.map_apply hG'm (hgoodm.inter isOpen_interior.measurableSet).compl, hG'map,
        compl_inter]
      exact measure_union_null hgood0 hμS
    · refine StatFormal.OTFD.WaveL3.cycMon_mono hΓ1 ?_
      rintro z ⟨⟨hz1, hz2, hz3⟩, hz4⟩
      refine ⟨(mvec MK (Q (G z.1)), G z.1), ?_, ?_⟩
      · refine ⟨?_, rfl⟩
        change G z.1 ∈ goodᶜ
        rw [← hG'eq _ hz1]; exact hz2
      · refine Prod.ext ?_ ?_
        · change mvec MK⁻¹ (mvec MK (Q (G z.1))) = z.1
          rw [mvec_inv_mul hdet, hQG _ hz1]
        · change mvec MK (G z.1) = z.2
          rw [hz4]; exact congrArg (mvec MK) (hG'eq _ hz1).symm
  -- `M F` is `P`-a.e. cyclically monotone
  have hMFcm : IsCMMapAE (P : Measure (Euc K)) (fun y => mvec MK (F y)) := by
    set gd : Set (Euc K) := {x | IsSubgrad ψ x (mvec MK (F x))}
    have hgd : (P : Measure (Euc K)) gdᶜ = 0 := hFsub
    refine ⟨(toMeasurable (P : Measure (Euc K)) gdᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact hgd
    · refine StatFormal.OTFD.WaveL3.cycMon_mono (StatFormal.OTFD.WaveL3.cycMon_subgradGraph ψ) ?_
      rintro z ⟨hz1, hz2⟩ y
      have hzg : z.1 ∈ gd := by
        by_contra hc
        exact hz1 (subset_toMeasurable _ gdᶜ hc)
      rw [hz2]; exact hzg y
  -- 3. uniqueness
  have huniq := StatFormal.OTFD.WaveL7.brenierUniq_of_bdd_target
    (StatFormal.OTFD.WaveL3.lipNull_of_ac hPac) hμ'R hMFm hMFmap hMFcm
  have hgr : Graph (P : Measure (Euc K)) (fun y => mvec MK (G' y)) =
      Graph (P : Measure (Euc K)) (fun y => mvec MK (F y)) := by
    have hcpl := StatFormal.OTFD.WaveL3.isCoupling_graph hMG'm hMG'map
    have : IsProbabilityMeasure (Graph (P : Measure (Euc K)) (fun y => mvec MK (G' y))) := by
      unfold Graph; infer_instance
    exact huniq _ inferInstance hcpl.fst_eq hcpl.snd_eq (StatFormal.OTFD.WaveL1.cmConc_graph hMG'm hMG'cm)
  have hMFG' := StatFormal.Wave23d.ae_eq_of_graph_eq hMG'm hMFm hgr
  have hFG' : F =ᵐ[(P : Measure (Euc K))] G' := by
    filter_upwards [hMFG'] with y hy
    have := congrArg (mvec MK⁻¹) hy
    simpa only [mvec_inv_mul hdet] using this.symm
  have hYae : ∀ᵐ y ∂(P : Measure (Euc K)), y ∈ Y := mem_ae_iff.2 hPY
  have hFG : ∀ᵐ y ∂(P : Measure (Euc K)), F y = G y := by
    filter_upwards [hFG', hYae] with y h1 h2
    rw [h1, hG'eq y h2]
  -- 4. subgradients everywhere on `int 𝒴`, differentiability
  have hψcont := StatFormal.Wave29p.continuous_of_lip hψL
  have hMGc : ContinuousOn (fun y => mvec MK (G y)) Y := (continuous_mvec MK).comp_continuousOn hGc
  have hGae : ∀ᵐ y ∂(P : Measure (Euc K)), IsSubgrad ψ y (mvec MK (G y)) := by
    filter_upwards [hFsub, hFG] with y h1 h2
    rwa [← h2]
  have hsubY : ∀ y ∈ Y, IsSubgrad ψ y (mvec MK (G y)) := fun y hy =>
    StatFormal.Wave29p.subgrad_of_ae hψcont isOpen_interior interior_subset hMGc hGae hy
  have hgradY : ∀ y ∈ Y, HasGradientAt ψ (mvec MK (G y)) y := fun y hy =>
    StatFormal.Wave29p.hasGradientAt_of_subgrad isOpen_interior hMGc hsubY hy
  -- the deterministic gauge bound
  have hgL : ∀ a b, |g a - g b| ≤ c' * ‖a - b‖ := by
    intro a b
    have h1 : g a ≤ g (a - b) + g b := by simpa using hgsub (a - b) b
    have h2 : g b ≤ g (b - a) + g a := by simpa using hgsub (b - a) a
    have h3 : g (b - a) = g (a - b) := by rw [← neg_sub, hgsym]
    have h4 := hgc (a - b)
    rw [abs_le]; constructor <;> linarith
  refine ⟨hFG, hgradY, fun n ω x => ?_, ?_⟩
  · have := hgL (G (PiK x)) (Fh n ω (PiK x))
    rw [show (1 - g (Fh n ω (PiK x))) - (1 - g (G (PiK x))) = g (G (PiK x)) - g (Fh n ω (PiK x)) by ring]
    rwa [norm_sub_rev] at this
  -- 5. the certified `cons_general_M` with the rank map `G'`
  have hG'sub : ∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (G' x)) := by
    filter_upwards [hFsub, hFG'] with y h1 h2
    rwa [← h2]
  have hG'grad : ∀ x ∈ 𝒦, HasGradientAt ψ (mvec MK (G' x)) x := fun x hx => by
    rw [hG'eq x (h𝒦i hx)]; exact hgradY x (h𝒦i hx)
  have hg1' : ∀ z ∈ 𝒦, g (G' z) ≤ 1 := fun z hz => by rw [hG'eq z (h𝒦i hz)]; exact hg1 z hz
  have hC := StatFormal.Wave29b.cons_general_M K Ω H Pr Z P μ MK ψ G' R L L' ψh γ Fh 𝒦 PiK g cK c' hMK hind hlaw
    hPac hμR hML' hψc hψL hG'm hG'map hG'sub h𝒦c h𝒦i hG'grad hfst hsnd hsupp hψhL hFh hgsub hgsym hgc hcK hg1'
  filter_upwards [hC.2] with ω h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.congr_right fun x hx => hG'eq x (h𝒦i hx), h2.congr_right fun x hx => ?_,
    h3.congr_right fun x hx => ?_⟩
  · simp only; rw [hG'eq _ (h𝒦i hx)]
  · simp only; rw [hG'eq _ (h𝒦i hx)]

theorem consB_homeo_allK : Claims.consB_homeo_allK := by
  intro K Ω H _ Pr _ Z P μ MK ψ F R L L' ψh γ Fh PiK g cK c' S Q G hMK hind hlaw hPac hμR hML' hμac hSc hS0
    hψc hψL hFm hFmap hFsub hQopt hQc hGc hQmaps hGmaps hGQ hQG hfst hsnd hsupp hψhL hFh hgsub hgsym hgc hcK hg1
  obtain ⟨C, hC, hcov⟩ := exists_exhaustion (K := K) (isOpen_interior (s := (P : Measure (Euc K)).support))
  have h : ∀ j, ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) G atTop (C j) ∧
      TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (G (PiK x))) atTop
        {x | PiK x ∈ C j} ∧
      TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (G (PiK x)))) atTop
        {x | PiK x ∈ C j} := fun j =>
    (consB_homeo K Ω H Pr Z P μ MK ψ F R L L' ψh γ Fh (C j) PiK g cK c' S Q G hMK hind hlaw hPac hμR hML' hμac
      hSc hS0 hψc hψL hFm hFmap hFsub hQopt hQc hGc hQmaps hGmaps hGQ hQG (hC j).1 (hC j).2 hfst hsnd hsupp hψhL
      (fun n ω x hx => hFh n ω x ((hC j).2 hx)) hgsub hgsym hgc hcK (fun z hz => hg1 z ((hC j).2 hz))).2.2.2
  filter_upwards [ae_all_iff.2 h] with ω hω 𝒦 h𝒦 hsub
  obtain ⟨j, hj⟩ := hcov 𝒦 h𝒦 hsub
  obtain ⟨a, b, c⟩ := hω j
  exact ⟨a.mono hj, b.mono fun x hx => hj hx, c.mono fun x hx => hj hx⟩

end StatFormal.Wave29w
