import StatFormal.Archive.Wave29p.Statements
import StatFormal.Archive.WaveP3c.Proofs
import StatFormal.Archive.OTFD.WaveL7.RouteMcCann
import StatFormal.Archive.Wave23d.RouteUniq
import StatFormal.Archive.OTFD.WaveL3.RouteCycMon
import Mathlib.Analysis.Convex.Measure

/-!
# Route — A `thm:consistency` under the printed homeomorphism hypothesis (untrusted)

1. `μ_K(int S) = 1` (the frontier of a convex set is Lebesgue-null), so `P_K(int 𝒴) = 1` (`Q` maps `int S` into
   `int 𝒴`).
2. `G' = 1_{int 𝒴} G` (Borel) pushes `P_K` to `μ_K` (`G ∘ Q = id` on `int S`) and is `P_K`-a.e. cyclically monotone
   (its graph over `int 𝒴 ∩ G'⁻¹(S_Q ∩ int S)` is the swap of the graph of `Q`).
3. Moment-free uniqueness with a bounded target (certified WaveL7 `brenierUniq_of_bdd_target`): `Graph(P, G') =
   Graph(P, F)`, hence `F = G'` `P`-a.e.
4. Closure: `G(y) ∈ ∂ψ(y)` for EVERY `y ∈ int 𝒴` (`P`-a.e. points are dense in `int 𝒴 ⊆ supp P`, `G` continuous,
   `ψ` continuous).
5. Differentiability: `0 ≤ ψ(y') − ψ(y) − ⟨G y, y' − y⟩ ≤ ⟨G y' − G y, y' − y⟩ = o(‖y' − y‖)`.
6. The certified WaveP3c `ghosal_sen_uniform`, `consistency_A_gs` with the rank map `G'`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29p

open StatFormal.OTFD.WaveL1 (Euc IsCMMapAE CycMon Graph)
open StatFormal.OTFD.Wave22a (IsSubgrad)

section Lemmas

variable {K : ℕ}

lemma ae_interior_of_convex {μ : Measure (Euc K)} (hac : μ ≪ volume) {S : Set (Euc K)} (hS : Convex ℝ S)
    (hS0 : μ Sᶜ = 0) : μ (interior S)ᶜ = 0 := by
  have hf : μ (frontier S) = 0 := hac (hS.addHaar_frontier volume)
  refine measure_mono_null (fun u hu => ?_) (measure_union_null hS0 hf)
  by_cases h : u ∈ S
  · exact Or.inr ⟨subset_closure h, hu⟩
  · exact Or.inl h

lemma continuous_of_lip {ψ : Euc K → ℝ} {L : ℝ} (h : ∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) : Continuous ψ := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (h x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))

/-- Closure step: a.e. subgradients along a continuous map are subgradients at every point of an open set inside the
support. -/
lemma subgrad_of_ae {P : Measure (Euc K)} {ψ : Euc K → ℝ} (hψ : Continuous ψ) {G : Euc K → Euc K}
    {V : Set (Euc K)} (hV : IsOpen V) (hVs : V ⊆ P.support) (hG : ContinuousOn G V)
    (hae : ∀ᵐ y ∂P, IsSubgrad ψ y (G y)) {y : Euc K} (hy : y ∈ V) : IsSubgrad ψ y (G y) := by
  intro x
  by_contra hlt
  push Not at hlt
  have hGa : ContinuousAt G y := hG.continuousAt (hV.mem_nhds hy)
  have hφ : ContinuousAt (fun y' => ψ y' + ⟪G y', x - y'⟫) y :=
    hψ.continuousAt.add (hGa.inner (continuousAt_const.sub continuousAt_id))
  have hev : ∀ᶠ y' in 𝓝 y, ψ x < ψ y' + ⟪G y', x - y'⟫ := hφ.eventually (lt_mem_nhds hlt)
  obtain ⟨W, hW, hWsub⟩ : ∃ W ∈ 𝓝 y, ∀ y' ∈ W, ψ x < ψ y' + ⟪G y', x - y'⟫ := ⟨_, hev, fun _ h => h⟩
  have hpos : 0 < P W := (Measure.mem_support_iff_forall y).1 (hVs hy) W hW
  have hbad : P {y' | ¬ IsSubgrad ψ y' (G y')} = 0 := by
    rw [← ae_iff]; exact hae
  have : W ⊆ {y' | ¬ IsSubgrad ψ y' (G y')} := fun y' hy' hsg => by
    have := hsg x; linarith [hWsub y' hy']
  exact hpos.ne' (measure_mono_null this hbad)

/-- Differentiability from subgradients along a map continuous at the point. -/
lemma hasGradientAt_of_subgrad {ψ : Euc K → ℝ} {G : Euc K → Euc K} {V : Set (Euc K)} (hV : IsOpen V)
    (hG : ContinuousOn G V) (hsub : ∀ y ∈ V, IsSubgrad ψ y (G y)) {y : Euc K} (hy : y ∈ V) :
    HasGradientAt ψ (G y) y := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hGa : ContinuousAt G y := hG.continuousAt (hV.mem_nhds hy)
  filter_upwards [hV.mem_nhds hy, hGa.eventually (Metric.closedBall_mem_nhds (G y) hc)] with y' hy'V hy'G
  rw [dist_eq_norm] at hy'G
  simp only [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs]
  have h1 := hsub y hy y'
  have h2 := hsub y' hy'V y
  have h3 : ⟪G y' - G y, y' - y⟫ ≤ ‖G y' - G y‖ * ‖y' - y‖ := real_inner_le_norm _ _
  have e1 : ⟪G y', y - y'⟫ = -⟪G y', y' - y⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪G y' - G y, y' - y⟫ = ⟪G y', y' - y⟫ - ⟪G y, y' - y⟫ := inner_sub_left _ _ _
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hc.le (norm_nonneg (y' - y))]
  · nlinarith [mul_le_mul_of_nonneg_right hy'G (norm_nonneg (y' - y))]

end Lemmas

theorem consA_homeo : Claims.consA_homeo := by
  classical
  intro K Ω H _ Pr _ Z P μ ψ F M L ψh γ Fh 𝒦 PiK Lm S Q G hind hlaw hPac hμM hμac hSc hS0 hψc hψL hFm hFmap
    hFsub hQm hQmap hQcm hQc hGc hQmaps hGmaps hGQ hQG h𝒦c h𝒦i hfst hsnd hsupp hψhL hFh
  set Y := interior (P : Measure (Euc K)).support with hY
  set G' : Euc K → Euc K := Y.piecewise G (fun _ => 0) with hG'
  have hG'm : Measurable G' := hGc.measurable_piecewise continuousOn_const isOpen_interior.measurableSet
  have hG'eq : ∀ y ∈ Y, G' y = G y := fun y hy => by simp [hG', hy]
  -- 1. full mass of the interiors
  have hμS : (μ : Measure (Euc K)) (interior S)ᶜ = 0 := ae_interior_of_convex hμac hSc hS0
  have hPY : (P : Measure (Euc K)) Yᶜ = 0 := by
    rw [← hQmap, Measure.map_apply hQm isOpen_interior.measurableSet.compl]
    refine measure_mono_null (fun u hu => ?_) hμS
    intro huS; exact hu (hQmaps huS)
  -- 2. `G'` pushes `P` to `μ`
  have hG'map : (P : Measure (Euc K)).map G' = μ := by
    rw [← hQmap, Measure.map_map hG'm hQm]
    have hae : G' ∘ Q =ᵐ[(μ : Measure (Euc K))] id := by
      filter_upwards [mem_ae_iff.2 hμS] with u hu
      simp only [Function.comp_apply, id]
      rw [hG'eq _ (hQmaps hu), hGQ u hu]
    rw [Measure.map_congr hae, Measure.map_id]
  -- `G'` is `P`-a.e. cyclically monotone
  have hG'cm : IsCMMapAE (P : Measure (Euc K)) G' := by
    obtain ⟨SQ, hSQm, hSQ0, hcm⟩ := hQcm
    refine ⟨Y ∩ G' ⁻¹' (SQ ∩ interior S), isOpen_interior.measurableSet.inter
      (hG'm (hSQm.inter isOpen_interior.measurableSet)), ?_, ?_⟩
    · rw [compl_inter]
      refine measure_union_null hPY ?_
      rw [← preimage_compl, ← Measure.map_apply hG'm (hSQm.inter isOpen_interior.measurableSet).compl, hG'map,
        compl_inter]
      exact measure_union_null hSQ0 hμS
    · refine StatFormal.OTFD.WaveL3.cycMon_mono (StatFormal.OTFD.WaveL3.cycMon_swap hcm) ?_
      rintro z ⟨⟨hz1, hz2⟩, hz3⟩
      refine ⟨?_, ?_⟩
      · simp only [Prod.fst_swap]; rw [hz3]; exact hz2.1
      · simp only [Prod.snd_swap, Prod.fst_swap]
        rw [hz3, hG'eq _ hz1, hQG _ hz1]
  -- `F` is `P`-a.e. cyclically monotone
  have hFcm : IsCMMapAE (P : Measure (Euc K)) F := by
    set good : Set (Euc K) := {x | IsSubgrad ψ x (F x)}
    have hgood : (P : Measure (Euc K)) goodᶜ = 0 := hFsub
    refine ⟨(toMeasurable (P : Measure (Euc K)) goodᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact hgood
    · refine StatFormal.OTFD.WaveL3.cycMon_mono (StatFormal.OTFD.WaveL3.cycMon_subgradGraph ψ) ?_
      rintro z ⟨hz1, hz2⟩ y
      have hzg : z.1 ∈ good := by
        by_contra hc
        exact hz1 (subset_toMeasurable _ goodᶜ hc)
      rw [hz2]; exact hzg y
  -- 3. uniqueness: `F = G'` a.e.
  have huniq := StatFormal.OTFD.WaveL7.brenierUniq_of_bdd_target
    (StatFormal.OTFD.WaveL3.lipNull_of_ac hPac) hμM hFm hFmap hFcm
  have hgr : Graph (P : Measure (Euc K)) G' = Graph (P : Measure (Euc K)) F := by
    have hcpl := StatFormal.OTFD.WaveL3.isCoupling_graph hG'm hG'map
    have : IsProbabilityMeasure (Graph (P : Measure (Euc K)) G') := by
      unfold Graph; infer_instance
    exact huniq _ inferInstance hcpl.fst_eq hcpl.snd_eq (StatFormal.OTFD.WaveL1.cmConc_graph hG'm hG'cm)
  have hFG' : F =ᵐ[(P : Measure (Euc K))] G' := (StatFormal.Wave23d.ae_eq_of_graph_eq hG'm hFm hgr).symm
  have hYae : ∀ᵐ y ∂(P : Measure (Euc K)), y ∈ Y := mem_ae_iff.2 hPY
  have hFG : ∀ᵐ y ∂(P : Measure (Euc K)), F y = G y := by
    filter_upwards [hFG', hYae] with y h1 h2
    rw [h1, hG'eq y h2]
  -- 4. subgradients everywhere on `int 𝒴`
  have hψcont := continuous_of_lip hψL
  have hGae : ∀ᵐ y ∂(P : Measure (Euc K)), IsSubgrad ψ y (G y) := by
    filter_upwards [hFsub, hFG] with y h1 h2
    rwa [← h2]
  have hsubY : ∀ y ∈ Y, IsSubgrad ψ y (G y) := fun y hy =>
    subgrad_of_ae hψcont isOpen_interior interior_subset hGc hGae hy
  -- 5. differentiability
  have hgradY : ∀ y ∈ Y, HasGradientAt ψ (G y) y := fun y hy =>
    hasGradientAt_of_subgrad isOpen_interior hGc hsubY hy
  refine ⟨hFG, hgradY, ?_⟩
  -- 6. the certified Ghosal–Sen consequences with the rank map `G'`
  have hG'sub : ∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (G' x) := by
    filter_upwards [hFsub, hFG'] with y h1 h2
    rwa [← h2]
  have hG'grad : ∀ x ∈ 𝒦, HasGradientAt ψ (G' x) x := fun x hx => by
    rw [hG'eq x (h𝒦i hx)]; exact hgradY x (h𝒦i hx)
  have hGS := StatFormal.WaveP3c.ghosal_sen_uniform K Ω Pr Z P μ ψ G' M L ψh γ Fh 𝒦 hind hlaw hPac hμM hψc hψL
    hG'm hG'map hG'sub h𝒦c h𝒦i hG'grad hfst hsnd hsupp hψhL hFh
  have hD := StatFormal.WaveP3c.consistency_A_gs K Ω H Pr Z P μ ψ G' M L ψh γ Fh 𝒦 PiK Lm hind hlaw hPac hμM hψc
    hψL hG'm hG'map hG'sub h𝒦c h𝒦i hG'grad hfst hsnd hsupp hψhL hFh
  filter_upwards [hGS, hD] with ω h1 h2
  refine ⟨h1.congr_right fun x hx => hG'eq x (h𝒦i hx), h2.congr_right fun x hx => ?_⟩
  simp only
  rw [hG'eq _ (h𝒦i hx)]

end StatFormal.Wave29p
