import StatFormal.Archive.Gaps1.Statements
import StatFormal.Archive.OTFD.Wave7a.Proofs
import StatFormal.Archive.OTFD.Wave16b.Proofs
import Mathlib.Analysis.Convex.Measure

/-!
# Route: otfd C `lem:full-support-region`(i) and the neural band claims without `hsupp` (untrusted)

* A convex set with nonempty interior has `cl(int A) = cl A` (Mathlib
  `Convex.closure_interior_eq_closure_of_nonempty_interior`); an open `N` meeting `A` therefore meets `int A`, and a
  ball inside `N ∩ int A` centred in `supp μ` (resp. in `O`) has positive mass.
* `μ ≪ Leb`, `μ(A) > 0` and convexity give `int A ≠ ∅`: otherwise `A ⊆ frontier A`, Lebesgue-null
  (`Convex.addHaar_frontier`).
* The neural claims: the frozen Wave 7a / 16b theorems applied with the support condition proved here.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped InnerProductSpace ENNReal

namespace StatFormal.Gaps1

open StatFormal.OTFD.Wave7a (NeuralSetting)

variable {K : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin K)

/-- An open set meeting a convex set with nonempty interior meets it in an open ball contained in the interior. -/
lemma exists_ball_of_convex {A N : Set 𝔼} (hc : Convex ℝ A) (hint : (interior A).Nonempty) (hN : IsOpen N)
    (hNA : (N ∩ A).Nonempty) : ∃ z ∈ interior A, ∃ r, 0 < r ∧ ball z r ⊆ A ∩ N := by
  obtain ⟨a, haN, haA⟩ := hNA
  have hcl : a ∈ closure (interior A) := by
    rw [hc.closure_interior_eq_closure_of_nonempty_interior hint]; exact subset_closure haA
  obtain ⟨z, hzN, hzI⟩ := mem_closure_iff.1 hcl N hN haN
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hN.inter isOpen_interior) z ⟨hzN, hzI⟩
  exact ⟨z, hzI, r, hr, fun y hy => ⟨interior_subset (hball hy).2, (hball hy).1⟩⟩

lemma hsupp_of_convex {μ : Measure 𝔼} {O A : Set 𝔼} (hpos : ∀ x ∈ O, ∀ r, 0 < r → 0 < μ (ball x r))
    (hAO : A ⊆ O) (hc : Convex ℝ A) (hint : (interior A).Nonempty) :
    ∀ N, IsOpen N → (N ∩ A).Nonempty → 0 < μ (A ∩ N) := by
  intro N hN hNA
  obtain ⟨z, hzI, r, hr, hsub⟩ := exists_ball_of_convex hc hint hN hNA
  exact (hpos z (hAO (interior_subset hzI)) r hr).trans_le (measure_mono hsub)

lemma interior_of_ac {μ : Measure 𝔼} {A : Set 𝔼} (hac : μ ≪ volume) (hc : Convex ℝ A) (hA : 0 < μ A) :
    (interior A).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hfr : A ⊆ frontier A := by
    intro a ha; rw [frontier, h, sdiff_empty]; exact subset_closure ha
  have h0 : volume A = 0 := measure_mono_null hfr (hc.addHaar_frontier volume)
  exact (ne_of_gt hA) (hac h0)

theorem region_interior : Claims.region_interior := fun _ _ _ hac hc hA => interior_of_ac hac hc hA

/-- The support condition of the frozen neural claims from convexity and absolute continuity. -/
lemma hsupp_of_setting {𝒯 : Type} {μ : Measure 𝔼} {O : Set 𝔼} {Q : 𝔼 → 𝔼} {A : ℝ → Set 𝔼} {δ : ℝ}
    {e : 𝒯 → 𝔼} {E : ℝ} (hset : NeuralSetting μ O Q A δ e E) (hac : μ ≪ volume)
    (hcv : ∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) :
    ∀ p, 0 < p → p ≤ 1 - δ → ∀ N, IsOpen N → (N ∩ A p).Nonempty → 0 < μ (A p ∩ N) := by
  obtain ⟨_, _, _, hSO, _, hpos, hreg, _⟩ := hset
  intro p hp0 hp1
  obtain ⟨hc, hm⟩ := hcv p hp0 hp1
  exact hsupp_of_convex hpos ((hreg p hp0 hp1).1.trans hSO) hc (interior_of_ac hac hc hm)

theorem full_support_region : Claims.full_support_region := by
  intro K μ A hA hc hint hsupp
  have hpos : ∀ N, IsOpen N → (N ∩ A).Nonempty → 0 < μ (A ∩ N) := by
    intro N hN hNA
    obtain ⟨z, hzI, r, hr, hsub⟩ := exists_ball_of_convex hc hint hN hNA
    have hz : z ∈ μ.support := hsupp (interior_subset hzI)
    exact ((Measure.mem_support_iff_forall z).1 hz _ (ball_mem_nhds z hr)).trans_le (measure_mono hsub)
  have hAm : MeasurableSet A := hA.measurableSet
  refine ⟨?_, hpos, ?_, ?_⟩
  · rw [hc.closure_interior_eq_closure_of_nonempty_interior hint, hA.closure_eq]
  · ext x
    constructor
    · intro hx
      by_contra hxA
      have h1 := (Measure.mem_support_iff_forall x).1 hx _ (hA.isOpen_compl.mem_nhds hxA)
      rw [Measure.restrict_apply hA.isOpen_compl.measurableSet, compl_inter_self, measure_empty] at h1
      exact lt_irrefl _ h1
    · intro hx
      rw [Measure.mem_support_iff_forall]
      intro U hU
      obtain ⟨V, hVU, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hU
      have := hpos V hVo ⟨x, hxV, hx⟩
      rw [inter_comm] at this
      exact this.trans_le ((Measure.le_restrict_apply _ _).trans (measure_mono hVU))
  · intro g hg
    apply le_antisymm
    · refine essSup_le_of_ae_le _ ((ae_restrict_mem hAm).mono fun u hu => ?_)
      exact le_iSup₂ (f := fun u (_ : u ∈ A) => ((g u : ℝ) : EReal)) u hu
    · refine iSup₂_le fun u hu => ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
      have hc2' : c < g u := by exact_mod_cast hc2
      obtain ⟨N, hNo, huN, hN⟩ : ∃ N, IsOpen N ∧ u ∈ N ∧ ∀ w ∈ N ∩ A, c < g w := by
        have h := (hg u hu).eventually (lt_mem_nhds hc2')
        rw [eventually_nhdsWithin_iff, _root_.eventually_nhds_iff] at h
        obtain ⟨N, hN, hNo, huN⟩ := h
        exact ⟨N, hNo, huN, fun w hw => hN w hw.1 hw.2⟩
      have hpos' := hpos N hNo ⟨u, huN, hu⟩
      have hae := ae_le_essSup (μ := μ.restrict A) (f := fun w => ((g w : ℝ) : EReal))
      rw [ae_iff] at hae
      have hsub : N ∩ A ⊆ {w | ¬ ((g w : ℝ) : EReal) ≤ essSup (fun w => ((g w : ℝ) : EReal)) (μ.restrict A)} := by
        intro w hw
        simp only [mem_ofPred_eq, not_le]
        exact hc1.trans (by exact_mod_cast hN w hw)
      have h0 := measure_mono_null hsub hae
      rw [Measure.restrict_apply (hNo.measurableSet.inter hAm), inter_assoc, inter_self, inter_comm] at h0
      exact (ne_of_gt hpos') h0

/-! ### the neural claims -/

theorem neural_band_uniform_convex : Claims.neural_band_uniform_convex := by
  intro K 𝒯 μ O Q A δ mo e E hset hac hcv
  exact StatFormal.OTFD.Wave7a.neural_band_uniform K 𝒯 μ O Q A δ mo e E hset (hsupp_of_setting hset hac hcv)

theorem neural_band_ae_convex : Claims.neural_band_ae_convex := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T hset hac hcv hmono hlim
  exact StatFormal.OTFD.Wave7a.neural_band_ae K 𝒯 μ O Q A δ mo e E Ω P T hset (hsupp_of_setting hset hac hcv)
    hmono hlim

theorem neural_band_prob_convex : Claims.neural_band_prob_convex := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T hset hac hcv hmono hlim
  exact StatFormal.OTFD.Wave7a.neural_band_prob K 𝒯 μ O Q A δ mo e E Ω P T hset (hsupp_of_setting hset hac hcv)
    hmono hlim

theorem neural_band_rate_convex : Claims.neural_band_rate_convex := by
  intro K ρ hK hρ
  obtain ⟨Cst, hC, H⟩ := StatFormal.OTFD.Wave7a.neural_band_rate K ρ hK hρ
  refine ⟨Cst, hC, fun 𝒯 μ O O' Q A δ mo e E L hset hac hcv => ?_⟩
  exact H 𝒯 μ O O' Q A δ mo e E L hset (hsupp_of_setting hset hac hcv)

theorem net_inner_two_sided_convex : Claims.net_inner_two_sided_convex := by
  intro K 𝒯 μ O Q A δ mo e E T N h η w hK hset hmono hac hcv
  exact StatFormal.OTFD.Wave16b.net_inner_two_sided K 𝒯 μ O Q A δ mo e E T N h η w hK hset hmono
    (hsupp_of_setting hset hac hcv)

theorem net_band_neural_two_sided_ae_convex : Claims.net_band_neural_two_sided_ae_convex := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hac hcv
  exact StatFormal.OTFD.Wave16b.net_band_neural_two_sided_ae K 𝒯 μ O Q A δ mo e E Ω P T N h hK hset hmono hTm
    (hsupp_of_setting hset hac hcv)

theorem net_band_neural_two_sided_prob_convex : Claims.net_band_neural_two_sided_prob_convex := by
  intro K 𝒯 μ O Q A δ mo e E Ω _ P T N h hK hset hmono hTm hac hcv
  exact StatFormal.OTFD.Wave16b.net_band_neural_two_sided_prob K 𝒯 μ O Q A δ mo e E Ω P T N h hK hset hmono hTm
    (hsupp_of_setting hset hac hcv)

theorem net_band_neural_rate_convex : Claims.net_band_neural_rate_convex := by
  intro K ρ hK hρ
  obtain ⟨Cst, hC, H⟩ := StatFormal.OTFD.Wave16b.net_band_neural_rate K ρ hK hρ
  refine ⟨Cst, hC, fun 𝒯 μ O O' Q A δ mo e E L hset hmono hac hcv => ?_⟩
  exact H 𝒯 μ O O' Q A δ mo e E L hset hmono (hsupp_of_setting hset hac hcv)

end StatFormal.Gaps1
