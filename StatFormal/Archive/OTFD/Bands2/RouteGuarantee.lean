import StatFormal.Archive.OTFD.Bands2.RouteInner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Matrix

/-!
# Route: `prop:band-guarantee` (containment, minimality, probability chain, trigger, preimage)
-/

noncomputable section
open Finset MeasureTheory Filter Topology

namespace StatFormal.OTFD.Bands2

open StatFormal.OTFD.Bands

variable {K : ℕ}

lemma mem_band_of_mem (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ))
    (mo : T → ℝ) (e : T → Fin K → ℝ) {u : Fin K → ℝ} (hu : u ∈ A) (t : T) :
    edgeLo Q A (mo t) (e t) ≤ ((curve mo e (Q u) t : ℝ) : EReal) ∧
      ((curve mo e (Q u) t : ℝ) : EReal) ≤ edgeUp Q A (mo t) (e t) := by
  unfold curve edgeLo edgeUp
  constructor
  · calc (mo t : EReal) - hsup Q A (-e t) ≤ (mo t : EReal) - (((-e t) ⬝ᵥ Q u : ℝ) : EReal) :=
          EReal.sub_le_sub le_rfl (le_hsup Q hu _)
      _ = ((mo t + e t ⬝ᵥ Q u : ℝ) : EReal) := by
          rw [← EReal.coe_sub, neg_dotProduct, sub_neg_eq_add]
  · rw [EReal.coe_add]
    gcongr
    exact le_hsup Q hu _

lemma curve_inj {T : Type} (mo : T → ℝ) (e : T → Fin K → ℝ)
    (hι : Function.Injective (fun c : Fin K → ℝ => fun t => e t ⬝ᵥ c)) {c c' : Fin K → ℝ}
    (h : curve mo e c = curve mo e c') : c = c' := by
  apply hι
  funext t
  have := congrFun h t
  unfold curve at this
  simpa using this

lemma calCdf_mono (μ : Measure (Fin K → ℝ)) [IsFiniteMeasure μ] (g : (Fin K → ℝ) → ℝ)
    {τ τ' : ℝ} (h : τ ≤ τ') : calCdf μ g τ ≤ calCdf μ g τ' := by
  unfold calCdf
  exact measureReal_mono (fun u (hu : g u ≤ τ) => hu.trans h)

namespace Claims

theorem guarantee_contain_proof : guarantee_contain := by
  intro K T Q A mo e
  rintro _ ⟨u, hu, rfl⟩ t
  exact mem_band_of_mem T Q A mo e hu t

theorem guarantee_minimal_proof : guarantee_minimal := by
  intro K T Q A mo e lo up h t
  have hmem : ∀ u ∈ A, lo t ≤ ((mo t + e t ⬝ᵥ Q u : ℝ) : EReal) ∧
      ((mo t + e t ⬝ᵥ Q u : ℝ) : EReal) ≤ up t := fun u hu => h ⟨u, hu, rfl⟩ t
  constructor
  · unfold edgeUp
    rw [add_comm, ← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))]
    unfold hsup
    refine iSup₂_le fun u hu => ?_
    rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      ← EReal.coe_add, add_comm]
    exact (hmem u hu).2
  · unfold edgeLo
    rw [EReal.le_sub_iff_add_le (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)),
      add_comm, ← EReal.le_sub_iff_add_le (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))]
    unfold hsup
    refine iSup₂_le fun u hu => ?_
    rw [EReal.le_sub_iff_add_le (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))]
    calc (((-e t) ⬝ᵥ Q u : ℝ) : EReal) + lo t = lo t + (((-e t) ⬝ᵥ Q u : ℝ) : EReal) := add_comm _ _
      _ ≤ ((mo t + e t ⬝ᵥ Q u : ℝ) : EReal) + (((-e t) ⬝ᵥ Q u : ℝ) : EReal) := by
          gcongr; exact (hmem u hu).1
      _ = (mo t : EReal) := by rw [← EReal.coe_add, neg_dotProduct]; congr 1; ring

theorem guarantee_prob_proof : guarantee_prob := by
  intro K T Ω _ P _ U Q g 𝒰 τhat mo e hU hQ hg h𝒰 h𝒰1 hι
  set A := {u | u ∈ 𝒰 ∧ g u ≤ τhat} with hAdef
  have hAc : IsCompact A := h𝒰.inter_right (isClosed_le hg continuous_const)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hQA : MeasurableSet (Q ⁻¹' (Q '' A)) :=
    hQ.measurable (hAc.image hQ).isClosed.measurableSet
  have hE1 : {ω | curve mo e (Q (U ω)) ∈ region Q A mo e} = U ⁻¹' (Q ⁻¹' (Q '' A)) := by
    ext ω
    simp only [region, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨u, hu, curve_inj mo e hι h⟩
    · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [h]⟩
  have hBclosed : IsClosed {c : Fin K → ℝ | curve mo e c ∈
      band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t))} := by
    have : {c : Fin K → ℝ | curve mo e c ∈
        band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t))} =
        ⋂ t, ({c | edgeLo Q A (mo t) (e t) ≤ ((mo t + e t ⬝ᵥ c : ℝ) : EReal)} ∩
          {c | ((mo t + e t ⬝ᵥ c : ℝ) : EReal) ≤ edgeUp Q A (mo t) (e t)}) := by
      ext c; simp [band, curve]
    rw [this]
    refine isClosed_iInter fun t => ?_
    have hc : Continuous fun c : Fin K → ℝ => ((mo t + e t ⬝ᵥ c : ℝ) : EReal) :=
      continuous_coe_real_ereal.comp
        (continuous_const.add (Continuous.dotProduct continuous_const continuous_id))
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  have hE2m : MeasurableSet {ω | curve mo e (Q (U ω)) ∈
      band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t))} :=
    hU (hQ.measurable hBclosed.measurableSet)
  have hmapA : P.map U A = P (U ⁻¹' A) := Measure.map_apply hU hAm
  have hsub12 : {ω | curve mo e (Q (U ω)) ∈ region Q A mo e} ⊆ {ω | curve mo e (Q (U ω)) ∈
      band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t))} :=
    fun ω hω => guarantee_contain_proof K T Q A mo e hω
  refine ⟨?_, hE2m, ?_, measure_mono hsub12, ?_, ?_, ?_⟩
  · rw [hE1]; exact hU hQA
  · rw [hmapA, hE1]
    exact measure_mono fun ω hω => ⟨U ω, hω, rfl⟩
  · unfold calCdf
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have h𝒰m : MeasurableSet 𝒰 := h𝒰.isClosed.measurableSet
    have hc : (P.map U) 𝒰ᶜ = 0 := (prob_compl_eq_zero_iff h𝒰m).mpr h𝒰1
    have : A = {u | g u ≤ τhat} ∩ 𝒰 := by ext u; simp [hAdef, and_comm]
    rw [this, measure_inter_conull hc]
  · rw [hE1, Measure.map_apply hU hQA]
  · intro hinj
    rw [hE1, Set.preimage_image_eq _ hinj, hmapA]

theorem guarantee_level_proof : guarantee_level := by
  intro K μ _ g p τhat hg hp hS hle
  set S := {τ | p ≤ calCdf μ g τ} with hSdef
  -- `S` is bounded below: `c(τ) → 0` as `τ → −∞`
  have hbot : ∃ N : ℕ, calCdf μ g (-(N : ℝ)) < p := by
    have hanti : Antitone fun N : ℕ => {u | g u ≤ -(N : ℝ)} := by
      intro N N' hNN u (hu : g u ≤ -(N' : ℝ))
      change g u ≤ -(N : ℝ)
      have : (N : ℝ) ≤ N' := by exact_mod_cast hNN
      linarith
    have hinter : (⋂ N : ℕ, {u | g u ≤ -(N : ℝ)}) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨N, hN⟩ := exists_nat_gt (-g u)
      exact ⟨N, by linarith⟩
    have ht := tendsto_measure_iInter_atTop (μ := μ)
      (fun N => (measurableSet_le hg measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at ht
    have hpos : (0 : ENNReal) < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
    refine ⟨N, ?_⟩
    unfold calCdf
    rw [measureReal_def]
    exact (ENNReal.toReal_lt_of_lt_ofReal hN)
  obtain ⟨N, hN⟩ := hbot
  have hbdd : BddBelow S := by
    refine ⟨-(N : ℝ), fun τ (hτ : p ≤ calCdf μ g τ) => ?_⟩
    by_contra hlt
    push Not at hlt
    have := calCdf_mono μ g hlt.le
    linarith
  set τp := sInf S
  -- right-continuity: `c(τp) ≥ p`
  have hτp : p ≤ calCdf μ g τp := by
    have hk : ∀ k : ℕ, ENNReal.ofReal p ≤ μ {u | g u ≤ τp + 1 / ((k : ℝ) + 1)} := by
      intro k
      have hlt : τp < τp + 1 / ((k : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      obtain ⟨τ, hτS, hτlt⟩ := exists_lt_of_csInf_lt hS hlt
      have h1 : p ≤ calCdf μ g (τp + 1 / ((k : ℝ) + 1)) :=
        (show p ≤ calCdf μ g τ from hτS).trans (calCdf_mono μ g hτlt.le)
      unfold calCdf at h1
      rw [measureReal_def] at h1
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr h1
    have hanti : Antitone fun k : ℕ => {u | g u ≤ τp + 1 / ((k : ℝ) + 1)} := by
      intro k k' hkk u (hu : g u ≤ τp + 1 / ((k' : ℝ) + 1))
      change g u ≤ τp + 1 / ((k : ℝ) + 1)
      have : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
        linarith
      linarith
    have hinter : (⋂ k : ℕ, {u | g u ≤ τp + 1 / ((k : ℝ) + 1)}) = {u | g u ≤ τp} := by
      ext u
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_contra hgt
        push Not at hgt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
        have := h k
        linarith
      · intro h k
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have ht := tendsto_measure_iInter_atTop (μ := μ)
      (fun k => (measurableSet_le hg measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter] at ht
    have hlim : ENNReal.ofReal p ≤ μ {u | g u ≤ τp} := ge_of_tendsto' ht hk
    unfold calCdf
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hlim
  exact hτp.trans (calCdf_mono μ g hle)

theorem guarantee_trigger_proof : guarantee_trigger := by
  intro K T Q A A' mo e t0 ub lb c hA' hub hlb hout
  have h1 : curve mo e c ∉ region Q A' mo e := by
    rintro ⟨u, hu, hcu⟩
    have hcu' : curve mo e (Q u) = curve mo e c := hcu
    obtain ⟨hlo, hup⟩ := mem_band_of_mem T Q A mo e (hA' hu) t0
    rw [hcu'] at hlo hup
    have hu' : ((curve mo e c t0 : ℝ) : EReal) ≤ ub := hup.trans hub
    have hl' : (lb : EReal) ≤ ((curve mo e c t0 : ℝ) : EReal) := hlb.trans hlo
    rw [EReal.coe_le_coe_iff] at hu' hl'
    rcases hout with h | h <;> linarith
  refine ⟨h1, ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact h1 ⟨u, hu, rfl⟩

theorem guarantee_trigger_raw_proof : guarantee_trigger_raw := by
  intro K T Q A A' mo e t0 ub lb r c x hA' hub hlb hr hout
  refine guarantee_trigger_proof K T Q A A' mo e t0 ub lb c hA' hub hlb ?_
  rw [abs_le] at hr
  rcases hout with h | h
  · left; linarith
  · right; linarith

end Claims

theorem guarantee_contain : Claims.guarantee_contain := Claims.guarantee_contain_proof
theorem guarantee_minimal : Claims.guarantee_minimal := Claims.guarantee_minimal_proof
theorem guarantee_prob : Claims.guarantee_prob := Claims.guarantee_prob_proof
theorem guarantee_level : Claims.guarantee_level := Claims.guarantee_level_proof
theorem guarantee_trigger : Claims.guarantee_trigger := Claims.guarantee_trigger_proof
theorem guarantee_trigger_raw : Claims.guarantee_trigger_raw := Claims.guarantee_trigger_raw_proof

end StatFormal.OTFD.Bands2
