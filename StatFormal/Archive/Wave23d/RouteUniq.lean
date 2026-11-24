import StatFormal.Archive.Wave23d.RouteGrad
import StatFormal.Archive.OTFD.WaveL3.RouteHilbert

/-!
# Route — A `lem:app-cm-plans` (iv) uniqueness under a first moment (untrusted)

* `GHSGradUnique` discharged: an `A`-a.e. Gâteaux gradient `T` of a finite convex Lipschitz `f` is `A`-a.e. a
  subgradient selection, so `T` is `A`-a.e. cyclically monotone (`cycMon_subgradGraph`); the certified wave-L3
  `brenier_uniq_H_bdd` makes every cyclically monotone coupling of `(A, B)` equal to `(Id × T)#A`, in particular
  `(Id × T')#A` (carried by the closed subdifferential graph of `f'`); equal graph plans give `T = T'` `A`-a.e.
* `cm_unique_uncond`: the graph plan of (iv) (`cm_graph_exists_thm`) is concentrated on `Γ`, so its map is `A`-a.e.
  cyclically monotone; `brenier_uniq_H_bdd` again.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.WaveL1 (CycMon CMConc Graph LipNull IsCMMapAE BrenierUniq)

section Uniq
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The subdifferential graph of a continuous function is closed. -/
lemma isClosed_subgradGraph {f : H → ℝ} (hf : Continuous f) :
    IsClosed {z : H × H | ∀ x, f z.1 + ⟪z.2, x - z.1⟫ ≤ f x} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun x => isClosed_le ?_ continuous_const
  exact (hf.comp continuous_fst).add (continuous_snd.inner (continuous_const.sub continuous_fst))

/-- A Gâteaux gradient of a convex Lipschitz function is a subgradient. -/
lemma subgrad_of_gatDiff {f : H → ℝ} {L : ℝ} (hf : ConvexOn ℝ univ f) (hL : ∀ x z, |f x - f z| ≤ L * ‖x - z‖)
    {x g : H} (hg : GatDiff f x g) (z : H) : f x + ⟪g, z - x⟫ ≤ f z := by
  have h1 := dd_le_quot hf hL x (z - x) one_pos
  rw [dd_of_gatDiff hf hL hg] at h1
  simp only [quot, one_smul, div_one, add_sub_cancel] at h1
  linarith

variable [MeasurableSpace H] [BorelSpace H]

/-- An `A`-a.e. Gâteaux gradient of a convex Lipschitz function is `A`-a.e. cyclically monotone. -/
lemma isCMMapAE_of_gatDiff {A : Measure H} {f : H → ℝ} {L : ℝ} (hf : ConvexOn ℝ univ f)
    (hL : ∀ x z, |f x - f z| ≤ L * ‖x - z‖) {T : H → H} (hT : ∀ᵐ x ∂A, GatDiff f x (T x)) : IsCMMapAE A T := by
  set good : Set H := {x | GatDiff f x (T x)}
  have hgood : A goodᶜ = 0 := hT
  refine ⟨(toMeasurable A goodᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact hgood
  · refine StatFormal.OTFD.WaveL3.cycMon_mono (StatFormal.OTFD.WaveL3.cycMon_subgradGraph f) ?_
    rintro z ⟨hz1, hz2⟩ y
    have hzg : z.1 ∈ good := by
      by_contra hc
      exact hz1 (subset_toMeasurable A goodᶜ hc)
    rw [hz2]; exact subgrad_of_gatDiff hf hL hzg y

/-- Equal graph plans have `A`-a.e. equal maps. -/
lemma ae_eq_of_graph_eq [SecondCountableTopology H] {A : Measure H} {T T' : H → H} (hT : Measurable T)
    (hT' : Measurable T') (h : Graph A T = Graph A T') : T =ᵐ[A] T' := by
  have hm : Measurable fun x : H => (x, T x) := measurable_id.prodMk hT
  have hm' : Measurable fun x : H => (x, T' x) := measurable_id.prodMk hT'
  have hD : MeasurableSet {p : H × H | p.2 ≠ T p.1} :=
    (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst)).compl
  have h1 : Graph A T {p : H × H | p.2 ≠ T p.1} = 0 := by
    unfold Graph; rw [Measure.map_apply hm hD]; simp
  rw [h] at h1
  unfold Graph at h1
  rw [Measure.map_apply hm' hD] at h1
  refine (measure_eq_zero_iff_ae_notMem.1 h1).mono fun x hx => ?_
  simp only [mem_preimage, mem_setOf_eq, ne_eq, not_not] at hx
  exact hx.symm

end Uniq

theorem ghs_grad_unique_m1_thm : Claims.ghs_grad_unique_m1 := by
  intro H _ _ _ _ _ _ A B M hA hLip hM1 hBM f f' T T' L L' hf hf' hL hL' hT hT' hg hg' hmT hmT'
  have hB : IsProbabilityMeasure B := by rw [← hmT]; exact (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 hA
  have hU := StatFormal.OTFD.WaveL3.brenier_uniq_H_bdd H ⟨A, hA⟩ ⟨B, hB⟩ T M hLip hM1 hBM hT hmT
    (isCMMapAE_of_gatDiff hf hL hg)
  have hgm : Measurable fun x : H => (x, T' x) := measurable_id.prodMk hT'
  have hprob : IsProbabilityMeasure (Graph A T') := (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 hA
  have hfst : (Graph A T').fst = A := by
    unfold Graph; rw [Measure.fst_map_prodMk (X := fun x : H => x) measurable_id hT']; exact Measure.map_id
  have hsnd : (Graph A T').snd = B := by
    unfold Graph; rw [Measure.snd_map_prodMk (X := fun x : H => x) measurable_id hT']; exact hmT'
  set Γ' : Set (H × H) := {z | ∀ x, f' z.1 + ⟪z.2, x - z.1⟫ ≤ f' x}
  have hΓ'm : MeasurableSet Γ' := (isClosed_subgradGraph (continuous_of_lip hL')).measurableSet
  have hcm : CMConc (Graph A T') := by
    refine ⟨Γ', hΓ'm, StatFormal.OTFD.WaveL3.cycMon_subgradGraph f', ?_⟩
    unfold Graph
    rw [Measure.map_apply hgm hΓ'm.compl]
    refine measure_eq_zero_iff_ae_notMem.2 (hg'.mono fun x hx => ?_)
    simp only [mem_preimage, mem_compl_iff, not_not]
    exact fun z => subgrad_of_gatDiff hf' hL' hx z
  have heq : Graph A T' = Graph A T := hU (Graph A T') hprob hfst hsnd hcm
  exact ae_eq_of_graph_eq hT hT' heq.symm

theorem cm_unique_uncond_thm : Claims.cm_unique_uncond := by
  intro H _ _ _ _ _ _ γ γ' M hγ hγ' hfst hsnd hA hM1 hM hcm hcm'
  obtain ⟨T, hT, hγT, hmap⟩ := cm_graph_exists_thm H γ hγ hA hcm
  obtain ⟨Γ, hΓm, hΓ, hΓ0⟩ := hcm
  have hcmT : IsCMMapAE γ.fst T := by
    have hgm : Measurable fun x : H => (x, T x) := measurable_id.prodMk hT
    refine ⟨(fun x => (x, T x)) ⁻¹' Γ, hgm hΓm, ?_, ?_⟩
    · rw [← preimage_compl, ← Measure.map_apply hgm hΓm.compl]
      have : Graph γ.fst T = γ.fst.map fun x => (x, T x) := rfl
      rw [← this, ← hγT]; exact hΓ0
    · refine StatFormal.OTFD.WaveL3.cycMon_mono hΓ ?_
      rintro z ⟨hz1, hz2⟩
      have : z = (z.1, T z.1) := Prod.ext rfl hz2
      rw [this]; exact hz1
  have hfstP : IsProbabilityMeasure γ.fst := by
    infer_instance
  have hsndP : IsProbabilityMeasure γ.snd := by
    infer_instance
  have hU := StatFormal.OTFD.WaveL3.brenier_uniq_H_bdd H ⟨γ.fst, hfstP⟩ ⟨γ.snd, hsndP⟩ T M hA hM1 hM hT hmap hcmT
  rw [hU γ' hγ' hfst hsnd hcm']
  exact hγT.symm

end StatFormal.Wave23d
