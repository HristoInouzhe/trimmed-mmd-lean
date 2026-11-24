import StatFormal.Archive.OTFD.WaveL9.Statements
import StatFormal.Archive.OTFD.WaveL7.RouteClaims

/-!
# Route (wave L9): gradients of arbitrary convex potentials are cyclically monotone; uniqueness

Untrusted route file.
* `subgrad_of_gatDiffDom`: a Gâteaux gradient `g` of the proper convex `φ = (C, f)` at a core point `x` is a
  subgradient: for `z ∈ C` the line function `t ↦ f(x + t(z − x))` is convex on `[0, 1]`, so its right slopes at `0`
  are `≤ f z − f x`, and they tend to `⟨g, z − x⟩`.
* The subdifferential graph of `φ` is cyclically monotone (telescoping), so an `A`-a.e. gradient map is `IsCMMapAE`.
* `ae_eq_of_isCMMapAE`: two a.e.-measurable `A`-a.e. cyclically monotone maps pushing a Lipschitz-null `A` to the
  same bounded `B` agree `A`-a.e., by the certified wave-L7 `brenier_uniq_H_bdd` (moment-free McCann) applied to Borel
  versions, and equal graph plans (`Wave23d.ae_eq_of_graph_eq`).
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL9

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph BrenierUniq LipNull)

section Convex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma mem_of_gatDiffDom {C : Set H} {f : H → ℝ} {x g : H} (hg : GatDiffDom C f x g) : x ∈ C := by
  simpa using (hg 0).1.self_of_nhds

lemma gatDiffDom_univ {f : H → ℝ} {x g : H} (hg : StatFormal.Wave23d.GatDiff f x g) : GatDiffDom univ f x g :=
  fun h => ⟨Eventually.of_forall fun _ => mem_univ _, hg h⟩

/-- A Gâteaux gradient of a proper convex potential is a subgradient (on the domain; off it `φ = +∞`). -/
lemma subgrad_of_gatDiffDom {C : Set H} {f : H → ℝ} (hf : ConvexOn ℝ C f) {x g : H} (hg : GatDiffDom C f x g)
    {z : H} (hz : z ∈ C) : f x + ⟪g, z - x⟫ ≤ f z := by
  have hx := mem_of_gatDiffDom hg
  have ht := (hg (z - x)).2.tendsto_slope_zero_right
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((fun t : ℝ => f (x + t • (z - x))) (0 + t) - (fun t : ℝ => f (x + t • (z - x))) 0) ≤ f z - f x := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t htI
    have hc := hf.2 hx hz (show (0 : ℝ) ≤ 1 - t by linarith [htI.2]) htI.1.le (by ring)
    have heq : x + t • (z - x) = (1 - t) • x + t • z := by
      rw [smul_sub, sub_smul, one_smul]; abel
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hc ⊢
    rw [heq, inv_mul_le_iff₀ htI.1]
    nlinarith
  have := le_of_tendsto ht hle
  linarith

/-- The subdifferential graph of a proper convex potential `(C, f)` is cyclically monotone. -/
lemma cycMon_subgradGraphDom (C : Set H) (f : H → ℝ) :
    CycMon {z : H × H | z.1 ∈ C ∧ ∀ w ∈ C, f z.1 + ⟪z.2, w - z.1⟫ ≤ f w} := by
  intro m z hz
  have h : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤
      f (z (finRotate m i)).1 - f (z i).1 := fun i => by
    have := (hz i).2 (z (finRotate m i)).1 (hz (finRotate m i)).1
    linarith
  calc ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫
      ≤ ∑ i, (f (z (finRotate m i)).1 - f (z i).1) := Finset.sum_le_sum fun i _ => h i
    _ = 0 := by
      rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) (fun i => f (z i).1), sub_self]

variable [MeasurableSpace H]

/-- An `A`-a.e. Gâteaux gradient of a proper convex potential is `A`-a.e. cyclically monotone. -/
lemma isCMMapAE_of_gatDiffDom {A : Measure H} {C : Set H} {f : H → ℝ} (hf : ConvexOn ℝ C f) {T : H → H}
    (hT : ∀ᵐ x ∂A, GatDiffDom C f x (T x)) : IsCMMapAE A T := by
  set good : Set H := {x | GatDiffDom C f x (T x)}
  have hgood : A goodᶜ = 0 := hT
  refine ⟨(toMeasurable A goodᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact hgood
  · refine StatFormal.OTFD.WaveL3.cycMon_mono (cycMon_subgradGraphDom C f) ?_
    rintro z ⟨hz1, hz2⟩
    have hzg : z.1 ∈ good := by
      by_contra hc
      exact hz1 (subset_toMeasurable A goodᶜ hc)
    refine ⟨mem_of_gatDiffDom hzg, fun w hw => ?_⟩
    rw [hz2]; exact subgrad_of_gatDiffDom hf hzg hw

/-- An `A`-a.e. selection of the subdifferential of a proper convex potential is `A`-a.e. cyclically monotone. -/
lemma isCMMapAE_of_subgrad {A : Measure H} {C : Set H} {f : H → ℝ} {T : H → H}
    (hT : ∀ᵐ x ∂A, x ∈ C ∧ ∀ z ∈ C, f x + ⟪T x, z - x⟫ ≤ f z) : IsCMMapAE A T := by
  set good : Set H := {x | x ∈ C ∧ ∀ z ∈ C, f x + ⟪T x, z - x⟫ ≤ f z}
  have hgood : A goodᶜ = 0 := hT
  refine ⟨(toMeasurable A goodᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact hgood
  · refine StatFormal.OTFD.WaveL3.cycMon_mono (cycMon_subgradGraphDom C f) ?_
    rintro z ⟨hz1, hz2⟩
    have hzg : z.1 ∈ good := by
      by_contra hc
      exact hz1 (subset_toMeasurable A goodᶜ hc)
    exact ⟨hzg.1, fun w hw => by rw [hz2]; exact hzg.2 w hw⟩

/-- `IsCMMapAE` is invariant under `A`-a.e. modification of the map. -/
lemma isCMMapAE_congr {A : Measure H} {T T₀ : H → H} (hT : IsCMMapAE A T) (h : T =ᵐ[A] T₀) : IsCMMapAE A T₀ := by
  obtain ⟨S, hS, hS0, hcm⟩ := hT
  set bad : Set H := {x | T x ≠ T₀ x}
  have hbad : A bad = 0 := ae_iff.1 h
  refine ⟨S ∩ (toMeasurable A bad)ᶜ, hS.inter (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_inter, compl_compl]
    exact measure_union_null hS0 (by rw [measure_toMeasurable]; exact hbad)
  · refine StatFormal.OTFD.WaveL3.cycMon_mono hcm ?_
    rintro z ⟨⟨hz1, hz1'⟩, hz2⟩
    refine ⟨hz1, ?_⟩
    have : T z.1 = T₀ z.1 := by
      by_contra hc
      exact hz1' (subset_toMeasurable A bad hc)
    rw [hz2, this]

end Convex

section Uniq
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The graph plan of a Borel `A`-a.e. cyclically monotone map is concentrated on a Borel cyclically monotone set. -/
lemma cmConc_graph {A : Measure H} {T : H → H} (hTm : Measurable T) (hT : IsCMMapAE A T) : CMConc (Graph A T) := by
  obtain ⟨S, hS, hS0, hcm⟩ := hT
  have hgm : Measurable fun x : H => (x, T x) := measurable_id.prodMk hTm
  have hΓ : MeasurableSet {z : H × H | z.1 ∈ S ∧ z.2 = T z.1} :=
    (measurable_fst hS).inter (measurableSet_eq_fun measurable_snd (hTm.comp measurable_fst))
  refine ⟨_, hΓ, hcm, ?_⟩
  unfold Graph
  rw [Measure.map_apply hgm hΓ.compl]
  have : (fun x : H => (x, T x)) ⁻¹' {z : H × H | z.1 ∈ S ∧ z.2 = T z.1}ᶜ = Sᶜ := by
    ext x; simp
  rw [this]; exact hS0

/-- Two a.e.-measurable, `A`-a.e. cyclically monotone maps pushing a Lipschitz-null probability `A` to the same `B`
carried by `B̄(0, M)` agree `A`-a.e. (moment-free; certified wave-L7 `brenier_uniq_H_bdd`). -/
theorem ae_eq_of_isCMMapAE {A B : Measure H} [hA : IsProbabilityMeasure A] {M : ℝ} (hLip : LipNull A)
    (hBM : B (Metric.closedBall 0 M)ᶜ = 0) {T T' : H → H} (hT : AEMeasurable T A) (hT' : AEMeasurable T' A)
    (hcm : IsCMMapAE A T) (hcm' : IsCMMapAE A T') (hmT : A.map T = B) (hmT' : A.map T' = B) : T =ᵐ[A] T' := by
  set T₀ := hT.mk T
  set T₀' := hT'.mk T'
  have hT₀ : Measurable T₀ := hT.measurable_mk
  have hT₀' : Measurable T₀' := hT'.measurable_mk
  have hmT₀ : A.map T₀ = B := by rw [← Measure.map_congr hT.ae_eq_mk]; exact hmT
  have hmT₀' : A.map T₀' = B := by rw [← Measure.map_congr hT'.ae_eq_mk]; exact hmT'
  have hB : IsProbabilityMeasure B := by
    rw [← hmT₀]; exact (Measure.isProbabilityMeasure_map_iff hT₀.aemeasurable).2 hA
  have hU := StatFormal.OTFD.WaveL7.brenier_uniq_H_bdd H ⟨A, hA⟩ ⟨B, hB⟩ T₀ M hLip hBM hT₀ hmT₀
    (isCMMapAE_congr hcm hT.ae_eq_mk)
  have hgm : Measurable fun x : H => (x, T₀' x) := measurable_id.prodMk hT₀'
  have hprob : IsProbabilityMeasure (Graph A T₀') := (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 hA
  have hfst : (Graph A T₀').fst = A := by
    unfold Graph; rw [Measure.fst_map_prodMk (X := fun x : H => x) measurable_id hT₀']; exact Measure.map_id
  have hsnd : (Graph A T₀').snd = B := by
    unfold Graph; rw [Measure.snd_map_prodMk (X := fun x : H => x) measurable_id hT₀']; exact hmT₀'
  have heq : Graph A T₀' = Graph A T₀ :=
    hU (Graph A T₀') hprob hfst hsnd (cmConc_graph hT₀' (isCMMapAE_congr hcm' hT'.ae_eq_mk))
  exact hT.ae_eq_mk.trans ((StatFormal.Wave23d.ae_eq_of_graph_eq hT₀ hT₀' heq.symm).trans hT'.ae_eq_mk.symm)

end Uniq

end StatFormal.OTFD.WaveL9
