import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelFacts.Contact
import StatFormal.Wave31to.RouteC
import StatFormal.Wave31tp.RouteS

/-!
# Wave 31tr, chunk M1: `contact_densities`, `contact_gauss_mix`, `minimax_class_apart` (T29)

(a) On `𝒳 = U` (connected open, Lebesgue measure through `Subtype.val`, positive on nonempty open sets since `U` is open), the
general contact lemma `KernelFacts.support_sub_inf_inter_nonempty` gives `supp P₀ ∩ supp Q₀ ≠ ∅`; `TV > 0` from `P ≠ Q`
(`KernelFacts.tvDist_pos_of_ne`), and the certified `Wave31to.newslope_b` gives the rest. (b) the certified 31tp L27(b), (c)
(`gaussMix_facts`, `gaussMix_distinct`) give the densities, their continuity and positivity, and the empty interior of `{p = q}`;
`TV < 1` from the common part `min(p, q)·λ ≠ 0` (`KernelFacts.tvDist_lt_one_of_common`); then the contact lemma on `ℝ^d` and
`newslope_b`. (c) `InM` includes `PolyMargin φ P Q c₀ 1`, which `newslope_b` excludes when the supports meet.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteMisc1

open StatFormal.Wave31tn

/-- Lebesgue measure on an open `U ⊆ ℝ^d`, as a measure on the subtype, is positive on nonempty open sets. -/
lemma isOpenPosMeasure_comap_val {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    (Measure.comap Subtype.val (volume : Measure (EuclideanSpace ℝ (Fin d))) : Measure ↥U).IsOpenPosMeasure := by
  refine ⟨fun O hO hne => ?_⟩
  rw [comap_subtype_coe_apply hU.measurableSet]
  exact (hU.isOpenMap_subtype_val O hO).measure_ne_zero volume (hne.image _)

/-- An open subset of `U` (subtype topology) is open in `ℝ^d`, so empty interior of `{x ∈ U : p x = q x}` in `ℝ^d` gives empty
interior of `{x : U | p x = q x}` in `U`. -/
lemma interior_subtype_eq_empty {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {p q : EuclideanSpace ℝ (Fin d) → ℝ} (hint : interior {x | x ∈ U ∧ p x = q x} = ∅) :
    interior {x : ↥U | p x = q x} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_interior.1 hx
  have hO' : IsOpen (Subtype.val '' O) := hU.isOpenMap_subtype_val O hOo
  have hsub : Subtype.val '' O ⊆ {x | x ∈ U ∧ p x = q x} := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hOsub hy⟩
  have := interior_maximal hsub hO'
  rw [hint] at this
  exact this ⟨x, hxO, rfl⟩

theorem contact_densities_route : Claims.contact_densities := by
  intro d U p q P Q _ _ hU hconn hpc hqc hp0 hq0 hP hQ hPQ hint
  haveI : ConnectedSpace ↥U := isConnected_iff_connectedSpace.1 hconn
  haveI := isOpenPosMeasure_comap_val hU
  have hsupp : ((P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support).Nonempty :=
    KernelFacts.support_sub_inf_inter_nonempty (Measure.comap Subtype.val volume) (p := fun x : ↥U => p x)
      (q := fun x : ↥U => q x) hpc.restrict hqc.restrict (fun x => hp0 x x.2) (fun x => hq0 x x.2) P Q hP hQ hPQ
      (interior_subtype_eq_empty hU hint)
  refine ⟨hsupp, fun htv H _ _ _ _ φ κ hφ hφc hκ => ?_⟩
  exact StatFormal.Wave31to.RouteC.newslope_b_route ↥U H P Q φ κ hφ hφc hκ (KernelFacts.tvDist_pos_of_ne hPQ) htv hsupp

/-- A finite Gaussian mixture with positive weights summing to `1` is a probability measure. -/
lemma gaussMix_isProb {d n : ℕ} (w : Fin n → ℝ) (μ : Fin n → EuclideanSpace ℝ (Fin d)) (S : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (StatFormal.Wave31tp.gaussMix w μ S) := by
  constructor
  simp only [StatFormal.Wave31tp.gaussMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), hs, ENNReal.ofReal_one]

theorem contact_gauss_mix_route : Claims.contact_gauss_mix := by
  intro d n n' w μ S w' μ' S' hw hs hS hw' hs' hS' hne
  obtain ⟨hP, hPan, hPpos⟩ := StatFormal.Wave31tp.RouteS.gaussMix_facts_route d n w μ S hw hs hS
  obtain ⟨hQ, hQan, hQpos⟩ := StatFormal.Wave31tp.RouteS.gaussMix_facts_route d n' w' μ' S' hw' hs' hS'
  haveI := gaussMix_isProb w μ S hw hs
  haveI := gaussMix_isProb w' μ' S' hw' hs'
  set f := StatFormal.Wave31tp.gaussMixDens w μ S
  set f' := StatFormal.Wave31tp.gaussMixDens w' μ' S'
  have hfc : Continuous f := continuousOn_univ.1 hPan.continuousOn
  have hf'c : Continuous f' := continuousOn_univ.1 hQan.continuousOn
  have hint : interior {x | f x = f' x} = ∅ := by
    by_contra hne'
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne'
    obtain ⟨y, hy, hyne⟩ := StatFormal.Wave31tp.RouteS.gaussMix_distinct_route d n n' w μ S w' μ' S' hw hs hS hw' hs' hS'
      hne (interior {x | f x = f' x}) isOpen_interior ⟨x, hx⟩
    have hy' : y ∈ {x | f x = f' x} := interior_subset hy
    exact hyne hy'
  have htv : StatFormal.Distances.tvDist (StatFormal.Wave31tp.gaussMix w μ S) (StatFormal.Wave31tp.gaussMix w' μ' S') < 1 := by
    refine KernelFacts.tvDist_lt_one_of_common (volume.withDensity fun x => ENNReal.ofReal (min (f x) (f' x)))
      (hP ▸ KernelFacts.withDensity_le_of_le volume fun x => min_le_left _ _)
      (hQ ▸ KernelFacts.withDensity_le_of_le volume fun x => min_le_right _ _) ?_
    intro h0
    have hm : Measurable fun x => ENNReal.ofReal (min (f x) (f' x)) :=
      ENNReal.measurable_ofReal.comp (hfc.min hf'c).measurable
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff hm] at h0
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin d))) univ ≠ 0 :=
      isOpen_univ.measure_ne_zero volume univ_nonempty
    have : (volume : Measure (EuclideanSpace ℝ (Fin d))) {x | ENNReal.ofReal (min (f x) (f' x)) ≠ 0} = 0 := h0
    have huniv : {x | ENNReal.ofReal (min (f x) (f' x)) ≠ 0} = univ := by
      refine eq_univ_of_forall fun x => ?_
      simp only [mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_min (hPpos x) (hQpos x)
    rw [huniv] at this
    exact hvol this
  have hsupp := KernelFacts.support_sub_inf_inter_nonempty volume hfc hf'c (fun x => (hPpos x).le) (fun x => (hQpos x).le)
    _ _ hP hQ hne hint
  refine ⟨inferInstance, inferInstance, hP, hQ, hfc, hf'c, fun x => (hPpos x).le, fun x => (hQpos x).le, hint, htv, hsupp,
    fun H _ _ _ _ φ κ hφ hφc hκ => ?_⟩
  exact StatFormal.Wave31to.RouteC.newslope_b_route _ H _ _ φ κ hφ hφc hκ (KernelFacts.tvDist_pos_of_ne hne) htv hsupp

theorem minimax_class_apart_route : Claims.minimax_class_apart := by
  have part1 : ∀ (𝒳 H : Type) [TopologicalSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] [NormedAddCommGroup H]
      [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (φ : 𝒳 → H) (κ a₀ a₁ c₀ : ℝ)
      (P Q : Measure 𝒳), StronglyMeasurable φ → Continuous φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < a₀ → a₁ < 1 → InM φ a₀ a₁ c₀ P Q →
        (P - P ⊓ Q).support ∩ (Q - P ⊓ Q).support = ∅ := by
    intro 𝒳 H _ _ _ _ _ _ _ φ κ a₀ a₁ c₀ P Q hφ hφc hκ ha₀ ha₁ hM
    obtain ⟨hPp, hQp, h1, h2, hpm⟩ := hM
    by_contra hne
    exact (StatFormal.Wave31to.RouteC.newslope_b_route 𝒳 H P Q φ κ hφ hφc hκ (by linarith) (by linarith)
      (nonempty_iff_ne_empty.2 hne)).2 ⟨c₀, hpm⟩
  refine ⟨part1, ?_⟩
  intro d U p q P Q H _ _ _ _ φ κ a₀ a₁ c₀ hU hconn hpc hqc hp0 hq0 hP hQ hPQ hint hφ hφc hκ ha₀ ha₁ hM
  obtain ⟨hPp, hQp, h1, h2, hpm⟩ := hM
  have := (contact_densities_route d U p q P Q hU hconn hpc hqc hp0 hq0 hP hQ hPQ hint).2 (by linarith) H φ κ hφ hφc hκ
  exact this.2 ⟨c₀, hpm⟩

end StatFormal.Wave31tr.RouteMisc1
