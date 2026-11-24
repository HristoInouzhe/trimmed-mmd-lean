import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Lib.OTLimits.PlanStability

/-!
# Route (wave L1): cyclically monotone plans and their weak limits

Untrusted route file. The paper's cyclical monotonicity (`CycMon`, cycles of inner products)
passes to the support of weak limits of plans concentrated on cyclically monotone sets; with the
uniqueness hypothesis `BrenierUniq` this gives convergence of the whole sequence (Villani 5.20,
in the cyclically monotone form of otfd A `lem:plan-stability-H`(a)).
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL1

section Support

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- A plan concentrated on `Γ` charges an open set only if it meets `Γ`. -/
theorem nonempty_inter_of_pos {π : Measure (E × E)} {Γ : Set (E × E)} (hΓ : π Γᶜ = 0)
    {U : Set (E × E)} (hU : 0 < π U) : (U ∩ Γ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hsub : U ⊆ Γᶜ := fun z hz hzΓ => (h ▸ (⟨hz, hzΓ⟩ : z ∈ U ∩ Γ) : z ∈ (∅ : Set _))
  exact hU.ne' (measure_mono_null hsub hΓ)

/-- **Cyclical monotonicity of supports passes to weak limits** (paper form). -/
theorem cycMon_support_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hcm : ∀ i, CMConc (πs i : Measure (E × E))) :
    CycMon (π : Measure (E × E)).support := by
  intro m z hmem
  by_contra hlt
  rw [not_le] at hlt
  set f : (Fin m → E × E) → ℝ := fun w ↦ ∑ i, ⟪(w i).2, (w (finRotate m i)).1 - (w i).1⟫
    with hfdef
  have hf : Continuous f := continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).snd).inner
      (((continuous_apply (finRotate m i)).fst).sub ((continuous_apply i).fst))
  have hopen : IsOpen {w | 0 < f w} := isOpen_lt continuous_const hf
  obtain ⟨U, hU, hUsub⟩ := isOpen_pi_iff'.1 hopen z hlt
  have hpos : ∀ i, 0 < (π : Measure (E × E)) (U i) := fun i ↦
    (Measure.mem_support_iff_forall _).1 (hmem i) _ ((hU i).1.mem_nhds (hU i).2)
  have hev : ∀ᶠ j in l, ∀ i, 0 < (πs j : Measure (E × E)) (U i) :=
    eventually_all.2 fun i ↦ StatFormal.OTLimits.eventually_pos_measure_of_tendsto hπ (hU i).1
      (hpos i)
  obtain ⟨j, hj⟩ := hev.exists
  obtain ⟨Γ, -, hΓ, hΓ0⟩ := hcm j
  choose w hwU hwΓ using fun i ↦ nonempty_inter_of_pos hΓ0 (hj i)
  have hw : 0 < f w := hUsub fun i _ ↦ hwU i
  exact (hΓ m w hwΓ).not_gt hw

/-- The support of a weak limit of cyclically monotone plans is a Borel cyclically monotone set of
full mass. -/
theorem cmConc_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {πs : ι → ProbabilityMeasure (E × E)} {π : ProbabilityMeasure (E × E)}
    (hπ : Tendsto πs l (𝓝 π)) (hcm : ∀ i, CMConc (πs i : Measure (E × E))) :
    CMConc (π : Measure (E × E)) :=
  ⟨_, Measure.isClosed_support.measurableSet, cycMon_support_of_tendsto hπ hcm,
    Measure.measure_compl_support⟩

end Support

section Stability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **Core stability theorem** (otfd A `lem:plan-stability-H`(a), R `lem:plan-w2`(a)): weak
convergence of the marginals, cyclically monotone plans and uniqueness of the cyclically monotone
coupling of the limit marginals give weak convergence of the whole sequence of plans. -/
theorem tendsto_of_cmConc {P μ : ProbabilityMeasure E} {F : E → E}
    {α ν : ℕ → ProbabilityMeasure E} {π : ℕ → ProbabilityMeasure (E × E)}
    {G : ProbabilityMeasure (E × E)}
    (huniq : BrenierUniq (P : Measure E) μ F)
    (hα : Tendsto α atTop (𝓝 P)) (hν : Tendsto ν atTop (𝓝 μ))
    (hfst : ∀ K, (π K : Measure (E × E)).fst = α K)
    (hsnd : ∀ K, (π K : Measure (E × E)).snd = ν K)
    (hcm : ∀ K, CMConc (π K : Measure (E × E)))
    (hG : (G : Measure (E × E)) = Graph (P : Measure E) F) :
    Tendsto π atTop (𝓝 G) := by
  by_contra hnot
  obtain ⟨U, hU, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  set lb : Filter ℕ := atTop ⊓ 𝓟 {n | π n ∉ U}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have hlb : lb ≤ atTop := inf_le_left
  have hcoup : ∀ K, IsCoupling (π K : Measure (E × E)) (α K) (ν K) := fun K ↦ ⟨hfst K, hsnd K⟩
  obtain ⟨l', σ, hne', hle, hconv, hσ⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb)
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hα).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    ⟨univ, univ_mem, (isTightMeasureSet_range_of_tendsto hν).subset
      (by rintro - ⟨i, -, rfl⟩; exact mem_range_self i)⟩
    (hα.mono_left hlb) (hν.mono_left hlb) (Eventually.of_forall hcoup)
  have := hne'
  have hσcm : CMConc (σ : Measure (E × E)) := cmConc_of_tendsto hconv fun K ↦ hcm K
  have hσG : σ = G := by
    apply Subtype.ext
    change (σ : Measure (E × E)) = (G : Measure (E × E))
    rw [hG]
    exact huniq _ inferInstance hσ.fst_eq hσ.snd_eq hσcm
  rw [hσG] at hconv
  have hout : ∀ᶠ n in l', π n ∉ U :=
    (eventually_inf_principal.2 (Eventually.of_forall fun _ h ↦ h)).filter_mono hle
  exact ((hconv.eventually (mem_of_superset hU fun _ h ↦ h)).and hout).exists.elim
    fun _ h ↦ h.2 h.1

end Stability

end StatFormal.OTFD.WaveL1
