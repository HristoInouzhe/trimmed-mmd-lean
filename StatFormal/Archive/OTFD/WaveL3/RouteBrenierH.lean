import StatFormal.Archive.OTFD.WaveL3.RouteCycMon
import StatFormal.Archive.OTFD.WaveL1.RouteL2
import StatFormal.Lib.Potentials.HilbertUniqueness

/-!
# Route (wave L3): Brenier uniqueness `BrenierUniq` in a separable Hilbert space

Untrusted route file. From the library theorem
`StatFormal.Potentials.eq_graphPlan_of_isCyclicallyMonotone_of_lipNull` (AGS Thm 6.2.10: for `P`
null on Lipschitz hypersurfaces and finite second moments, every coupling concentrated on a
quadratic-cyclically monotone set is one graph plan `(id × T)#P`) and the conversion
`CycMon ↔ IsCyclicallyMonotone` (`RouteCycMon`):
* `brenierUniq_of_lipNull`: `BrenierUniq P μ F` for every Borel `F`, `P`-a.e. cyclically monotone,
  pushing `P` to `μ`;
* `brenierUniq_swap_of_lipNull`: the exchanged form `BrenierUniq μ P Q` (quantile maps), with the
  Lipschitz-null law `P` as the *target* (exchange of coordinates);
* `exists_brenierMap_of_lipNull`: such an `F` exists (nonvacuity).
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The frozen `LipNull` is the library's Lipschitz-null hypothesis (verbatim copies). -/
theorem lipGraph_null {P : Measure H} (hP : LipNull P) :
    ∀ S : Set H, StatFormal.Potentials.IsLipGraph S → P S = 0 := fun S hS => hP S hS

theorem memLp_id_of_mom2' {P : Measure H} (h : Mom2 P ≠ ∞) : MemLp id 2 P :=
  memLp_of_mom2 measurable_id (by rwa [Measure.map_id])

theorem isCoupling_graph {P μ : Measure H} {F : H → H} (hF : Measurable F) (hmap : P.map F = μ) :
    IsCoupling (Graph P F) P μ :=
  ⟨graph_fst hF, (graph_snd hF).trans hmap⟩

/-- The library uniqueness in the frozen vocabulary: one map `T` induces every `CMConc` coupling. -/
theorem exists_graphPlan_of_lipNull {P μ : Measure H} [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hP : LipNull P) (hP2 : Mom2 P ≠ ∞) (hμ2 : Mom2 μ ≠ ∞) :
    ∃ T : H → H, Measurable T ∧
      IsOptimalCoupling (StatFormal.OTLimits.quadCost H) (graphPlan T P) P μ ∧
      ∀ π : Measure (H × H), IsCoupling π P μ → CMConc π → π = graphPlan T P := by
  obtain ⟨T, hT, hopt, huniq⟩ :=
    StatFormal.Potentials.eq_graphPlan_of_isCyclicallyMonotone_of_lipNull (lipGraph_null hP)
      (memLp_id_of_mom2' hP2) (memLp_id_of_mom2' hμ2)
  exact ⟨T, hT, hopt, fun π hπ hcm => huniq π hπ (exists_isCyclicallyMonotone_of_cmConc hcm)⟩

/-- **`BrenierUniq` in a separable Hilbert space** (A `lem:app-cm-plans`(iv), GHS 2026, AGS
Thm 6.2.10): `P` null on Lipschitz hypersurfaces, finite second moments, `F` Borel, `P`-a.e.
cyclically monotone, `F#P = μ`. -/
theorem brenierUniq_of_lipNull {P μ : Measure H} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (hP : LipNull P) (hP2 : Mom2 P ≠ ∞) (hμ2 : Mom2 μ ≠ ∞) {F : H → H} (hF : Measurable F)
    (hmap : P.map F = μ) (hcm : IsCMMapAE P F) : BrenierUniq P μ F := by
  obtain ⟨T, -, -, huniq⟩ := exists_graphPlan_of_lipNull hP hP2 hμ2
  have hG := huniq _ (isCoupling_graph hF hmap) (cmConc_graph hF hcm)
  intro π _ hfst hsnd hcmπ
  rw [huniq π ⟨hfst, hsnd⟩ hcmπ, hG]

theorem cmConc_map_swap {π : Measure (H × H)} (h : CMConc π) : CMConc (π.map Prod.swap) := by
  obtain ⟨Γ, hΓm, hΓ, hΓ0⟩ := h
  refine ⟨Prod.swap ⁻¹' Γ, measurable_swap hΓm, cycMon_swap hΓ, ?_⟩
  rw [Measure.map_apply measurable_swap (measurable_swap hΓm).compl]
  have : Prod.swap ⁻¹' (Prod.swap ⁻¹' Γ)ᶜ = Γᶜ := by ext z; simp
  rw [this, hΓ0]

theorem map_swap_map_swap (π : Measure (H × H)) : (π.map Prod.swap).map Prod.swap = π := by
  rw [Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

/-- **Exchanged uniqueness** (quantile maps; GHS Lemma 4.3 form): if the *target* `P` is null on
Lipschitz hypersurfaces and both laws have finite second moments, every coupling of `(μ, P)`
concentrated on a cyclically monotone set is induced by any Borel `Q`, `μ`-a.e. cyclically monotone,
pushing `μ` to `P`. -/
theorem brenierUniq_swap_of_lipNull {P μ : Measure H} [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hP : LipNull P) (hP2 : Mom2 P ≠ ∞) (hμ2 : Mom2 μ ≠ ∞) {Q : H → H}
    (hQ : Measurable Q) (hmap : μ.map Q = P) (hcm : IsCMMapAE μ Q) : BrenierUniq μ P Q := by
  obtain ⟨T, -, -, huniq⟩ := exists_graphPlan_of_lipNull hP hP2 hμ2
  have key : ∀ π : Measure (H × H), IsCoupling π μ P → CMConc π →
      π.map Prod.swap = graphPlan T P := fun π hπ hcm =>
    huniq _ ⟨by rw [Measure.fst_map_swap, hπ.snd_eq], by rw [Measure.snd_map_swap, hπ.fst_eq]⟩
      (cmConc_map_swap hcm)
  have hG := key _ (isCoupling_graph hQ hmap) (cmConc_graph hQ hcm)
  intro π _ hfst hsnd hcmπ
  have h := (key π ⟨hfst, hsnd⟩ hcmπ).trans hG.symm
  rw [← map_swap_map_swap π, h, map_swap_map_swap]

/-- **Existence of the Brenier map** `𝔽^μ_P` in the frozen vocabulary (nonvacuity of the
unconditional claims): a Borel map, `P`-a.e. cyclically monotone, pushing `P` to `μ`. -/
theorem exists_brenierMap_of_lipNull {P μ : Measure H} [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hP : LipNull P) (hP2 : Mom2 P ≠ ∞) (hμ2 : Mom2 μ ≠ ∞) :
    ∃ F : H → H, Measurable F ∧ P.map F = μ ∧ IsCMMapAE P F := by
  obtain ⟨T, hT, hopt, -⟩ := exists_graphPlan_of_lipNull hP hP2 hμ2
  have hfin := StatFormal.OTLimits.transportCost_quadCost_ne_top P μ
    (by simpa [Mom2] using hP2) (by simpa [Mom2] using hμ2)
  have hcmE := hopt.isCyclicallyMonotone_support StatFormal.OTLimits.continuous_quadCost hfin
  have hcmR : IsCyclicallyMonotone (fun p : H × H => ‖p.1 - p.2‖ ^ 2 / 2)
      (graphPlan T P).support :=
    (isCyclicallyMonotone_ofReal_iff (fun z => by positivity)).1 hcmE
  have hcyc := cycMon_of_isCyclicallyMonotone hcmR
  refine ⟨T, hT, ?_, ?_⟩
  · rw [← snd_graphPlan hT.aemeasurable]; exact hopt.toIsCoupling.snd_eq
  refine ⟨{x | (x, T x) ∈ (graphPlan T P).support}, ?_, ?_, ?_⟩
  · exact (measurable_id.prodMk hT) Measure.isClosed_support.measurableSet
  · have h0 := (graphPlan T P).measure_compl_support
    rw [graphPlan_apply hT.aemeasurable Measure.isClosed_support.measurableSet.compl] at h0
    simpa [compl_setOf] using h0
  · refine cycMon_mono hcyc ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only at hx hy
    rw [hy]; exact hx

end StatFormal.OTFD.WaveL3
