import StatFormal.Archive.Wave23d.RouteUniq
import StatFormal.Lib.McCannH.Uniqueness

/-!
# Route (wave L7): moment-free uniqueness of cyclically monotone couplings with a bounded target

Untrusted route file. A coupling `π ∈ Π(P, μ)` concentrated on a Borel cyclically monotone `Γ`, with `μ` carried by
`B̄(0, M)`, is concentrated on `Γ' = Γ ∩ (H × B̄(0, M))`, nonempty, cyclically monotone, with slopes `≤ M`; the
certified wave-23d Rockafellar construction (`cm_rockafellar_thm`) puts `Γ'` inside the subdifferential graph of a
finite convex `M`-Lipschitz `φ`. Two such couplings are equal by the library's moment-free McCann argument
(`McCannH.eq_of_ae_mem_subgradGraph`, `P` null on Lipschitz hypersurfaces). No moment is used anywhere.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL7

open StatFormal.OTFD.WaveL1

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A `CMConc` coupling with a target carried by `B̄(0, M)` lies, a.e., in the subdifferential graph of a finite
continuous (convex `M`-Lipschitz) potential. -/
theorem exists_potential_of_cmConc {P μ : Measure H} [IsProbabilityMeasure P] {M : ℝ}
    (hμM : μ (Metric.closedBall 0 M)ᶜ = 0) {π : Measure (H × H)} (hπ : IsCoupling π P μ) (hc : CMConc π) :
    ∃ φ : H → ℝ, Continuous φ ∧ ∀ᵐ z ∂π, z ∈ StatFormal.McCannH.subgradGraph φ := by
  obtain ⟨Γ, -, hΓ, hΓ0⟩ := hc
  have hAB := StatFormal.OTFD.WaveL3.ae_mem_prod hπ MeasurableSet.univ Metric.isClosed_closedBall.measurableSet
    (by simp) hμM
  have hae : ∀ᵐ z ∂π, z ∈ Γ ∩ (univ ×ˢ Metric.closedBall (0 : H) M) := by
    filter_upwards [hAB, measure_eq_zero_iff_ae_notMem.1 hΓ0] with z hz hz'
    exact ⟨Set.notMem_compl_iff.1 hz', hz⟩
  have hπ0 : π ≠ 0 := by
    intro h0
    have h1 : π univ = 1 := by
      rw [← Measure.fst_univ, hπ.fst_eq, measure_univ]
    rw [h0] at h1
    simp at h1
  haveI : (ae π).NeBot := ae_neBot.2 hπ0
  obtain ⟨p, hp⟩ := hae.exists
  obtain ⟨φ, -, hφL, hsub⟩ := StatFormal.Wave23d.cm_rockafellar_thm H (Γ ∩ (univ ×ˢ Metric.closedBall (0 : H) M)) M
    ⟨p, hp⟩ (StatFormal.OTFD.WaveL3.cycMon_mono hΓ inter_subset_left)
    (fun q hq => by simpa [Metric.mem_closedBall, dist_zero_right] using hq.2.2)
  refine ⟨φ, StatFormal.Wave23d.continuous_of_lip hφL, hae.mono fun z hz x => hsub z hz x⟩

/-- **Moment-free uniqueness of cyclically monotone couplings, bounded target.** -/
theorem eq_of_cmConc_of_bdd_target {P μ : Measure H} [IsProbabilityMeasure P] (hP : LipNull P) {M : ℝ}
    (hμM : μ (Metric.closedBall 0 M)ᶜ = 0) {π₁ π₂ : Measure (H × H)} (h₁ : IsCoupling π₁ P μ)
    (h₂ : IsCoupling π₂ P μ) (hc₁ : CMConc π₁) (hc₂ : CMConc π₂) : π₁ = π₂ := by
  obtain ⟨φ₁, hφ₁, hπ₁⟩ := exists_potential_of_cmConc hμM h₁ hc₁
  obtain ⟨φ₂, hφ₂, hπ₂⟩ := exists_potential_of_cmConc hμM h₂ hc₂
  exact StatFormal.McCannH.eq_of_ae_mem_subgradGraph (StatFormal.OTFD.WaveL3.lipGraph_null hP) h₁ h₂ hφ₁ hφ₂
    hπ₁ hπ₂

/-- `BrenierUniq` with a bounded target and no moment (A `lem:app-cm-plans`(iv)). -/
theorem brenierUniq_of_bdd_target {P μ : Measure H} [IsProbabilityMeasure P] (hP : LipNull P) {M : ℝ}
    (hμM : μ (Metric.closedBall 0 M)ᶜ = 0) {F : H → H} (hF : Measurable F) (hmap : P.map F = μ)
    (hcm : IsCMMapAE P F) : BrenierUniq P μ F := fun _ _ hfst hsnd hcmπ =>
  eq_of_cmConc_of_bdd_target hP hμM ⟨hfst, hsnd⟩ (StatFormal.OTFD.WaveL3.isCoupling_graph hF hmap) hcmπ
    (cmConc_graph hF hcm)

end StatFormal.OTFD.WaveL7
