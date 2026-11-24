import StatFormal.Archive.OTFD.WaveL3.RouteBrenierH
import StatFormal.Lib.McCannH.Extended

/-!
# Route (wave L8): moment-free uniqueness of cyclically monotone couplings, ANY target

Untrusted route file. A coupling `π ∈ Π(P, μ)` concentrated on a Borel cyclically monotone `Γ` is (since `π ≠ 0`)
concentrated on a nonempty cyclically monotone set, which lies in the relative subdifferential graph `∂_D φ` of
the extended-valued Rockafellar potential (`McCannH.exists_subgradGraphOn_of_cycMon`, `D = {f < ∞}`). Two such
couplings are equal by McCann's moment-free comparison with relative conjugates
(`McCannH.eq_of_ae_mem_subgradGraphOn`, `P` null on Lipschitz hypersurfaces). No moment of `P` or `μ`, and no bound
on `μ`, is used. The exchanged form (Lipschitz-null *target*) follows by swapping coordinates.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL8

open StatFormal.OTFD.WaveL1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- A `CMConc` coupling lies, a.e., in the relative subdifferential graph of a Borel potential on a Borel domain. -/
theorem exists_potentialOn_of_cmConc {P μ : Measure H} [IsProbabilityMeasure P] {π : Measure (H × H)}
    (hπ : IsCoupling π P μ) (hc : CMConc π) :
    ∃ (D : Set H) (φ : H → ℝ), MeasurableSet D ∧ Measurable φ ∧
      ∀ᵐ z ∂π, z ∈ StatFormal.McCannH.subgradGraphOn D φ := by
  obtain ⟨Γ, -, hΓ, hΓ0⟩ := hc
  have hae : ∀ᵐ z ∂π, z ∈ Γ := (measure_eq_zero_iff_ae_notMem.1 hΓ0).mono fun _ h => Set.notMem_compl_iff.1 h
  have hπ0 : π ≠ 0 := by
    intro h0
    have h1 : π univ = 1 := by
      rw [← Measure.fst_univ, hπ.fst_eq, measure_univ]
    rw [h0] at h1
    simp at h1
  have : (ae π).NeBot := ae_neBot.2 hπ0
  obtain ⟨p, hp⟩ := hae.exists
  obtain ⟨D, φ, hD, hφ, hsub⟩ := StatFormal.McCannH.exists_subgradGraphOn_of_cycMon hΓ ⟨p, hp⟩
  exact ⟨D, φ, hD, hφ, hae.mono fun z hz => hsub hz⟩

/-- **Moment-free uniqueness of cyclically monotone couplings** (any target): two couplings of `(P, μ)`
concentrated on Borel cyclically monotone sets coincide, for `P` null on Lipschitz hypersurfaces. -/
theorem eq_of_cmConc {P μ : Measure H} [IsProbabilityMeasure P] (hP : LipNull P) {π₁ π₂ : Measure (H × H)}
    (h₁ : IsCoupling π₁ P μ) (h₂ : IsCoupling π₂ P μ) (hc₁ : CMConc π₁) (hc₂ : CMConc π₂) : π₁ = π₂ := by
  obtain ⟨D₁, φ₁, hD₁, hφ₁, hπ₁⟩ := exists_potentialOn_of_cmConc h₁ hc₁
  obtain ⟨D₂, φ₂, hD₂, hφ₂, hπ₂⟩ := exists_potentialOn_of_cmConc h₂ hc₂
  exact StatFormal.McCannH.eq_of_ae_mem_subgradGraphOn (StatFormal.OTFD.WaveL3.lipGraph_null hP) h₁ h₂ hD₁ hD₂
    hφ₁ hφ₂ hπ₁ hπ₂

/-- `BrenierUniq` with no moment and no bound on the target (A `lem:app-cm-plans`(iv), GHS, McCann). -/
theorem brenierUniq_general {P μ : Measure H} [IsProbabilityMeasure P] (hP : LipNull P) {F : H → H}
    (hF : Measurable F) (hmap : P.map F = μ) (hcm : IsCMMapAE P F) : BrenierUniq P μ F := fun _ _ hfst hsnd hcmπ =>
  eq_of_cmConc hP ⟨hfst, hsnd⟩ (StatFormal.OTFD.WaveL3.isCoupling_graph hF hmap) hcmπ (cmConc_graph hF hcm)

/-- The exchanged form, moment-free: the *target* `P` null on Lipschitz hypersurfaces, `Q#μ = P`, `Q`
`μ`-a.e. cyclically monotone ⇒ `BrenierUniq μ P Q`. -/
theorem brenierUniq_swap_general {P μ : Measure H} [IsProbabilityMeasure P] (hP : LipNull P) {Q : H → H}
    (hQ : Measurable Q) (hmap : μ.map Q = P) (hcm : IsCMMapAE μ Q) : BrenierUniq μ P Q := by
  have key : ∀ π : Measure (H × H), IsCoupling π μ P → CMConc π →
      π.map Prod.swap = (Graph μ Q).map Prod.swap := fun π hπ hcmπ =>
    have hG := StatFormal.OTFD.WaveL3.isCoupling_graph hQ hmap
    eq_of_cmConc hP ⟨by rw [Measure.fst_map_swap, hπ.snd_eq], by rw [Measure.snd_map_swap, hπ.fst_eq]⟩
      ⟨by rw [Measure.fst_map_swap, hG.snd_eq], by rw [Measure.snd_map_swap, hG.fst_eq]⟩
      (StatFormal.OTFD.WaveL3.cmConc_map_swap hcmπ)
      (StatFormal.OTFD.WaveL3.cmConc_map_swap (cmConc_graph hQ hcm))
  intro π _ hfst hsnd hcmπ
  have h := key π ⟨hfst, hsnd⟩ hcmπ
  rw [← StatFormal.OTFD.WaveL3.map_swap_map_swap π, h, StatFormal.OTFD.WaveL3.map_swap_map_swap]

end StatFormal.OTFD.WaveL8
