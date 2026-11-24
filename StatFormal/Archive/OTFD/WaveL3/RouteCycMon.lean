import StatFormal.Archive.OTFD.WaveL1.RouteFD

/-!
# Route (wave L3): the two forms of cyclical monotonicity

Untrusted route file. The paper's cycle form `CycMon` (frozen in `OTFD/WaveL1`) and Tau Ceti's
permutation form `IsCyclicallyMonotone (‖x − y‖²/2)` are equivalent (`WaveL1` proves `→`; the
converse uses the cyclic shift as the permutation). Both are invariant under exchanging the
coordinates, and subdifferential graphs of real functions are cyclically monotone.
-/

open MeasureTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1

section CM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Tau Ceti's cyclical monotonicity implies the paper's** (quadratic cost). -/
theorem cycMon_of_isCyclicallyMonotone {S : Set (E × E)}
    (hS : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S) : CycMon S := by
  rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le] at hS
  intro m z hz
  have h := hS m (fun i => (z i).1) (fun i => (z i).2) hz (finRotate m).symm
  have hre : ∑ i, ⟪(z i).1, (z ((finRotate m).symm i)).2⟫ =
      ∑ j, ⟪(z (finRotate m j)).1, (z j).2⟫ := by
    rw [← Equiv.sum_comp (finRotate m) (fun i => ⟪(z i).1, (z ((finRotate m).symm i)).2⟫)]
    simp only [Equiv.symm_apply_apply]
  rw [hre] at h
  have : ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ =
      ∑ j, ⟪(z (finRotate m j)).1, (z j).2⟫ - ∑ i, ⟪(z i).1, (z i).2⟫ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sub_right, real_inner_comm (z (finRotate m i)).1, real_inner_comm (z i).1]
  rw [this]
  linarith

/-- The two forms are equivalent. -/
theorem cycMon_iff_isCyclicallyMonotone {S : Set (E × E)} :
    CycMon S ↔ IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S :=
  ⟨isCyclicallyMonotone_of_cycMon, cycMon_of_isCyclicallyMonotone⟩

/-- Tau Ceti's quadratic cyclical monotonicity is invariant under exchanging the coordinates. -/
theorem isCyclicallyMonotone_swap {S : Set (E × E)}
    (hS : IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S) :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) (Prod.swap ⁻¹' S) := by
  rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le] at hS ⊢
  intro n x y hxy σ
  have h := hS n y x (fun i => hxy i) σ.symm
  have hre : ∑ i, ⟪y i, x (σ.symm i)⟫ = ∑ j, ⟪x j, y (σ j)⟫ := by
    rw [← Equiv.sum_comp σ (fun i => ⟪y i, x (σ.symm i)⟫)]
    simp [real_inner_comm]
  rw [hre] at h
  calc ∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪y i, x i⟫ := h
    _ = ∑ i, ⟪x i, y i⟫ := Finset.sum_congr rfl fun i _ => real_inner_comm _ _

/-- The paper's cyclical monotonicity is invariant under exchanging the coordinates. -/
theorem cycMon_swap {S : Set (E × E)} (hS : CycMon S) : CycMon (Prod.swap ⁻¹' S) :=
  cycMon_of_isCyclicallyMonotone (isCyclicallyMonotone_swap (isCyclicallyMonotone_of_cycMon hS))

/-- Cyclical monotonicity passes to subsets. -/
theorem cycMon_mono {S T : Set (E × E)} (hT : CycMon T) (hST : S ⊆ T) : CycMon S :=
  fun m z hz => hT m z fun i => hST (hz i)

/-- **Subdifferential graphs are cyclically monotone** (paper form): the pairs `(x, y)` with
`f x + ⟪y, x' − x⟫ ≤ f x'` for all `x'`. -/
theorem cycMon_subgradGraph (f : E → ℝ) :
    CycMon {z : E × E | ∀ x, f z.1 + ⟪z.2, x - z.1⟫ ≤ f x} := by
  intro m z hz
  have h : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤
      f (z (finRotate m i)).1 - f (z i).1 := fun i => by
    have := hz i (z (finRotate m i)).1
    linarith
  calc ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫
      ≤ ∑ i, (f (z (finRotate m i)).1 - f (z i).1) := Finset.sum_le_sum fun i _ => h i
    _ = 0 := by
      rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) (fun i => f (z i).1), sub_self]

end CM

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- A plan concentrated (a.e.) on a cyclically monotone set, measurable or not, is `CMConc`. -/
theorem cmConc_of_ae {π : Measure (E × E)} {S : Set (E × E)} (hS : CycMon S)
    (h : ∀ᵐ z ∂π, z ∈ S) : CMConc π := by
  refine ⟨(toMeasurable π Sᶜ)ᶜ, (measurableSet_toMeasurable π Sᶜ).compl,
    cycMon_mono hS (compl_subset_comm.1 (subset_toMeasurable π Sᶜ)), ?_⟩
  rw [compl_compl, measure_toMeasurable]
  exact ae_iff.1 h

/-- `CMConc` gives an a.e. statement in Tau Ceti's form. -/
theorem exists_isCyclicallyMonotone_of_cmConc {π : Measure (E × E)} (h : CMConc π) :
    ∃ S : Set (E × E), IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ∧
      ∀ᵐ z ∂π, z ∈ S := by
  obtain ⟨Γ, -, hΓ, hΓ0⟩ := h
  exact ⟨Γ, isCyclicallyMonotone_of_cycMon hΓ,
    (measure_eq_zero_iff_ae_notMem.1 hΓ0).mono fun _ h => Set.notMem_compl_iff.1 h⟩

end Measure

end StatFormal.OTFD.WaveL3
