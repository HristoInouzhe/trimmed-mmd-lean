import StatFormal.Wave30tm.Statements
import StatFormal.Archive.TrimmedMMD.Impossible.Mixture

set_option linter.style.longLine false

/-!
# Wave 30tm — the two-cell block construction (untrusted proof file)

`[0,1)` is cut into `K` blocks of `2` cells (the archived `cellSet K 2`). For `σ : Fin K → Fin 2`, `P_σ = Qσ K 2 σ` is
uniform on the chosen cell of every block and `Q_σ = Qσ K 2 (flipσ σ)` is uniform on the other cell. Both have density `2`
on `[0,1]` and they are mutually singular, so `TV(P_σ, Q_σ) = 1`. The block variant of the paper's "uniformly random half
of the cells": one cell out of each pair, chosen independently.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatFormal.Wave30tm

open StatFormal.TrimmedMMD.Impossible

variable {K : ℕ}

/-- The other cell of every block. -/
def flipσ (σ : Fin K → Fin 2) : Fin K → Fin 2 := fun b => (σ b).rev

theorem density2_Qσ (hK : 0 < K) (σ : Fin K → Fin 2) : Density2 (Qσ K 2 σ) := by
  refine ⟨isProbabilityMeasure_Qσ hK two_pos σ, ?_⟩
  rw [Measure.le_iff]
  intro s hs
  rw [Qσ, Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hs,
    Measure.restrict_apply hs, smul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  gcongr
  exact (cellSet_subset σ).trans Ico_subset_Icc_self

theorem pos_of_mem_cellSet {L : ℕ} {σ : Fin K → Fin L} {y : ℝ} (hy : y ∈ cellSet K L σ) : 0 < K := by
  simp only [cellSet, mem_iUnion] at hy
  obtain ⟨b, -⟩ := hy
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) b.isLt

theorem rev_ne_self_two (c : Fin 2) : c.rev ≠ c := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_rev] at this
  omega

theorem disjoint_cellSet_flip (σ : Fin K → Fin 2) :
    Disjoint (cellSet K 2 σ) (cellSet K 2 (flipσ σ)) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  have hK := pos_of_mem_cellSet h1
  have hy := cellSet_subset σ h1
  rw [mem_cellSet_iff' hK two_pos σ hy] at h1
  rw [mem_cellSet_iff' hK two_pos _ hy] at h2
  simp only [flipσ] at h2
  rw [h1] at h2
  exact rev_ne_self_two _ h2

/-- The two laws are mutually singular: `TV(P_σ, Q_σ) ≥ 1` (the cell set separates them). -/
theorem one_le_tvDist_flip (hK : 0 < K) (σ : Fin K → Fin 2) :
    1 ≤ StatFormal.Distances.tvDist (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) := by
  have := isProbabilityMeasure_Qσ hK two_pos σ
  have := isProbabilityMeasure_Qσ hK two_pos (flipσ σ)
  have h := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := Qσ K 2 σ)
    (ν := Qσ K 2 (flipσ σ)) (measurableSet_cellSet σ)
  have h1 : (Qσ K 2 σ).real (cellSet K 2 σ) = 1 := by
    rw [measureReal_def, Qσ_apply_cellSet hK two_pos, ENNReal.toReal_one]
  have h2 : (Qσ K 2 (flipσ σ)).real (cellSet K 2 σ) = 0 := by
    rw [measureReal_def, Qσ, Measure.smul_apply, Measure.restrict_apply (measurableSet_cellSet σ),
      (disjoint_cellSet_flip σ).inter_eq, measure_empty, smul_zero, ENNReal.toReal_zero]
  rw [h1, h2, sub_zero, abs_one] at h
  exact h

/-- Product of the `Qσ` with coordinate-dependent choices: `∏_i Qσ(s i) (B) = L^{|ι|} λ^ι(B ∩ ∏_i cellSet(s i))`. -/
theorem pi_Qσ_apply_coord {ι : Type*} [Fintype ι] {L : ℕ} (hK : 0 < K) (hL : 0 < L)
    (s : ι → Fin K → Fin L) {B : Set (ι → ℝ)} (hB : MeasurableSet B) :
    Measure.pi (fun i => Qσ K L (s i)) B =
      (L : ℝ≥0∞) ^ Fintype.card ι * Measure.pi (fun _ : ι => (volume : Measure ℝ))
        (B ∩ univ.pi fun i => cellSet K L (s i)) := by
  have : ∀ i, IsProbabilityMeasure (Qσ K L (s i)) := fun i => isProbabilityMeasure_Qσ hK hL (s i)
  have h : Measure.pi (fun i => Qσ K L (s i)) = (L : ℝ≥0∞) ^ Fintype.card ι •
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict
        (univ.pi fun i => cellSet K L (s i)) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi ht),
      ← Set.pi_inter_distrib, Measure.pi_pi, smul_eq_mul]
    simp only [Qσ, Measure.smul_apply, Measure.restrict_apply (ht _), smul_eq_mul,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [h, Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]

/-- The count of `card_extensions` over an arbitrary finite index type. -/
theorem card_extensions_fintype {ι : Type*} [Fintype ι] {L : ℕ} (β : ι → Fin K)
    (hβ : Function.Injective β) (lam : ι → Fin L) :
    (Finset.univ.filter (fun σ : Fin K → Fin L => ∀ i, σ (β i) = lam i)).card =
      L ^ (K - Fintype.card ι) := by
  classical
  set e := Fintype.equivFin ι
  have h := card_extensions (β ∘ e.symm) (hβ.comp e.symm.injective) (lam ∘ e.symm)
  rw [← h]
  congr 1
  refine Finset.filter_congr fun σ _ => ?_
  constructor
  · intro H j; exact H _
  · intro H i; simpa using H (e i)

end StatFormal.Wave30tm
