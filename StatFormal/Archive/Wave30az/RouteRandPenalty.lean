import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.Wave30az.RouteDecay
import StatFormal.Archive.Wave8a.RouteSharp
import StatFormal.Archive.Wave30ao.Proofs

/-!
# Route — SB `prop:randpenalty` at `t = 1` for the printed entropic plan

`def:repair` gives finite entropies (certified `cost_finite_iff`); a version `T` of the barycentric projection exists
(certified `sharp_bary_exists`); the printed plan has `T_#R ≠ ν` (certified `sharp_printed`, `d ≥ 1`), hence by the
certified `sharp_condVar` some coordinate has `∫ Var[X₁ⁱ | X₀] ≠ 0`; each such integral is `E(X₁ⁱ − E[X₁ⁱ|X₀])² ≥ 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set TauCeti
open scoped ENNReal

namespace StatFormal.Wave30az

open StatFormal.Wave30ao (entCost IsPrintedPlan HasFiniteEnt)

local notation "Eu" d => EuclideanSpace ℝ (Fin d)

theorem randpenalty_printed_trace : Claims.randpenalty_printed_trace := by
  intro d ε R ν π hd hε _ _ hR2 hν2 hc hπ
  have := isProb_coupling hπ.1
  obtain ⟨hR, hν⟩ := ((StatFormal.Wave30ao.cost_finite_iff d ε R ν hε inferInstance inferInstance hR2 hν2).1).1 hc
  have hsh := StatFormal.Wave30ao.sharp_printed d ε R ν hε inferInstance inferInstance hR2 hν2 hR hν
  have hνm : HasFiniteMoment 2 ν := StatFormal.Wave30ao.hasFiniteMoment_of_int hν2
  obtain ⟨T, hT⟩ := StatFormal.Wave8a.sharp_bary_exists d R ν π hπ.1 hνm
  have hne : R.map T ≠ ν := hsh.2.2.2 hd π T hπ hT
  have hiff := StatFormal.Wave8a.sharp_condVar d R ν π T hπ.1 hνm hT
  have hnn : ∀ i : Fin d, 0 ≤ ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
      (fun p : (Eu d) × (Eu d) => p.2 i) π p ∂π := by
    intro i
    rw [StatFormal.Wave8a.integral_condVar_eq (StatFormal.Wave8a.fstSigma_le d)]
    exact integral_nonneg fun p => sq_nonneg _
  have hex : ∃ i : Fin d, ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
      (fun p : (Eu d) × (Eu d) => p.2 i) π p ∂π ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (hiff.2 h)
  obtain ⟨i, hi⟩ := hex
  calc (0 : ℝ) < ∫ p, condVar (MeasurableSpace.comap Prod.fst inferInstance)
        (fun p : (Eu d) × (Eu d) => p.2 i) π p ∂π := lt_of_le_of_ne (hnn i) (Ne.symm hi)
    _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)

theorem randpenalty_printed_one : Claims.randpenalty_printed_one := by
  intro ε R ν π hε _ _ hR2 hν2 hc hπ
  have h := randpenalty_printed_trace 1 ε R ν π one_pos hε inferInstance inferInstance hR2 hν2 hc hπ
  rwa [Fin.sum_univ_one] at h

end StatFormal.Wave30az
