import StatFormal.Archive.WaveP2c.Statements
import StatFormal.Archive.Wave21a.RouteTax

/-!
# Route (wave P2c): measure identities for `prop:tax`(b) (untrusted)

* `pi_conv_pi`: `(⊗_k μ_k) ∗ (⊗_k ν_k) = ⊗_k (μ_k ∗ ν_k)` on `Fin d → ℝ`;
* `map_conv_affine`: `(μ ∗ ν) ∘ A⁻¹ = (μ ∘ (s·)⁻¹) ∗ (ν ∘ A⁻¹)` for `A u = y + s u`;
* `klRef_restrict`: `KL(P ‖ ν|_K) = KL(P ‖ ν)` when `P(Kᶜ) = 0` (the paper's `KL`, no mass correction);
* `conv_finsum`: `G ∗ Σ_i c_i m_i = Σ_i c_i (G ∗ m_i)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Finset
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.WaveP2c

open StatFormal.RobustEquality (klRef)

theorem pi_conv_pi {d : ℕ} (μ ν : Fin d → Measure ℝ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, IsProbabilityMeasure (ν k)] :
    Measure.pi μ ∗ Measure.pi ν = Measure.pi fun k => μ k ∗ ν k := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d) μ ν
  rw [Measure.conv, ← hmp.map_eq, Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  have hf : (fun x : (Fin d → ℝ) × (Fin d → ℝ) => x.1 + x.2) ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)) =
      fun (w : Fin d → ℝ × ℝ) k => (fun p : ℝ × ℝ => p.1 + p.2) (w k) := by
    funext w k; rfl
  rw [hf]
  exact Measure.pi_map_pi (f := fun _ (p : ℝ × ℝ) => p.1 + p.2) (fun k => by fun_prop)

theorem map_conv_affine (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (y s : ℝ) :
    (μ ∗ ν).map (fun u => y + s * u) = (μ.map fun u => s * u) ∗ (ν.map fun u => y + s * u) := by
  rw [Measure.conv, Measure.conv, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_prod_map μ ν (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  ring

theorem klRef_restrict {E : Type*} [MeasurableSpace E] (P ν : Measure E) [IsProbabilityMeasure P]
    [IsFiniteMeasure ν] {K : Set E} (hK : MeasurableSet K) (hPK : P Kᶜ = 0) :
    klRef P (ν.restrict K) = klRef P ν := by
  unfold klRef
  by_cases hac : P ≪ ν
  · set f := P.rnDeriv ν with hf
    have hPw : P = ν.withDensity f := (Measure.withDensity_rnDeriv_eq P ν hac).symm
    have hPwK : P = (ν.restrict K).withDensity f := by
      ext A hA
      rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
      rw [← withDensity_apply _ (hA.inter hK), ← hPw]
      have h1 : P A = P (A ∩ K) + P (A \ K) := (measure_inter_add_sdiff A hK).symm
      have h2 : P (A \ K) = 0 := measure_mono_null (fun x hx => hx.2) hPK
      rw [h1, h2, add_zero]
    have hacK : P ≪ ν.restrict K := by rw [hPwK]; exact withDensity_absolutelyContinuous _ _
    have hrn : P.rnDeriv (ν.restrict K) =ᵐ[ν.restrict K] f := by
      have := Measure.rnDeriv_withDensity (ν.restrict K) (Measure.measurable_rnDeriv P ν)
      rw [← hPwK] at this
      exact this
    have hllr : llr P (ν.restrict K) =ᵐ[P] llr P ν := by
      filter_upwards [hacK.ae_le hrn] with x hx
      simp only [llr, hx, hf]
    have hint : Integrable (llr P (ν.restrict K)) P ↔ Integrable (llr P ν) P := integrable_congr hllr
    by_cases hi : Integrable (llr P ν) P
    · rw [if_pos ⟨hacK, hint.2 hi⟩, if_pos ⟨hac, hi⟩, integral_congr_ae hllr]
    · rw [if_neg (fun h => hi (hint.1 h.2)), if_neg (fun h => hi h.2)]
  · have hnK : ¬ P ≪ ν.restrict K := fun h => hac (h.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
    rw [if_neg (fun h => hnK h.1), if_neg (fun h => hac h.1)]

theorem conv_finsum {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E] {ι : Type*} (T : Finset ι)
    (G : Measure E) [IsFiniteMeasure G] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) (m : ι → Measure E)
    [∀ i, IsFiniteMeasure (m i)] :
    G ∗ (∑ i ∈ T, c i • m i) = ∑ i ∈ T, c i • (G ∗ m i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Measure.conv_zero]
  | insert j T hj ih =>
    have : IsFiniteMeasure (c j • m j) := by
      refine ⟨?_⟩; rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top (hc j).lt_top (measure_lt_top _ _)
    have : IsFiniteMeasure (∑ i ∈ T, c i • m i) := by
      refine ⟨?_⟩
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      exact ENNReal.sum_lt_top.2 fun i _ => by
        rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top (hc i).lt_top (measure_lt_top _ _)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Measure.conv_add, Measure.conv_smul_right, ih]

end StatFormal.WaveP2c
