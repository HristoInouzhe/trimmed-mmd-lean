import StatFormal.Wave30tm.RouteMixture
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.longLine false

/-!
# Wave 30tm — assembly of `thm:impossible` (JMLR) (untrusted proof file)

For `K ≥ 1` and every `σ : Fin K → Fin 2`, the pair `(P_σ, Q_σ)` lies in `𝒫₂` with `TV = 1`, so
`Pr_{P_σ,Q_σ}(Û < 1) ≤ δ`. Index the data by `Fin n ⊕ Fin m` (`measurePreserving_sumPiEquivProdPi`) and disintegrate
along the data: on the event that the `n + m` points fall in distinct blocks the uniform mixture over `σ` dominates
`P_u^{n+m}` (`RouteMixture`), and the complement has mass `≤ (n+m)²/K`. Hence
`Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ − (n+m)²/K`; let `K → ∞`. (Paper: `M` cells, a uniformly random half `S`, TV bound
between the mixture and the product of uniforms; here one cell of each pair, chosen independently, and one-sided
domination instead of a TV bound.)
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30tm

open StatFormal.TrimmedMMD.Impossible

theorem isProbabilityMeasure_dataLaw2 {Ξ : Type*} [MeasurableSpace Ξ] (n m : ℕ) (P Q : Measure ℝ)
    (R : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    IsProbabilityMeasure (dataLaw n m P Q R) := by
  unfold dataLaw; infer_instance

theorem sigmaFinite_sumElim (P Q : Measure ℝ) [SigmaFinite P] [SigmaFinite Q] {n m : ℕ} :
    ∀ i : Fin n ⊕ Fin m, SigmaFinite (Sum.elim (fun _ => P) (fun _ => Q) i) := by
  intro i
  rcases i with i | i
  · exact inferInstanceAs (SigmaFinite P)
  · exact inferInstanceAs (SigmaFinite Q)

/-- Disintegration of `dataLaw` along the data, with the `n + m` observations indexed by `Fin n ⊕ Fin m`. -/
theorem dataLaw_apply_eq_lintegral_pi {n m : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (R : Measure Ξ)
    [IsProbabilityMeasure R] (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {B : Set (((Fin n → ℝ) × (Fin m → ℝ)) × Ξ)} (hB : MeasurableSet B) :
    dataLaw n m P Q R B = ∫⁻ z, R (Prod.mk (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin n ⊕ Fin m => ℝ) z) ⁻¹' B)
      ∂(Measure.pi (Sum.elim (fun _ => P) (fun _ => Q))) := by
  have := sigmaFinite_sumElim P Q (n := n) (m := m)
  unfold dataLaw
  rw [Measure.prod_apply hB]
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin m => ℝ)
    (Sum.elim (fun _ => P) (fun _ => Q))
  exact (hmp.lintegral_comp (measurable_measure_prodMk_left hB)).symm

/-- The core quantitative step: `Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ − (n+m)²/K`. -/
theorem key_bound2 {n m : ℕ} {δ : ℝ} {Ξ : Type} [MeasurableSpace Ξ] {R : Measure Ξ}
    [IsProbabilityMeasure R] {U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hδ : 0 ≤ δ)
    (hU : Measurable U)
    (H : ∀ P Q : Measure ℝ, Density2 P → Density2 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z})
    {K : ℕ} (hK : 0 < K) :
    1 - δ - (Fintype.card (Fin n ⊕ Fin m) : ℝ) * Fintype.card (Fin n ⊕ Fin m) / K ≤
      (dataLaw n m (volume.restrict (Icc (0 : ℝ) 1))
        (volume.restrict (Icc (0 : ℝ) 1)) R).real {z | 1 ≤ U z} := by
  set P₀ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hP₀
  set A := {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 ≤ U z} with hAdef
  have hA : MeasurableSet A := measurableSet_le measurable_const hU
  set w : ℝ≥0∞ := ((((2 : ℕ) : ℝ≥0∞)) ^ K)⁻¹ with hw
  -- each `(P_σ, Q_σ)` is covered and has `TV = 1`, so `Pr(Aᶜ) ≤ δ`
  have hσ : ∀ σ : Fin K → Fin 2,
      dataLaw n m (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) R Aᶜ ≤ ENNReal.ofReal δ := by
    intro σ
    have := isProbabilityMeasure_Qσ hK two_pos σ
    have := isProbabilityMeasure_Qσ hK two_pos (flipσ σ)
    have := isProbabilityMeasure_dataLaw2 n m (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) R
    have h := H _ _ (density2_Qσ hK σ) (density2_Qσ hK (flipσ σ))
    have hsub : {z | StatFormal.Distances.tvDist (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) ≤ U z} ⊆ A :=
      fun z hz => (one_le_tvDist_flip hK σ).trans hz
    have h' := h.trans (measureReal_mono hsub)
    have hc := measureReal_add_measureReal_compl
      (μ := dataLaw n m (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) R) hA
    rw [probReal_univ] at hc
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- disintegrate along the data
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ) with he
  set G : (Fin n ⊕ Fin m → ℝ) → ℝ≥0∞ := fun z => R (Prod.mk (e z) ⁻¹' Aᶜ) with hG
  have hG1 : ∀ z, G z ≤ 1 := fun z => prob_le_one
  have hEm := measurableSet_goodSetι K (Fin n ⊕ Fin m)
  set Pι := Measure.pi fun _ : Fin n ⊕ Fin m => P₀ with hPι
  have hD₀ : dataLaw n m P₀ P₀ R Aᶜ = ∫⁻ z, G z ∂Pι := by
    rw [dataLaw_apply_eq_lintegral_pi R P₀ P₀ hA.compl]
    have hP : (Sum.elim (fun _ => P₀) (fun _ => P₀) : Fin n ⊕ Fin m → Measure ℝ) = fun _ => P₀ := by
      funext i; rcases i with i | i <;> rfl
    rw [hP]
  have hDσ : ∀ σ : Fin K → Fin 2, dataLaw n m (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) R Aᶜ =
      ∫⁻ z, G z ∂(Measure.pi fun i : Fin n ⊕ Fin m => Qσ K 2 (sig σ i)) := by
    intro σ
    have := isProbabilityMeasure_Qσ hK two_pos σ
    have := isProbabilityMeasure_Qσ hK two_pos (flipσ σ)
    rw [dataLaw_apply_eq_lintegral_pi R _ _ hA.compl]
    have hP : (Sum.elim (fun _ => Qσ K 2 σ) (fun _ => Qσ K 2 (flipσ σ)) :
        Fin n ⊕ Fin m → Measure ℝ) = fun i => Qσ K 2 (sig σ i) := by
      funext i; rcases i with i | i <;> rfl
    rw [hP]
  have hmain : dataLaw n m P₀ P₀ R Aᶜ ≤ ENNReal.ofReal δ +
      ENNReal.ofReal ((Fintype.card (Fin n ⊕ Fin m) : ℝ) * Fintype.card (Fin n ⊕ Fin m) / K) := by
    rw [hD₀, ← lintegral_add_compl G hEm]
    gcongr
    · calc ∫⁻ z in goodSetι K (Fin n ⊕ Fin m), G z ∂Pι
          ≤ ∫⁻ z, G z ∂(∑ σ : Fin K → Fin 2,
              w • Measure.pi (fun i : Fin n ⊕ Fin m => Qσ K 2 (sig σ i))) :=
            lintegral_mono' (restrict_goodSetι_le_mixture hK) le_rfl
        _ = ∑ σ : Fin K → Fin 2, w * dataLaw n m (Qσ K 2 σ) (Qσ K 2 (flipσ σ)) R Aᶜ := by
            rw [lintegral_finsetSum_measure]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [lintegral_smul_measure, smul_eq_mul, hDσ σ]
        _ ≤ ∑ _σ : Fin K → Fin 2, w * ENNReal.ofReal δ := by
            gcongr with σ; exact hσ σ
        _ = ENNReal.ofReal δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hw, Nat.cast_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero _ (by norm_num))
                (ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2)), one_mul]
    · calc ∫⁻ z in (goodSetι K (Fin n ⊕ Fin m))ᶜ, G z ∂Pι
          ≤ ∫⁻ _z in (goodSetι K (Fin n ⊕ Fin m))ᶜ, (1 : ℝ≥0∞) ∂Pι :=
            lintegral_mono fun z => hG1 z
        _ = Pι (goodSetι K (Fin n ⊕ Fin m))ᶜ := by rw [lintegral_one, Measure.restrict_apply_univ]
        _ ≤ _ := pi_goodSetι_compl_le hK
  have := isProbabilityMeasure_dataLaw2 n m P₀ P₀ R
  rw [← ENNReal.ofReal_add hδ (by positivity)] at hmain
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
  have hc := measureReal_add_measureReal_compl (μ := dataLaw n m P₀ P₀ R) hA
  rw [probReal_univ] at hc
  simp only [measureReal_def] at hc ⊢
  linarith

theorem impossible_route : Claims.impossible := by
  intro n m δ Ξ _ R _ U _ _ hδ _ hU H
  set N : ℕ := Fintype.card (Fin n ⊕ Fin m)
  have ht : Tendsto (fun K : ℕ => 1 - δ - (N : ℝ) * N / K) atTop (𝓝 (1 - δ - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at ht
  refine le_of_tendsto ht (eventually_atTop.2 ⟨1, fun K hK => ?_⟩)
  exact key_bound2 hδ.le hU H (by omega)

theorem bddDensity01_of_density2 {P : Measure ℝ} (h : Density2 P) : BddDensity01 P :=
  ⟨h.1, 2, by simpa using h.2⟩

theorem impossible_implies_archived_route : Claims.impossible_implies_archived := by
  intro h n m δ Ξ _ R _ U hn hm hδ hδ1 hU H
  exact h n m δ Ξ R U hn hm hδ hδ1 hU fun P Q hP hQ =>
    H P Q (bddDensity01_of_density2 hP) (bddDensity01_of_density2 hQ)

end StatFormal.Wave30tm
