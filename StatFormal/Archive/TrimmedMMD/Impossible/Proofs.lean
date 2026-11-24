import StatFormal.Archive.TrimmedMMD.Impossible.Mixture
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proofs — trimmed MMD: no assumption-free upper confidence bound for total variation

Proof of `Claims.impossible` (`supplement.tex:442-484`), with a block variant of the paper's
random-cell construction: `[0,1)` is cut into `K` blocks of `L` cells and, for
`σ : Fin K → Fin L`, `Qσ K L σ` is uniform on the union of the cells `σ b` of the blocks `b`
(`Cells.lean`). Then `TV(P₀, Qσ) ≥ 1 - 1/L`, and the uniform mixture over `σ` of `Qσ^m`
dominates `P₀^m` on the event that the `m` points fall in distinct blocks (`Mixture.lean`,
via the exact count of `Counting.lean`), whose complement has `P₀^m`-mass `≤ m²/K`.
Hence `Pr_{P₀,P₀}(Û ≥ 1 - 1/L) ≥ 1 - δ - m²/K`; let `K → ∞`, then `L → ∞` (continuity from
above).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.TrimmedMMD.Impossible

/-- Disintegration of `(μ ⊗ ν) ⊗ R` along the `ν` coordinate. -/
theorem prod_prod_apply_eq_lintegral {X Y Ξ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ξ] (μ : Measure X) (ν : Measure Y) (R : Measure Ξ) [SFinite μ] [SFinite ν]
    [SFinite R] {B : Set ((X × Y) × Ξ)} (hB : MeasurableSet B) :
    ((μ.prod ν).prod R) B = ∫⁻ y, ∫⁻ x, R (Prod.mk (x, y) ⁻¹' B) ∂μ ∂ν := by
  rw [Measure.prod_apply hB]
  exact lintegral_prod_symm (fun p : X × Y => R (Prod.mk p ⁻¹' B))
    (measurable_measure_prodMk_left hB).aemeasurable

theorem isProbabilityMeasure_dataLaw {Ξ : Type*} [MeasurableSpace Ξ] (n m : ℕ) (P Q : Measure ℝ)
    (R : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    IsProbabilityMeasure (dataLaw n m P Q R) := by
  unfold dataLaw; infer_instance

/-- The core quantitative step: `Pr_{P₀,P₀}(Û ≥ 1 - 1/L) ≥ 1 - δ - m²/K`. -/
theorem key_bound {n m : ℕ} {δ : ℝ} {Ξ : Type} [MeasurableSpace Ξ] {R : Measure Ξ}
    [IsProbabilityMeasure R] {U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hδ : 0 ≤ δ)
    (hU : Measurable U)
    (H : ∀ P Q : Measure ℝ, BddDensity01 P → BddDensity01 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z})
    {K L : ℕ} (hK : 0 < K) (hL : 0 < L) :
    1 - δ - (m : ℝ) * m / K ≤ (dataLaw n m (volume.restrict (Icc (0 : ℝ) 1))
      (volume.restrict (Icc (0 : ℝ) 1)) R).real {z | 1 - 1 / (L : ℝ) ≤ U z} := by
  set P₀ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hP₀
  set A := {z : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ | 1 - 1 / (L : ℝ) ≤ U z} with hAdef
  have hA : MeasurableSet A := measurableSet_le measurable_const hU
  set w : ℝ≥0∞ := ((L : ℝ≥0∞) ^ K)⁻¹ with hw
  -- each `Qσ` is covered, so `Pr(Aᶜ) ≤ δ`
  have hσ : ∀ σ : Fin K → Fin L, dataLaw n m P₀ (Qσ K L σ) R Aᶜ ≤ ENNReal.ofReal δ := by
    intro σ
    have := isProbabilityMeasure_Qσ hK hL σ
    have := isProbabilityMeasure_dataLaw n m P₀ (Qσ K L σ) R
    have h := H P₀ (Qσ K L σ) bddDensity01_P₀ (bddDensity01_Qσ hK hL σ)
    have hsub : {z | StatFormal.Distances.tvDist P₀ (Qσ K L σ) ≤ U z} ⊆ A :=
      fun z hz => (tvDist_Qσ hK hL σ).trans hz
    have h' := h.trans (measureReal_mono hsub)
    have hc := measureReal_add_measureReal_compl (μ := dataLaw n m P₀ (Qσ K L σ) R) hA
    rw [probReal_univ] at hc
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- disintegrate along the `Y` sample
  set Pn := Measure.pi fun _ : Fin n => P₀ with hPn
  set G : (Fin m → ℝ) → ℝ≥0∞ := fun y => ∫⁻ x, R (Prod.mk (x, y) ⁻¹' Aᶜ) ∂Pn with hG
  have hD : ∀ Q : Measure ℝ, IsProbabilityMeasure Q →
      dataLaw n m P₀ Q R Aᶜ = ∫⁻ y, G y ∂(Measure.pi fun _ : Fin m => Q) := by
    intro Q _
    exact prod_prod_apply_eq_lintegral _ _ _ hA.compl
  have hG1 : ∀ y, G y ≤ 1 := by
    intro y
    calc G y ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂Pn := lintegral_mono fun x => prob_le_one
      _ = 1 := by rw [lintegral_one, measure_univ]
  have hE := measurableSet_goodSet K m
  set P₀m := Measure.pi fun _ : Fin m => P₀ with hP₀m
  have hmain : dataLaw n m P₀ P₀ R Aᶜ ≤ ENNReal.ofReal δ + ENNReal.ofReal ((m : ℝ) * m / K) := by
    rw [hD P₀ inferInstance, ← lintegral_add_compl G hE]
    gcongr
    · calc ∫⁻ y in goodSet K m, G y ∂P₀m
          ≤ ∫⁻ y, G y ∂(∑ σ : Fin K → Fin L, w • Measure.pi (fun _ : Fin m => Qσ K L σ)) :=
            lintegral_mono' (restrict_goodSet_le_mixture hK hL) le_rfl
        _ = ∑ σ : Fin K → Fin L, w * dataLaw n m P₀ (Qσ K L σ) R Aᶜ := by
            rw [lintegral_finsetSum_measure]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [lintegral_smul_measure, smul_eq_mul,
              hD (Qσ K L σ) (isProbabilityMeasure_Qσ hK hL σ)]
        _ ≤ ∑ _σ : Fin K → Fin L, w * ENNReal.ofReal δ := by
            gcongr with σ; exact hσ σ
        _ = ENNReal.ofReal δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hw, Nat.cast_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast hL.ne'))
                (ENNReal.pow_ne_top (ENNReal.natCast_ne_top L)), one_mul]
    · calc ∫⁻ y in (goodSet K m)ᶜ, G y ∂P₀m ≤ ∫⁻ _y in (goodSet K m)ᶜ, (1 : ℝ≥0∞) ∂P₀m :=
            lintegral_mono fun y => hG1 y
        _ = P₀m (goodSet K m)ᶜ := by rw [lintegral_one, Measure.restrict_apply_univ]
        _ ≤ _ := pi_goodSet_compl_le hK
  have := isProbabilityMeasure_dataLaw n m P₀ P₀ R
  rw [← ENNReal.ofReal_add hδ (by positivity)] at hmain
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
  have hc := measureReal_add_measureReal_compl (μ := dataLaw n m P₀ P₀ R) hA
  rw [probReal_univ] at hc
  simp only [measureReal_def] at hc ⊢
  linarith

/-- Letting `K → ∞`: `Pr_{P₀,P₀}(Û ≥ 1 - 1/L) ≥ 1 - δ`. -/
theorem level_bound {n m : ℕ} {δ : ℝ} {Ξ : Type} [MeasurableSpace Ξ] {R : Measure Ξ}
    [IsProbabilityMeasure R] {U : ((Fin n → ℝ) × (Fin m → ℝ)) × Ξ → ℝ} (hδ : 0 ≤ δ)
    (hU : Measurable U)
    (H : ∀ P Q : Measure ℝ, BddDensity01 P → BddDensity01 Q →
      1 - δ ≤ (dataLaw n m P Q R).real {z | StatFormal.Distances.tvDist P Q ≤ U z})
    {L : ℕ} (hL : 0 < L) :
    1 - δ ≤ (dataLaw n m (volume.restrict (Icc (0 : ℝ) 1))
      (volume.restrict (Icc (0 : ℝ) 1)) R).real {z | 1 - 1 / (L : ℝ) ≤ U z} := by
  have ht : Tendsto (fun K : ℕ => 1 - δ - (m : ℝ) * m / K) atTop (𝓝 (1 - δ - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at ht
  refine le_of_tendsto ht (eventually_atTop.2 ⟨1, fun K hK => ?_⟩)
  exact key_bound hδ hU H (by omega) hL

theorem impossible : Claims.impossible := by
  intro n m δ Ξ _ R _ U _ _ hδ _ hU H
  set D := dataLaw n m (volume.restrict (Icc (0 : ℝ) 1)) (volume.restrict (Icc (0 : ℝ) 1)) R
  have := isProbabilityMeasure_dataLaw n m (volume.restrict (Icc (0 : ℝ) 1))
    (volume.restrict (Icc (0 : ℝ) 1)) R
  set s : ℕ → Set (((Fin n → ℝ) × (Fin m → ℝ)) × Ξ) :=
    fun L => {z | 1 - 1 / ((L : ℝ) + 1) ≤ U z} with hs
  have hanti : Antitone s := by
    intro L L' hLL' z hz
    simp only [hs, mem_ofPred_eq] at hz ⊢
    have : 1 / ((L' : ℝ) + 1) ≤ 1 / ((L : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hLL' 1)
    linarith
  have hinter : (⋂ L, s L) = {z | 1 ≤ U z} := by
    ext z
    simp only [hs, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      have ht : Tendsto (fun L : ℕ => 1 - 1 / ((L : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
      rw [sub_zero] at ht
      exact le_of_tendsto ht (Eventually.of_forall h)
    · intro h L
      have : 0 ≤ 1 / ((L : ℝ) + 1) := by positivity
      linarith
  have hmeas : ∀ L, NullMeasurableSet (s L) D :=
    fun L => (measurableSet_le measurable_const hU).nullMeasurableSet
  have hlim := hanti.measure_iInter hmeas ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hlim
  have hbound : ∀ L, ENNReal.ofReal (1 - δ) ≤ D (s L) := by
    intro L
    have h := level_bound (L := L + 1) hδ.le hU H (Nat.succ_pos L)
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    have : s L = {z | 1 - 1 / (((L + 1 : ℕ) : ℝ)) ≤ U z} := by
      simp only [hs]; push_cast; rfl
    rw [this]
    exact h
  have hfin : ENNReal.ofReal (1 - δ) ≤ D {z | 1 ≤ U z} := by
    rw [hlim]; exact le_iInf hbound
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)] at hfin
  exact hfin

end StatFormal.TrimmedMMD.Impossible
