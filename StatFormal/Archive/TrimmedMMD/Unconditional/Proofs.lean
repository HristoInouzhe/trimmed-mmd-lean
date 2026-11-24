import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Archive.TrimmedMMD.Concentration.Proofs
import StatFormal.Archive.TrimmedMMD.AlphaHat

/-!
# Proofs: the trimmed-MMD threshold estimator, unconditionally

* `events`: `cor:uniform` (`Concentration.uniform_alpha`) at level `δ/2` for each sample gives
  measurable `AP`, `AQ`; their cylinders have probability `≥ 1 − δ/2` under the product law
  (`Measure.prod_prod` with `univ`); and `|setDist(A',B') − setDist(A,B)| ≤ d_H(A,A') + d_H(B,B')`
  for nonempty bounded sets (`abs_setDist_sub_le`) turns the two region bounds into
  `|D̂_α − D_α| ≤ τ_{n,m}(α,δ)`.
* `consistency_i`, `consistency_i_zero`, `rate`: on `E = EP ∩ EQ` (measurable), the certified
  pathwise lemmas of `TrimmedMMD/AlphaHat.lean`; probability by the union bound (`prob_inter_ge`).
-/

noncomputable section
open MeasureTheory Set Metric

namespace StatFormal.TrimmedMMD.Unconditional

open StatFormal.TrimmedMMD.Concentration

/-! ### Set distance under Hausdorff perturbation -/

section SetDist

variable {H : Type*} [NormedAddCommGroup H]

theorem setDist_le_norm {A B : Set H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) :
    setDist A B ≤ ‖a - b‖ :=
  csInf_le ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩ ⟨a, ha, b, hb, rfl⟩

theorem setDist_le_setDist_add {A B A' B' : Set H} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA' : A'.Nonempty) (hB' : B'.Nonempty) (hfA : hausdorffEDist A A' ≠ ⊤)
    (hfB : hausdorffEDist B B' ≠ ⊤) :
    setDist A' B' ≤ setDist A B + hausdorffDist A A' + hausdorffDist B B' := by
  have key : ∀ a ∈ A, ∀ b ∈ B,
      setDist A' B' ≤ ‖a - b‖ + hausdorffDist A A' + hausdorffDist B B' := by
    intro a ha b hb
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 : infDist a A' < hausdorffDist A A' + ε / 2 :=
      lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem ha hfA) (by linarith)
    have h2 : infDist b B' < hausdorffDist B B' + ε / 2 :=
      lt_of_le_of_lt (infDist_le_hausdorffDist_of_mem hb hfB) (by linarith)
    obtain ⟨a', ha', hda⟩ := (infDist_lt_iff hA').1 h1
    obtain ⟨b', hb', hdb⟩ := (infDist_lt_iff hB').1 h2
    rw [dist_eq_norm] at hda hdb
    have htri : ‖a' - b'‖ ≤ ‖a - b‖ + ‖a - a'‖ + ‖b - b'‖ := by
      have : a' - b' = (a - b) - (a - a') + (b - b') := by abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le (a - b) (a - a')
      linarith
    linarith [setDist_le_norm ha' hb']
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hne : {r | ∃ a ∈ A, ∃ b ∈ B, r = ‖a - b‖}.Nonempty := ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩
  have : setDist A' B' - hausdorffDist A A' - hausdorffDist B B' ≤ setDist A B := by
    refine le_csInf hne ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    linarith [key a ha b hb]
  linarith

theorem abs_setDist_sub_le {A B A' B' : Set H} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA' : A'.Nonempty) (hB' : B'.Nonempty) (hbA : Bornology.IsBounded A)
    (hbB : Bornology.IsBounded B) (hbA' : Bornology.IsBounded A')
    (hbB' : Bornology.IsBounded B') :
    |setDist A' B' - setDist A B| ≤ hausdorffDist A A' + hausdorffDist B B' := by
  have hf1 := hausdorffEDist_ne_top_of_nonempty_of_bounded hA hA' hbA hbA'
  have hf2 := hausdorffEDist_ne_top_of_nonempty_of_bounded hB hB' hbB hbB'
  have hf1' := hausdorffEDist_ne_top_of_nonempty_of_bounded hA' hA hbA' hbA
  have hf2' := hausdorffEDist_ne_top_of_nonempty_of_bounded hB' hB hbB' hbB
  have h1 := setDist_le_setDist_add hA hB hA' hB' hf1 hf2
  have h2 := setDist_le_setDist_add hA' hB' hA hB hf1' hf2'
  rw [hausdorffDist_comm (s := A'), hausdorffDist_comm (s := B')] at h2
  rw [abs_le]; constructor <;> linarith

end SetDist

/-! ### Regions are nonempty and bounded -/

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem region_isBounded (Q : Measure 𝒳) [IsFiniteMeasure Q] {φ : 𝒳 → H} {κ α : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : Bornology.IsBounded (region φ α Q) := by
  refine (isBounded_closedBall (x := (0 : H)) (r := 1 / (1 - α) * κ * Q.real univ)).subset ?_
  rintro _ ⟨g, -, hgb, -, rfl⟩
  rw [mem_closedBall, dist_zero_right]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb x).1]
  exact mul_le_mul (hgb x).2 (hκ x) (norm_nonneg _) ((hgb x).1.trans (hgb x).2)

/-- The deterministic perturbation bound behind `events`. -/
theorem abs_Demp_sub_Dpop_le {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {φ : 𝒳 → H} {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n m : ℕ}
    (hn : n ≠ 0) (hm : m ≠ 0) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    |Demp φ x y α - Dpop φ P Q α| ≤
      hausdorffDist (region φ α (empirical x)) (region φ α P) +
        hausdorffDist (region φ α (empirical y)) (region φ α Q) := by
  haveI := isProbabilityMeasure_empirical hn x
  haveI := isProbabilityMeasure_empirical hm y
  have h := abs_setDist_sub_le (A := region φ α P) (B := region φ α Q)
    (A' := region φ α (empirical x)) (B' := region φ α (empirical y))
    (region_nonempty P hα0 hα1) (region_nonempty Q hα0 hα1)
    (region_nonempty _ hα0 hα1) (region_nonempty _ hα0 hα1)
    (region_isBounded P hκ) (region_isBounded Q hκ) (region_isBounded _ hκ)
    (region_isBounded _ hκ)
  rw [hausdorffDist_comm (s := region φ α P), hausdorffDist_comm (s := region φ α Q)] at h
  exact h

/-! ### The events -/

theorem exists_events {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ δ : ℝ}
    {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ (AP : Set (Fin n → 𝒳)) (AQ : Set (Fin m → 𝒳)), MeasurableSet AP ∧ MeasurableSet AQ ∧
      ENNReal.ofReal (1 - δ / 2) ≤
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) (Prod.fst ⁻¹' AP) ∧
      ENNReal.ofReal (1 - δ / 2) ≤
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) (Prod.snd ⁻¹' AQ) ∧
      ∀ z ∈ Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, ∀ α ∈ Ico (0 : ℝ) 1,
        |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ StatFormal.TrimmedMMD.tau κ α δ n m := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 < 1 := by linarith
  obtain ⟨AP, hAPm, hAPp, hAP⟩ := uniform_alpha 𝒳 H P φ κ (δ / 2) n hφ hκ hn hδ2 hδ21
  obtain ⟨AQ, hAQm, hAQp, hAQ⟩ := uniform_alpha 𝒳 H Q φ κ (δ / 2) m hφ hκ hm hδ2 hδ21
  refine ⟨AP, AQ, hAPm, hAQm, ?_, ?_, ?_⟩
  · rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAPp
  · rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hAQp
  · rintro z ⟨hz1, hz2⟩ α ⟨hα0, hα1⟩
    have h1 := hAP hz1 α hα0 hα1
    have h2 := hAQ hz2 α hα0 hα1
    refine (abs_Demp_sub_Dpop_le hκ hα0 hα1 (Nat.one_le_iff_ne_zero.1 hn)
      (Nat.one_le_iff_ne_zero.1 hm) z.1 z.2).trans ?_
    unfold StatFormal.TrimmedMMD.tau
    linarith

theorem events : Claims.events := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ _ hδ0 hδ1 hn hm
  obtain ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩ := exists_events P Q hφ hκ hδ0 hδ1 hn hm
  exact ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩

theorem consistency_i : Claims.consistency_i := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ αs n m hφ hκ _ hδ0 hδ1 hn hm hαs hD
  obtain ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩ := exists_events P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAPm).inter (measurable_snd hAQm),
    StatFormal.TrimmedMMD.prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ, fun z hz => ?_⟩
  exact StatFormal.TrimmedMMD.alphaHat_le_of_event hαs hD (hE z hz)

theorem consistency_i_zero : Claims.consistency_i_zero := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ _ hδ0 hδ1 hn hm hD
  obtain ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩ := exists_events P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAPm).inter (measurable_snd hAQm),
    StatFormal.TrimmedMMD.prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ, fun z hz => ?_⟩
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hle := StatFormal.TrimmedMMD.alphaHat_le_of_event h0 hD (hE z hz)
  have hge := StatFormal.TrimmedMMD.alphaHat_nonneg
    ⟨0, StatFormal.TrimmedMMD.mem_crossSet_of_event h0 hD (hE z hz)⟩
  exact le_antisymm hle hge

theorem rate : Claims.rate := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ αs n m om ε hφ hκ hκpos hδ0 hδ1 hn hm hαs hD hom hmar hε
    hωε
  obtain ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩ := exists_events P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAPm).inter (measurable_snd hAQm),
    StatFormal.TrimmedMMD.prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ, fun z hz => ?_⟩
  exact StatFormal.TrimmedMMD.rate_det hκpos hαs hD hom hmar hε hωε (hE z hz)

end StatFormal.TrimmedMMD.Unconditional
