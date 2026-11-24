import StatFormal.Wave30tl.RouteCrossing
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Wave 30tl — `cor:confset`, `cor:upperfs` (untrusted proof route)

The concentration event `E` is the certified-route `Unconditional.exists_events` (`cor:uniform` for each sample at `δ/2`, no
`κ > 0` needed) with the union bound `prob_inter_ge`. On `E`, `α̂ ≤ α*` (`D(α*) = 0` by the certified `zero_of_tv_le`, no (A3)),
`α̂` lies in the crossing set (`lem:crossing`), so `D(α̂) ≤ D̂(α̂) + τ(α̂) ≤ 2τ(α̂)`, and the margin at `ε = α* − α̂ ∈ [0, α*]` gives
`α* − α̂ ≤ ω^←(2τ(α̂))` (the route of the revised printed proof). The superseded `â` form follows by monotonicity of `τ` and `ω^←`.
`cor:upperfs`: the printed proof.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-! ### The generalized inverse -/

theorem omegaGen_bddAbove (ω : ℝ → ℝ) (u : ℝ) : BddAbove {e | e ∈ Icc (0 : ℝ) 1 ∧ ω e ≤ u} :=
  ⟨1, fun _ he => he.1.2⟩

theorem omegaGen_nonneg (ω : ℝ → ℝ) (u : ℝ) : 0 ≤ omegaGen ω u :=
  Real.sSup_nonneg fun _ he => he.1.1

theorem omegaGen_le_one (ω : ℝ → ℝ) (u : ℝ) : omegaGen ω u ≤ 1 :=
  Real.sSup_le (fun _ he => he.1.2) zero_le_one

theorem le_omegaGen {ω : ℝ → ℝ} {u e : ℝ} (he : e ∈ Icc (0 : ℝ) 1) (hωe : ω e ≤ u) : e ≤ omegaGen ω u :=
  le_csSup (omegaGen_bddAbove ω u) ⟨he, hωe⟩

theorem omegaGen_mono (ω : ℝ → ℝ) {u u' : ℝ} (h : u ≤ u') : omegaGen ω u ≤ omegaGen ω u' := by
  rcases Set.eq_empty_or_nonempty {e | e ∈ Icc (0 : ℝ) 1 ∧ ω e ≤ u} with he | he
  · unfold omegaGen; rw [he, Real.sSup_empty]; exact omegaGen_nonneg ω u'
  · exact csSup_le_csSup (omegaGen_bddAbove ω u') he fun e h' => ⟨h'.1, h'.2.trans h⟩

/-- For strictly increasing `ω` on `[0,1]` and `ε ∈ [0,1]`, `ω^←(ω ε) ≤ ε`. -/
theorem omegaGen_apply_le {ω : ℝ → ℝ} (hω : StrictMonoOn ω (Icc 0 1)) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    omegaGen ω (ω ε) ≤ ε :=
  csSup_le ⟨ε, hε, le_rfl⟩ fun e he => (hω.le_iff_le he.1 hε).1 he.2

theorem omegaGen_spec : Claims.omegaGen_spec := by
  intro ω hω hc h0
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hivt := intermediate_value_Icc (zero_le_one' ℝ) hc
    rw [h0] at hivt
    obtain ⟨e, he, rfl⟩ := hivt hu
    have heq : omegaGen ω (ω e) = e :=
      le_antisymm (omegaGen_apply_le hω he) (le_omegaGen he le_rfl)
    rw [heq]
    exact ⟨he, rfl⟩
  · have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    exact le_antisymm (omegaGen_le_one ω u) (le_omegaGen h1 hu)

/-! ### The concentration event -/

section Event

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem exists_event (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ δ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
      ∀ z ∈ E, ∀ α ∈ Ico (0 : ℝ) 1, |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ tau κ α δ n m := by
  obtain ⟨AP, AQ, hAPm, hAQm, hP, hQ, hE⟩ := exists_events P Q hφ hκ hδ0 hδ1 hn hm
  exact ⟨Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, (measurable_fst hAPm).inter (measurable_snd hAQm),
    prob_inter_ge hδ0 hδ1 (measurable_snd hAQm) hP hQ, hE⟩

theorem Dpop_tv_eq_zero (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (htv : StatFormal.Distances.tvDist P Q < 1) :
    Dpop φ P Q (StatFormal.Distances.tvDist P Q) = 0 :=
  StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P Q φ κ _ hφ hκ (StatFormal.Distances.tvDist_nonneg P Q) htv
    le_rfl

/-- Pathwise core on the event: `α̂ ≤ α*` and `α* ≤ α̂ + ω^←(2τ(α̂))`. -/
theorem core_onEvent (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ δ : ℝ}
    {ω : ℝ → ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (htv : StatFormal.Distances.tvDist P Q < 1) (hmar : KnownMargin φ P Q ω) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hz : ∀ α ∈ Ico (0 : ℝ) 1, |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ tau κ α δ n m) :
    alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) ≤ StatFormal.Distances.tvDist P Q ∧
      StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) +
        omegaGen ω (2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m) := by
  set T := StatFormal.Distances.tvDist P Q with hT
  set a := alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) with ha
  have hT0 : 0 ≤ T := StatFormal.Distances.tvDist_nonneg P Q
  have hTI : T ∈ Ico (0 : ℝ) 1 := ⟨hT0, htv⟩
  have hle : a ≤ T := alphaHat_le_of_event hTI (Dpop_tv_eq_zero P Q hφ hκ htv) hz
  refine ⟨hle, ?_⟩
  have hmem := alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm z.1 z.2
  rw [← ha] at hmem
  have hD : Dpop φ P Q a ≤ 2 * tau κ a δ n m := by
    have h1 := (abs_le.1 (hz a hmem.1)).1
    have h2 : Demp φ z.1 z.2 a ≤ tau κ a δ n m := hmem.2
    linarith
  have hε : T - a ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hmem.1.1]⟩
  have hmarg := hmar.2.2.2.2 (T - a) hε
  rw [sub_sub_cancel] at hmarg
  have hε1 : T - a ∈ Icc (0 : ℝ) 1 := ⟨hε.1, by linarith [hmem.1.1]⟩
  have := le_omegaGen hε1 (hmarg.trans hD)
  linarith

end Event

/-! ### Certified claims: `cor:confset` (superseded `â` form) -/

theorem aHat_wellDefined : Claims.aHat_wellDefined := by
  intro 𝒳 H _ _ _ _ _ φ κ δ ab ω n m hφ hκ hδ0 hδ1 hab0 hab1 hn hm x y
  have h0 : (0 : ℝ) ∈ {a | a ∈ Icc (0 : ℝ) ab ∧
      a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + omegaGen ω (2 * tau κ a δ n m)} :=
    ⟨⟨le_rfl, hab0⟩, add_nonneg (alphaHat_nonneg (crossSet_Demp_nonempty hκ hδ0 hδ1 hn hm x y))
      (omegaGen_nonneg _ _)⟩
  exact ⟨h0, isLUB_csSup ⟨0, h0⟩ ⟨ab, fun a ha => ha.1.2⟩⟩

theorem confset_crude : Claims.confset_crude := by
  intro 𝒳 H _ _ _ _ _ φ κ δ ab ω n m hφ hκ hδ0 hδ1 hab0 hab1 hn hm x y
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (x ⟨0, hn⟩)
  have h0 : (0 : ℝ) ∈ {a | a ∈ Icc (0 : ℝ) ab ∧
      a ≤ alphaHat (Demp φ x y) (fun α => tau κ α δ n m) + omegaGen ω (2 * tau κ a δ n m)} :=
    ⟨⟨le_rfl, hab0⟩, add_nonneg (alphaHat_nonneg (crossSet_Demp_nonempty hκ hδ0 hδ1 hn hm x y))
      (omegaGen_nonneg _ _)⟩
  refine csSup_le ⟨0, h0⟩ fun a ha => ha.2.trans ?_
  have := omegaGen_mono ω (by linarith [tau_mono hκ0 ha.1.2 hab1 δ n m] :
    2 * tau κ a δ n m ≤ 2 * tau κ ab δ n m)
  linarith

theorem confset : Claims.confset := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ ab ω n m hφ hκ htv hmar hδ0 hδ1 hab0 hab1 hn hm htvab
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨hle, hup⟩ := core_onEvent P Q hφ hκ htv hmar hδ0 hδ1 hn hm z (hE z hz)
  refine ⟨hle, ?_⟩
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (z.1 ⟨0, hn⟩)
  have hmono := omegaGen_mono ω (by linarith [tau_mono hκ0 hle htv δ n m] :
    2 * tau κ (alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) δ n m ≤
      2 * tau κ (StatFormal.Distances.tvDist P Q) δ n m)
  refine le_csSup ⟨ab, fun a ha => ha.1.2⟩ ⟨⟨StatFormal.Distances.tvDist_nonneg P Q, htvab⟩, ?_⟩
  linarith

/-! ### Certified claims: `cor:upperfs` -/

theorem alphaHi_bddBelow (ω Dc : ℝ → ℝ) :
    BddBelow ((fun α => α + omegaGen ω (Dc α)) '' Ico (0 : ℝ) 1) :=
  ⟨0, by rintro _ ⟨α, hα, rfl⟩; exact add_nonneg hα.1 (omegaGen_nonneg _ _)⟩

theorem alphaHi_isGLB : Claims.alphaHi_isGLB := by
  intro 𝒳 H _ _ _ _ _ φ κ δ ω n m hφ hκ hδ0 hδ1 hn hm x y
  exact isGLB_csInf ((nonempty_Ico.2 zero_lt_one).image _) (alphaHi_bddBelow _ _)

theorem upperfs_onEvent {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {ω : ℝ → ℝ} (hmar : KnownMargin φ P Q ω) (htv : StatFormal.Distances.tvDist P Q < 1) {Dc : ℝ → ℝ}
    (hDc : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Dc α) :
    StatFormal.Distances.tvDist P Q ≤ alphaHi ω Dc := by
  refine le_csInf ((nonempty_Ico.2 zero_lt_one).image _) ?_
  rintro _ ⟨α, hα, rfl⟩
  set T := StatFormal.Distances.tvDist P Q
  by_cases hTα : T ≤ α
  · linarith [omegaGen_nonneg ω (Dc α)]
  · push_neg at hTα
    have hε : T - α ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hα.1]⟩
    have hmarg := hmar.2.2.2.2 (T - α) hε
    rw [sub_sub_cancel] at hmarg
    have hε1 : T - α ∈ Icc (0 : ℝ) 1 := ⟨hε.1, by linarith [hα.1]⟩
    have := le_omegaGen hε1 (hmarg.trans (hDc α hα))
    linarith

theorem upperfs : Claims.upperfs := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  have hDc : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + tau κ α δ n m := fun α hα => by
    have := (abs_le.1 (hE z hz α hα)).1
    linarith
  exact ⟨hDc, upperfs_onEvent P Q hmar htv hDc⟩

end StatFormal.Wave30tl
