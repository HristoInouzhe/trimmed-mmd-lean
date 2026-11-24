import StatFormal.Wave30tw.RouteCoupled

/-!
# Wave 30tw — route: the closed-form candidates, the full `τ_{n,m}` and the crossing set (untrusted proof material)

* `τ^A = βτ^A(0)`, `τ^P ≥ βD√(sL/2)` on `(0,1)`: continuous (Wave 30tu instance route) and `→ ∞` for `D > 0`.
* The full thresholds are minima of continuous candidates; `→ ∞` iff every candidate does, and with `D = 0` the closed form is `≡ 0`.
* `crossingFacts_of`: for `τ ≥ 0` nondecreasing on `[0,1)`, continuous on `(0,1)`, with `τ → ∞` when `φ` is not constant, every clause
  of `CrossingFacts` follows from the certified generic Wave 30tu `crossing`, `crossing_meas`, `alphaest_wellDefined`, `tauRight_spec`;
  a constant `φ` gives `D̂ ≡ 0` (Wave 30ts `Demp_le_zero`); an empty `𝒳` makes every clause vacuous.
-/

noncomputable section
open MeasureTheory Real Set Filter Topology

namespace StatFormal.Wave30tw

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30ts StatFormal.Wave30tp
open StatFormal.Wave30tu.Full

/-! ### The closed-form candidates -/

theorem tauA_tendsto {κ D δ : ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : Tendsto (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) (𝓝[<] 1) atTop := by
  have hs := sNM_pos hn hm
  have hL1 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set CA := 2 * κ * √(sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) +
    D * √(sNM n m * Real.log (1 / δ) / 2) with hCA
  have hCA0 : 0 < CA := by
    have h1 : 0 ≤ 2 * κ * √(sNM n m) := by positivity
    have h2 : 0 ≤ 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) :=
      mul_nonneg (by positivity) (add_nonneg (StatFormal.Wave30tu.Instance.ek_nonneg n)
        (StatFormal.Wave30tu.Instance.ek_nonneg m))
    have h3 : 0 < D * √(sNM n m * Real.log (1 / δ) / 2) := mul_pos hD (Real.sqrt_pos.2 (by positivity))
    linarith
  exact (StatFormal.Wave30tu.Instance.tendsto_one_div_one_sub.atTop_mul_const hCA0).congr fun α => by
    simp only [StatFormal.Wave30tr.tauA, hCA]

theorem tauP_tendsto {D v ρbar δ : ℝ} {n m : ℕ} (hD : 0 < D) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : Tendsto (fun α => tauP D v ρbar α δ n m) (𝓝[<] 1) atTop := by
  have hs := sNM_pos hn hm
  have hc := cNM_pos (m := m) hn
  have hL6 : 0 < Real.log (6 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set c₁ := D * √(sNM n m * Real.log (6 / δ) / 2) with hc₁
  have hc₁0 : 0 < c₁ := mul_pos hD (Real.sqrt_pos.2 (by positivity))
  refine tendsto_atTop_mono' _ ?_ (StatFormal.Wave30tu.Instance.tendsto_one_div_one_sub.atTop_mul_const hc₁0)
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α hα
  simp only [tauP, if_neg hα.1.ne', T1, T2]
  have e1 := Real.sqrt_nonneg (1 / (1 - α) * v ^ 2 * sNM n m)
  have e3 : 0 ≤ ρbar * (√(2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ)) + cNM n m * Real.log (6 / δ) / 3) :=
    mul_nonneg hρ (by positivity)
  have e5 : 1 / (1 - α) * c₁ = 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2) := by rw [hc₁]; ring
  linarith

theorem closed_candidates : Claims.closed_candidates := fun κ D v ρbar δ n m =>
  ⟨StatFormal.Wave30tu.Instance.tauA_continuousOn κ D δ n m, StatFormal.Wave30tu.Instance.tauP_continuousOn D v ρbar δ n m,
    fun hδ0 hδ1 hn hm hκ hD => tauA_tendsto hκ hD hδ0 hδ1 hn hm,
    fun hδ0 hδ1 hn hm hD hρ => tauP_tendsto hD hρ hδ0 hδ1 hn hm⟩

/-! ### The full `τ_{n,m}` -/

theorem tauP_degenerate {κ α δ : ℝ} {n m : ℕ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    tauP 0 (√(min (κ ^ 2) ((0 : ℝ) ^ 2 / 2))) 0 α δ n m = 0 := by
  have hmin : min (κ ^ 2) ((0 : ℝ) ^ 2 / 2) = 0 := by
    rw [show (0 : ℝ) ^ 2 / 2 = 0 by norm_num]; exact min_eq_right (sq_nonneg κ)
  simp only [tauP, if_neg hα.1.ne', T1, hmin, Real.sqrt_zero]
  simp

theorem tauFull_continuousOn {κ D δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : ContinuousOn (fun α => tauFull κ D α δ n m) (Ioo 0 1) :=
  (StatFormal.Wave30tu.Instance.tauA_continuousOn κ D δ n m).inf
    ((StatFormal.Wave30tu.Instance.tauP_continuousOn _ _ _ δ n m).inf
      (tauPs_continuousOn hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm))

theorem tauFullCpl_continuousOn {κ D δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : ContinuousOn (fun α => tauFullCpl κ D α δ n m) (Ioo 0 1) :=
  (StatFormal.Wave30tu.Instance.tauA_continuousOn κ D δ n m).inf
    ((StatFormal.Wave30tu.Instance.tauP_continuousOn _ _ _ δ n m).inf
      ((tauPs_continuousOn hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm).inf (tauCpl_continuousOn hD hδ0 hδ1 hn hm)))

theorem tauFullGrid_continuousOn {κ D δ : ℝ} {J : ℕ} {vg ρg : ℕ → ℝ} {n m : ℕ} (hD : 0 ≤ D)
    (hvρ : ∀ j < J, 0 ≤ vg j ∧ 0 ≤ ρg j) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ContinuousOn (fun α => tauFullGrid κ D vg ρg J α δ n m) (Ioo 0 1) :=
  (StatFormal.Wave30tu.Instance.tauA_continuousOn κ D δ n m).inf
    ((StatFormal.Wave30tu.Instance.tauP_continuousOn _ _ _ δ n m).inf
      ((tauPs_continuousOn hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm).inf (tauGrid_continuousOn hD hvρ hδ0 hδ1 hn hm)))

theorem tauFull_continuous : Claims.tauFull_continuous := fun _ _ _ _ _ hD hδ0 hδ1 hn hm =>
  ⟨tauFull_continuousOn hD hδ0 hδ1 hn hm, tauFullCpl_continuousOn hD hδ0 hδ1 hn hm,
    fun _ _ _ hvρ => tauFullGrid_continuousOn hD hvρ hδ0 hδ1 hn hm⟩

theorem tauFull_tendsto_iff {κ D δ : ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : Tendsto (fun α => tauFull κ D α δ n m) (𝓝[<] 1) atTop ↔ 0 < D := by
  constructor
  · intro ht
    by_contra hD0
    have hD0' : D = 0 := le_antisymm (not_lt.1 hD0) hD
    subst hD0'
    refine not_tendsto_of_le (C := 0) (fun α hα => ?_) ht
    unfold tauFull
    rw [tauP_degenerate hα]
    exact (min_le_right _ _).trans (min_le_left _ _)
  · intro hDp
    exact tendsto_min_atTop (tauA_tendsto hκ hDp hδ0 hδ1 hn hm) (tendsto_min_atTop (tauP_tendsto hDp hD hδ0 hδ1 hn hm)
      ((tauPs_tendsto_iff hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm).2 (Or.inl hDp)))

theorem tauFullCpl_tendsto_iff {κ D δ : ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : Tendsto (fun α => tauFullCpl κ D α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∧ 0 < κ) := by
  constructor
  · intro ht
    by_contra hc
    rcases not_and_or.1 hc with hD0 | hκ0
    · have hD0' : D = 0 := le_antisymm (not_lt.1 hD0) hD
      subst hD0'
      refine not_tendsto_of_le (C := 0) (fun α hα => ?_) ht
      unfold tauFullCpl
      rw [tauP_degenerate hα]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · have hκ0' : κ = 0 := le_antisymm (not_lt.1 hκ0) hκ
      refine not_tendsto_of_le (C := 0) (fun α hα => ?_) ht
      unfold tauFullCpl
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
      refine tauCpl_le le_rfl fun u hu => ?_
      exfalso
      have := hu.2
      rw [hκ0'] at this
      simp at this
      linarith [hu.1]
  · rintro ⟨hDp, hκp⟩
    exact tendsto_min_atTop (tauA_tendsto hκ hDp hδ0 hδ1 hn hm) (tendsto_min_atTop (tauP_tendsto hDp hD hδ0 hδ1 hn hm)
      (tendsto_min_atTop ((tauPs_tendsto_iff hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm).2 (Or.inl hDp))
        ((tauCpl_tendsto_iff hD hδ0 hδ1 hn hm).2 hκp.ne')))

theorem tauFullGrid_tendsto_iff {κ D δ : ℝ} {J : ℕ} {vg ρg : ℕ → ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hD : 0 ≤ D)
    (hvρ : ∀ j < J, 0 ≤ vg j ∧ 0 ≤ ρg j) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun α => tauFullGrid κ D vg ρg J α δ n m) (𝓝[<] 1) atTop ↔ (0 < D ∧ 0 < J) := by
  constructor
  · intro ht
    by_contra hc
    rcases not_and_or.1 hc with hD0 | hJ0
    · have hD0' : D = 0 := le_antisymm (not_lt.1 hD0) hD
      subst hD0'
      refine not_tendsto_of_le (C := 0) (fun α hα => ?_) ht
      unfold tauFullGrid
      rw [tauP_degenerate hα]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · have hJ : J = 0 := by omega
      subst hJ
      refine not_tendsto_of_le (C := 0) (fun α hα => ?_) ht
      unfold tauFullGrid
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
      simp [tauGrid]
  · rintro ⟨hDp, hJp⟩
    exact tendsto_min_atTop (tauA_tendsto hκ hDp hδ0 hδ1 hn hm) (tendsto_min_atTop (tauP_tendsto hDp hD hδ0 hδ1 hn hm)
      (tendsto_min_atTop ((tauPs_tendsto_iff hD (Real.sqrt_nonneg _) hD hδ0 hδ1 hn hm).2 (Or.inl hDp))
        ((tauGrid_tendsto_iff hD hvρ hδ0 hδ1 hn hm).2 ⟨0, hJp, Or.inl hDp⟩)))

theorem tauFull_tendsto : Claims.tauFull_tendsto := fun _ _ _ _ _ hκ hD hδ0 hδ1 hn hm =>
  ⟨tauFull_tendsto_iff hκ hD hδ0 hδ1 hn hm, tauFullCpl_tendsto_iff hκ hD hδ0 hδ1 hn hm,
    fun _ _ _ hvρ => tauFullGrid_tendsto_iff hκ hD hvρ hδ0 hδ1 hn hm⟩

/-! ### The crossing set -/

section Crossing

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem alphaHat_mem_Ico {Dh τ : ℝ → ℝ} (hne : (crossSet Dh τ).Nonempty) :
    0 ≤ alphaHat Dh τ ∧ alphaHat Dh τ < 1 := by
  obtain ⟨s, hs⟩ := hne
  exact ⟨Real.sInf_nonneg fun α hα => hα.1.1,
    (csInf_le ⟨0, fun α hα => hα.1.1⟩ hs).trans_lt hs.1.2⟩

theorem crossing_union_min : Claims.crossing_union_min := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm hnn hmono hcont hne a
  have h := (StatFormal.Wave30tu.crossing_meas 𝒳 H φ κ τ n m hφ hκ hn hm hnn hmono hcont hne).1 (min a 1)
  rw [← h]
  ext z
  simp only [mem_ofPred_eq, lt_min_iff]
  exact ⟨fun h1 => ⟨h1, (alphaHat_mem_Ico (hne z.1 z.2)).2⟩, fun h1 => h1.1⟩

theorem crossingFacts_empty {φ : 𝒳 → H} {κ : ℝ} {τ : ℝ → ℝ} {n m : ℕ} (hn : 1 ≤ n) (h𝒳 : IsEmpty 𝒳) :
    CrossingFacts φ κ n m τ := by
  have : IsEmpty ((Fin n → 𝒳) × (Fin m → 𝒳)) := ⟨fun z => isEmptyElim (z.1 ⟨0, by omega⟩)⟩
  refine ⟨fun x _ => isEmptyElim (x ⟨0, by omega⟩), fun a => ?_, Subsingleton.measurable⟩
  ext z
  exact isEmptyElim z

theorem crossingFacts_of {φ : 𝒳 → H} {κ : ℝ} {τ : ℝ → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hτ : Nonempty 𝒳 → (∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) ∧ MonotoneOn τ (Ico 0 1) ∧ ContinuousOn τ (Ioo 0 1) ∧
      ((∃ x₁ x₂ : 𝒳, φ x₁ ≠ φ x₂) → Tendsto τ (𝓝[<] 1) atTop)) :
    CrossingFacts φ κ n m τ := by
  rcases isEmpty_or_nonempty 𝒳 with h𝒳 | h𝒳
  · exact crossingFacts_empty hn h𝒳
  obtain ⟨x0⟩ := h𝒳
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  obtain ⟨hnn, hmono, hcont, htend⟩ := hτ ⟨x0⟩
  have hconst : (∀ x₁ x₂ : 𝒳, φ x₁ = φ x₂) → ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), ∀ α ∈ Ico (0 : ℝ) 1,
      Demp φ x y α = 0 := fun hc x y α hα => by
    have hD0 : ∀ x x', ‖φ x - φ x'‖ ≤ 0 := fun x x' => by rw [hc x x', sub_self, norm_zero]
    exact le_antisymm (Demp_le_zero hφ hD0 hα.1 hα.2 hn hm x y) (StatFormal.Wave30tl.Demp_nonneg φ x y α)
  have hfacts : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳),
      (crossSet (Demp φ x y) τ).Nonempty ∧ ∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ 2 * κ := fun x y => by
    by_cases hc : ∀ x₁ x₂ : 𝒳, φ x₁ = φ x₂
    · have h0 := hconst hc x y
      refine ⟨⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩, fun α hα => ?_⟩
      · rw [h0 0 ⟨le_rfl, zero_lt_one⟩]; exact hnn 0 ⟨le_rfl, zero_lt_one⟩
      · rw [h0 α hα]; linarith
    · push Not at hc
      obtain ⟨h1, h2⟩ := StatFormal.Wave30tu.alphaest_wellDefined 𝒳 H φ κ τ n m hφ hκ hn hm (htend hc) x y
      exact ⟨h2, h1⟩
  have hne : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳), (crossSet (Demp φ x y) τ).Nonempty := fun x y => (hfacts x y).1
  refine ⟨fun x y => ?_, fun a => crossing_union_min 𝒳 H φ κ τ n m hφ hκ hn hm hnn hmono hcont hne a,
    (StatFormal.Wave30tu.crossing_meas 𝒳 H φ κ τ n m hφ hκ hn hm hnn hmono hcont hne).2⟩
  obtain ⟨hpath, hIoo, hright, hS⟩ :=
    StatFormal.Wave30tu.crossing 𝒳 H φ κ τ n m hφ hκ hn hm hnn hmono hcont x y (hne x y)
  obtain ⟨ha0, ha1⟩ := alphaHat_mem_Ico (hne x y)
  refine ⟨hne x y, (hfacts x y).2, fun hc => ⟨hconst hc x y, ?_⟩, hpath, hIoo, hright, fun hpos =>
    ⟨(StatFormal.Wave30tu.tauRight_spec τ _ hnn hmono ha0 ha1).2.2 hpos hcont, hS hpos⟩⟩
  ext α
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [hconst hc x y α h]
  exact hnn α h

/-- `φ` not constant gives `D > 0` and `κ > 0`. -/
theorem consts_pos_of_nonconst {φ : 𝒳 → H} {κ D : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D)
    (h : ∃ x₁ x₂ : 𝒳, φ x₁ ≠ φ x₂) : 0 < D ∧ 0 < κ := by
  obtain ⟨x₁, x₂, h12⟩ := h
  refine ⟨(norm_pos_iff.2 (sub_ne_zero.2 h12)).trans_le (hD x₁ x₂), ?_⟩
  by_cases h1 : φ x₁ = 0
  · have h2 : φ x₂ ≠ 0 := fun h2 => h12 (h1.trans h2.symm)
    exact (norm_pos_iff.2 h2).trans_le (hκ x₂)
  · exact (norm_pos_iff.2 h1).trans_le (hκ x₁)

end Crossing

theorem crossing_full_cont : Claims.crossing_full_cont := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hφ hκ hD hδ0 hδ1 hn hm
  refine crossingFacts_of hφ hκ hn hm fun ⟨x0⟩ => ?_
  obtain ⟨hκ0, hD0⟩ := StatFormal.Wave30tu.Instance.consts_nonneg hκ hD x0
  obtain ⟨-, hmA, hnA⟩ := StatFormal.Wave30tr.tauA_scale κ D δ n m hκ0 hD0 hδ0 hδ1 hn hm
  obtain ⟨hmP, hnP⟩ := StatFormal.Wave30tp.plugin_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  obtain ⟨hmS, hnS⟩ := StatFormal.Wave30ts.sharp_tau_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  refine ⟨fun α hα => le_min (hnA α hα) (le_min (hnP α hα) (hnS α hα)), mono_min hmA (mono_min hmP hmS),
    tauFull_continuousOn hD0 hδ0 hδ1 hn hm, fun hc => ?_⟩
  exact (tauFull_tendsto_iff hκ0 hD0 hδ0 hδ1 hn hm).2 (consts_pos_of_nonconst hκ hD hc).1

theorem crossing_full_cpl : Claims.crossing_full_cpl := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hφ hκ hD hδ0 hδ1 hn hm
  refine crossingFacts_of hφ hκ hn hm fun ⟨x0⟩ => ?_
  obtain ⟨hκ0, hD0⟩ := StatFormal.Wave30tu.Instance.consts_nonneg hκ hD x0
  obtain ⟨-, hmA, hnA⟩ := StatFormal.Wave30tr.tauA_scale κ D δ n m hκ0 hD0 hδ0 hδ1 hn hm
  obtain ⟨hmP, hnP⟩ := StatFormal.Wave30tp.plugin_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  obtain ⟨hmS, hnS⟩ := StatFormal.Wave30ts.sharp_tau_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  have hmC := tauCpl_monotone (κ := κ) hD0 hδ0 hδ1 hn hm
  refine ⟨fun α hα => le_min (hnA α hα) (le_min (hnP α hα) (le_min (hnS α hα) (tauCpl_nonneg _ _ _ _ _ _))),
    mono_min hmA (mono_min hmP (mono_min hmS hmC)), tauFullCpl_continuousOn hD0 hδ0 hδ1 hn hm, fun hc => ?_⟩
  exact (tauFullCpl_tendsto_iff hκ0 hD0 hδ0 hδ1 hn hm).2 (consts_pos_of_nonconst hκ hD hc)

theorem crossing_full_grid : Claims.crossing_full_grid := by
  intro 𝒳 H _ _ _ _ _ φ κ D J vg ρg δ n m hφ hκ hD hJ hvρ hδ0 hδ1 hn hm
  refine crossingFacts_of hφ hκ hn hm fun ⟨x0⟩ => ?_
  obtain ⟨hκ0, hD0⟩ := StatFormal.Wave30tu.Instance.consts_nonneg hκ hD x0
  obtain ⟨-, hmA, hnA⟩ := StatFormal.Wave30tr.tauA_scale κ D δ n m hκ0 hD0 hδ0 hδ1 hn hm
  obtain ⟨hmP, hnP⟩ := StatFormal.Wave30tp.plugin_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  obtain ⟨hmS, hnS⟩ := StatFormal.Wave30ts.sharp_tau_monotone D _ D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  obtain ⟨hmG, hnG⟩ := tauGrid_monotone hD0 hvρ hδ0 hδ1 hn hm
  refine ⟨fun α hα => le_min (hnA α hα) (le_min (hnP α hα) (le_min (hnS α hα) (hnG α hα))),
    mono_min hmA (mono_min hmP (mono_min hmS hmG)), tauFullGrid_continuousOn hD0 hvρ hδ0 hδ1 hn hm, fun hc => ?_⟩
  exact (tauFullGrid_tendsto_iff hκ0 hD0 hvρ hδ0 hδ1 hn hm).2 ⟨(consts_pos_of_nonconst hκ hD hc).1, hJ⟩

end StatFormal.Wave30tw
