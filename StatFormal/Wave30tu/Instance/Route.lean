import StatFormal.Wave30tu.Instance.Statements
import StatFormal.Wave30tu.RouteConsistency
import StatFormal.Wave30tu.RouteRatecond
import StatFormal.Wave30tp.Proofs
import StatFormal.Wave30tr.Proofs

/-!
# Wave 30tu, instance — the paper's thresholds (untrusted proof route)

* `τ^P` valid, nonnegative and nondecreasing: the certified Wave 30tp `plugin_level_explicit`, `plugin_monotone`; continuous on
  `(0,1)`, where it is `T₁ + ρ̄T₂`; `≥ βD√(sL/2)` there.
* `τ^A`: the certified Wave 30tr `thmA` (events `E⁺`, `E⁻` per pair), `tauA_scale` (nonnegative, nondecreasing, `= βτ^A(0)`),
  `thmA_compare` (`≤ r_n + r_m` for `D ≤ 2κ`); valid by the certified Wave 30tu `upper_valid`.
* The minimum of two valid thresholds is valid (deterministic thresholds: the minimum is one of them at each `α`); the printed results
  are the certified Wave 30tu claims applied to these.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu.Instance

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl StatFormal.Wave30tu
open StatFormal.Wave30tp StatFormal.Wave30tr

section Thresholds

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem consts_nonneg {φ : 𝒳 → H} {κ D : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (x0 : 𝒳) :
    0 ≤ κ ∧ 0 ≤ D :=
  ⟨(norm_nonneg _).trans (hκ x0), (norm_nonneg _).trans (hD x0 x0)⟩

theorem valid_min {φ : 𝒳 → H} {n m : ℕ} {δ : ℝ} {τ₁ τ₂ : ℝ → ℝ} (h1 : ValidThreshold φ n m δ τ₁)
    (h2 : ValidThreshold φ n m δ τ₂) : ValidThreshold φ n m δ (fun α => min (τ₁ α) (τ₂ α)) := by
  refine ⟨fun α hα => le_min (h1.1 α hα) (h2.1 α hα),
    fun a ha b hb hab => min_le_min (h1.2.1 ha hb hab) (h2.2.1 ha hb hab), fun α hα P' Q' hP' hQ' htv => ?_⟩
  rcases min_choice (τ₁ α) (τ₂ α) with h | h
  · simp only [h]; exact h1.2.2 α hα P' Q' hP' hQ' htv
  · simp only [h]; exact h2.2.2 α hα P' Q' hP' hQ' htv

theorem tauP_valid {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (x0 : 𝒳) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ValidThreshold φ n m δ (fun α => tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m) := by
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨hmono, hnn⟩ :=
    plugin_monotone D (√(min (κ ^ 2) (D ^ 2 / 2))) D δ n m hD0 (Real.sqrt_nonneg _) hD0 hδ0 hδ1 hn hm
  refine ⟨hnn, hmono, fun α hα P' Q' hP' hQ' htv => ?_⟩
  haveI := hP'
  haveI := hQ'
  exact plugin_level_explicit 𝒳 H φ κ D P' Q' α δ n m hφ hκ hD hα.1 hα.2 hδ0 hδ1 hn hm htv

variable [TopologicalSpace.SeparableSpace H]

theorem tauA_valid {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (x0 : 𝒳) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ValidThreshold φ n m δ (fun α => tauA κ D α δ n m) := by
  obtain ⟨hκ0, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨-, hmono, hnn⟩ := StatFormal.Wave30tr.tauA_scale κ D δ n m hκ0 hD0 hδ0 hδ1 hn hm
  refine StatFormal.Wave30tu.upper_valid 𝒳 H φ κ δ _ n m hφ hκ hδ0 hδ1 hn hm hnn hmono fun P' Q' hP' hQ' => ?_
  haveI := hP'
  haveI := hQ'
  obtain ⟨Ep, Em, hEpm, hEpp, -, -, hEp, -⟩ := StatFormal.Wave30tr.thmA 𝒳 H φ κ D P' Q' δ n m hφ hκ hD hδ0 hδ1 hn hm
  exact ⟨Ep, hEpm, hEpp, fun z hz α hα => (hEp z hz α hα).1⟩

theorem tauA_lower (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ D δ : ℝ}
    {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    UpperTool φ P Q n m δ (fun α => tauA κ D α δ n m) ∧ LowerTool φ P Q n m δ (fun α => tauA κ D α δ n m) := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  obtain ⟨hκ0, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨-, hmono, hnn⟩ := StatFormal.Wave30tr.tauA_scale κ D δ n m hκ0 hD0 hδ0 hδ1 hn hm
  obtain ⟨Ep, Em, hEpm, hEpp, hEmm, hEmp, hEp, hEm⟩ :=
    StatFormal.Wave30tr.thmA 𝒳 H φ κ D P Q δ n m hφ hκ hD hδ0 hδ1 hn hm
  exact ⟨⟨Ep, hEpm, hEpp, fun z hz α hα => (hEp z hz α hα).1⟩, hnn, hmono, Em, hEmm, hEmp, hEm⟩

end Thresholds

theorem one_div_one_sub_continuousOn : ContinuousOn (fun α : ℝ => 1 / (1 - α)) (Ioo 0 1) :=
  continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun α hα => sub_ne_zero.2 (ne_of_gt hα.2)

theorem tauP_continuousOn (D v ρ δ : ℝ) (n m : ℕ) : ContinuousOn (fun α => tauP D v ρ α δ n m) (Ioo 0 1) := by
  have heq : EqOn (fun α => T1 D v α δ n m + ρ * T2 α δ n m) (fun α => tauP D v ρ α δ n m) (Ioo 0 1) :=
    fun α hα => by simp only [tauP, if_neg hα.1.ne']
  refine ContinuousOn.congr ?_ heq.symm
  have hb := one_div_one_sub_continuousOn
  have h1 : ContinuousOn (fun α => √(1 / (1 - α) * v ^ 2 * sNM n m)) (Ioo 0 1) :=
    Real.continuous_sqrt.comp_continuousOn ((hb.mul continuousOn_const).mul continuousOn_const)
  have h2 : ContinuousOn (fun α => 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2)) (Ioo 0 1) :=
    (hb.mul continuousOn_const).mul continuousOn_const
  have h3 : ContinuousOn (fun α => √(2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ))) (Ioo 0 1) :=
    Real.continuous_sqrt.comp_continuousOn
      (((continuousOn_const.mul (hb.sub continuousOn_const)).mul continuousOn_const).mul continuousOn_const)
  exact (h1.add h2).add (continuousOn_const.mul (h3.add continuousOn_const))

theorem tauA_continuousOn (κ D δ : ℝ) (n m : ℕ) : ContinuousOn (fun α => tauA κ D α δ n m) (Ioo 0 1) :=
  one_div_one_sub_continuousOn.mul continuousOn_const

theorem ek_nonneg (k : ℕ) : 0 ≤ ek k := by
  unfold ek
  refine div_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (Nat.cast_nonneg _)

theorem sNM_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < sNM n m := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : (0 : ℝ) < m := by exact_mod_cast hm
  unfold sNM; positivity

theorem cNM_pos {n m : ℕ} (hn : 1 ≤ n) : 0 < cNM n m := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cNM; exact lt_max_of_lt_left (by positivity)

theorem tendsto_one_div_one_sub : Tendsto (fun α : ℝ => 1 / (1 - α)) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun α : ℝ => 1 - α) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact mem_Ioi.2 (sub_pos.2 (mem_Iio.1 hα))
  exact (tendsto_inv_nhdsGT_zero.comp h1).congr fun α => by simp

theorem tauNM_tendsto {κ D δ : ℝ} {n m : ℕ} (hκ0 : 0 ≤ κ) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : Tendsto (fun α => tauNM κ D α δ n m) (𝓝[<] 1) atTop := by
  have hs := sNM_pos hn hm
  have hc := cNM_pos (m := m) hn
  have hL6 : 0 < Real.log (6 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hL1 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set c₁ := D * √(sNM n m * Real.log (6 / δ) / 2)
  have hc₁ : 0 < c₁ := mul_pos hD (Real.sqrt_pos.2 (by positivity))
  set CA := 2 * κ * √(sNM n m) + 2 * κ * (ek n + ek m) + D * √(sNM n m * Real.log (1 / δ) / 2)
  have hCA : 0 < CA := by
    have h1 : 0 ≤ 2 * κ * √(sNM n m) := by positivity
    have h2 : 0 ≤ 2 * κ * (ek n + ek m) := mul_nonneg (by positivity) (add_nonneg (ek_nonneg n) (ek_nonneg m))
    have h3 : 0 < D * √(sNM n m * Real.log (1 / δ) / 2) := mul_pos hD (Real.sqrt_pos.2 (by positivity))
    linarith
  set c₀ := min c₁ CA
  have hc₀ : 0 < c₀ := lt_min hc₁ hCA
  have hlim := tendsto_one_div_one_sub.atTop_mul_const hc₀
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α hα
  have hβ : 0 < 1 / (1 - α) := one_div_pos.2 (by linarith [hα.2])
  have hP : 1 / (1 - α) * c₀ ≤ tauP D (√(min (κ ^ 2) (D ^ 2 / 2))) D α δ n m := by
    simp only [tauP, if_neg hα.1.ne', T1, T2]
    have e1 := Real.sqrt_nonneg (1 / (1 - α) * √(min (κ ^ 2) (D ^ 2 / 2)) ^ 2 * sNM n m)
    have e2 := Real.sqrt_nonneg (2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ))
    have e3 : 0 ≤ D * (√(2 * (1 / (1 - α) - 1) * sNM n m * Real.log (6 / δ)) + cNM n m * Real.log (6 / δ) / 3) :=
      mul_nonneg hD.le (by positivity)
    have e4 : 1 / (1 - α) * c₀ ≤ 1 / (1 - α) * c₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) hβ.le
    have e5 : 1 / (1 - α) * c₁ = 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2) := by simp only [c₁]; ring
    linarith
  have hA : 1 / (1 - α) * c₀ ≤ tauA κ D α δ n m := by
    simp only [tauA]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le
  exact le_min hP hA

/-! ### Certified claims -/

theorem tauNM_threshold : Claims.tauNM_threshold := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hne hφ hκ hD hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := hne
  obtain ⟨hκ0, -⟩ := consts_nonneg hκ hD x0
  refine ⟨valid_min (tauP_valid hφ hκ hD x0 hδ0 hδ1 hn hm) (tauA_valid hφ hκ hD x0 hδ0 hδ1 hn hm),
    ContinuousOn.inf (tauP_continuousOn _ _ _ _ n m) (tauA_continuousOn _ _ _ n m), fun hDpos => tauNM_tendsto hκ0 hDpos hδ0 hδ1 hn hm,
    fun α _ => min_le_right _ _⟩

theorem tauNM_oneevent : Claims.tauNM_oneevent := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ n m hφ hκ hD hδ0 hδ1 hn hm
  have hv := (tauNM_threshold 𝒳 H φ κ D δ n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hδ0 hδ1 hn hm).1
  by_cases htv : StatFormal.Distances.tvDist P Q < 1
  · obtain ⟨hmeas, hprob, hz⟩ := StatFormal.Wave30tu.oneevent 𝒳 H P Q φ κ δ _ n m hφ hκ hδ0 hδ1 hn hm hv htv
    exact ⟨_, hmeas, hprob, fun z hzE α hα htα => hz z hzE α ⟨htα, hα.2⟩⟩
  · refine ⟨univ, MeasurableSet.univ, by rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith),
      fun z _ α hα htα => absurd (htα.trans_lt hα.2) htv⟩

theorem tauA_tool : Claims.tauA_tool := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ n m hφ hκ hD hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  obtain ⟨hU, hL⟩ := tauA_lower P Q hφ hκ hD hδ0 hδ1 hn hm
  exact ⟨hU, hL, fun h2κ α hα =>
    StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm⟩

section Inst

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem tauNM_valid' (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) : ValidThreshold φ n m δ (fun α => tauNM κ D α δ n m) :=
  (tauNM_threshold 𝒳 H φ κ D δ n m (nonempty_of_isProbabilityMeasure P) hφ hκ hD hδ0 hδ1 hn hm).1

theorem tauNM_le_tau (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ D δ : ℝ} {n m : ℕ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (h2κ : D ≤ 2 * κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ α ∈ Ico (0 : ℝ) 1, tauA κ D α δ n m ≤ tau κ α δ n m) ∧
      ∀ α ∈ Ico (0 : ℝ) 1, tauNM κ D α δ n m ≤ tau κ α δ n m := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  obtain ⟨-, hD0⟩ := consts_nonneg hκ hD x0
  have h := fun α (hα : α ∈ Ico (0 : ℝ) 1) =>
    StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm
  exact ⟨h, fun α hα => (min_le_right _ _).trans (h α hα)⟩

end Inst

theorem consistency_i_inst : Claims.consistency_i_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ n m hφ hκ hD htv hδ0 hδ1 hn hm
  exact StatFormal.Wave30tu.consistency_i 𝒳 H P Q φ κ δ _ n m hφ hκ htv hδ0 hδ1 hn hm
    (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm)

theorem consistency_ii_inst : Claims.consistency_ii_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ hφ hκ hD h2κ hchar htv0 htv hδ0 hδ1 ε hε η hη0 hη1
  exact StatFormal.Wave30tu.consistency_ii 𝒳 H P Q φ κ δ (fun n m α => tauNM κ D α δ n m)
    (fun n m η α => tauA κ D α η n m) hφ hκ hchar htv0 htv hδ0 hδ1
    (fun n m hn hm => ⟨tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm, (tauNM_le_tau P hκ hD h2κ hδ0 hδ1 hn hm).2⟩)
    (fun n m hn hm η hη0 hη1 => ⟨(tauA_lower P Q hφ hκ hD hη0 hη1 hn hm).2,
      (tauNM_le_tau P hκ hD h2κ hη0 hη1 hn hm).1⟩) ε hε η hη0 hη1

theorem cor_consistency_inst : Claims.cor_consistency_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D ι l n m δ hφ hκ hD h2κ hchar htv hn hm hδ0 hδ hrate e he
  exact StatFormal.Wave30tu.cor_consistency 𝒳 H P Q φ κ (fun n m d α => tauNM κ D α d n m)
    (fun n m d α => tauA κ D α d n m) ι l n m δ hφ hκ hchar htv
    (fun n m hn hm d hd0 hd1 => ⟨tauNM_valid' P hφ hκ hD hd0 hd1 hn hm,
      (tauNM_le_tau P hκ hD h2κ hd0 hd1 hn hm).2, (tauA_lower P Q hφ hκ hD hd0 hd1 hn hm).2,
      (tauNM_le_tau P hκ hD h2κ hd0 hd1 hn hm).1⟩) hn hm hδ0 hδ hrate e he

theorem rate_inst : Claims.rate_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m ε hφ hκ hD htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm hε hωε
  exact StatFormal.Wave30tu.rate 𝒳 H P Q φ κ δ δ' _ _ ω n m ε hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
    (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2 hε hωε

theorem confset_inst : Claims.confset_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m hφ hκ hD htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
  exact StatFormal.Wave30tu.confset 𝒳 H P Q φ κ δ δ' _ _ ω n m hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
    (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2

theorem upperfs_inst : Claims.upperfs_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ ω n m hφ hκ hD htv hmar hδ0 hδ1 hn hm
  exact StatFormal.Wave30tu.upperfs 𝒳 H P Q φ κ δ _ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
    (tauA_lower P Q hφ hκ hD hδ0 hδ1 hn hm).2

theorem upperfs_interval_inst : Claims.upperfs_interval_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ ω n m hφ hκ hD htv hmar hδ0 hδ1 hn hm
  exact StatFormal.Wave30tu.upperfs_interval 𝒳 H P Q φ κ δ _ _ ω n m hφ hκ htv hmar hδ0 hδ1 hn hm
    (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ0 hδ1 hn hm).2

theorem rate_poly_inst : Claims.rate_poly_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' c₀ γ n m hφ hκ hD h2κ htv hc0 hγ hmarg hδ0 hδ1 hδ'0 hδ'1 hn hm ht
  obtain ⟨h1, h2⟩ := StatFormal.Wave30tu.rate_poly 𝒳 H P Q φ κ δ δ' c₀ γ _ _ n m hφ hκ htv hc0 hγ hmarg hδ0 hδ1 hδ'0 hδ'1
    hn hm (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2 ht
  have hTI : StatFormal.Distances.tvDist P Q ∈ Ico (0 : ℝ) 1 := ⟨StatFormal.Distances.tvDist_nonneg P Q, htv⟩
  exact ⟨h1, h2 ((tauNM_le_tau P hκ hD h2κ hδ0 hδ1 hn hm).2 _ hTI) ((tauNM_le_tau P hκ hD h2κ hδ'0 hδ'1 hn hm).1 _ hTI)⟩

theorem confset_width_inst : Claims.confset_width_inst := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m hφ hκ hD htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
  exact StatFormal.Wave30tu.confset_width 𝒳 H P Q φ κ δ δ' _ _ ω n m hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm
    (tauNM_valid' P hφ hκ hD hδ0 hδ1 hn hm) (tauA_lower P Q hφ hκ hD hδ'0 hδ'1 hn hm).2

end StatFormal.Wave30tu.Instance
