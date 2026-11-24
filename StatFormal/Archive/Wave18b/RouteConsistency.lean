import StatFormal.Archive.Wave18b.RouteContinuity
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs

/-!
# Route: TM `cor:consistency` (untrusted)

* On the certified concentration event of `Unconditional.events` (probability `≥ 1 − δ_i`),
  `|D̂_α − D_α| ≤ τ_i(α)` for all `α ∈ [0,1)`.
* `D_{TV} = 0` (certified `zero_of_tv_le`), so `TV` is in the crossing set and `α̂ ≤ TV`.
* For `α < a := TV − e`: `D_α ≥ D_a > 0` (antitone; certified `zeroeq` with a characteristic kernel), and
  `τ_i(α) ≤ τ_i(a)` (certified `tau_mono`); once `2τ_i(a) < D_a` no such `α` crosses, so `α̂ ≥ TV − e`.
* `τ_i(a) → 0` along the schedule: `log(1/δ_i) ≥ 1` eventually, so `1/min(n_i,m_i) ≤ log(1/δ_i)/min → 0`, and
  `log(4/δ_i)/n_i ≤ log 4/min + log(1/δ_i)/min → 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric Filter Topology

namespace StatFormal.Wave18b

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma setDist_anti {A B A' B' : Set H} (hA : A.Nonempty) (hB : B.Nonempty) (hAA : A ⊆ A')
    (hBB : B ⊆ B') : setDist A' B' ≤ setDist A B := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  refine le_csInf ⟨_, a₀, ha₀, b₀, hb₀, rfl⟩ ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact setDist_le_norm (hAA ha) (hBB hb)

lemma Dpop_anti (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    {α α' : ℝ} (h0 : 0 ≤ α) (hle : α ≤ α') (hα' : α' < 1) : Dpop φ P Q α' ≤ Dpop φ P Q α :=
  setDist_anti (region_nonempty P h0 (hle.trans_lt hα')) (region_nonempty Q h0 (hle.trans_lt hα'))
    (region_mono P φ hle hα') (region_mono Q φ hle hα')

/-- `r_n(a, δ/2)` along a schedule with `1/n → 0` and `log(4/δ)/n → 0`. -/
lemma tendsto_rn_sched {ι : Type*} {l : Filter ι} {κ a : ℝ} {n : ι → ℕ} {δ : ι → ℝ}
    (h1 : Tendsto (fun i => 1 / (n i : ℝ)) l (𝓝 0))
    (h2 : Tendsto (fun i => Real.log (2 / (δ i / 2)) / (n i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => rn κ a (δ i / 2) (n i)) l (𝓝 0) := by
  have hA : Tendsto (fun i => 4 / √(n i : ℝ)) l (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul 4
    rw [Real.sqrt_zero, mul_zero] at this
    refine this.congr fun i => ?_
    simp [Function.comp, Real.sqrt_inv, div_eq_mul_inv]
  have hB : Tendsto (fun i => √(2 * Real.log (2 / (δ i / 2)) / (n i : ℝ))) l (𝓝 0) := by
    have h2' := h2.const_mul 2
    rw [mul_zero] at h2'
    have := (Real.continuous_sqrt.tendsto 0).comp h2'
    rw [Real.sqrt_zero] at this
    refine this.congr fun i => ?_
    simp [Function.comp, mul_div_assoc]
  have := (hA.add hB).const_mul (κ / (1 - a))
  rw [add_zero, mul_zero] at this
  exact this.congr fun i => by rw [rn]

lemma sched_facts {ι : Type*} {l : Filter ι} {n m : ι → ℕ} {δ : ι → ℝ} (hn : ∀ i, 1 ≤ n i)
    (hm : ∀ i, 1 ≤ m i) (hδ0 : ∀ i, 0 < δ i) (hδ : Tendsto δ l (𝓝 0))
    (hL : Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0)) :
    Tendsto (fun i => 1 / (n i : ℝ)) l (𝓝 0) ∧ Tendsto (fun i => 1 / (m i : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => Real.log (2 / (δ i / 2)) / (n i : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => Real.log (2 / (δ i / 2)) / (m i : ℝ)) l (𝓝 0) := by
  set M : ι → ℝ := fun i => ((min (n i) (m i) : ℕ) : ℝ) with hM
  have hMpos : ∀ i, 0 < M i := fun i => by
    simp only [hM]; exact_mod_cast lt_min (hn i) (hm i)
  have hMn : ∀ i, M i ≤ n i := fun i => by simp only [hM]; exact_mod_cast min_le_left _ _
  have hMm : ∀ i, M i ≤ m i := fun i => by simp only [hM]; exact_mod_cast min_le_right _ _
  -- eventually `log(1/δ) ≥ 1`
  have hev : ∀ᶠ i in l, 1 ≤ Real.log (1 / δ i) := by
    have hpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    filter_upwards [hδ.eventually (gt_mem_nhds hpos)] with i hi
    rw [one_div, Real.log_inv, le_neg]
    calc Real.log (δ i) ≤ Real.log (Real.exp (-1)) := Real.log_le_log (hδ0 i) hi.le
      _ = -1 := Real.log_exp _
  have h1M : Tendsto (fun i => 1 / M i) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL
      (Eventually.of_forall fun i => (one_div_pos.2 (hMpos i)).le) ?_
    filter_upwards [hev] with i hi
    exact div_le_div_of_nonneg_right hi (hMpos i).le
  have hlog4 : ∀ i, Real.log (2 / (δ i / 2)) = Real.log 4 + Real.log (1 / δ i) := by
    intro i
    rw [← Real.log_mul (by norm_num) (by have := hδ0 i; positivity)]
    congr 1; field_simp; ring
  have hLM : Tendsto (fun i => Real.log (2 / (δ i / 2)) / M i) l (𝓝 0) := by
    have := (h1M.const_mul (Real.log 4)).add hL
    rw [mul_zero, add_zero] at this
    refine this.congr fun i => ?_
    rw [hlog4]; simp only [hM]; ring
  have hcmp : ∀ (k : ι → ℕ), (∀ i, M i ≤ k i) →
      Tendsto (fun i => 1 / (k i : ℝ)) l (𝓝 0) ∧
        Tendsto (fun i => Real.log (2 / (δ i / 2)) / (k i : ℝ)) l (𝓝 0) := by
    intro k hk
    have hkpos : ∀ i, 0 < (k i : ℝ) := fun i => (hMpos i).trans_le (hk i)
    refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1M
      (fun i => (one_div_pos.2 (hkpos i)).le) (fun i => one_div_le_one_div_of_le (hMpos i) (hk i)), ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLM ?_ ?_
    · filter_upwards [hev] with i hi
      rw [hlog4]
      exact div_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) (hkpos i).le
    · filter_upwards [hev] with i hi
      rw [hlog4]
      exact div_le_div_of_nonneg_left (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)])
        (hMpos i) (hk i)
  obtain ⟨a1, a2⟩ := hcmp n hMn
  obtain ⟨b1, b2⟩ := hcmp m hMm
  exact ⟨a1, b1, a2, b2⟩

theorem cor_consistency : Claims.cor_consistency := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ ι l n m δ hφ hκ hκpos hchar htv hn hm hδ0 hδ hL e he
  set T := StatFormal.Distances.tvDist P Q with hT
  have hT0 : 0 ≤ T := StatFormal.Distances.tvDist_nonneg P Q
  set a := T - e with ha
  set μ : ∀ i, Measure ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)) :=
    fun i => (Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q) with hμ
  -- the population discrepancy at `a` is positive when `a ≥ 0`
  have hDa : 0 ≤ a → 0 < Dpop φ P Q a := by
    intro ha0
    have hne : Dpop φ P Q a ≠ 0 := by
      intro h0
      have := (zeroeq 𝒳 H P Q φ κ a hφ hκ hchar ha0 (by linarith)).1 h0
      linarith
    have hnn : 0 ≤ Dpop φ P Q a := Real.sInf_nonneg (by rintro _ ⟨x, -, y, -, rfl⟩; exact norm_nonneg _)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hDT : Dpop φ P Q T = 0 := zero_of_tv_le 𝒳 H P Q φ κ T hφ hκ hT0 htv le_rfl
  -- good indices
  let Good : ι → Prop := fun i => δ i < 1 ∧ (0 ≤ a → 2 * tau κ a (δ i) (n i) (m i) < Dpop φ P Q a)
  have hgood : ∀ᶠ i in l, Good i := by
    obtain ⟨f1, f2, f3, f4⟩ := sched_facts hn hm hδ0 hδ hL
    have htau : Tendsto (fun i => tau κ a (δ i) (n i) (m i)) l (𝓝 0) := by
      have := (tendsto_rn_sched (κ := κ) (a := a) f1 f3).add (tendsto_rn_sched (κ := κ) (a := a) f2 f4)
      rw [add_zero] at this
      exact this
    refine (hδ.eventually (gt_mem_nhds one_pos)).and ?_
    by_cases ha0 : 0 ≤ a
    · have := (htau.const_mul 2).eventually (gt_mem_nhds (by rw [mul_zero]; exact hDa ha0))
      filter_upwards [this] with i hi _ using hi
    · exact Eventually.of_forall fun i h => absurd h ha0
  classical
  have hev : ∀ i, Good i → ∃ (AP : Set (Fin (n i) → 𝒳)) (AQ : Set (Fin (m i) → 𝒳)), MeasurableSet AP ∧
      MeasurableSet AQ ∧ ENNReal.ofReal (1 - δ i / 2) ≤ μ i (Prod.fst ⁻¹' AP) ∧
      ENNReal.ofReal (1 - δ i / 2) ≤ μ i (Prod.snd ⁻¹' AQ) ∧
      ∀ z ∈ Prod.fst ⁻¹' AP ∩ Prod.snd ⁻¹' AQ, ∀ α ∈ Ico (0 : ℝ) 1,
        |Demp φ z.1 z.2 α - Dpop φ P Q α| ≤ tau κ α (δ i) (n i) (m i) :=
    fun i hi => exists_events P Q hφ hκ (hδ0 i) hi.1 (hn i) (hm i)
  let E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)) := fun i =>
    if hi : Good i then Prod.fst ⁻¹' (hev i hi).choose ∩ Prod.snd ⁻¹' (hev i hi).choose_spec.choose else ∅
  refine ⟨E, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [E]
    split_ifs with hi
    · obtain ⟨h1, h2, -⟩ := (hev i hi).choose_spec.choose_spec
      exact (measurable_fst h1).inter (measurable_snd h2)
    · exact MeasurableSet.empty
  · simp only [E]
    split_ifs with hi
    · obtain ⟨-, -, -, -, hz⟩ := (hev i hi).choose_spec.choose_spec
      intro z hzE
      have hE := hz z hzE
      set τf := fun α => tau κ α (δ i) (n i) (m i)
      have hup : alphaHat (Demp φ z.1 z.2) τf ≤ T :=
        alphaHat_le_of_event (D := Dpop φ P Q) ⟨hT0, htv⟩ hDT hE
      have hmem : T ∈ crossSet (Demp φ z.1 z.2) τf := mem_crossSet_of_event ⟨hT0, htv⟩ hDT hE
      have hlow : a ≤ alphaHat (Demp φ z.1 z.2) τf := by
        refine le_alphaHat ⟨T, hmem⟩ fun α hα => ?_
        by_contra hlt
        push Not at hlt
        have ha0 : 0 ≤ a := hα.1.1.trans hlt.le
        have h2 := hi.2 ha0
        have hDα : Dpop φ P Q a ≤ Dpop φ P Q α := Dpop_anti P Q φ hα.1.1 hlt.le (by linarith)
        have hτ : τf α ≤ τf a := tau_mono hκpos.le hlt.le (by linarith) _ _ _
        have hτa := tau_nonneg hκpos.le (show a < 1 by linarith) (δ i) (n i) (m i)
        have hcl := (abs_le.1 (hE α hα.1)).1
        have hcr := hα.2
        simp only [τf] at hτ hcr hcl
        linarith
      change |alphaHat (Demp φ z.1 z.2) τf - T| ≤ e
      rw [abs_le]; constructor <;> linarith
    · exact fun z hz => absurd hz (Set.notMem_empty z)
  · -- probabilities
    have hlow : ∀ᶠ i in l, ENNReal.ofReal (1 - δ i) ≤ μ i (E i) := by
      filter_upwards [hgood] with i hi
      simp only [E, dite_eq_left hi]
      obtain ⟨-, h2, hp1, hp2, -⟩ := (hev i hi).choose_spec.choose_spec
      exact prob_inter_ge (hδ0 i) hi.1 (measurable_snd h2) hp1 hp2
    have hlim : Tendsto (fun i => ENNReal.ofReal (1 - δ i)) l (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.tendsto (1 - 0)).comp (tendsto_const_nhds.sub hδ)
      rw [sub_zero, ENNReal.ofReal_one] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
      (Eventually.of_forall fun i => prob_le_one)

end StatFormal.Wave18b
