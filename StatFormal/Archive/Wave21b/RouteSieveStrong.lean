import StatFormal.Archive.Wave21b.Statements

/-!
# Route — otfd A `prop:integrated-sieve-strong`, the consequences of the `L²` limit (untrusted)

* radial ranks: `|‖a‖ − ‖b‖| ≤ ‖a − b‖`;
* signs: for `y ≠ 0`, `‖s(x) − s(y)‖ ≤ (2 + ‖c‖)‖x − y‖/‖y‖`, so the bad event splits into `{‖Y‖ ≤ η}` (small for
  small `η` because `P(Y = 0) = 0`) and `{‖Y_K − Y‖ ≥ εη/(2 + ‖c‖)}` (small by Markov);
* `L²`: signs are bounded by `max(1, ‖c‖)`, so `E‖s_K − s‖² ≤ ε² + B² P(‖s_K − s‖ ≥ ε)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave21b

section Signs
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma norm_nsign_le (c y : H) : ‖nsign c y‖ ≤ max 1 ‖c‖ := by
  unfold nsign
  split_ifs with hy
  · exact le_max_right _ _
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
    exact le_max_left _ _

lemma nsign_sub_le (c x y : H) (hy : y ≠ 0) :
    ‖nsign c x - nsign c y‖ ≤ (2 + ‖c‖) * ‖x - y‖ / ‖y‖ := by
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [le_div_iff₀ hny]
  unfold nsign
  simp only [hy, ite_false]
  split_ifs with hx
  · subst hx
    have h1 : ‖c - ‖y‖⁻¹ • y‖ ≤ ‖c‖ + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
    rw [zero_sub, norm_neg]
    nlinarith [norm_nonneg c]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hkey : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = ‖y‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • x := by
      rw [smul_sub, sub_smul]; abel
    rw [hkey]
    have h2 : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • x‖ ≤ ‖x - y‖ / ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖x‖ = (‖y‖ - ‖x‖) / ‖y‖ := by field_simp
      calc |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖x‖| := by rw [abs_mul, abs_of_pos hnx]
        _ = |‖y‖ - ‖x‖| / ‖y‖ := by rw [this, abs_div, abs_of_pos hny]
        _ ≤ ‖x - y‖ / ‖y‖ := by
          gcongr
          rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
    have h3 : ‖‖y‖⁻¹ • (x - y)‖ = ‖x - y‖ / ‖y‖ := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    have h4 := norm_add_le (‖y‖⁻¹ • (x - y)) ((‖x‖⁻¹ - ‖y‖⁻¹) • x)
    have h5 : (‖x - y‖ / ‖y‖) * ‖y‖ = ‖x - y‖ := by field_simp
    nlinarith [norm_nonneg c, norm_nonneg (x - y), div_nonneg (norm_nonneg (x - y)) hny.le]

end Signs

theorem sieve_strong_radial : Claims.sieve_strong_radial := by
  intro Ω H _ _ _ P Y Yl h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) (fun K => ?_)
  refine lintegral_mono fun ω => ?_
  rw [← ofReal_norm, ← ofReal_norm]
  gcongr
  rw [Real.norm_eq_abs]
  exact abs_norm_sub_norm_le _ _

/-- Markov: the `L²` limit gives convergence in measure. -/
lemma tendstoInMeasure_of_lintegral_sq {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
    (P : Measure Ω) (Y : ℕ → Ω → H) (Yl : Ω → H)
    (hY : ∀ K, AEStronglyMeasurable (Y K) P) (hYl : AEStronglyMeasurable Yl P)
    (h : Tendsto (fun K => ∫⁻ ω, ‖Y K ω - Yl ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun K => P {ω | ε ≤ ‖Y K ω - Yl ω‖}) atTop (𝓝 0) := by
  have hε2 : (ENNReal.ofReal ε) ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hε).ne'
  have hlim : Tendsto (fun K => (∫⁻ ω, ‖Y K ω - Yl ω‖ₑ ^ 2 ∂P) / (ENNReal.ofReal ε) ^ 2) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.div_const h (Or.inr hε2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) (fun K => ?_)
  have hm : AEMeasurable (fun ω => ‖Y K ω - Yl ω‖ₑ ^ 2) P :=
    (((hY K).sub hYl).enorm).pow_const 2
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div hm hε2 (by simp))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [← ofReal_norm]
  gcongr

theorem sieve_strong_signs_prob : Claims.sieve_strong_signs_prob := by
  intro Ω H _ _ _ P _ Y Yl c hY hYl h h0
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  -- choose η with `P{‖Yl‖ ≤ η} ≤ δ/2`
  have hcont : Tendsto (fun j : ℕ => P {ω | ‖Yl ω‖ ≤ 1 / ((j : ℝ) + 1)}) atTop (𝓝 (P {ω | Yl ω = 0})) := by
    have hinter : (⋂ j : ℕ, {ω | ‖Yl ω‖ ≤ 1 / ((j : ℝ) + 1)}) = {ω | Yl ω = 0} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hω
        by_contra hne
        have hpos : 0 < ‖Yl ω‖ := norm_pos_iff.2 hne
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
        exact absurd (hω j) (not_le.2 hj)
      · intro hω j; rw [hω, norm_zero]; positivity
    rw [← hinter]
    refine tendsto_measure_iInter_atTop (fun j => ?_) (fun i j hij => ?_) ⟨0, measure_ne_top _ _⟩
    · exact nullMeasurableSet_le hYl.norm.aemeasurable aemeasurable_const
    · intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      refine hω.trans ?_
      gcongr
  rw [h0] at hcont
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨j, hj⟩ := (eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hcont) _ hδ2))
  set η : ℝ := 1 / ((j : ℝ) + 1)
  have hη : 0 < η := by positivity
  have hm := tendstoInMeasure_of_lintegral_sq P Y Yl hY hYl h (ε * η / (2 + ‖c‖)) (by positivity)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hm) _ hδ2] with K hK
  calc P {ω | ε ≤ ‖nsign c (Y K ω) - nsign c (Yl ω)‖}
      ≤ P ({ω | ‖Yl ω‖ ≤ η} ∪ {ω | ε * η / (2 + ‖c‖) ≤ ‖Y K ω - Yl ω‖}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        by_cases hle : ‖Yl ω‖ ≤ η
        · exact Or.inl hle
        · right
          have hpos : 0 < ‖Yl ω‖ := hη.trans (not_le.1 hle)
          have hne : Yl ω ≠ 0 := norm_pos_iff.1 hpos
          have h1 := nsign_sub_le c (Y K ω) (Yl ω) hne
          have hc : 0 < 2 + ‖c‖ := by positivity
          rw [div_le_iff₀ hc]
          have h2 : ε * ‖Yl ω‖ ≤ (2 + ‖c‖) * ‖Y K ω - Yl ω‖ := by
            have := hω.trans h1
            rwa [le_div_iff₀ hpos] at this
          nlinarith [not_le.1 hle, norm_nonneg (Y K ω - Yl ω)]
    _ ≤ P {ω | ‖Yl ω‖ ≤ η} + P {ω | ε * η / (2 + ‖c‖) ≤ ‖Y K ω - Yl ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hj j le_rfl) hK
    _ = δ := ENNReal.add_halves δ

theorem sieve_strong_signs_L2 : Claims.sieve_strong_signs_L2 := by
  intro Ω H _ _ _ P _ Y Yl c hY hYl h h0
  have hprob := sieve_strong_signs_prob Ω H P Y Yl c hY hYl h h0
  rw [tendstoInMeasure_iff_norm] at hprob
  set B : ℝ := 2 * max 1 ‖c‖
  have hB : ∀ x y : H, ‖nsign c x - nsign c y‖ ≤ B := fun x y =>
    (norm_sub_le _ _).trans (by linarith [norm_nsign_le c x, norm_nsign_le c y])
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  -- pick `ε` with `ε² ≤ δ/2`
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal (ε ^ 2) ≤ δ / 2 := by
    by_cases htop : δ / 2 = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · refine ⟨√((δ / 2).toReal), Real.sqrt_pos.2 (ENNReal.toReal_pos hδ2.ne' htop), ?_⟩
      rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
  have hBpos : 0 < ENNReal.ofReal (B ^ 2) := by
    apply ENNReal.ofReal_pos.2; have : 0 < B := by positivity
    positivity
  have hq : 0 < δ / 2 / ENNReal.ofReal (B ^ 2) :=
    ENNReal.div_pos hδ2.ne' ENNReal.ofReal_ne_top
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hprob ε hε)) _ hq] with K hK
  set S := {ω | ε ≤ ‖nsign c (Y K ω) - nsign c (Yl ω)‖}
  have hpt : ∀ ω, ‖nsign c (Y K ω) - nsign c (Yl ω)‖ₑ ^ 2 ≤
      ENNReal.ofReal (ε ^ 2) + (toMeasurable P S).indicator (fun _ => ENNReal.ofReal (B ^ 2)) ω := by
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem (subset_toMeasurable P S hω)]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact pow_le_pow_left₀ (norm_nonneg _) (hB _ _) 2
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      simp only [S, Set.mem_ofPred_eq, not_le] at hω
      exact pow_le_pow_left₀ (norm_nonneg _) hω.le 2
  calc ∫⁻ ω, ‖nsign c (Y K ω) - nsign c (Yl ω)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (ε ^ 2) + (toMeasurable P S).indicator (fun _ => ENNReal.ofReal (B ^ 2)) ω) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (ε ^ 2) + ENNReal.ofReal (B ^ 2) * P S := by
        rw [lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const (measurableSet_toMeasurable P S), measure_toMeasurable]
    _ ≤ δ / 2 + δ / 2 := by
        refine add_le_add hεδ ?_
        calc ENNReal.ofReal (B ^ 2) * P S ≤ ENNReal.ofReal (B ^ 2) * (δ / 2 / ENNReal.ofReal (B ^ 2)) := by
              gcongr
          _ = δ / 2 := ENNReal.mul_div_cancel hBpos.ne' ENNReal.ofReal_ne_top
    _ = δ := ENNReal.add_halves δ

end StatFormal.Wave21b
