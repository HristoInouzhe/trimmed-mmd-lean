import StatFormal.Wave30tu.RouteMain

/-!
# Wave 30tu — `thm:consistency` (ii) and `cor:consistency` (untrusted proof route)

The printed proof: `c(ε) = D_{α*−ε}(P,Q) > 0` (the certified `zeroeq`, characteristic kernel), both thresholds are
`≤ r_n + r_m → 0`, and on `E⁰ ∩ E⁻_η` no `α ≤ α* − ε` is in the crossing set. For the schedule, `r_n(α*, δ_i/2) + r_m(α*, δ_i/2) → 0`
because `1/min(n,m) ≤ log(1/δ)/min(n,m)` once `δ < e^{−1}`; the event at index `i` has probability `≥ 1 − 2δ_i`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

/-- `r_n(α,d) → 0` as `n → ∞`. -/
theorem rn_tendsto (κ α d : ℝ) : Tendsto (fun n : ℕ => rn κ α d n) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun u => κ / (1 - α) * (4 * √u + √(2 * Real.log (2 / d) * u))
  have heq : ∀ n : ℕ, g ((n : ℝ)⁻¹) = rn κ α d n := by
    intro n
    simp only [g, rn, Real.sqrt_inv, div_eq_mul_inv]
  have hc : Continuous g := by fun_prop
  have h := (hc.tendsto 0).comp (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h0 : g 0 = 0 := by simp [g]
  rw [h0] at h
  exact h.congr fun n => heq n

/-- Under the schedule, `r_n(α,δ_i/2) + r_m(α,δ_i/2) → 0`. -/
theorem tau_sched {ι : Type*} {l : Filter ι} {n m : ι → ℕ} {δ : ι → ℝ} (κ α : ℝ) (hα : α < 1) (hκ : 0 ≤ κ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hδ0 : ∀ i, 0 < δ i) (hδ : Tendsto δ l (𝓝 0))
    (hrate : Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0)) :
    Tendsto (fun i => tau κ α (δ i) (n i) (m i)) l (𝓝 0) := by
  set M : ι → ℝ := fun i => ((min (n i) (m i) : ℕ) : ℝ)
  have hM : ∀ i, 0 < M i := fun i => by
    have : 1 ≤ min (n i) (m i) := le_min (hn i) (hm i)
    simp only [M]; exact_mod_cast this
  have hev : ∀ᶠ i in l, δ i < Real.exp (-1) := hδ.eventually (gt_mem_nhds (Real.exp_pos _))
  have hL1 : ∀ᶠ i in l, 1 < Real.log (1 / δ i) := by
    filter_upwards [hev] with i hi
    have := Real.log_lt_log (hδ0 i) hi
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  set u : ι → ℝ := fun i => 1 / M i
  set w : ι → ℝ := fun i => Real.log (4 / δ i) / M i
  have hu : Tendsto u l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
      (Eventually.of_forall fun i => (one_div_pos.2 (hM i)).le) ?_
    filter_upwards [hL1] with i hi
    exact div_le_div_of_nonneg_right hi.le (hM i).le
  have hw : Tendsto w l (𝓝 0) := by
    have heq : ∀ i, Real.log 4 * u i + Real.log (1 / δ i) / (min (n i) (m i) : ℕ) = w i := by
      intro i
      have h4 : (4 : ℝ) / δ i = 4 * (1 / δ i) := by ring
      simp only [w, u, M]
      rw [h4, Real.log_mul (by norm_num) (one_div_pos.2 (hδ0 i)).ne']
      ring
    have := (hu.const_mul (Real.log 4)).add hrate
    rw [mul_zero, add_zero] at this
    exact this.congr heq
  set β := κ / (1 - α)
  have hβ : 0 ≤ β := div_nonneg hκ (by linarith)
  set g : ℝ → ℝ → ℝ := fun a b => 2 * (β * (4 * √a + √(2 * b)))
  have hg : Tendsto (fun i => g (u i) (w i)) l (𝓝 0) := by
    have hsu := (Real.continuous_sqrt.tendsto 0).comp hu
    have hsw := (Real.continuous_sqrt.tendsto (2 * 0)).comp (hw.const_mul 2)
    simp only [mul_zero, Real.sqrt_zero] at hsu hsw
    have := ((hsu.const_mul 4).add hsw).const_mul β |>.const_mul 2
    simp only [mul_zero, add_zero] at this
    exact this
  have hbound : ∀ᶠ i in l, tau κ α (δ i) (n i) (m i) ≤ g (u i) (w i) := by
    filter_upwards [hL1] with i hi
    have hlog4 : Real.log (2 / (δ i / 2)) = Real.log (4 / δ i) := by
      congr 1; field_simp; ring
    have hL0 : 0 ≤ Real.log (4 / δ i) := by
      have h4 : (4 : ℝ) / δ i = 4 * (1 / δ i) := by ring
      rw [h4, Real.log_mul (by norm_num) (one_div_pos.2 (hδ0 i)).ne']
      have : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith
    have hrn : ∀ k : ℕ, M i ≤ k → rn κ α (δ i / 2) k ≤ β * (4 * √(u i) + √(2 * w i)) := by
      intro k hk
      have hk0 : 0 < (k : ℝ) := (hM i).trans_le hk
      unfold rn
      rw [hlog4]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hβ
      · have h1 : √(M i) ≤ √(k : ℝ) := Real.sqrt_le_sqrt hk
        have h2 : 4 / √(k : ℝ) ≤ 4 / √(M i) :=
          div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (hM i)) h1
        have h3 : 4 / √(M i) = 4 * √(u i) := by
          simp only [u]; rw [Real.sqrt_div' 1 (hM i).le, Real.sqrt_one]; ring
        linarith
      · refine Real.sqrt_le_sqrt ?_
        have : 2 * Real.log (4 / δ i) / k ≤ 2 * Real.log (4 / δ i) / M i :=
          div_le_div_of_nonneg_left (by positivity) (hM i) hk
        simp only [w]
        calc 2 * Real.log (4 / δ i) / k ≤ 2 * Real.log (4 / δ i) / M i := this
          _ = 2 * (Real.log (4 / δ i) / M i) := by ring
    have hMn : M i ≤ (n i : ℝ) := by simp only [M]; exact_mod_cast min_le_left _ _
    have hMm : M i ≤ (m i : ℝ) := by simp only [M]; exact_mod_cast min_le_right _ _
    have := add_le_add (hrn (n i) hMn) (hrn (m i) hMm)
    simp only [g, tau]
    linarith
  have hnn : ∀ᶠ i in l, 0 ≤ tau κ α (δ i) (n i) (m i) :=
    Eventually.of_forall fun i => add_nonneg (rn_nonneg hκ hα _ _) (rn_nonneg hκ hα _ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hnn hbound

section Core

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Pathwise lower bound of `thm:consistency` (ii). -/
theorem lower_core (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hκ0 : 0 ≤ κ) (htv : StatFormal.Distances.tvDist P Q < 1) {δ η : ℝ} {τ τA : ℝ → ℝ} {n m : ℕ}
    (hτle : ∀ α ∈ Ico (0 : ℝ) 1, τ α ≤ tau κ α δ n m) (hτAle : ∀ α ∈ Ico (0 : ℝ) 1, τA α ≤ tau κ α η n m)
    {ε : ℝ} (hε : ε ∈ Ioc 0 (StatFormal.Distances.tvDist P Q))
    (hsmall : tau κ (StatFormal.Distances.tvDist P Q) δ n m + tau κ (StatFormal.Distances.tvDist P Q) η n m <
      Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε))
    (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hz : Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q))
    (hlow : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - τA α ≤ Demp φ z.1 z.2 α) :
    StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) τ ∧
      alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q := by
  set T := StatFormal.Distances.tvDist P Q
  have hTmem := tv_mem_crossSet P Q htv z hz
  refine ⟨le_csInf ⟨T, hTmem⟩ fun s hs => ?_, alphaHat_le_of_mem hTmem⟩
  by_contra hlt
  push_neg at hlt
  have hsT : s ≤ T := by linarith [hε.1]
  have hTε : T - ε ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hs.1.1], by linarith [hε.1]⟩
  have h1 : Dpop φ P Q (T - ε) ≤ Dpop φ P Q s := StatFormal.WaveP1a.Dpop_antitoneOn φ P Q hs.1 hTε hlt.le
  have h2 := hlow s hs.1
  have h3 : τA s ≤ tau κ T η n m := (hτAle s hs.1).trans (tau_mono hκ0 hsT htv η n m)
  have h4 : τ s ≤ tau κ T δ n m := (hτle s hs.1).trans (tau_mono hκ0 hsT htv δ n m)
  have h5 := hs.2
  linarith

variable [TopologicalSpace.SeparableSpace H]

theorem Dpop_pos (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hchar : StatFormal.TrimmedMMD.ZeroSet.Characteristic φ)
    (htv : StatFormal.Distances.tvDist P Q < 1) {ε : ℝ} (hε : ε ∈ Ioc 0 (StatFormal.Distances.tvDist P Q)) :
    0 < Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) := by
  have h0 : 0 ≤ StatFormal.Distances.tvDist P Q - ε := by linarith [hε.2]
  have h1 : StatFormal.Distances.tvDist P Q - ε < 1 := by linarith [hε.1]
  have hiff := StatFormal.TrimmedMMD.ZeroSet.zeroeq 𝒳 H P Q φ κ _ hφ hκ hchar h0 h1
  have hne : Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε) ≠ 0 := fun h => by
    have := hiff.1 h
    linarith [hε.1]
  exact lt_of_le_of_ne (StatFormal.WaveP1a.setDist_nonneg' _ _) (Ne.symm hne)

end Core

theorem consistency_ii : Claims.consistency_ii := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ τA hφ hκ hchar htv0 htv hδ0 hδ1 hτfam hτAfam ε hε η hη0 hη1
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 := kappa_nonneg_of hκ x0
  have hc := Dpop_pos P Q hφ hκ hchar htv hε
  set c := Dpop φ P Q (StatFormal.Distances.tvDist P Q - ε)
  have hc4 : 0 < c / 4 := by linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((rn_tendsto κ (StatFormal.Distances.tvDist P Q) (δ / 2)).eventually (gt_mem_nhds hc4))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1
    ((rn_tendsto κ (StatFormal.Distances.tvDist P Q) (η / 2)).eventually (gt_mem_nhds hc4))
  refine ⟨max N1 N2, fun n m hnN hmN hn hm => ?_⟩
  obtain ⟨hv, hτle⟩ := hτfam n m hn hm
  obtain ⟨hlow, hτAle⟩ := hτAfam n m hn hm η hη0 hη1
  have hsmall : tau κ (StatFormal.Distances.tvDist P Q) δ n m + tau κ (StatFormal.Distances.tvDist P Q) η n m < c := by
    have a1 := hN1 n (le_of_max_le_left hnN)
    have a2 := hN1 m (le_of_max_le_left hmN)
    have a3 := hN2 n (le_of_max_le_right hnN)
    have a4 := hN2 m (le_of_max_le_right hmN)
    simp only [tau]
    linarith
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hη0.le hn hm hv P Q htv hlow
  exact ⟨E, hEm, hEp, fun z hz => lower_core P Q hκ0 htv hτle hτAle hε hsmall z (hE z hz).1 (hE z hz).2⟩

theorem cor_consistency : Claims.cor_consistency := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ τ τA ι l n m δ hφ hκ hchar htv hfam hn hm hδ0 hδ hrate e he
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 := kappa_nonneg_of hκ x0
  set T := StatFormal.Distances.tvDist P Q with hTdef
  have hT0 : 0 ≤ T := StatFormal.Distances.tvDist_nonneg P Q
  set ε' := min e T
  set Cnd : ι → Prop := fun i => δ i < 1 ∧
    (0 < T → tau κ T (δ i) (n i) (m i) + tau κ T (δ i) (n i) (m i) < Dpop φ P Q (T - ε'))
  have key : ∀ i, Cnd i → ∃ F : Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), MeasurableSet F ∧
      ENNReal.ofReal (1 - 2 * δ i) ≤ ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) F ∧
      F ⊆ {z | |alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i)) - T| ≤ e} := by
    intro i hi
    obtain ⟨hv, hτle, hlow, hτAle⟩ := hfam (n i) (m i) (hn i) (hm i) (δ i) (hδ0 i) hi.1
    obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ (hδ0 i).le (hδ0 i).le (hn i) (hm i) hv P Q htv hlow
    refine ⟨E, hEm, by rw [show 1 - 2 * δ i = 1 - δ i - δ i by ring]; exact hEp, fun z hz => ?_⟩
    have hTmem := tv_mem_crossSet P Q htv z (hE z hz).1
    have hle := alphaHat_le_of_mem hTmem
    have hnn := alphaHat_nonneg ⟨_, hTmem⟩
    simp only [mem_setOf_eq]
    rw [abs_le]
    rcases hT0.lt_or_eq with hTpos | hTz
    · have hε' : ε' ∈ Ioc 0 T := ⟨lt_min he hTpos, min_le_right _ _⟩
      obtain ⟨hlo, -⟩ := lower_core P Q hκ0 htv hτle hτAle hε' (hi.2 hTpos) z (hE z hz).1 (hE z hz).2
      have : ε' ≤ e := min_le_left _ _
      constructor <;> linarith
    · constructor <;> linarith
  have key' : ∀ i, ∃ F : Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), MeasurableSet F ∧
      F ⊆ {z | |alphaHat (Demp φ z.1 z.2) (τ (n i) (m i) (δ i)) - T| ≤ e} ∧
      (Cnd i → ENNReal.ofReal (1 - 2 * δ i) ≤
        ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) F) := by
    intro i
    by_cases h : Cnd i
    · obtain ⟨F, hFm, hFp, hFs⟩ := key i h
      exact ⟨F, hFm, hFs, fun _ => hFp⟩
    · exact ⟨∅, MeasurableSet.empty, empty_subset _, fun h' => absurd h' h⟩
  choose F hFm hFs hFp using key'
  have hev : ∀ᶠ i in l, Cnd i := by
    refine (hδ.eventually (gt_mem_nhds one_pos)).and ?_
    by_cases hTpos : 0 < T
    · have hε' : ε' ∈ Ioc 0 T := ⟨lt_min he hTpos, min_le_right _ _⟩
      have hc := Dpop_pos P Q hφ hκ hchar htv hε'
      have ht := tau_sched κ T htv hκ0 hn hm hδ0 hδ hrate
      have h2 := ht.add ht
      rw [add_zero] at h2
      filter_upwards [h2.eventually (gt_mem_nhds hc)] with i hi
      exact fun _ => hi
    · exact Eventually.of_forall fun i h => absurd h hTpos
  refine ⟨F, hFm, hFs, ?_⟩
  have hlow : Tendsto (fun i => ENNReal.ofReal (1 - 2 * δ i)) l (𝓝 1) := by
    have : Tendsto (fun i => 1 - 2 * δ i) l (𝓝 (1 - 2 * 0)) := tendsto_const_nhds.sub (hδ.const_mul 2)
    rw [mul_zero, sub_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun i => prob_le_one)
  filter_upwards [hev] with i hi
  exact hFp i hi

end StatFormal.Wave30tu
