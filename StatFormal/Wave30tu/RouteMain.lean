import StatFormal.Wave30tu.RouteBasic
import StatFormal.Wave30tl.RouteLevel

/-!
# Wave 30tu — main claims (untrusted proof route)

The printed proofs, on the event `E⁰ = {D̂_{α*} ≤ τ(α*)}` (validity at the true null) intersected with `E⁻`:
* `α* ∈ S`, so `α̂ ≤ α*` and `S ≠ ∅`; upward closure and `D̂_{α̂} ≤ τ(α̂+)` come from `RouteBasic`.
* `thm:rate`: for `s ∈ S` with `s < α* − ε`, `ε' = α* − s > ε` gives `τ(α*) + τ^A(α*) = ω(ε) < ω(ε') ≤ D_s ≤ D̂_s + τ^A(s) ≤ τ(s) + τ^A(α*)`,
  a contradiction (no limit `ε ↓ ε_{n,m}` is needed).
* `cor:confset`: the margin at `ε = α* − α̂`, `D_{α̂} ≤ D̂_{α̂} + τ^A(α̂) ≤ τ(α̂+) + τ^A(α̂)`.
* Instances: the v1 threshold from the certified Wave 30tl `test_level` and the `cor:uniform` events (`exists_event`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

section Core

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem tv_mem_Ico (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (htv : StatFormal.Distances.tvDist P Q < 1) : StatFormal.Distances.tvDist P Q ∈ Ico (0 : ℝ) 1 :=
  ⟨StatFormal.Distances.tvDist_nonneg P Q, htv⟩

/-- The two events of the printed proofs: `E⁰` (validity at `α*`) and `E⁻`. -/
theorem two_events {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {δ δ' : ℝ} (hδ0 : 0 ≤ δ) (hδ'0 : 0 ≤ δ')
    {τ τA : ℝ → ℝ} {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hv : ValidThreshold φ n m δ τ) (P Q : Measure 𝒳)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (htv : StatFormal.Distances.tvDist P Q < 1)
    (hlow : LowerTool φ P Q n m δ' τA) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ - δ') ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
      ∀ z ∈ E, Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q) ∧
        ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - τA α ≤ Demp φ z.1 z.2 α := by
  obtain ⟨hm0, hp0⟩ := valid_event hφ hδ0 hn hm hv P Q (tv_mem_Ico P Q htv) le_rfl
  obtain ⟨-, -, F, hFm, hFp, hF⟩ := hlow
  exact ⟨_, hm0.inter hFm, inter_prob hm0 hFm hδ0 hδ'0 hp0 hFp, fun z hz => ⟨hz.1, hF z hz.2⟩⟩

theorem tv_mem_crossSet (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {τ : ℝ → ℝ} (htv : StatFormal.Distances.tvDist P Q < 1) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hz : Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q)) :
    StatFormal.Distances.tvDist P Q ∈ crossSet (Demp φ z.1 z.2) τ :=
  ⟨tv_mem_Ico P Q htv, hz⟩

/-- Pathwise `thm:rate`. -/
theorem rate_det (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {τ τA ω : ℝ → ℝ} (htv : StatFormal.Distances.tvDist P Q < 1) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hz : Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q))
    (hlow : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - τA α ≤ Demp φ z.1 z.2 α)
    (hτm : MonotoneOn τ (Ico 0 1)) (hτAm : MonotoneOn τA (Ico 0 1))
    (hωm : StrictMonoOn ω (Icc 0 (StatFormal.Distances.tvDist P Q)))
    (hωD : ∀ e ∈ Icc (0 : ℝ) (StatFormal.Distances.tvDist P Q),
      ω e ≤ Dpop φ P Q (StatFormal.Distances.tvDist P Q - e))
    {ε : ℝ} (hε : ε ∈ Icc 0 (StatFormal.Distances.tvDist P Q))
    (hωε : ω ε = τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) :
    StatFormal.Distances.tvDist P Q - ε ≤ alphaHat (Demp φ z.1 z.2) τ ∧
      alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q := by
  set T := StatFormal.Distances.tvDist P Q
  have hTI : T ∈ Ico (0 : ℝ) 1 := tv_mem_Ico P Q htv
  have hTmem := tv_mem_crossSet P Q htv z hz
  refine ⟨le_csInf ⟨T, hTmem⟩ fun s hs => ?_, alphaHat_le_of_mem hTmem⟩
  by_contra hlt
  push_neg at hlt
  have hsT : s ≤ T := by linarith [hε.1]
  have he' : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hs.1.1]⟩
  have h1 : ω ε < ω (T - s) := hωm hε he' (by linarith)
  have h2 := hωD (T - s) he'
  rw [sub_sub_cancel] at h2
  have h3 := hlow s hs.1
  have h4 : τA s ≤ τA T := hτAm hs.1 hTI hsT
  have h5 : τ s ≤ τ T := hτm hs.1 hTI hsT
  have h6 := hs.2
  linarith

/-- Pathwise `cor:confset`. -/
theorem confset_det (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ : ℝ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {τ τA ω : ℝ → ℝ}
    (htv : StatFormal.Distances.tvDist P Q < 1) (hmar : KnownMargin φ P Q ω) (hτm : MonotoneOn τ (Ico 0 1))
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (z : (Fin n → 𝒳) × (Fin m → 𝒳))
    (hz : Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) ≤ τ (StatFormal.Distances.tvDist P Q))
    (hlow : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α - τA α ≤ Demp φ z.1 z.2 α) :
    alphaHat (Demp φ z.1 z.2) τ ≤ StatFormal.Distances.tvDist P Q ∧
      StatFormal.Distances.tvDist P Q ≤ alphaHat (Demp φ z.1 z.2) τ +
        omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ)) := by
  set T := StatFormal.Distances.tvDist P Q
  have hTmem := tv_mem_crossSet P Q htv z hz
  have hne : (crossSet (Demp φ z.1 z.2) τ).Nonempty := ⟨T, hTmem⟩
  set a := alphaHat (Demp φ z.1 z.2) τ
  have hle : a ≤ T := alphaHat_le_of_mem hTmem
  have haI := alphaHat_mem_Ico hne
  refine ⟨hle, ?_⟩
  have hR := le_tauRight (Demp_continuousOn hφ hκ hn hm z.1 z.2) (Demp_antitoneOn φ hn hm z.1 z.2) hτm hne
  have hD : Dpop φ P Q a ≤ tauRight τ a + τA a := by linarith [hlow a haI]
  have hε : T - a ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [haI.1]⟩
  have hmarg := hmar.2.2.2.2 (T - a) hε
  rw [sub_sub_cancel] at hmarg
  have hε1 : T - a ∈ Icc (0 : ℝ) 1 := ⟨hε.1, by linarith [haI.1, htv]⟩
  have := le_omegaGen hε1 (hmarg.trans hD)
  linarith

/-- Pathwise sentence after `cor:upperfs`. -/
theorem alphaHi_le_det {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    {τ τA ω : ℝ → ℝ} (hτm : MonotoneOn τ (Ico 0 1)) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) (hne : (crossSet (Demp φ x y) τ).Nonempty) :
    alphaHi ω (fun α => Demp φ x y α + τA α) ≤
      alphaHat (Demp φ x y) τ + omegaGen ω (tauRight τ (alphaHat (Demp φ x y) τ) + τA (alphaHat (Demp φ x y) τ)) := by
  have haI := alphaHat_mem_Ico hne
  refine (csInf_le (alphaHi_bddBelow _ _) ⟨_, haI, rfl⟩).trans ?_
  have hR := le_tauRight (Demp_continuousOn hφ hκ hn hm x y) (Demp_antitoneOn φ hn hm x y) hτm hne
  have := omegaGen_mono ω (by linarith : Demp φ x y (alphaHat (Demp φ x y) τ) + τA (alphaHat (Demp φ x y) τ) ≤
    tauRight τ (alphaHat (Demp φ x y) τ) + τA (alphaHat (Demp φ x y) τ))
  show alphaHat (Demp φ x y) τ + omegaGen ω (Demp φ x y (alphaHat (Demp φ x y) τ) + τA (alphaHat (Demp φ x y) τ)) ≤ _
  exact add_le_add le_rfl this

end Core

/-! ### Certified claims -/

theorem oneevent : Claims.oneevent := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ n m hφ hκ hδ0 hδ1 hn hm hv htv
  have hTI := tv_mem_Ico P Q htv
  obtain ⟨hmeas, hprob⟩ := valid_event hφ hδ0.le hn hm hv P Q hTI le_rfl
  refine ⟨hmeas, hprob, fun z hz α hα => ?_⟩
  have hαI : α ∈ Ico (0 : ℝ) 1 := ⟨hTI.1.trans hα.1, hα.2⟩
  calc Demp φ z.1 z.2 α ≤ Demp φ z.1 z.2 (StatFormal.Distances.tvDist P Q) :=
        Demp_antitoneOn φ hn hm z.1 z.2 hTI hαI hα.1
    _ ≤ τ (StatFormal.Distances.tvDist P Q) := hz
    _ ≤ τ α := hv.2.1 hTI hαI hα.1

theorem threshold_min : Claims.threshold_min := by
  intro 𝒳 H _ _ _ φ δ n m ι s hs τ hτ
  refine ⟨⟨fun α hα => Finset.le_inf' hs _ fun i hi => (hτ i hi).1 α hα, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hab
    exact Finset.le_inf' hs _ fun i hi => (Finset.inf'_le _ hi).trans ((hτ i hi).2.1 ha hb hab)
  · intro α hα P' Q' hP' hQ' htv
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs (fun i => τ i α)
    simp only [heq]
    exact (hτ i hi).2.2 α hα P' Q' hP' hQ' htv
  · intro hc
    exact ContinuousOn.finset_inf'_apply hs hc
  · intro ht
    refine tendsto_atTop.2 fun b => ?_
    have := (Filter.eventually_all_finset s).2 fun i hi => tendsto_atTop.1 (ht i hi) b
    filter_upwards [this] with α hα
    exact Finset.le_inf' hs _ hα

theorem upper_valid : Claims.upper_valid := by
  intro 𝒳 H _ _ _ _ _ φ κ δ τA n m hφ hκ hδ0 hδ1 hn hm h0 hmono hup
  refine ⟨h0, hmono, fun α hα P' Q' hP' hQ' htv => ?_⟩
  obtain ⟨E, hEm, hEp, hE⟩ := hup P' Q' hP' hQ'
  haveI := hP'
  haveI := hQ'
  have hD0 : Dpop φ P' Q' α = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le 𝒳 H P' Q' φ κ α hφ hκ hα.1 hα.2 htv
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | τA α < Demp φ z.1 z.2 α} ⊆ Eᶜ := by
    intro z hz hzE
    have := hE z hzE α hα
    rw [hD0, zero_add] at this
    exact absurd hz (not_lt.2 this)
  exact (measure_mono hsub).trans (compl_le_of_ge hEm hEp)

theorem alphaest_wellDefined : Claims.alphaest_wellDefined := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm hτ x y
  have hle := Demp_le_two_kappa hκ hn hm x y
  refine ⟨hle, ?_⟩
  have hev := (tendsto_atTop.1 hτ (2 * κ)).and (Ioo_mem_nhdsLT (zero_lt_one' ℝ))
  obtain ⟨α, hα, hαI⟩ := hev.exists
  exact ⟨α, ⟨hαI.1.le, hαI.2⟩, (hle α ⟨hαI.1.le, hαI.2⟩).trans hα⟩

theorem tauRight_spec : Claims.tauRight_spec := by
  intro τ a _ hm ha0 ha1
  exact ⟨tauRight_tendsto hm ha0 ha1, le_tauRight_self hm ha0 ha1, fun hpos hc => tauRight_eq hm hpos ha1 hc⟩

theorem crossing : Claims.crossing := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm _ hτm hτc x y hne
  have hD := Demp_continuousOn hφ hκ hn hm x y
  have hDa := Demp_antitoneOn φ hn hm x y
  have hup := Ioo_subset_crossSet hDa hτm hne
  have hle := le_tauRight hD hDa hτm hne
  refine ⟨⟨hD, hDa⟩, hup, hle, fun hpos => ?_⟩
  have haI := alphaHat_mem_Ico hne
  have hmem : alphaHat (Demp φ x y) τ ∈ crossSet (Demp φ x y) τ :=
    ⟨haI, by rw [← tauRight_eq hτm hpos haI.2 hτc]; exact hle⟩
  ext α
  constructor
  · intro hα
    exact ⟨alphaHat_le_of_mem hα, hα.1.2⟩
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h | h
    · exact hup ⟨h, h2⟩
    · rw [← h]; exact hmem

theorem crossing_meas : Claims.crossing_meas := by
  intro 𝒳 H _ _ _ _ _ φ κ τ n m hφ hκ hn hm _ hτm _ hne
  have hformula : ∀ a : ℝ, {z : (Fin n → 𝒳) × (Fin m → 𝒳) | alphaHat (Demp φ z.1 z.2) τ < a} =
      ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ) ∧ (q : ℝ) < a), {z | Demp φ z.1 z.2 q ≤ τ q} := by
    intro a
    ext z
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    have hnz := hne z.1 z.2
    have hDa := Demp_antitoneOn φ hn hm z.1 z.2
    have hlt1 := alphaHat_lt_one hnz
    constructor
    · intro ha
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min ha hlt1)
      have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (alphaHat_nonneg hnz) hq1
      exact ⟨q, ⟨hq0, hq2.trans_le (min_le_left _ _)⟩,
        (Ioo_subset_crossSet hDa hτm hnz ⟨hq1, hq2.trans_le (min_le_right _ _)⟩).2⟩
    · rintro ⟨q, ⟨hq0, hqa⟩, hq⟩
      by_cases hq1 : (q : ℝ) < 1
      · exact (alphaHat_le_of_mem ⟨⟨hq0.le, hq1⟩, hq⟩).trans_lt hqa
      · exact hlt1.trans_le ((not_lt.1 hq1).trans hqa.le)
  refine ⟨hformula, measurable_of_Iio fun a => ?_⟩
  by_cases ha : a ≤ 1
  · have : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) τ) ⁻¹' Iio a =
        {z | alphaHat (Demp φ z.1 z.2) τ < a} := rfl
    rw [this, hformula a]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    exact measurableSet_le (measurable_Demp hφ hn hm hq.1.le (hq.2.trans_le ha)) measurable_const
  · push_neg at ha
    convert MeasurableSet.univ
    ext z
    simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
    exact (alphaHat_lt_one (hne z.1 z.2)).trans ha

theorem grid_mesh : Claims.grid_mesh := by
  intro 𝒳 H _ _ _ _ _ φ κ h τ n m G hφ hκ hn hm _ hτm hG x y hne
  have hDa := Demp_antitoneOn φ hn hm x y
  exact ⟨fun a ha => gridReturn_le' hDa hτm hne hG ha,
    fun b hb => lastRejected_le hDa hτm hne hG hb.1.1 hb.1.2⟩

theorem grid_prob : Claims.grid_prob := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ n m hφ hκ htv hδ0 hδ1 hn hm hv
  have hTI := tv_mem_Ico P Q htv
  obtain ⟨hmeas, hprob⟩ := valid_event hφ hδ0.le hn hm hv P Q hTI le_rfl
  refine ⟨_, hmeas, hprob, fun z hz G h hG => ?_⟩
  have hTmem := tv_mem_crossSet P Q htv z hz
  have hne : (crossSet (Demp φ z.1 z.2) τ).Nonempty := ⟨_, hTmem⟩
  have hDa := Demp_antitoneOn φ hn hm z.1 z.2
  have hle := alphaHat_le_of_mem hTmem
  refine ⟨fun a ha => (gridReturn_le' hDa hv.2.1 hne hG ha).trans (by linarith), fun b hb => ?_⟩
  by_contra hbT
  push_neg at hbT
  have hbI : b ∈ Ico (0 : ℝ) 1 := hG.1 b hb.1.1
  have : Demp φ z.1 z.2 b ≤ τ b := (hDa hTI hbI hbT).trans (hz.trans (hv.2.1 hTI hbI hbT))
  exact absurd hb.1.2 (not_lt.2 this)

theorem consistency_i : Claims.consistency_i := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ n m hφ hκ htv hδ0 hδ1 hn hm hv
  obtain ⟨hmeas, hprob⟩ := valid_event hφ hδ0.le hn hm hv P Q (tv_mem_Ico P Q htv) le_rfl
  refine ⟨_, hmeas, hprob, fun z hz => ?_⟩
  have hTmem := tv_mem_crossSet P Q htv z hz
  have hle := alphaHat_le_of_mem hTmem
  exact ⟨hle, fun h0 => le_antisymm (hle.trans h0.le) (alphaHat_nonneg ⟨_, hTmem⟩)⟩

theorem Demp_le_Dphi : Claims.Demp_le_Dphi := by
  intro 𝒳 H _ _ _ _ _ φ κ D n m hφ hκ hD hn hm x y α hα
  exact Demp_le_D hφ hD hn hm x y hα

theorem rate_eps : Claims.rate_eps := by
  intro 𝒳 H _ _ _ P Q _ _ φ ω t hmar ht0 htT
  have hT0 := StatFormal.Distances.tvDist_nonneg P Q
  have hivt := intermediate_value_Icc hT0 hmar.2.1
  rw [hmar.2.2.1] at hivt
  obtain ⟨ε, hε, hωε⟩ := hivt ⟨ht0, htT⟩
  exact ⟨ε, ⟨hε, hωε⟩, fun e he => hmar.1.injOn he.1 hε (he.2.trans hωε.symm)⟩

theorem rate : Claims.rate := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' τ τA ω n m ε hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm hv hlow hε hωε
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hδ'0.le hn hm hv P Q htv hlow
  exact ⟨E, hEm, hEp, fun z hz =>
    rate_det P Q htv z (hE z hz).1 (hE z hz).2 hv.2.1 hlow.2.1 hmar.1 hmar.2.2.2.2 hε hωε⟩

theorem confset : Claims.confset := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' τ τA ω n m hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm hv hlow
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hδ'0.le hn hm hv P Q htv hlow
  exact ⟨E, hEm, hEp, fun z hz => confset_det P Q hφ hκ htv hmar hv.2.1 hn hm z (hE z hz).1 (hE z hz).2⟩

theorem confset_width : Claims.confset_width := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ δ' τ τA ω n m hφ hκ htv hmar hδ0 hδ1 hδ'0 hδ'1 hn hm hv hlow
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hδ'0.le hn hm hv P Q htv hlow
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨hle, hup⟩ := confset_det P Q hφ hκ htv hmar hv.2.1 hn hm z (hE z hz).1 (hE z hz).2
  refine ⟨hle, hup, fun hlt ε hε hωε => ?_⟩
  have hTI := tv_mem_Ico P Q htv
  have hne : (crossSet (Demp φ z.1 z.2) τ).Nonempty := ⟨_, tv_mem_crossSet P Q htv z (hE z hz).1⟩
  have haI := alphaHat_mem_Ico hne
  have h1 : tauRight τ (alphaHat (Demp φ z.1 z.2) τ) ≤ τ (StatFormal.Distances.tvDist P Q) :=
    tauRight_le hv.2.1 haI.1 ⟨hlt, htv⟩
  have h2 : τA (alphaHat (Demp φ z.1 z.2) τ) ≤ τA (StatFormal.Distances.tvDist P Q) :=
    hlow.2.1 haI hTI hlt.le
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans htv.le⟩
  calc omegaGen ω (tauRight τ (alphaHat (Demp φ z.1 z.2) τ) + τA (alphaHat (Demp φ z.1 z.2) τ))
      ≤ omegaGen ω (τ (StatFormal.Distances.tvDist P Q) + τA (StatFormal.Distances.tvDist P Q)) :=
        omegaGen_mono ω (add_le_add h1 h2)
    _ = omegaGen ω (ω ε) := by rw [hωε]
    _ ≤ ε := omegaGen_apply_le hmar.1 hε1

theorem upperfs : Claims.upperfs := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τA ω n m hφ hκ htv hmar hδ0 hδ1 hn hm hlow
  obtain ⟨-, -, E, hEm, hEp, hE⟩ := hlow
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  have hDc : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + τA α := fun α hα => by
    linarith [hE z hz α hα]
  exact ⟨hDc, upperfs_onEvent P Q hmar htv hDc⟩

theorem alphaHi_le : Claims.alphaHi_le := by
  intro 𝒳 H _ _ _ _ _ φ κ τ τA ω n m hφ hκ hn hm _ hτm x y hne
  exact alphaHi_le_det hφ hκ hτm hn hm x y hne

theorem upperfs_interval : Claims.upperfs_interval := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ τ τA ω n m hφ hκ htv hmar hδ0 hδ1 hn hm hv hlow
  obtain ⟨E, hEm, hEp, hE⟩ := two_events hφ hδ0.le hδ0.le hn hm hv P Q htv hlow
  refine ⟨E, hEm, by rw [show 1 - 2 * δ = 1 - δ - δ by ring]; exact hEp, fun z hz => ?_⟩
  have hTmem := tv_mem_crossSet P Q htv z (hE z hz).1
  have hDc : ∀ α ∈ Ico (0 : ℝ) 1, Dpop φ P Q α ≤ Demp φ z.1 z.2 α + τA α := fun α hα => by
    linarith [(hE z hz).2 α hα]
  exact ⟨alphaHat_le_of_mem hTmem, upperfs_onEvent P Q hmar htv hDc,
    alphaHi_le_det hφ hκ hv.2.1 hn hm z.1 z.2 ⟨_, hTmem⟩⟩

/-! ### Instances: the v1 threshold -/

theorem hausdorff_valid : Claims.hausdorff_valid := by
  intro 𝒳 H _ _ _ _ _ φ κ δ n m hφ hκ hκ0 hδ0 hδ1 hn hm
  refine ⟨⟨fun α hα => add_nonneg (rn_nonneg hκ0 hα.2 _ n) (rn_nonneg hκ0 hα.2 _ m),
    tau_monotoneOn hκ0 δ n m, ?_⟩, (tau_continuousOn κ δ n m).mono fun x hx => hx.2, fun hκpos => ?_⟩
  · intro α hα P' Q' hP' hQ' htv
    haveI := hP'
    haveI := hQ'
    exact (test_level 𝒳 H P' Q' φ κ α δ n m hφ hκ hα.1 hα.2 hδ0 hδ1 hn hm htv).2
  · set C := (4 / √(n : ℝ) + √(2 * Real.log (2 / (δ / 2)) / n)) +
      (4 / √(m : ℝ) + √(2 * Real.log (2 / (δ / 2)) / m)) with hCdef
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hC : 0 < C := by
      have h1 : 0 < 4 / √(n : ℝ) := div_pos (by norm_num) (Real.sqrt_pos.2 hn')
      have h2 : 0 < 4 / √(m : ℝ) := div_pos (by norm_num) (Real.sqrt_pos.2 hm')
      have h3 := Real.sqrt_nonneg (2 * Real.log (2 / (δ / 2)) / n)
      have h4 := Real.sqrt_nonneg (2 * Real.log (2 / (δ / 2)) / m)
      linarith
    have heq : ∀ α, κ * (1 - α)⁻¹ * C = tau κ α δ n m := by
      intro α; simp only [tau, rn, hCdef]; ring
    have h1 : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun α : ℝ => 1 - α) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with α hα
        exact mem_Ioi.2 (sub_pos.2 (mem_Iio.1 hα))
    have h3 := ((tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hκpos).atTop_mul_const hC
    exact h3.congr fun α => heq α

theorem hausdorff_lower : Claims.hausdorff_lower := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ δ n m hφ hκ hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ x0
  obtain ⟨E, hEm, hEp, hE⟩ := exists_event P Q hφ hκ hδ0 hδ1 hn hm
  refine ⟨fun α hα => add_nonneg (rn_nonneg hκ0 hα.2 _ n) (rn_nonneg hκ0 hα.2 _ m),
    tau_monotoneOn hκ0 δ n m, E, hEm, hEp, fun z hz α hα => ?_⟩
  linarith [(abs_le.1 (hE z hz α hα)).1]

end StatFormal.Wave30tu
