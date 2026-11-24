import StatFormal.Wave30tu.Statements
import StatFormal.Wave30tl.RouteConfset

/-!
# Wave 30tu — basic route (untrusted): events, the crossing set for a general threshold, `rem:grid`, `lem:oneevent`

* `valid_event`: validity at a true null makes `{D̂_α ≤ τ(α)}` a measurable event of probability `≥ 1 − δ`.
* `inter_prob`: `P(A ∩ B) ≥ 1 − a − b` (union bound).
* The crossing set of a nondecreasing `τ` and the continuous nonincreasing path contains `(α̂,1)`; `D̂_{α̂} ≤ τ(α̂+)` by letting
  `a ↓ α̂` (Mathlib's `MonotoneOn.tendsto_nhdsWithin_Ioo_right` gives the right limit).
* `D̂ ≤ D_φ`: the capped-simplex representation (Wave 8a `georep_empirical`) and convex weights.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tu

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.Wave30tl

/-! ### Probability helpers -/

theorem compl_le_of_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} {a : ℝ}
    (hA : MeasurableSet A) (hμA : ENNReal.ofReal (1 - a) ≤ μ A) : μ Aᶜ ≤ ENNReal.ofReal a := by
  rw [prob_compl_eq_one_sub hA]
  calc 1 - μ A ≤ 1 - ENNReal.ofReal (1 - a) := tsub_le_tsub_left hμA 1
    _ ≤ ENNReal.ofReal a := by
      rw [tsub_le_iff_right]
      calc (1 : ENNReal) = ENNReal.ofReal (a + (1 - a)) := by simp
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal (1 - a) := ENNReal.ofReal_add_le

theorem ge_of_compl_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} {a : ℝ}
    (hA : MeasurableSet A) (ha : 0 ≤ a) (hc : μ Aᶜ ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ μ A := by
  calc ENNReal.ofReal (1 - a) = 1 - ENNReal.ofReal a := by rw [ENNReal.ofReal_sub _ ha, ENNReal.ofReal_one]
    _ ≤ 1 - μ Aᶜ := tsub_le_tsub_left hc 1
    _ = μ A := by rw [prob_compl_eq_one_sub hA, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

theorem inter_prob {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω} {a b : ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμA : ENNReal.ofReal (1 - a) ≤ μ A) (hμB : ENNReal.ofReal (1 - b) ≤ μ B) :
    ENNReal.ofReal (1 - a - b) ≤ μ (A ∩ B) := by
  have hc : μ (A ∩ B)ᶜ ≤ ENNReal.ofReal (a + b) := by
    rw [Set.compl_inter]
    calc μ (Aᶜ ∪ Bᶜ) ≤ μ Aᶜ + μ Bᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add (compl_le_of_ge hA hμA) (compl_le_of_ge hB hμB)
      _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
  have := ge_of_compl_le (hA.inter hB) (add_nonneg ha hb) hc
  rwa [show 1 - (a + b) = 1 - a - b by ring] at this

/-! ### The crossing set of a general threshold -/

theorem alphaHat_lt_one {D τ : ℝ → ℝ} (hne : (crossSet D τ).Nonempty) : alphaHat D τ < 1 := by
  obtain ⟨s, hs⟩ := hne
  exact lt_of_le_of_lt (csInf_le (crossSet_bddBelow D τ) hs) hs.1.2

theorem alphaHat_mem_Ico {D τ : ℝ → ℝ} (hne : (crossSet D τ).Nonempty) : alphaHat D τ ∈ Ico (0 : ℝ) 1 :=
  ⟨alphaHat_nonneg hne, alphaHat_lt_one hne⟩

theorem alphaHat_le_of_mem {D τ : ℝ → ℝ} {a : ℝ} (ha : a ∈ crossSet D τ) : alphaHat D τ ≤ a :=
  csInf_le (crossSet_bddBelow D τ) ha

theorem Ioo_subset_crossSet {D τ : ℝ → ℝ} (hDa : AntitoneOn D (Ico 0 1)) (hτm : MonotoneOn τ (Ico 0 1))
    (hne : (crossSet D τ).Nonempty) : Ioo (alphaHat D τ) 1 ⊆ crossSet D τ := by
  intro α hα
  obtain ⟨s, hs, hsα⟩ := exists_lt_of_csInf_lt hne hα.1
  have hαI : α ∈ Ico (0 : ℝ) 1 := ⟨(alphaHat_nonneg hne).trans hα.1.le, hα.2⟩
  refine ⟨hαI, ?_⟩
  calc D α ≤ D s := hDa hs.1 hαI hsα.le
    _ ≤ τ s := hs.2
    _ ≤ τ α := hτm hs.1 hαI hsα.le

theorem tauRight_bddBelow {τ : ℝ → ℝ} {a : ℝ} (hτm : MonotoneOn τ (Ico 0 1)) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    BddBelow (τ '' Ioo a 1) :=
  ⟨τ a, by rintro _ ⟨t, ht, rfl⟩; exact hτm ⟨ha0, ha1⟩ ⟨ha0.trans ht.1.le, ht.2⟩ ht.1.le⟩

theorem tauRight_tendsto {τ : ℝ → ℝ} {a : ℝ} (hτm : MonotoneOn τ (Ico 0 1)) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto τ (𝓝[>] a) (𝓝 (tauRight τ a)) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 ha1)
    (hτm.mono fun t ht => ⟨ha0.trans ht.1.le, ht.2⟩) (tauRight_bddBelow hτm ha0 ha1)

theorem le_tauRight_self {τ : ℝ → ℝ} {a : ℝ} (hτm : MonotoneOn τ (Ico 0 1)) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    τ a ≤ tauRight τ a :=
  le_csInf ((nonempty_Ioo.2 ha1).image _) (by
    rintro _ ⟨t, ht, rfl⟩; exact hτm ⟨ha0, ha1⟩ ⟨ha0.trans ht.1.le, ht.2⟩ ht.1.le)

theorem tauRight_le {τ : ℝ → ℝ} {a b : ℝ} (hτm : MonotoneOn τ (Ico 0 1)) (ha0 : 0 ≤ a) (hb : b ∈ Ioo a 1) :
    tauRight τ a ≤ τ b :=
  csInf_le (tauRight_bddBelow hτm ha0 (hb.1.trans hb.2)) ⟨b, hb, rfl⟩

theorem tauRight_eq {τ : ℝ → ℝ} {a : ℝ} (hτm : MonotoneOn τ (Ico 0 1)) (ha0 : 0 < a) (ha1 : a < 1)
    (hτc : ContinuousOn τ (Ioo 0 1)) : tauRight τ a = τ a := by
  have h1 := tauRight_tendsto hτm ha0.le ha1
  have h2 : Tendsto τ (𝓝[>] a) (𝓝 (τ a)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((hτc.continuousAt (Ioo_mem_nhds ha0 ha1)).tendsto)
  exact tendsto_nhds_unique h1 h2

/-- `D(α̂) ≤ τ(α̂+)` for a continuous nonincreasing path and a nondecreasing threshold. -/
theorem le_tauRight {D τ : ℝ → ℝ} (hD : ContinuousOn D (Ico 0 1)) (hDa : AntitoneOn D (Ico 0 1))
    (hτm : MonotoneOn τ (Ico 0 1)) (hne : (crossSet D τ).Nonempty) :
    D (alphaHat D τ) ≤ tauRight τ (alphaHat D τ) := by
  set a := alphaHat D τ
  have haI := alphaHat_mem_Ico hne
  have hup := Ioo_subset_crossSet hDa hτm hne
  have hsub : Ioi a ⊆ Ico (0 : ℝ) 1 ∪ Ici 1 := fun t ht => by
    by_cases h : t < 1
    · exact Or.inl ⟨haI.1.trans ht.le, h⟩
    · exact Or.inr (not_lt.1 h)
  have hDt : Tendsto D (𝓝[>] a) (𝓝 (D a)) := by
    have : 𝓝[Ioo a 1] a = 𝓝[>] a := nhdsWithin_Ioo_eq_nhdsGT haI.2
    rw [← this]
    exact ((hD a haI).mono fun t ht => ⟨haI.1.trans ht.1.le, ht.2⟩).tendsto
  have hev : ∀ᶠ t in 𝓝[>] a, D t ≤ τ t := by
    filter_upwards [Ioo_mem_nhdsGT haI.2] with t ht
    exact (hup ht).2
  exact le_of_tendsto_of_tendsto hDt (tauRight_tendsto hτm haI.1 haI.2) hev

/-! ### The empirical path -/

section Path

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem norm_convex_sub_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (f : ι → H) (c : H) (D : ℝ) (hD : ∀ i, ‖f i - c‖ ≤ D) : ‖∑ i, w i • f i - c‖ ≤ D := by
  have h : ∑ i, w i • f i - c = ∑ i, w i • (f i - c) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  rw [h]
  calc ‖∑ i, w i • (f i - c)‖ ≤ ∑ i, ‖w i • (f i - c)‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖f i - c‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hw0 i)]
    _ ≤ ∑ i, w i * D := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hD i) (hw0 i)
    _ = D := by rw [← Finset.sum_mul, hw1, one_mul]

/-- `D̂_α ≤ D_φ` (convex combinations of feature vectors). -/
theorem Demp_le_D {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {D : ℝ} (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) :
    Demp φ x y α ≤ D := by
  have hrep := Demp_eq_sInf_wobj hφ hn hm hα.1 hα.2 (x, y)
  obtain ⟨w, hw⟩ := capped_nonempty hn hα.1 hα.2
  obtain ⟨v, hv⟩ := capped_nonempty hm hα.1 hα.2
  have hle : Demp φ (x, y).1 (x, y).2 α ≤ wobj φ (w, v) (x, y) := by
    rw [hrep]
    exact csInf_le ⟨0, by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg _⟩ ⟨(w, v), ⟨hw, hv⟩, rfl⟩
  refine hle.trans ?_
  show ‖∑ i, w i • φ (x i) - ∑ j, v j • φ (y j)‖ ≤ D
  refine norm_convex_sub_le w (fun i => (hw.1 i).1) hw.2 _ _ D fun i => ?_
  rw [norm_sub_rev]
  exact norm_convex_sub_le v (fun j => (hv.1 j).1) hv.2 _ _ D fun j => hD _ _

end Path

/-! ### The event of a valid threshold -/

section Events

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem valid_event {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {δ : ℝ} (hδ0 : 0 ≤ δ) {τ : ℝ → ℝ} {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hv : ValidThreshold φ n m δ τ) (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) (htv : StatFormal.Distances.tvDist P Q ≤ α) :
    MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | Demp φ z.1 z.2 α ≤ τ α} ∧
      ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
        {z | Demp φ z.1 z.2 α ≤ τ α} := by
  have hm' : MeasurableSet {z : (Fin n → 𝒳) × (Fin m → 𝒳) | Demp φ z.1 z.2 α ≤ τ α} :=
    measurableSet_le (measurable_Demp hφ hn hm hα.1 hα.2) measurable_const
  refine ⟨hm', ge_of_compl_le hm' hδ0 ?_⟩
  have hc : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | Demp φ z.1 z.2 α ≤ τ α}ᶜ = {z | τ α < Demp φ z.1 z.2 α} := by
    ext z; simp [not_le]
  rw [hc]
  exact hv.2.2 α hα P Q inferInstance inferInstance htv

end Events

/-! ### Grid helpers (`rem:grid`) -/

theorem mesh_nonneg {G : Finset ℝ} {h : ℝ} (hG : MeshGrid G h) (hne : G.Nonempty) : 0 ≤ h := by
  obtain ⟨g, hg⟩ := hne
  obtain ⟨g', -, h1, h2⟩ := hG.2 0 le_rfl ⟨g, hg, (hG.1 g hg).1⟩
  linarith

theorem lastRejected_le {D τ : ℝ → ℝ} (hDa : AntitoneOn D (Ico 0 1)) (hτm : MonotoneOn τ (Ico 0 1))
    (hne : (crossSet D τ).Nonempty) {G : Finset ℝ} {h : ℝ} (hG : MeshGrid G h) {b : ℝ}
    (hb : b ∈ G) (hrej : τ b < D b) : b ≤ alphaHat D τ := by
  by_contra hlt
  push_neg at hlt
  have := (Ioo_subset_crossSet hDa hτm hne ⟨hlt, (hG.1 b hb).2⟩).2
  linarith

theorem gridReturn_le' {D τ : ℝ → ℝ} (hDa : AntitoneOn D (Ico 0 1)) (hτm : MonotoneOn τ (Ico 0 1))
    (hne : (crossSet D τ).Nonempty) {G : Finset ℝ} {h : ℝ} (hG : MeshGrid G h) {a : ℝ}
    (ha : GridReturn G D τ a) : a ≤ alphaHat D τ + h := by
  set A := alphaHat D τ
  have hA0 : 0 ≤ A := alphaHat_nonneg hne
  rcases ha with ha | ⟨hall, ha⟩
  · have hGne : G.Nonempty := ⟨a, ha.1.1⟩
    have hh := mesh_nonneg hG hGne
    by_cases hex : ∃ g ∈ G, A < g
    · classical
      set F := G.filter (fun g => A < g)
      have hFne : F.Nonempty := by
        obtain ⟨g, hg, hgA⟩ := hex
        exact ⟨g, Finset.mem_filter.2 ⟨hg, hgA⟩⟩
      set g₀ := F.min' hFne
      have hg₀F : g₀ ∈ F := F.min'_mem hFne
      have hg₀G : g₀ ∈ G := (Finset.mem_filter.1 hg₀F).1
      have hg₀A : A < g₀ := (Finset.mem_filter.1 hg₀F).2
      have hg₀le : g₀ ≤ A + h := by
        by_contra hgt
        push_neg at hgt
        set d := g₀ - h - A
        have hd : 0 < d := by simp only [d]; linarith
        obtain ⟨g, hgG, hg1, hg2⟩ := hG.2 (A + d / 2) (by linarith) ⟨g₀, hg₀G, by simp only [d]; linarith⟩
        have hgF : g ∈ F := Finset.mem_filter.2 ⟨hgG, by linarith⟩
        have := F.min'_le g hgF
        simp only [d] at hg2
        linarith
      have hmem : g₀ ∈ crossSet D τ := Ioo_subset_crossSet hDa hτm hne ⟨hg₀A, (hG.1 g₀ hg₀G).2⟩
      exact (ha.2 ⟨hg₀G, hmem.2⟩).trans hg₀le
    · push_neg at hex
      linarith [hex a ha.1.1]
  · have hGne : G.Nonempty := ⟨a, ha.1⟩
    have hh := mesh_nonneg hG hGne
    have := lastRejected_le hDa hτm hne hG ha.1 (hall a ha.1)
    linarith

end StatFormal.Wave30tu
