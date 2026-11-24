import StatFormal.Wave30tl.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Proofs
import StatFormal.Archive.TrimmedMMD.AlphaHat
import StatFormal.Archive.Wave18b.RouteContinuity
import StatFormal.Archive.WaveP1a.RouteConsistency
import StatFormal.Archive.Wave8a.RouteGeorep

/-!
# Wave 30tl — `lem:crossing` (untrusted proof route)

* Continuity of `α ↦ D̂_α`: the certified Wave 18b `continuity_cont` at the empirical laws (`D̂ = D_{P_n,Q_m}` by definition).
  Monotonicity: nested regions (WaveP1a `Dpop_antitoneOn`).
* The crossing set is nonempty (`D̂ ≤ 2κ` and the certified `alphaest_wellDefined` for `κ > 0`; `κ = 0` gives `τ ≡ 0 ≥ D̂`),
  upward closed (`τ` nondecreasing), and contains its infimum (continuity, limit from the right).
* Measurability of `D̂_a`: the certified Wave 8a `georep_empirical` turns the regions into capped-simplex polytopes, so
  `{D̂_a < c}` is a countable union over a countable dense set of weight pairs of measurable sets.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

section Basic

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem kappa_nonneg_of {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (x : 𝒳) : 0 ≤ κ :=
  (norm_nonneg _).trans (hκ x)

theorem one_mem_region (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) : ∫ x, (1 : ℝ) • φ x ∂P ∈ region φ α P := by
  refine ⟨fun _ => 1, measurable_const, fun _ => ⟨zero_le_one, ?_⟩, by simp, rfl⟩
  rw [le_div_iff₀ (by linarith)]; linarith

theorem norm_one_integral_le (P : Measure 𝒳) [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ : ℝ}
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : ‖∫ x, (1 : ℝ) • φ x ∂P‖ ≤ κ := by
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun x => (1 : ℝ) • φ x) (C := κ)
    (ae_of_all _ fun x => by simpa using hκ x)
  simpa using h

/-- `D_{α,k}(P,Q) ≤ 2κ` for probability laws (`lem:attainment`: the regions are bounded by `κ`). -/
theorem Dpop_le_two_kappa (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : 𝒳 → H}
    {κ α : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) : Dpop φ P Q α ≤ 2 * κ := by
  refine (setDist_le_norm (one_mem_region P φ hα0 hα1) (one_mem_region Q φ hα0 hα1)).trans ?_
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_one_integral_le P hκ, norm_one_integral_le Q hκ]

theorem Demp_eq_Dpop {φ : 𝒳 → H} {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    Demp φ x y = Dpop φ (empirical x) (empirical y) := rfl

theorem Demp_le_two_kappa {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ∀ α ∈ Ico (0 : ℝ) 1, Demp φ x y α ≤ 2 * κ := by
  intro α hα
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hn) x
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hm) y
  exact Dpop_le_two_kappa _ _ hκ hα.1 hα.2

theorem Demp_nonneg (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (α : ℝ) : 0 ≤ Demp φ x y α :=
  StatFormal.WaveP1a.setDist_nonneg' _ _

theorem Demp_antitoneOn (φ : 𝒳 → H) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    AntitoneOn (Demp φ x y) (Ico 0 1) := by
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hn) x
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hm) y
  exact StatFormal.WaveP1a.Dpop_antitoneOn φ (empirical x) (empirical y)

theorem tau_zero_kappa (α δ : ℝ) (n m : ℕ) : tau 0 α δ n m = 0 := by
  simp [tau, rn]

theorem tau_continuousOn (κ δ : ℝ) (n m : ℕ) : ContinuousOn (fun α => tau κ α δ n m) (Iio 1) := by
  have hc : ContinuousOn (fun α : ℝ => κ / (1 - α)) (Iio 1) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun α hα => by
      simp only [mem_Iio] at hα; linarith
  unfold tau rn
  exact (hc.mul continuousOn_const).add (hc.mul continuousOn_const)

theorem tau_monotoneOn {κ : ℝ} (hκ : 0 ≤ κ) (δ : ℝ) (n m : ℕ) :
    MonotoneOn (fun α => tau κ α δ n m) (Ico 0 1) :=
  fun _ _ _ hb hab => tau_mono hκ hab hb.2 δ n m

/-- The crossing set is nonempty for every realization (`n, m ≥ 1`). -/
theorem crossSet_Demp_nonempty {φ : 𝒳 → H} {κ δ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    (crossSet (Demp φ x y) (fun α => tau κ α δ n m)).Nonempty := by
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (x ⟨0, hn⟩)
  have hle := Demp_le_two_kappa hκ hn hm x y
  rcases hκ0.lt_or_eq with hκpos | hκz
  · exact alphaest_wellDefined κ δ n m (Demp φ x y) hκpos hδ0 hδ1 hn hm hle
  · subst hκz
    refine ⟨0, ⟨le_rfl, one_pos⟩, ?_⟩
    show Demp φ x y 0 ≤ tau 0 0 δ n m
    rw [tau_zero_kappa]
    simpa using hle 0 ⟨le_rfl, one_pos⟩

end Basic

/-! ### The crossing set is `[α̂, 1)` (abstract) -/

theorem crossSet_eq_Ico {D τ : ℝ → ℝ} (hD : ContinuousOn D (Ico 0 1)) (hDa : AntitoneOn D (Ico 0 1))
    (hτc : ContinuousOn τ (Iio 1)) (hτm : MonotoneOn τ (Ico 0 1)) (hne : (crossSet D τ).Nonempty) :
    crossSet D τ = Ico (alphaHat D τ) 1 := by
  have h0 : 0 ≤ alphaHat D τ := alphaHat_nonneg hne
  obtain ⟨s₀, hs₀⟩ := hne
  have hlt1 : alphaHat D τ < 1 := lt_of_le_of_lt (csInf_le (crossSet_bddBelow D τ) hs₀) hs₀.1.2
  have hup : ∀ α ∈ Ioo (alphaHat D τ) 1, α ∈ crossSet D τ := by
    intro α hα
    obtain ⟨s, hs, hsα⟩ := exists_lt_of_csInf_lt ⟨s₀, hs₀⟩ hα.1
    have hαI : α ∈ Ico (0 : ℝ) 1 := ⟨h0.trans hα.1.le, hα.2⟩
    refine ⟨hαI, ?_⟩
    calc D α ≤ D s := hDa hs.1 hαI hsα.le
      _ ≤ τ s := hs.2
      _ ≤ τ α := hτm hs.1 hαI hsα.le
  have hat : alphaHat D τ ∈ crossSet D τ := by
    set a := alphaHat D τ
    have haI : a ∈ Ico (0 : ℝ) 1 := ⟨h0, hlt1⟩
    refine ⟨haI, ?_⟩
    haveI := left_nhdsWithin_Ioo_neBot hlt1
    have hsub : Ioo a 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨h0.trans ht.1.le, ht.2⟩
    have hsub' : Ioo a 1 ⊆ Iio (1 : ℝ) := fun t ht => ht.2
    have hf : Tendsto (fun t => D t - τ t) (𝓝[Ioo a 1] a) (𝓝 (D a - τ a)) :=
      (((hD a haI).mono hsub).sub ((hτc a hlt1).mono hsub')).tendsto
    have hev : ∀ᶠ t in 𝓝[Ioo a 1] a, D t - τ t ≤ 0 :=
      eventually_nhdsWithin_of_forall fun t ht => by have := (hup t ht).2; linarith
    have := le_of_tendsto hf hev
    linarith
  ext α
  constructor
  · intro hα
    exact ⟨csInf_le (crossSet_bddBelow D τ) hα, hα.1.2⟩
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h | h
    · exact hup α ⟨h, h2⟩
    · rw [← h]; exact hat

section Crossing

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem Demp_continuousOn {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) : ContinuousOn (Demp φ x y) (Ico 0 1) := by
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hn) x
  haveI := isProbabilityMeasure_empirical (Nat.one_le_iff_ne_zero.1 hm) y
  exact StatFormal.Wave18b.continuity_cont 𝒳 H (empirical x) (empirical y) φ κ hφ hκ

theorem crossSet_Demp_eq {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    crossSet (Demp φ x y) (fun α => tau κ α δ n m) =
      Ico (alphaHat (Demp φ x y) (fun α => tau κ α δ n m)) 1 :=
  crossSet_eq_Ico (Demp_continuousOn hφ hκ hn hm x y) (Demp_antitoneOn φ hn hm x y)
    (tau_continuousOn κ δ n m) (tau_monotoneOn (kappa_nonneg_of hκ (x ⟨0, hn⟩)) δ n m)
    (crossSet_Demp_nonempty hκ hδ0 hδ1 hn hm x y)

theorem alphaHat_mem_crossSet {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    alphaHat (Demp φ x y) (fun α => tau κ α δ n m) ∈ crossSet (Demp φ x y) (fun α => tau κ α δ n m) := by
  have hne := crossSet_Demp_nonempty hκ hδ0 hδ1 hn hm x y
  rw [crossSet_Demp_eq hφ hκ hδ0 hδ1 hn hm x y]
  rw [crossSet_Demp_eq hφ hκ hδ0 hδ1 hn hm x y] at hne
  obtain ⟨s, hs⟩ := hne
  exact ⟨le_rfl, lt_of_le_of_lt hs.1 hs.2⟩

theorem mem_crossSet_iff_le {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    alphaHat (Demp φ x y) (fun α => tau κ α δ n m) ≤ a ↔ Demp φ x y a ≤ tau κ a δ n m := by
  have h := crossSet_Demp_eq hφ hκ hδ0 hδ1 hn hm x y
  constructor
  · intro hle
    have : a ∈ crossSet (Demp φ x y) (fun α => tau κ α δ n m) := by rw [h]; exact ⟨hle, ha1⟩
    exact this.2
  · intro hle
    have : a ∈ crossSet (Demp φ x y) (fun α => tau κ α δ n m) := ⟨⟨ha0, ha1⟩, hle⟩
    rw [h] at this
    exact this.1

/-- A rejected level (`τ(g) < D̂_g`) in `[0,1)` lies below `α̂`. -/
theorem lt_alphaHat_of_reject {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) (hrej : tau κ g δ n m < Demp φ x y g) :
    g < alphaHat (Demp φ x y) (fun α => tau κ α δ n m) := by
  by_contra h
  push_neg at h
  have := (mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm x y hg0 hg1).1 h
  linarith

end Crossing

/-! ### Measurability of `D̂_a` and of `α̂` -/

section Meas

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The weight-pair objective `‖Σ w_i φ(x_i) − Σ v_j φ(y_j)‖`. -/
def wobj (φ : 𝒳 → H) {n m : ℕ} (p : (Fin n → ℝ) × (Fin m → ℝ)) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  ‖∑ i, p.1 i • φ (z.1 i) - ∑ j, p.2 j • φ (z.2 j)‖

theorem wobj_measurable {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {n m : ℕ}
    (p : (Fin n → ℝ) × (Fin m → ℝ)) : Measurable (wobj φ p) := by
  have h1 : ∀ i, StronglyMeasurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => p.1 i • φ (z.1 i) := fun i =>
    (hφ.comp_measurable ((measurable_pi_apply i).comp measurable_fst)).const_smul (p.1 i)
  have h2 : ∀ j, StronglyMeasurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => p.2 j • φ (z.2 j) := fun j =>
    (hφ.comp_measurable ((measurable_pi_apply j).comp measurable_snd)).const_smul (p.2 j)
  have hs1 := Finset.stronglyMeasurable_fun_sum
    (f := fun i (z : (Fin n → 𝒳) × (Fin m → 𝒳)) => p.1 i • φ (z.1 i)) Finset.univ (fun i _ => h1 i)
  have hs2 := Finset.stronglyMeasurable_fun_sum
    (f := fun j (z : (Fin n → 𝒳) × (Fin m → 𝒳)) => p.2 j • φ (z.2 j)) Finset.univ (fun j _ => h2 j)
  exact (hs1.sub hs2).norm.measurable

theorem wobj_continuous (φ : 𝒳 → H) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) => wobj φ p z := by
  unfold wobj
  fun_prop

theorem Demp_eq_sInf_wobj {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Demp φ z.1 z.2 a =
      sInf ((fun p => wobj φ p z) ''
        (StatFormal.TrimmedMMD.BangBang.capped n a ×ˢ StatFormal.TrimmedMMD.BangBang.capped m a)) := by
  have hx := StatFormal.Wave8a.georep_empirical 𝒳 H φ a n z.1 hφ ha0 ha1 hn
  have hy := StatFormal.Wave8a.georep_empirical 𝒳 H φ a m z.2 hφ ha0 ha1 hm
  unfold Demp setDist
  rw [hx, hy]
  congr 1
  ext r
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, v, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨(w, w'), ⟨hw, hw'⟩, rfl⟩
  · rintro ⟨⟨w, w'⟩, ⟨hw, hw'⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, _, ⟨w', hw', rfl⟩, rfl⟩

theorem capped_nonempty {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (StatFormal.TrimmedMMD.BangBang.capped n a).Nonempty := by
  refine ⟨fun _ => 1 / n, fun _ => ⟨by positivity, ?_⟩, ?_⟩
  · unfold StatFormal.TrimmedMMD.BangBang.cap
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ hn' (mul_pos hn' (by linarith))]
    nlinarith
  · have hn' : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact this.ne'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem measurable_Demp {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Demp φ z.1 z.2 a := by
  set K := StatFormal.TrimmedMMD.BangBang.capped n a ×ˢ StatFormal.TrimmedMMD.BangBang.capped m a
  have hKne : K.Nonempty := (capped_nonempty hn ha0 ha1).prod (capped_nonempty hm ha0 ha1)
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hbdd : ∀ z, BddBelow ((fun p => wobj φ p z) '' K) := fun z =>
    ⟨0, by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg _⟩
  have key : ∀ c, (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => Demp φ z.1 z.2 a) ⁻¹' Iio c =
      ⋃ d ∈ D, {z | wobj φ d z < c} := by
    intro c
    ext z
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq, exists_prop]
    rw [Demp_eq_sInf_wobj hφ hn hm ha0 ha1 z, csInf_lt_iff (hbdd z) (hKne.image _)]
    constructor
    · rintro ⟨_, ⟨p, hpK, rfl⟩, hpc⟩
      have hU : IsOpen {q : (Fin n → ℝ) × (Fin m → ℝ) | wobj φ q z < c} :=
        isOpen_lt (wobj_continuous φ z) continuous_const
      obtain ⟨d, hdU, hdD⟩ := mem_closure_iff.1 (hKD hpK) _ hU hpc
      exact ⟨d, hdD, hdU⟩
    · rintro ⟨d, hdD, hdc⟩
      exact ⟨_, ⟨d, hDK hdD, rfl⟩, hdc⟩
  refine measurable_of_Iio fun c => ?_
  rw [key c]
  exact MeasurableSet.biUnion hDc fun d _ => measurableSet_lt (wobj_measurable hφ d) measurable_const

theorem measurable_alphaHat {φ : 𝒳 → H} {κ δ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Measurable fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) := by
  refine measurable_of_Iic fun c => ?_
  by_cases hc0 : c < 0
  · convert MeasurableSet.empty
    ext z
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hc0 (alphaHat_nonneg (crossSet_Demp_nonempty hκ hδ0 hδ1 hn hm z.1 z.2))
  push_neg at hc0
  by_cases hc1 : c < 1
  · have : (fun z : (Fin n → 𝒳) × (Fin m → 𝒳) => alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m)) ⁻¹'
        Iic c = {z | Demp φ z.1 z.2 c ≤ tau κ c δ n m} := by
      ext z
      exact mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm z.1 z.2 hc0 hc1
    rw [this]
    exact measurableSet_le (measurable_Demp hφ hn hm hc0 hc1) measurable_const
  · push_neg at hc1
    convert MeasurableSet.univ
    ext z
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    exact ((alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm z.1 z.2).1.2.le).trans hc1

end Meas

/-! ### Certified claims: `lem:crossing` -/

theorem crossing_path : Claims.crossing_path := by
  intro 𝒳 H _ _ _ _ _ φ κ n m hφ hκ hn hm x y
  exact ⟨Demp_continuousOn hφ hκ hn hm x y, Demp_antitoneOn φ hn hm x y⟩

theorem crossing_set : Claims.crossing_set := by
  intro 𝒳 H _ _ _ _ _ φ κ δ n m hφ hκ hδ0 hδ1 hn hm x y
  exact crossSet_Demp_eq hφ hκ hδ0 hδ1 hn hm x y

theorem crossing_attained : Claims.crossing_attained := by
  intro 𝒳 H _ _ _ _ _ φ κ δ n m hφ hκ hδ0 hδ1 hn hm x y
  exact ⟨alphaHat_mem_crossSet hφ hκ hδ0 hδ1 hn hm x y, fun α hα => csInf_le (crossSet_bddBelow _ _) hα⟩

theorem crossing_le_iff : Claims.crossing_le_iff := by
  intro 𝒳 H _ _ _ _ _ φ κ δ n m hφ hκ hδ0 hδ1 hn hm a ha0 ha1
  ext z
  exact mem_crossSet_iff_le hφ hκ hδ0 hδ1 hn hm z.1 z.2 ha0 ha1

theorem crossing_measurable : Claims.crossing_measurable := by
  intro 𝒳 H _ _ _ _ _ φ κ δ n m hφ hκ hδ0 hδ1 hn hm
  exact ⟨fun a ha0 ha1 => measurable_Demp hφ hn hm ha0 ha1, measurable_alphaHat hφ hκ hδ0 hδ1 hn hm⟩

end StatFormal.Wave30tl
