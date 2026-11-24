import StatFormal.Wave30tz.Statements
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Route: Lemma 7 (ramps of a fixed direction are bounded by `KS⁺`) (untrusted proof material)

Proves the frozen claim `Claims.ramp_ks` of `StatFormal.Wave30tz.Statements`.

* `ksPlus_bdd`, `le_ksPlus`: the `iSup` defining `KS⁺` is bounded above (values in `[-1, 1]`),
  so it dominates each value;
* `sub_le_ksPlus_of_iInter`: limits of the values along decreasing level sets stay below `KS⁺`;
  hence `ksPlus_nonneg` and the closed level sets `{c ≤ f}`;
* `sub_le_ksPlus_of_isUpperSet`: `P(f ∈ U) − Q(f ∈ U) ≤ KS⁺(f)` for every up-set `U ⊆ ℝ`;
* `integral_eq_intervalIntegral_meas_lt`: the layer cake `E g = ∫_0^1 P(g > s) ds` for
  measurable `g` with values in `[0,1]`;
* `ramp_ks_route : Claims.ramp_ks`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq

section KS

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem ksPlus_bdd (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (f : 𝒳 → ℝ) :
    BddAbove (range fun x : ℝ => P.real {z | x < f z} - Q.real {z | x < f z}) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h1 : P.real {z | x < f z} ≤ 1 := measureReal_le_one
  have h2 : 0 ≤ Q.real {z | x < f z} := measureReal_nonneg
  simp only
  linarith

theorem le_ksPlus (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (f : 𝒳 → ℝ) (x : ℝ) :
    P.real {z | x < f z} - Q.real {z | x < f z} ≤ ksPlus P Q f :=
  le_ciSup (f := fun x : ℝ => P.real {z | x < f z} - Q.real {z | x < f z}) (ksPlus_bdd P Q f) x

theorem tendsto_measureReal_iInter_of_antitone (μ : Measure 𝒳) [IsFiniteMeasure μ] {s : ℕ → Set 𝒳}
    (hs : ∀ n, MeasurableSet (s n)) (hm : Antitone s) :
    Tendsto (fun n => μ.real (s n)) atTop (𝓝 (μ.real (⋂ n, s n))) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hs n).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ _⟩
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

theorem sub_le_ksPlus_of_iInter (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hf : Measurable f) {x : ℕ → ℝ} (hx : Monotone x) {S : Set 𝒳} (hS : ⋂ n, {z | x n < f z} = S) :
    P.real S - Q.real S ≤ ksPlus P Q f := by
  have hm : Antitone fun n => {z | x n < f z} := fun m n hmn z hz => lt_of_le_of_lt (hx hmn) hz
  have hs : ∀ n, MeasurableSet {z | x n < f z} := fun n => measurableSet_lt measurable_const hf
  have h := (tendsto_measureReal_iInter_of_antitone P hs hm).sub (tendsto_measureReal_iInter_of_antitone Q hs hm)
  rw [hS] at h
  exact le_of_tendsto' h fun n => le_ksPlus P Q f (x n)

theorem ksPlus_nonneg (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hf : Measurable f) : 0 ≤ ksPlus P Q f := by
  have h := sub_le_ksPlus_of_iInter P Q hf (x := fun n : ℕ => (n : ℝ)) (fun m n hmn => Nat.cast_le.2 hmn)
    (S := ∅) (by
      ext z
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_gt (f z)
      exact ⟨n, hn.le⟩)
  simpa using h

theorem sub_le_ksPlus_Ici (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hf : Measurable f) (c : ℝ) : P.real {z | c ≤ f z} - Q.real {z | c ≤ f z} ≤ ksPlus P Q f := by
  refine sub_le_ksPlus_of_iInter P Q hf (x := fun n : ℕ => c - 1 / ((n : ℝ) + 1)) ?_ ?_
  · intro m n hmn
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    have := one_div_le_one_div_of_le h1 h2
    simp only
    linarith
  · ext z
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      have := h n
      linarith
    · intro h n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith

/-- `P(f ∈ U) − Q(f ∈ U) ≤ KS⁺(f)` for every up-set `U` of `ℝ` (`∅`, `ℝ`, `(c, ∞)` or `[c, ∞)`). -/
theorem sub_le_ksPlus_of_isUpperSet (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hf : Measurable f) {U : Set ℝ} (hU : IsUpperSet U) :
    P.real (f ⁻¹' U) - Q.real (f ⁻¹' U) ≤ ksPlus P Q f := by
  by_cases hne : U.Nonempty
  · by_cases hbdd : BddBelow U
    · set c := sInf U with hc_def
      have hIoi : Ioi c ⊆ U := fun y hy => by
        obtain ⟨w, hwU, hwy⟩ := exists_lt_of_csInf_lt hne hy
        exact hU hwy.le hwU
      have hIci : U ⊆ Ici c := fun y hy => csInf_le hbdd hy
      by_cases hc : c ∈ U
      · have hUe : U = Ici c := by
          ext y
          refine ⟨fun hy => hIci hy, fun hy => ?_⟩
          rcases eq_or_lt_of_le (mem_Ici.1 hy) with h | h
          · exact h ▸ hc
          · exact hIoi h
        rw [hUe]
        exact sub_le_ksPlus_Ici P Q hf c
      · have hUe : U = Ioi c := by
          ext y
          refine ⟨fun hy => lt_of_le_of_ne (mem_Ici.1 (hIci hy)) (fun h : c = y => hc (by rw [h]; exact hy)),
            fun hy => hIoi hy⟩
        rw [hUe]
        exact le_ksPlus P Q f c
    · have hUe : U = univ := by
        rw [not_bddBelow_iff] at hbdd
        ext y
        simp only [mem_univ, iff_true]
        obtain ⟨w, hwU, hwy⟩ := hbdd y
        exact hU hwy.le hwU
      rw [hUe, preimage_univ, probReal_univ, probReal_univ, sub_self]
      exact ksPlus_nonneg P Q hf
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, preimage_empty, measureReal_empty, measureReal_empty, sub_self]
    exact ksPlus_nonneg P Q hf

/-- The layer cake on `[0,1]`: `E_P g = ∫_0^1 P(g > s) ds` for measurable `g` with values in `[0,1]`. -/
theorem integral_eq_intervalIntegral_meas_lt (P : Measure 𝒳) [IsFiniteMeasure P] {g : 𝒳 → ℝ}
    (hg : Measurable g) (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1) :
    ∫ z, g z ∂P = ∫ s in (0 : ℝ)..1, P.real {z | s < g z} := by
  have hint : Integrable g P :=
    Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ fun z => ⟨h0 z, h1 z⟩)
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ h0), intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro s hs
  have hs1 : 1 < s := by
    simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hs
    exact hs.2 hs.1
  have : {z | s < g z} = ∅ := by
    ext z
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    linarith [h1 z]
  rw [this, measureReal_empty]

theorem antitone_measureReal_lt (P : Measure 𝒳) [IsFiniteMeasure P] (g : 𝒳 → ℝ) :
    Antitone fun s : ℝ => P.real {z | s < g z} :=
  fun _ _ hst => measureReal_mono (fun _ hz => lt_of_le_of_lt hst hz)

/-- `E_P g − E_Q g = ∫_0^1 {P(g > s) − Q(g > s)} ds` for measurable `g` with values in `[0,1]`. -/
theorem integral_sub_eq_intervalIntegral (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : 𝒳 → ℝ} (hg : Measurable g) (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1) :
    (∫ z, g z ∂P) - (∫ z, g z ∂Q) = ∫ s in (0 : ℝ)..1, (P.real {z | s < g z} - Q.real {z | s < g z}) := by
  rw [integral_eq_intervalIntegral_meas_lt P hg h0 h1, integral_eq_intervalIntegral_meas_lt Q hg h0 h1,
    intervalIntegral.integral_sub ((antitone_measureReal_lt P g).intervalIntegrable)
      ((antitone_measureReal_lt Q g).intervalIntegrable)]

/-- Lemma 7 (b): `E_P h(f) − E_Q h(f) ≤ KS⁺(f)` for nondecreasing `h : ℝ → [0,1]`. -/
theorem monotone_sub_le_ksPlus (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {f : 𝒳 → ℝ}
    (hf : Measurable f) {h : ℝ → ℝ} (hh : Monotone h) (hI : ∀ s, h s ∈ Icc (0 : ℝ) 1) :
    (∫ x, h (f x) ∂P) - (∫ y, h (f y) ∂Q) ≤ ksPlus P Q f := by
  have hg : Measurable fun z => h (f z) := hh.measurable.comp hf
  rw [integral_sub_eq_intervalIntegral P Q hg (fun z => (hI _).1) (fun z => (hI _).2)]
  have hii : IntervalIntegrable (fun s : ℝ => P.real {z | s < h (f z)} - Q.real {z | s < h (f z)}) volume 0 1 :=
    ((antitone_measureReal_lt P _).intervalIntegrable).sub ((antitone_measureReal_lt Q _).intervalIntegrable)
  calc ∫ s in (0 : ℝ)..1, (P.real {z | s < h (f z)} - Q.real {z | s < h (f z)})
      ≤ ∫ _ in (0 : ℝ)..1, ksPlus P Q f :=
        intervalIntegral.integral_mono_on zero_le_one hii intervalIntegrable_const fun s _ => by
          have hU : IsUpperSet {y : ℝ | s < h y} := fun a b hab ha => lt_of_lt_of_le ha (hh hab)
          exact sub_le_ksPlus_of_isUpperSet P Q hf hU
    _ = ksPlus P Q f := by simp

omit [MeasurableSpace 𝒳] in
/-- The level sets of the ramp: for `t > u` and `s ∈ [0,1)`, `{g > s} = {f > u + s(t−u)}`. -/
theorem ramp_lt_iff {f : 𝒳 → ℝ} {t u : ℝ} (htu : u < t) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (z : 𝒳) :
    s < ramp f t u z ↔ u + s * (t - u) < f z := by
  have hpos : 0 < t - u := sub_pos.2 htu
  unfold ramp clip
  rw [lt_div_iff₀ hpos]
  have key : s * (t - u) < min (max (f z) u) t - u ↔ u + s * (t - u) < min (max (f z) u) t := by
    constructor <;> intro h <;> linarith
  rw [key, lt_min_iff, lt_max_iff]
  have h1 : u + s * (t - u) < t := by nlinarith
  have h2 : ¬ u + s * (t - u) < u := by nlinarith
  tauto

omit [MeasurableSpace 𝒳] in
theorem ramp_mem_Icc {f : 𝒳 → ℝ} {t u : ℝ} (htu : u < t) (z : 𝒳) : ramp f t u z ∈ Icc (0 : ℝ) 1 := by
  have hpos : 0 < t - u := sub_pos.2 htu
  unfold ramp clip
  constructor
  · apply div_nonneg _ hpos.le
    have : u ≤ min (max (f z) u) t := le_min (le_max_right _ _) htu.le
    linarith
  · rw [div_le_one hpos]
    have : min (max (f z) u) t ≤ t := min_le_right _ _
    linarith

/-- Lemma 7. -/
theorem ramp_ks_route : Claims.ramp_ks := by
  intro 𝒳 _ P Q _ _ f hf
  refine ⟨fun t u htu => ?_, fun h hh hI => monotone_sub_le_ksPlus P Q hf hh hI⟩
  have hpos : 0 < t - u := sub_pos.2 htu
  -- the ramp as a nondecreasing function of `f`
  set r : ℝ → ℝ := fun y => (min (max y u) t - u) / (t - u) with hr
  have hrf : ∀ z, ramp f t u z = r (f z) := fun z => rfl
  have hrmono : Monotone r := by
    intro a b hab
    simp only [hr]
    apply div_le_div_of_nonneg_right _ hpos.le
    have := min_le_min_right t (max_le_max_right u hab)
    linarith
  have hrI : ∀ y, r y ∈ Icc (0 : ℝ) 1 := by
    intro y
    have := ramp_mem_Icc (f := fun _ : Unit => y) htu ()
    exact this
  have hg : Measurable (ramp f t u) := hrmono.measurable.comp hf
  refine ⟨?_, ?_⟩
  · rw [integral_sub_eq_intervalIntegral P Q hg (fun z => (ramp_mem_Icc htu z).1) (fun z => (ramp_mem_Icc htu z).2),
      intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hset : {z | s < ramp f t u z} = {z | u + s * (t - u) < f z} := by
      ext z
      exact ramp_lt_iff htu hs.1.le hs.2 z
    simp only [hset]
  · have := monotone_sub_le_ksPlus P Q hf hrmono hrI
    simpa only [← hrf] using this

end KS

end StatFormal.Wave30tz
