import StatFormal.Wave31tu.Statements
import StatFormal.Wave30tz.RouteLower
import StatFormal.Wave31tl.RouteArith

/-!
# Wave 31tu route T: the event `𝓔_fit` of the proof of Theorem S4.19 (S4 :1349-1353; untrusted proof material)

* `exists_gapsGe`: a strictly increasing finite grid has a positive lower bound `h₀` on its consecutive gaps (the `h₀` of `J_ε`).
* `nullSingleton_of_density`: a law with a Lebesgue density has no atoms.
* `measurableSet_cross`: `{z | ∀ i j, z.1 i ≠ z.2 j}` is measurable.
* `fitSample_compl_le`: an event of probability `≥ 1 − a` for the fitting sample of batch `b` (an i.i.d. sample of size `n_{<b}`) has
  probability `≥ 1 − a` as a function of the whole sample (the certified marginal `Wave30tz.Lower.map_fitSample`).
* `fit_event`: the intersection of the four events of Lemma S4.23 (`η′ = η/8`, the common `x = log(16(n∨m+1)²/η)`) for the `X`'s and
  the `Y`'s of batch 0 and of batches 0 and 1, and of the a.s. event "no `X` equals a `Y`" (Lemma S4.23 (c)), has complement of
  probability `≤ η/2` (Claim Y4 as a hypothesis).
* `default_batches`: with the batches of Section 4.2 and `n∧m ≥ 10`, every pair lies in batch 1 or 2, the fitting samples of batches 1
  and 2 have at least `(n∧m)/5` and at most `n`, `m` observations, and `N ≥ (n∧m)/2`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteT

open StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave30tv

/-- A strictly increasing grid has a positive lower bound on its consecutive gaps. -/
lemma exists_gapsGe {J : ℕ} {α : Fin J → ℝ} (hα : StrictMono α) : ∃ h0 : ℝ, 0 < h0 ∧ GapsGe α h0 := by
  classical
  by_cases hJ : J ≤ 1
  · exact ⟨1, one_pos, fun j hj => absurd hj (by omega)⟩
  · push_neg at hJ
    let gap : Fin J → ℝ := fun j => if h : j.1 + 1 < J then α ⟨j.1 + 1, h⟩ - α j else 1
    have hpos : ∀ j, 0 < gap j := by
      intro j
      simp only [gap]
      split_ifs with h
      · have : α j < α ⟨j.1 + 1, h⟩ := hα (Fin.mk_lt_mk.2 (by simp))
        linarith
      · exact one_pos
    have hne : (Finset.univ : Finset (Fin J)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    refine ⟨Finset.univ.inf' hne gap, (Finset.lt_inf'_iff hne).2 fun j _ => hpos j, fun j hj => ?_⟩
    have h1 := Finset.inf'_le gap (Finset.mem_univ j)
    have h2 : gap j = α ⟨j.1 + 1, hj⟩ - α j := by simp only [gap, dif_pos hj]
    linarith

/-- A law with a Lebesgue density has no atoms. -/
lemma nullSingleton_of_density {P : Measure ℝ} {p : ℝ → ℝ}
    (hP : P = volume.withDensity fun x => ENNReal.ofReal (p x)) : NullSingletonClass P :=
  ⟨fun x => by rw [hP]; exact withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

/-- `{z | ∀ i j, z.1 i ≠ z.2 j}` is measurable. -/
lemma measurableSet_cross (n m : ℕ) : MeasurableSet {z : (Fin n → ℝ) × (Fin m → ℝ) | ∀ i j, z.1 i ≠ z.2 j} := by
  have : {z : (Fin n → ℝ) × (Fin m → ℝ) | ∀ i j, z.1 i ≠ z.2 j} = ⋂ i, ⋂ j, {z | z.1 i = z.2 j}ᶜ := by
    ext z; simp
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (measurableSet_eq_fun ?_ ?_).compl
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- `1 − ofReal(1 − a) = ofReal a`-style bound on a complement. -/
lemma compl_le_of_ofReal_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h : ENNReal.ofReal (1 - a) ≤ μ S) :
    μ Sᶜ ≤ ENNReal.ofReal a := by
  rw [prob_compl_eq_one_sub hS]
  calc 1 - μ S ≤ 1 - ENNReal.ofReal (1 - a) := tsub_le_tsub_left h 1
    _ = ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]; congr 1; ring

/-- An event of probability `≥ 1 − a` for the `X`'s of the fitting sample of batch `b`, as an event of the whole sample. -/
lemma fitSample_compl_le_X (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    (lx : Fin n → ℕ) (b : ℕ) {E : Set (Fin (fitCard lx b) → ℝ)} (hE : MeasurableSet E) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (h : ENNReal.ofReal (1 - a) ≤ (Measure.pi fun _ : Fin (fitCard lx b) => P) E) :
    MeasurableSet {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample lx b z.1 ∈ E} ∧
      sampleLaw P Q n m {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample lx b z.1 ∈ E}ᶜ ≤ ENNReal.ofReal a := by
  have hmeas : Measurable fun z : (Fin n → ℝ) × (Fin m → ℝ) => fitSample lx b z.1 :=
    (Lower.measurable_fitSample lx b).comp measurable_fst
  refine ⟨hmeas hE, ?_⟩
  have e : {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample lx b z.1 ∈ E}ᶜ = Prod.fst ⁻¹' (fitSample lx b ⁻¹' Eᶜ) := by
    ext z; simp
  rw [e]
  unfold sampleLaw
  rw [show Prod.fst ⁻¹' (fitSample lx b ⁻¹' Eᶜ) = (fitSample lx b ⁻¹' Eᶜ) ×ˢ (univ : Set (Fin m → ℝ)) by
    ext z; simp, Measure.prod_prod, measure_univ, mul_one,
    ← Measure.map_apply (Lower.measurable_fitSample lx b) hE.compl, Lower.map_fitSample]
  exact compl_le_of_ofReal_le _ hE ha0 ha1 h

/-- An event of probability `≥ 1 − a` for the `Y`'s of the fitting sample of batch `b`, as an event of the whole sample. -/
lemma fitSample_compl_le_Y (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    (ly : Fin m → ℕ) (b : ℕ) {E : Set (Fin (fitCard ly b) → ℝ)} (hE : MeasurableSet E) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (h : ENNReal.ofReal (1 - a) ≤ (Measure.pi fun _ : Fin (fitCard ly b) => Q) E) :
    MeasurableSet {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample ly b z.2 ∈ E} ∧
      sampleLaw P Q n m {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample ly b z.2 ∈ E}ᶜ ≤ ENNReal.ofReal a := by
  have hmeas : Measurable fun z : (Fin n → ℝ) × (Fin m → ℝ) => fitSample ly b z.2 :=
    (Lower.measurable_fitSample ly b).comp measurable_snd
  refine ⟨hmeas hE, ?_⟩
  have e : {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample ly b z.2 ∈ E}ᶜ = Prod.snd ⁻¹' (fitSample ly b ⁻¹' Eᶜ) := by
    ext z; simp
  rw [e]
  unfold sampleLaw
  rw [show Prod.snd ⁻¹' (fitSample ly b ⁻¹' Eᶜ) = (univ : Set (Fin n → ℝ)) ×ˢ (fitSample ly b ⁻¹' Eᶜ) by
    ext z; simp, Measure.prod_prod, measure_univ, one_mul,
    ← Measure.map_apply (Lower.measurable_fitSample ly b) hE.compl, Lower.map_fitSample]
  exact compl_le_of_ofReal_le _ hE ha0 ha1 h

lemma fitCard_le {p : ℕ} (l : Fin p → ℕ) (b : ℕ) : fitCard l b ≤ p := by
  unfold fitCard
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- One interval event of Lemma S4.23 for a sample of size `k ≤ M`, at `η′ = η/8` and the common `x ≥ log(16(M+1)²/η)`. -/
lemma one_interval_event (h4 : Claims.lap_intervals) (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]
    {k : ℕ} (hk : 1 ≤ k) {M η c : ℝ} (hkM : (k : ℝ) ≤ M) (hη0 : 0 < η) (hη1 : η < 1)
    (hc : Real.log (16 * (M + 1) ^ 2 / η) ≤ c) :
    ∃ E : Set (Fin k → ℝ), MeasurableSet E ∧ ENNReal.ofReal (1 - η / 8) ≤ (Measure.pi fun _ : Fin k => P) E ∧
      ∀ x ∈ E, IntervalEvent P x c := by
  obtain ⟨E, hEm, hEp, hEsub⟩ := h4.1 P k (η / 8) hk (by positivity) (by linarith)
  refine ⟨E, hEm, hEp, fun x hx => h4.2.1 P k x _ c ?_ ?_ (hEsub hx)⟩
  · refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  · refine le_trans (Real.log_le_log (by positivity) ?_) hc
    rw [show 2 * ((k : ℝ) + 1) ^ 2 / (η / 8) = 16 * ((k : ℝ) + 1) ^ 2 / η by field_simp; ring]
    gcongr

/-- **The event `𝓔_fit`** (S4 :1349-1353). -/
lemma fit_event (h4 : Claims.lap_intervals) (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [NullSingletonClass P] [NullSingletonClass Q] {n m : ℕ} (lx : Fin n → ℕ) (ly : Fin m → ℕ) {η c : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hn1 : 1 ≤ fitCard lx 1) (hm1 : 1 ≤ fitCard ly 1)
    (hc : Real.log (16 * (((max n m : ℕ) : ℝ) + 1) ^ 2 / η) ≤ c) :
    ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧ sampleLaw P Q n m Eᶜ ≤ ENNReal.ofReal (η / 2) ∧
      ∀ z ∈ E, (∀ i j, z.1 i ≠ z.2 j) ∧ ∀ b, 1 ≤ b → b ≤ 2 →
        IntervalEvent P (fitSample lx b z.1) c ∧ IntervalEvent Q (fitSample ly b z.2) c := by
  have hnM : ∀ b, (fitCard lx b : ℝ) ≤ ((max n m : ℕ) : ℝ) := fun b => by
    exact_mod_cast (fitCard_le lx b).trans (le_max_left n m)
  have hmM : ∀ b, (fitCard ly b : ℝ) ≤ ((max n m : ℕ) : ℝ) := fun b => by
    exact_mod_cast (fitCard_le ly b).trans (le_max_right n m)
  have hn2 : 1 ≤ fitCard lx 2 := hn1.trans (Core.fitCard_mono lx (by norm_num))
  have hm2 : 1 ≤ fitCard ly 2 := hm1.trans (Core.fitCard_mono ly (by norm_num))
  have ha0 : (0 : ℝ) ≤ η / 8 := by positivity
  have ha1 : η / 8 ≤ 1 := by linarith
  obtain ⟨EX1, hX1m, hX1p, hX1⟩ := one_interval_event h4 P hn1 (hnM 1) hη0 hη1 hc
  obtain ⟨EY1, hY1m, hY1p, hY1⟩ := one_interval_event h4 Q hm1 (hmM 1) hη0 hη1 hc
  obtain ⟨EX2, hX2m, hX2p, hX2⟩ := one_interval_event h4 P hn2 (hnM 2) hη0 hη1 hc
  obtain ⟨EY2, hY2m, hY2p, hY2⟩ := one_interval_event h4 Q hm2 (hmM 2) hη0 hη1 hc
  obtain ⟨FX1m, FX1p⟩ := fitSample_compl_le_X P Q (m := m) lx 1 hX1m ha0 ha1 hX1p
  obtain ⟨FY1m, FY1p⟩ := fitSample_compl_le_Y P Q (n := n) ly 1 hY1m ha0 ha1 hY1p
  obtain ⟨FX2m, FX2p⟩ := fitSample_compl_le_X P Q (m := m) lx 2 hX2m ha0 ha1 hX2p
  obtain ⟨FY2m, FY2p⟩ := fitSample_compl_le_Y P Q (n := n) ly 2 hY2m ha0 ha1 hY2p
  set G := {z : (Fin n → ℝ) × (Fin m → ℝ) | ∀ i j, z.1 i ≠ z.2 j} with hGdef
  have hGm : MeasurableSet G := measurableSet_cross n m
  have hG0 : sampleLaw P Q n m Gᶜ = 0 := by
    refine measure_mono_null (fun z hz => ?_) (h4.2.2 P Q n m)
    simp only [hGdef, mem_compl_iff, mem_setOf_eq, not_forall, not_not] at hz ⊢
    obtain ⟨i, j, hij⟩ := hz
    exact fun h => h.2.2 i j hij
  set FX1 := {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample lx 1 z.1 ∈ EX1}
  set FY1 := {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample ly 1 z.2 ∈ EY1}
  set FX2 := {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample lx 2 z.1 ∈ EX2}
  set FY2 := {z : (Fin n → ℝ) × (Fin m → ℝ) | fitSample ly 2 z.2 ∈ EY2}
  refine ⟨FX1 ∩ FY1 ∩ FX2 ∩ FY2 ∩ G, FX1m.inter FY1m |>.inter FX2m |>.inter FY2m |>.inter hGm, ?_, ?_⟩
  · simp only [compl_inter]
    calc sampleLaw P Q n m (FX1ᶜ ∪ FY1ᶜ ∪ FX2ᶜ ∪ FY2ᶜ ∪ Gᶜ)
        ≤ sampleLaw P Q n m FX1ᶜ + sampleLaw P Q n m FY1ᶜ + sampleLaw P Q n m FX2ᶜ + sampleLaw P Q n m FY2ᶜ +
            sampleLaw P Q n m Gᶜ := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8) + 0 := by
          rw [hG0]; gcongr
      _ = ENNReal.ofReal (η / 2) := by
          rw [add_zero, ← ENNReal.ofReal_add ha0 ha0, ← ENNReal.ofReal_add (by positivity) ha0,
            ← ENNReal.ofReal_add (by positivity) ha0]
          congr 1; ring
  · rintro z ⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩
    refine ⟨hz5, fun b hb1 hb2 => ?_⟩
    rcases (show b = 1 ∨ b = 2 by omega) with rfl | rfl
    · exact ⟨hX1 _ hz1, hY1 _ hz2⟩
    · exact ⟨hX2 _ hz3, hY2 _ hz4⟩

/-- The default batches: every pair lies in batch 1 or 2; the fitting samples of batches 1 and 2 have at least `(n∧m)/5` and at
most `n`, `m` observations; `N ≥ (n∧m)/2`. -/
lemma default_batches {𝒳 : Type*} {J n m : ℕ} (R : LoRun 𝒳 J n m) (hdef : IsDefaultRun R)
    (hpair : IsBatchPairing R.lx R.ly R.bat R.A R.B) (hN10 : 10 ≤ min n m) :
    (∀ k, 1 ≤ R.bat k ∧ R.bat k ≤ 2) ∧
    (∀ b, 1 ≤ b → b ≤ 2 → ((min n m : ℕ) : ℝ) / 5 ≤ fitCard R.lx b ∧ ((min n m : ℕ) : ℝ) / 5 ≤ fitCard R.ly b ∧
      fitCard R.lx b ≤ n ∧ fitCard R.ly b ≤ m) ∧
    ((min n m : ℕ) : ℝ) / 2 ≤ R.N := by
  obtain ⟨bn1, bn2, bm1, bm2, hcn, hcm, hlx, hly, hN⟩ := hdef
  have hlx' : R.lx = fun i : Fin n => defaultLabel bn1 bn2 i := funext hlx
  have hly' : R.ly = fun j : Fin m => defaultLabel bm1 bm2 j := funext hly
  have hn : 10 ≤ n := le_trans hN10 (min_le_left _ _)
  have hm : 10 ≤ m := le_trans hN10 (min_le_right _ _)
  obtain ⟨hn12, hn2, hn0, -, -⟩ := Arith.cuts_bounds (by omega) hcn
  obtain ⟨hm12, hm2, hm0, -, -⟩ := Arith.cuts_bounds (by omega) hcm
  obtain ⟨cn0, -, -⟩ := Arith.counts hn12 hn2
  obtain ⟨cm0, -, -⟩ := Arith.counts hm12 hm2
  have hb := lorate_batches_route n m bn1 bn2 bm1 bm2 hN10 hcn hcm
  have hNr : (10 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast hN10
  have hnr : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (10 : ℝ) ≤ m := by exact_mod_cast hm
  have hMn : ((min n m : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_left n m
  have hMm : ((min n m : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_right n m
  refine ⟨fun k => ⟨hpair.2.2.1 k, ?_⟩, fun b hb1 hb2 => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hpair.1.1 k
    rw [← hpair.2.2.2.1 k i hi, hlx']
    exact Arith.label_le_two _ _ _
  · have h1 : fitCard R.lx 1 ≤ fitCard R.lx b := Core.fitCard_mono _ hb1
    have h2 : fitCard R.ly 1 ≤ fitCard R.ly b := Core.fitCard_mono _ hb1
    rw [hlx'] at h1 ⊢
    rw [hly'] at h2 ⊢
    rw [cn0] at h1
    rw [cm0] at h2
    have h1r : (bn1 : ℝ) ≤ fitCard (fun i : Fin n => defaultLabel bn1 bn2 i) b := by exact_mod_cast h1
    have h2r : (bm1 : ℝ) ≤ fitCard (fun j : Fin m => defaultLabel bm1 bm2 j) b := by exact_mod_cast h2
    refine ⟨by linarith, by linarith, fitCard_le _ _, fitCard_le _ _⟩
  · have := hb.2.2.2
    rw [← hlx', ← hly', ← hN] at this
    exact this

end StatFormal.Wave31tu.RouteT
