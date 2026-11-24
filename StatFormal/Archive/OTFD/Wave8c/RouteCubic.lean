import StatFormal.Archive.OTFD.Wave8c.Statements
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Route: B `lem:ext-cubic-bracket`

* Coordinates are independent `Unif[−a_k, a_k]`; `T_k = (u_k/D_K)²` has CDF `min(√y/ω_k, 1)` and no atoms.
* Coupling: `hν_k ≤ T_k < h(ν_k + 1)` and `T_k − hν_k ≤ min(h, ω_k²)`; `T_k/h ∉ ℤ` a.s. gives the ceiling identity.
* (i)–(iv) are set inclusions on the full-measure set where the coupling holds; (ii) uses right-continuity of
  `c_K` and minimality of `i_p`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.OTFD.Wave8c

/-! ### The uniform law on `[−c, c]` -/

lemma unifSym_univ {c : ℝ} (hc : 0 < c) : unifSym c univ = 1 := by
  rw [unifSym, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  rw [show 1 / (2 * c) * (c - -c) = 1 by field_simp; ring, ENNReal.ofReal_one]

lemma unifSym_prob {c : ℝ} (hc : 0 < c) : IsProbabilityMeasure (unifSym c) := ⟨unifSym_univ hc⟩

lemma unifSym_ac (c : ℝ) : unifSym c ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [unifSym, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
    measure_mono_null inter_subset_left h0, mul_zero]

lemma unifSym_ae (c : ℝ) : ∀ᵐ x ∂unifSym c, x ∈ Icc (-c) c := by
  rw [ae_iff, unifSym, Measure.smul_apply, Measure.restrict_apply' measurableSet_Icc]
  have : {x : ℝ | ¬x ∈ Icc (-c) c} ∩ Icc (-c) c = ∅ := by ext; simp
  rw [this, measure_empty, smul_zero]

lemma unifSym_Icc {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    unifSym c (Icc (-r) r) = ENNReal.ofReal (min (r / c) 1) := by
  rw [unifSym, Measure.smul_apply, Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_neg_neg,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases le_total r c with h | h
  · rw [min_eq_left h, min_eq_left ((div_le_one hc).2 h)]; field_simp; ring
  · rw [min_eq_right h, min_eq_right ((one_le_div hc).2 h)]; field_simp; ring

/-! ### Standing facts -/

section Setting
variable {N : ℕ} {a : Fin N → ℝ} {h Dinf : ℝ}

lemma dK_pos (hs : CubicSetting a h Dinf) : 0 < dK a := by
  obtain ⟨hN, ha, -, -⟩ := hs
  exact Real.sqrt_pos.2 (Finset.sum_pos (fun k _ => pow_pos (ha k) 2) ⟨⟨0, hN⟩, Finset.mem_univ _⟩)

lemma om_pos (hs : CubicSetting a h Dinf) (k : Fin N) : 0 < om a k := div_pos (hs.2.1 k) (dK_pos hs)

lemma dK_sq (a : Fin N → ℝ) : dK a ^ 2 = ∑ k, a k ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)

lemma sum_om_sq (hs : CubicSetting a h Dinf) : ∑ k, om a k ^ 2 = 1 := by
  simp only [om, div_pow, ← Finset.sum_div, ← dK_sq]
  exact div_self (pow_pos (dK_pos hs) 2).ne'

lemma cubic_unif_prob (hs : CubicSetting a h Dinf) (k : Fin N) : IsProbabilityMeasure (unifSym (a k)) :=
  unifSym_prob (hs.2.1 k)

lemma cubic_prob (hs : CubicSetting a h Dinf) : IsProbabilityMeasure (cubicLaw a) := by
  haveI := cubic_unif_prob hs
  unfold cubicLaw; infer_instance

lemma cubic_eval (hs : CubicSetting a h Dinf) (k : Fin N) :
    (cubicLaw a).map (fun u => u k) = unifSym (a k) := by
  haveI := cubic_unif_prob hs
  exact (measurePreserving_eval (fun k => unifSym (a k)) k).map_eq

lemma cubic_coord_ae (hs : CubicSetting a h Dinf) (k : Fin N) {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂unifSym (a k), p x) : ∀ᵐ u ∂cubicLaw a, p (u k) := by
  rw [← cubic_eval hs k] at hp
  exact ae_of_ae_map (measurable_pi_apply k).aemeasurable hp

lemma measurable_termT (a : Fin N → ℝ) (k : Fin N) : Measurable (termT a k) :=
  ((measurable_pi_apply k).div_const _).pow_const 2

lemma measurable_sumS (a : Fin N → ℝ) : Measurable (sumS a) :=
  Finset.measurable_sum _ fun k _ => measurable_termT a k

lemma measurable_nuSum (a : Fin N → ℝ) (h : ℝ) : Measurable (nuSum a h) :=
  Finset.measurable_sum _ fun k _ => ((measurable_termT a k).div_const h).floor

lemma termT_set (hs : CubicSetting a h Dinf) (k : Fin N) {y : ℝ} (hy : 0 ≤ y) :
    {u : Fin N → ℝ | termT a k u ≤ y} = (fun u => u k) ⁻¹' Icc (-(dK a * Real.sqrt y)) (dK a * Real.sqrt y) := by
  have hD := dK_pos hs
  ext u
  simp only [mem_setOf_eq, mem_preimage, mem_Icc, ← abs_le, termT, div_pow]
  rw [div_le_iff₀ (by positivity), ← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hD.le, mul_comm (Real.sqrt y)]

theorem cubic_term_cdf : Claims.cubic_term_cdf := by
  intro N a h Dinf hs k
  haveI := cubic_prob hs
  have hD := dK_pos hs
  have hω := om_pos hs k
  refine ⟨?_, fun y hy => ?_⟩
  · filter_upwards [cubic_coord_ae hs k (unifSym_ae (a k))] with u hu
    refine ⟨sq_nonneg _, ?_⟩
    simp only [termT, om, div_pow]
    exact div_le_div_of_nonneg_right (sq_le_sq' hu.1 hu.2) (sq_nonneg _)
  · rw [termT_set hs k hy, measureReal_def, ← Measure.map_apply (measurable_pi_apply k) measurableSet_Icc,
      cubic_eval hs k, unifSym_Icc (hs.2.1 k) (mul_nonneg hD.le (Real.sqrt_nonneg _)),
      ENNReal.toReal_ofReal (le_min (div_nonneg (mul_nonneg hD.le (Real.sqrt_nonneg _)) (hs.2.1 k).le)
        zero_le_one), cdfK, om]
    congr 1
    field_simp

lemma mreal_mono_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {s t : Set α}
    (h : ∀ᵐ u ∂μ, u ∈ s → u ∈ t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

lemma termT_eq_null (hs : CubicSetting a h Dinf) (k : Fin N) (y : ℝ) :
    cubicLaw a {u | termT a k u = y} = 0 := by
  have hD := dK_pos hs
  have hsub : {u : Fin N → ℝ | termT a k u = y} ⊆
      (fun u => u k) ⁻¹' {dK a * Real.sqrt y, -(dK a * Real.sqrt y)} := by
    intro u hu
    simp only [mem_setOf_eq, termT] at hu
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
    have hy : 0 ≤ y := hu ▸ sq_nonneg _
    have h2 : (u k / dK a) ^ 2 = Real.sqrt y ^ 2 := by rw [hu, Real.sq_sqrt hy]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · left; field_simp at h3; linarith
    · right; field_simp at h3; linarith
  refine measure_mono_null hsub ?_
  rw [← Measure.map_apply (measurable_pi_apply k) (Set.toFinite _).measurableSet, cubic_eval hs k]
  exact unifSym_ac _ ((Set.toFinite _).measure_zero volume)

lemma termT_lt_eq (hs : CubicSetting a h Dinf) (k : Fin N) (y : ℝ) :
    (cubicLaw a).real {u | termT a k u < y} = (cubicLaw a).real {u | termT a k u ≤ y} := by
  haveI := cubic_prob hs
  refine measureReal_congr ?_
  have := termT_eq_null hs k y
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with u hu
  have hu' : termT a k u ≠ y := hu
  show (termT a k u < y) = (termT a k u ≤ y)
  exact propext ⟨le_of_lt, fun h' => lt_of_le_of_ne h' hu'⟩

theorem cubic_bin_law : Claims.cubic_bin_law := by
  intro N a h Dinf hs
  haveI := cubic_prob hs
  haveI := cubic_unif_prob hs
  have hh := hs.2.2.1
  refine ⟨fun k i => ?_, ?_⟩
  · have hset : {u | nuK a h k u = (i : ℤ)} =
        {u | termT a k u < (i + 1) * h} \ {u | termT a k u < i * h} := by
      ext u
      simp only [nuK, mem_setOf_eq, mem_diff, Int.floor_eq_iff, Int.cast_natCast, not_lt]
      rw [le_div_iff₀ hh, div_lt_iff₀ hh]
      tauto
    have hsub : {u | termT a k u < (i : ℝ) * h} ⊆ {u | termT a k u < (i + 1) * h} := by
      intro u hu; simp only [mem_setOf_eq] at hu ⊢; nlinarith
    rw [hset, measureReal_sdiff hsub (measurableSet_lt (measurable_termT a k) measurable_const),
      termT_lt_eq hs, termT_lt_eq hs, (cubic_term_cdf N a h Dinf hs k).2 _ (by positivity),
      (cubic_term_cdf N a h Dinf hs k).2 _ (by positivity)]
  · exact iIndepFun_pi (X := fun k (x : ℝ) => ⌊(x / dK a) ^ 2 / h⌋) (μ := fun k => unifSym (a k))
      fun k => (((measurable_id.div_const _).pow_const 2).div_const h).floor.aemeasurable

theorem cubic_ck_eq : Claims.cubic_ck_eq := by
  intro N a h Dinf hs τ hτ
  have hD := dK_pos hs
  have hDi := hs.2.2.2
  unfold cK cdfS
  congr 1
  ext u
  simp only [mem_setOf_eq, rhoBox, sumS, termT, sOf, div_pow, ← Finset.sum_div]
  rw [div_le_iff₀ hDi, div_le_div_iff_of_pos_right (by positivity)]
  have hsum : 0 ≤ ∑ k, u k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  constructor
  · intro h1
    rw [← Real.sq_sqrt hsum]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  · intro h1
    calc Real.sqrt (∑ k, u k ^ 2) ≤ Real.sqrt ((τ * Dinf) ^ 2) := Real.sqrt_le_sqrt h1
      _ = τ * Dinf := Real.sqrt_sq (by positivity)

/-- The full-measure set on which the coupling holds. -/
def Good (a : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) : Prop :=
  ∀ k, u k ∈ Icc (-a k) (a k) ∧ termT a k u / h ∉ range (Int.cast : ℤ → ℝ)

lemma ae_good (hs : CubicSetting a h Dinf) : ∀ᵐ u ∂cubicLaw a, Good a h u := by
  show ∀ᵐ u ∂cubicLaw a, ∀ k, _
  rw [ae_all_iff]
  intro k
  refine (cubic_coord_ae hs k (unifSym_ae (a k))).and ?_
  have hnull : cubicLaw a {u | termT a k u / h ∈ range (Int.cast : ℤ → ℝ)} = 0 := by
    have : {u | termT a k u / h ∈ range (Int.cast : ℤ → ℝ)} ⊆ ⋃ z : ℤ, {u | termT a k u = z * h} := by
      rintro u ⟨z, hz⟩
      simp only [mem_iUnion, mem_setOf_eq]
      exact ⟨z, by rw [hz, div_mul_cancel₀ _ hs.2.2.1.ne']⟩
    exact measure_mono_null this (measure_iUnion_null fun z => termT_eq_null hs k _)
  exact measure_eq_zero_iff_ae_notMem.1 hnull

lemma good_props (hs : CubicSetting a h Dinf) {u : Fin N → ℝ} (hu : Good a h u) (k : Fin N) :
    h * nuK a h k u ≤ termT a k u ∧ termT a k u - h * nuK a h k u ≤ min h (om a k ^ 2) ∧
      (⌈termT a k u / h⌉ : ℤ) = nuK a h k u + 1 := by
  have hh := hs.2.2.1
  have hD := dK_pos hs
  have hT0 : 0 ≤ termT a k u := sq_nonneg _
  have h1 : (nuK a h k u : ℝ) ≤ termT a k u / h := Int.floor_le _
  have h2 : termT a k u / h < nuK a h k u + 1 := Int.lt_floor_add_one _
  have h0 : 0 ≤ nuK a h k u := Int.floor_nonneg.2 (div_nonneg hT0 hh.le)
  have h0' : (0 : ℝ) ≤ nuK a h k u := by exact_mod_cast h0
  have hTle : termT a k u ≤ om a k ^ 2 := by
    simp only [termT, om, div_pow]
    exact div_le_div_of_nonneg_right (sq_le_sq' (hu k).1.1 (hu k).1.2) (sq_nonneg _)
  rw [le_div_iff₀ hh] at h1
  rw [div_lt_iff₀ hh] at h2
  refine ⟨by linarith, le_min (by nlinarith) (by nlinarith), ?_⟩
  exact (Int.ceil_eq_floor_add_one_iff_notMem _).2 (hu k).2

lemma good_T_le (hs : CubicSetting a h Dinf) {u : Fin N → ℝ} (hu : Good a h u) (k : Fin N) :
    termT a k u ≤ om a k ^ 2 := by
  simp only [termT, om, div_pow]
  exact div_le_div_of_nonneg_right (sq_le_sq' (hu k).1.1 (hu k).1.2) (sq_nonneg _)

lemma good_S_le (hs : CubicSetting a h Dinf) {u : Fin N → ℝ} (hu : Good a h u) : sumS a u ≤ 1 := by
  rw [← sum_om_sq hs]; exact Finset.sum_le_sum fun k _ => good_T_le hs hu k

lemma deltaG_nonneg (hs : CubicSetting a h Dinf) : 0 ≤ deltaG a h :=
  Finset.sum_nonneg fun k _ => le_min hs.2.2.1.le (sq_nonneg _)

lemma deltaG_le (hs : CubicSetting a h Dinf) : deltaG a h ≤ N * h := by
  calc deltaG a h ≤ ∑ _k : Fin N, h := Finset.sum_le_sum fun k _ => min_le_left _ _
    _ = N * h := by simp

lemma good_coupling (hs : CubicSetting a h Dinf) {u : Fin N → ℝ} (hu : Good a h u) :
    h * nuSum a h u ≤ sumS a u ∧ sumS a u ≤ h * nuSum a h u + deltaG a h := by
  have hnu : h * (nuSum a h u : ℝ) = ∑ k, h * nuK a h k u := by
    simp [nuSum, Finset.mul_sum]
  rw [hnu, sumS, deltaG]
  constructor
  · exact Finset.sum_le_sum fun k _ => (good_props hs hu k).1
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => by linarith [(good_props hs hu k).2.1]

theorem cubic_coupling : Claims.cubic_coupling := by
  intro N a h Dinf hs
  filter_upwards [ae_good hs] with u hu
  obtain ⟨h1, h2⟩ := good_coupling hs hu
  refine ⟨h1, h2, by have := deltaG_le hs; linarith, ?_⟩
  have : ∀ k, h * (⌈termT a k u / h⌉ : ℝ) = h * nuK a h k u + h := by
    intro k; rw [(good_props hs hu k).2.2]; push_cast; ring
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib]
  simp [nuSum, Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]

end Setting

/-! ### (i)–(iv) -/

section Brackets
variable {N : ℕ} {a : Fin N → ℝ} {h Dinf : ℝ}

theorem cubic_bracket_cdf : Claims.cubic_bracket_cdf := by
  intro N a h Dinf hs x
  haveI := cubic_prob hs
  have hh := hs.2.2.1
  unfold cdfL cdfS
  refine ⟨?_, ?_, ?_⟩
  · refine measureReal_mono (fun u hu => ?_)
    simp only [mem_setOf_eq] at hu ⊢
    refine hu.trans (Int.floor_mono ?_)
    have := deltaG_le hs
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · refine mreal_mono_ae ?_
    filter_upwards [ae_good hs] with u hu hmem
    obtain ⟨-, h2⟩ := good_coupling hs hu
    show sumS a u ≤ x
    have : (nuSum a h u : ℝ) ≤ (x - deltaG a h) / h := Int.le_floor.1 hmem
    rw [le_div_iff₀ hh] at this
    linarith
  · refine mreal_mono_ae ?_
    filter_upwards [ae_good hs] with u hu hmem
    obtain ⟨h1, -⟩ := good_coupling hs hu
    have hmem' : sumS a u ≤ x := hmem
    show nuSum a h u ≤ ⌊x / h⌋
    apply Int.le_floor.2
    rw [le_div_iff₀ hh]; linarith

lemma rhoBox_nonneg (hs : CubicSetting a h Dinf) (u : Fin N → ℝ) : 0 ≤ rhoBox Dinf u :=
  div_nonneg (Real.sqrt_nonneg _) hs.2.2.2.le

lemma measurable_rhoBox (Dinf : ℝ) : Measurable (rhoBox (N := N) Dinf) := by
  unfold rhoBox
  exact (Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).pow_const 2).sqrt.div_const _

lemma cK_mono (hs : CubicSetting a h Dinf) : Monotone (cK a Dinf) := by
  haveI := cubic_prob hs
  intro s t hst
  exact measureReal_mono fun u hu => le_trans (show rhoBox Dinf u ≤ s from hu) hst

lemma cK_neg (hs : CubicSetting a h Dinf) {t : ℝ} (ht : t < 0) : cK a Dinf t = 0 := by
  have : {u : Fin N → ℝ | rhoBox Dinf u ≤ t} = ∅ := by
    ext u; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le ht (rhoBox_nonneg hs u)
  rw [cK, this, measureReal_empty]

lemma cK_top (hs : CubicSetting a h Dinf) : cK a Dinf (dK a / Dinf) = 1 := by
  haveI := cubic_prob hs
  have hD := dK_pos hs
  apply le_antisymm (by rw [cK]; exact measureReal_le_one)
  rw [← probReal_univ (μ := cubicLaw a)]
  refine mreal_mono_ae ?_
  filter_upwards [ae_good hs] with u hu _
  show rhoBox Dinf u ≤ dK a / Dinf
  apply div_le_div_of_nonneg_right _ hs.2.2.2.le
  rw [dK]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => sq_le_sq' (hu k).1.1 (hu k).1.2)

lemma cK_eq_cdf (hs : CubicSetting a h Dinf) :
    cK a Dinf = cdf ((cubicLaw a).map (rhoBox Dinf)) := by
  haveI := cubic_prob hs
  funext t
  rw [cdf_eq_real, map_measureReal_apply (measurable_rhoBox Dinf) measurableSet_Iic]
  rfl

lemma tau_props (hs : CubicSetting a h Dinf) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ tauKp a Dinf p ∧ p ≤ cK a Dinf (tauKp a Dinf p) ∧
      ∀ t, p ≤ cK a Dinf t → tauKp a Dinf p ≤ t := by
  have hne : {t : ℝ | p ≤ cK a Dinf t}.Nonempty := ⟨dK a / Dinf, by simp [cK_top hs, hp1]⟩
  have hlow : ∀ t ∈ {t : ℝ | p ≤ cK a Dinf t}, 0 ≤ t := by
    intro t ht
    by_contra hneg
    push_neg at hneg
    have : p ≤ cK a Dinf t := ht
    rw [cK_neg hs hneg] at this
    linarith
  have hbdd : BddBelow {t : ℝ | p ≤ cK a Dinf t} := ⟨0, hlow⟩
  refine ⟨le_csInf hne hlow, ?_, fun t ht => csInf_le hbdd ht⟩
  have hev : ∀ᶠ t in 𝓝[>] (tauKp a Dinf p), p ≤ cK a Dinf t := by
    refine eventually_nhdsWithin_of_forall fun t ht => ?_
    obtain ⟨t', ht', ht't⟩ := exists_lt_of_csInf_lt hne ht
    exact le_trans ht' (cK_mono hs ht't.le)
  have hrc : ContinuousWithinAt (cK a Dinf) (Ici (tauKp a Dinf p)) (tauKp a Dinf p) := by
    rw [cK_eq_cdf hs]; exact (cdf _).right_continuous _
  exact ge_of_tendsto (hrc.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)) hev

lemma ip_props (hs : CubicSetting a h Dinf) {p : ℝ} (hp1 : p ≤ 1) :
    p ≤ (cubicLaw a).real {u | nuSum a h u ≤ ip a h p} ∧
      ∀ j : ℕ, j < ip a h p → (cubicLaw a).real {u | nuSum a h u ≤ j} < p := by
  haveI := cubic_prob hs
  have hh := hs.2.2.1
  have hne : {i : ℕ | p ≤ (cubicLaw a).real {u | nuSum a h u ≤ i}}.Nonempty := by
    refine ⟨⌈1 / h⌉₊, ?_⟩
    show p ≤ _
    refine le_trans hp1 (le_trans (le_of_eq (probReal_univ (μ := cubicLaw a)).symm) ?_)
    refine mreal_mono_ae ?_
    filter_upwards [ae_good hs] with u hu _
    show nuSum a h u ≤ (⌈1 / h⌉₊ : ℤ)
    obtain ⟨h1, -⟩ := good_coupling hs hu
    have h2 := good_S_le hs hu
    have : (nuSum a h u : ℝ) ≤ ⌈1 / h⌉₊ := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ hh]; linarith
    exact_mod_cast this
  exact ⟨Nat.sInf_mem hne, fun j hj => not_le.1 (Nat.notMem_of_lt_sInf hj)⟩

lemma sOf_dK (hs : CubicSetting a h Dinf) {x : ℝ} (hx : 0 ≤ x) :
    sOf a Dinf (dK a / Dinf * Real.sqrt x) = x := by
  have hD := dK_pos hs
  have hDi := hs.2.2.2
  rw [sOf, show dK a / Dinf * Real.sqrt x * Dinf / dK a = Real.sqrt x by field_simp, Real.sq_sqrt hx]

lemma tau_of_sOf (hs : CubicSetting a h Dinf) {t : ℝ} (ht : 0 ≤ t) :
    dK a / Dinf * Real.sqrt (sOf a Dinf t) = t := by
  have hD := dK_pos hs
  have hDi := hs.2.2.2
  rw [sOf, Real.sqrt_sq (by positivity)]
  field_simp

lemma cK_tauhi (hs : CubicSetting a h Dinf) {p : ℝ} (hp1 : p ≤ 1) :
    p ≤ cK a Dinf (dK a / Dinf * Real.sqrt (h * ip a h p + deltaG a h)) := by
  have hh := hs.2.2.1
  have hx : 0 ≤ h * ip a h p + deltaG a h := by
    have := deltaG_nonneg hs; positivity
  rw [cubic_ck_eq N a h Dinf hs _ (mul_nonneg (div_nonneg (dK_pos hs).le hs.2.2.2.le) (Real.sqrt_nonneg _)),
    sOf_dK hs hx]
  refine le_trans ?_ (cubic_bracket_cdf N a h Dinf hs _).2.1
  rw [add_sub_cancel_right, cdfL, mul_div_cancel_left₀ _ hh.ne', Int.floor_natCast]
  exact (ip_props hs hp1).1

theorem cubic_bracket_threshold : Claims.cubic_bracket_threshold := by
  intro N a h Dinf hs p hp hp1
  haveI := cubic_prob hs
  have hh := hs.2.2.1
  have hD := dK_pos hs
  have hDi := hs.2.2.2
  obtain ⟨hq0, hpq, hqle⟩ := tau_props hs hp hp1
  set q := tauKp a Dinf p
  set i := ip a h p
  have hδ := deltaG_nonneg hs
  have hx : 0 ≤ h * i + deltaG a h := by positivity
  set tstar := dK a / Dinf * Real.sqrt (h * i + deltaG a h)
  have hqt : q ≤ tstar := hqle _ (cK_tauhi hs hp1)
  have hsq0 : 0 ≤ sOf a Dinf q := sq_nonneg _
  have hupper : sOf a Dinf q ≤ h * i + deltaG a h := by
    rw [← sOf_dK hs hx]
    unfold sOf
    exact pow_le_pow_left₀ (by positivity) (by gcongr) 2
  have hlower : h * i ≤ sOf a Dinf q := by
    by_contra hlt
    push_neg at hlt
    have hj0 : 0 ≤ ⌊sOf a Dinf q / h⌋ := Int.floor_nonneg.2 (div_nonneg hsq0 hh.le)
    have hjlt : ⌊sOf a Dinf q / h⌋ < (i : ℤ) := by
      rw [Int.floor_lt, div_lt_iff₀ hh]; push_cast; linarith
    have hjn : (⌊sOf a Dinf q / h⌋.toNat : ℕ) < i := by omega
    have h1 := (ip_props hs hp1).2 _ hjn
    rw [Int.toNat_of_nonneg hj0] at h1
    have h2 : cK a Dinf q ≤ cdfL a h (sOf a Dinf q) := by
      rw [cubic_ck_eq N a h Dinf hs q hq0]; exact (cubic_bracket_cdf N a h Dinf hs _).2.2
    rw [cdfL] at h2
    linarith
  refine ⟨hlower, hupper, by have := deltaG_le hs; nlinarith, ?_, hqt⟩
  rw [← tau_of_sOf hs hq0]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlower) (div_nonneg hD.le hDi.le)

theorem cubic_bracket_content : Claims.cubic_bracket_content := by
  intro N a h Dinf hs
  haveI := cubic_prob hs
  refine ⟨fun τh hτ => ?_, fun p _ hp1 => cK_tauhi hs hp1⟩
  have hb := cubic_bracket_cdf N a h Dinf hs (sOf a Dinf τh)
  rw [← cubic_ck_eq N a h Dinf hs τh hτ] at hb
  refine ⟨?_, hb.2.1, hb.2.2, hb.1⟩
  refine measureReal_congr ?_
  filter_upwards [Measure.support_mem_ae (μ := cubicLaw a)] with u hu
  show (u ∈ {u | rhoBox Dinf u ≤ τh} ∧ u ∈ (cubicLaw a).support) = (u ∈ {u | rhoBox Dinf u ≤ τh})
  exact propext ⟨And.left, fun h' => ⟨h', hu⟩⟩

lemma width_first (hs : CubicSetting a h Dinf) (x : ℝ) :
    cdfL a h x - cdfL a h (x - deltaG a h) ≤
      (cubicLaw a).real {u | x - deltaG a h < sumS a u ∧ sumS a u ≤ x + deltaG a h} := by
  haveI := cubic_prob hs
  have hh := hs.2.2.1
  have hδ := deltaG_nonneg hs
  have hsub : {u | nuSum a h u ≤ ⌊(x - deltaG a h) / h⌋} ⊆ {u | nuSum a h u ≤ ⌊x / h⌋} := by
    intro u hu
    exact le_trans hu (Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hh.le))
  unfold cdfL
  rw [← measureReal_sdiff hsub (measurableSet_le (measurable_nuSum a h) measurable_const)]
  refine mreal_mono_ae ?_
  filter_upwards [ae_good hs] with u hu hmem
  obtain ⟨h1, h2⟩ := good_coupling hs hu
  obtain ⟨hA, hB⟩ := hmem
  simp only [mem_setOf_eq, not_le] at hA hB
  have hA' : (nuSum a h u : ℝ) ≤ x / h := Int.le_floor.1 hA
  have hB' : (x - deltaG a h) / h < nuSum a h u := Int.floor_lt.1 hB
  rw [le_div_iff₀ hh] at hA'
  rw [div_lt_iff₀ hh] at hB'
  exact ⟨by linarith, by linarith⟩

end Brackets

/-! ### The density bound -/

lemma lintegral_inv_sqrt {ω b : ℝ} (hω : 0 < ω) (hb : 0 ≤ b) :
    ∫⁻ y in Ioc 0 b, ENNReal.ofReal (1 / (2 * ω * Real.sqrt y)) = ENNReal.ofReal (Real.sqrt b / ω) := by
  have hint : IntervalIntegrable (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have heq : EqOn (fun y : ℝ => 1 / (2 * ω * Real.sqrt y)) (fun y => 1 / (2 * ω) * y ^ (-(1 / 2 : ℝ)))
      (Ioc 0 b) := by
    intro y hy
    simp only
    rw [Real.rpow_neg hy.1.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hI : IntegrableOn (fun y : ℝ => 1 / (2 * ω * Real.sqrt y)) (Ioc 0 b) :=
    IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 (hint.const_mul _))
      heq.symm measurableSet_Ioc
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun y => by positivity)]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le hb,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
    Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  try field_simp
  try ring

/-- The density of `T_k`: `y ↦ 1{0 < y ≤ ω²}/(2ω√y)`. -/
def termDens (ω : ℝ) (y : ℝ) : ℝ≥0∞ :=
  (Ioc 0 (ω ^ 2)).indicator (fun y => ENNReal.ofReal (1 / (2 * ω * Real.sqrt y))) y

lemma measurable_termDens (ω : ℝ) : Measurable (termDens ω) :=
  (measurable_const.div (measurable_const.mul Real.continuous_sqrt.measurable)).ennreal_ofReal.indicator
    measurableSet_Ioc

section Dens
variable {N : ℕ} {a : Fin N → ℝ} {h Dinf : ℝ}

lemma law_termT (hs : CubicSetting a h Dinf) (k : Fin N) :
    (cubicLaw a).map (termT a k) = volume.withDensity (termDens (om a k)) := by
  haveI := cubic_prob hs
  have hω := om_pos hs k
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply (measurable_termT a k) measurableSet_Iic, withDensity_apply _ measurableSet_Iic]
  unfold termDens
  rw [setLIntegral_indicator measurableSet_Ioc]
  rw [show termT a k ⁻¹' Iic y = {u | termT a k u ≤ y} from rfl]
  rcases lt_or_ge y 0 with hy | hy
  · have h1 : {u : Fin N → ℝ | termT a k u ≤ y} = ∅ := by
      ext u; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hy (sq_nonneg _)
    have h2 : Ioc 0 (om a k ^ 2) ∩ Iic y = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h3⟩; linarith
    rw [h1, h2, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  · have h2 : Ioc 0 (om a k ^ 2) ∩ Iic y = Ioc 0 (min (om a k ^ 2) y) := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff]; tauto
    rw [h2, lintegral_inv_sqrt hω (le_min (sq_nonneg _) hy), ← ofReal_measureReal,
      (cubic_term_cdf N a h Dinf hs k).2 y hy, cdfK]
    congr 1
    rcases le_total (om a k ^ 2) y with hle | hle
    · rw [min_eq_left hle, Real.sqrt_sq hω.le, div_self hω.ne', min_eq_right]
      rw [le_div_iff₀ hω, one_mul, ← Real.sqrt_sq hω.le]
      exact Real.sqrt_le_sqrt hle
    · rw [min_eq_right hle, min_eq_left]
      rw [div_le_one hω, ← Real.sqrt_sq hω.le]
      exact Real.sqrt_le_sqrt hle

lemma lintegral_arcsine {z : ℝ} (hz : 0 < z) :
    ∫⁻ x in Ioo 0 z, ENNReal.ofReal (1 / Real.sqrt (x * (z - x))) = ENNReal.ofReal Real.pi := by
  set F := fun x : ℝ => Real.arcsin (2 * x / z - 1)
  set f := fun x : ℝ => 1 / Real.sqrt (x * (z - x))
  have hderiv : ∀ x ∈ Ioo 0 z, HasDerivAt F (f x) x := by
    intro x hx
    obtain ⟨hx0, hxz⟩ := hx
    have h1 : 2 * x / z - 1 ≠ -1 := by
      intro h; have : 2 * x / z = 0 := by linarith
      rw [div_eq_zero_iff] at this; rcases this with h | h <;> [linarith; linarith]
    have h2 : 2 * x / z - 1 ≠ 1 := by
      intro h; have : 2 * x / z = 2 := by linarith
      rw [div_eq_iff hz.ne'] at this; linarith
    have hd := (Real.hasDerivAt_arcsin h1 h2).comp x
      ((((hasDerivAt_id x).const_mul 2).div_const z).sub_const 1)
    have hp : 0 < x * (z - x) := mul_pos hx0 (by linarith)
    have key : 1 - (2 * x / z - 1) ^ 2 = (2 / z) ^ 2 * (x * (z - x)) := by field_simp; ring
    have hfx : 1 / Real.sqrt (1 - (2 * x / z - 1) ^ 2) * (2 * 1 / z) = f x := by
      rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      simp only [f]
      have := Real.sqrt_pos.2 hp
      field_simp
    rw [hfx] at hd
    exact hd
  have hcont : ContinuousOn F (Icc 0 z) :=
    (Real.continuous_arcsin.comp ((continuous_const.mul continuous_id).div_const z |>.sub
      continuous_const)).continuousOn
  have hpos : ∀ x ∈ Ioo 0 z, 0 ≤ f x := fun x _ => by positivity
  have hint : IntervalIntegrable f volume 0 z :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (by rwa [uIcc_of_le hz.le]) (by simpa [hz.le] using hderiv)
      (by simpa [hz.le] using hpos)
  have hval : ∫ x in (0 : ℝ)..z, f x = Real.pi := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz.le hcont hderiv hint]
    simp only [F, mul_zero, zero_div, zero_sub]
    rw [show 2 * z / z - 1 = 1 by field_simp; ring, Real.arcsin_one, Real.arcsin_neg_one]; ring
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).1 hint)
      (by filter_upwards with x using by positivity),
    ← intervalIntegral.integral_of_le hz.le, hval]

lemma termDens_mul_le {ω ω' : ℝ} (hω : 0 < ω) (hω' : 0 < ω') (w x : ℝ) :
    termDens ω x * termDens ω' (w - x) ≤
      ENNReal.ofReal (1 / (4 * ω * ω')) *
        (Ioo 0 w).indicator (fun x => ENNReal.ofReal (1 / Real.sqrt (x * (w - x)))) x := by
  simp only [termDens]
  by_cases h1 : x ∈ Ioc 0 (ω ^ 2)
  · by_cases h2 : w - x ∈ Ioc 0 (ω' ^ 2)
    · have hx : x ∈ Ioo 0 w := ⟨h1.1, by linarith [h2.1]⟩
      rw [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply le_of_eq
      congr 1
      have hx0 := Real.sqrt_pos.2 h1.1
      have hwx := Real.sqrt_pos.2 h2.1
      rw [Real.sqrt_mul h1.1.le]
      field_simp
      norm_num
    · rw [indicator_of_notMem h2, mul_zero]; exact bot_le
  · rw [indicator_of_notMem h1, zero_mul]; exact bot_le

lemma law_pair (hs : CubicSetting a h Dinf) {i j : Fin N} (hij : i ≠ j) :
    (cubicLaw a).map (fun u => termT a i u + termT a j u) ≤
      ENNReal.ofReal (Real.pi / (4 * om a i * om a j)) • volume := by
  haveI := cubic_prob hs
  haveI := cubic_unif_prob hs
  have hωi := om_pos hs i
  have hωj := om_pos hs j
  have hind : IndepFun (termT a i) (termT a j) (cubicLaw a) :=
    (iIndepFun_pi (X := fun k (x : ℝ) => (x / dK a) ^ 2) (μ := fun k => unifSym (a k))
      fun k => ((measurable_id.div_const _).pow_const 2).aemeasurable).indepFun hij
  have hmap := hind.map_add_eq_map_conv_map (measurable_termT a i) (measurable_termT a j)
  rw [show (fun u => termT a i u + termT a j u) = termT a i + termT a j from rfl, hmap, law_termT hs i,
    law_termT hs j]
  set di := termDens (om a i)
  set dj := termDens (om a j)
  have hdi := measurable_termDens (om a i)
  have hdj := measurable_termDens (om a j)
  rw [Measure.le_iff]
  intro B hB
  have hBi : Measurable (B.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hB
  rw [← lintegral_indicator_one hB, Measure.lintegral_conv hBi,
    lintegral_withDensity_eq_lintegral_mul _ hdi
      (Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => B.indicator 1 (p.1 + p.2))
        (hBi.comp (measurable_fst.add measurable_snd)))]
  have hinner : ∀ x, ∫⁻ y, B.indicator 1 (x + y) ∂volume.withDensity dj =
      ∫⁻ w, dj (w - x) * B.indicator 1 w := by
    intro x
    rw [lintegral_withDensity_eq_lintegral_mul _ hdj
      (show Measurable fun y => B.indicator (1 : ℝ → ℝ≥0∞) (x + y) from hBi.comp (measurable_const_add x))]
    rw [← lintegral_add_left_eq_self (fun w => dj (w - x) * B.indicator 1 w) x]
    simp only [Pi.mul_apply, add_sub_cancel_left]
    rfl
  simp only [Pi.mul_apply, hinner]
  have hm2 : Measurable (Function.uncurry fun x w : ℝ => di x * (dj (w - x) * B.indicator 1 w)) := by
    refine (hdi.comp measurable_fst).mul ((hdj.comp (measurable_snd.sub measurable_fst)).mul
      (hBi.comp measurable_snd))
  calc ∫⁻ x, di x * ∫⁻ w, dj (w - x) * B.indicator 1 w
      = ∫⁻ x, ∫⁻ w, di x * (dj (w - x) * B.indicator 1 w) := by
        congr 1; funext x
        exact (lintegral_const_mul _ (show Measurable fun w => dj (w - x) * B.indicator 1 w from
          (hdj.comp (measurable_id.sub_const x)).mul hBi)).symm
    _ = ∫⁻ w, ∫⁻ x, di x * (dj (w - x) * B.indicator 1 w) := lintegral_lintegral_swap hm2.aemeasurable
    _ ≤ ∫⁻ w, B.indicator (fun _ => ENNReal.ofReal (Real.pi / (4 * om a i * om a j))) w := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ B
        · rw [indicator_of_mem hw]
          simp only [indicator_of_mem hw, Pi.one_apply, mul_one]
          calc ∫⁻ x, di x * dj (w - x)
              ≤ ∫⁻ x, ENNReal.ofReal (1 / (4 * om a i * om a j)) *
                  (Ioo 0 w).indicator (fun x => ENNReal.ofReal (1 / Real.sqrt (x * (w - x)))) x :=
                lintegral_mono fun x => termDens_mul_le hωi hωj w x
            _ = ENNReal.ofReal (1 / (4 * om a i * om a j)) *
                  ∫⁻ x in Ioo 0 w, ENNReal.ofReal (1 / Real.sqrt (x * (w - x))) := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioo]
            _ ≤ ENNReal.ofReal (1 / (4 * om a i * om a j)) * ENNReal.ofReal Real.pi := by
                gcongr
                rcases lt_or_ge 0 w with hw0 | hw0
                · rw [lintegral_arcsine hw0]
                · rw [Ioo_eq_empty (not_lt.2 hw0), Measure.restrict_empty, lintegral_zero_measure]
                  exact bot_le
            _ = ENNReal.ofReal (Real.pi / (4 * om a i * om a j)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
        · rw [indicator_of_notMem hw]; simp [indicator_of_notMem hw]
    _ = ENNReal.ofReal (Real.pi / (4 * om a i * om a j)) * volume B := lintegral_indicator_const hB _
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul]

lemma conv_le_of_le {ν ρ : Measure ℝ} [SFinite ν] [IsProbabilityMeasure ρ] {C : ℝ≥0∞}
    (hν : ν ≤ C • volume) : ν ∗ ρ ≤ C • volume := by
  rw [Measure.conv_comm, Measure.le_iff]
  intro B hB
  have hBi : Measurable (B.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hB
  rw [← lintegral_indicator_one hB, Measure.lintegral_conv hBi]
  calc ∫⁻ y, ∫⁻ x, B.indicator 1 (y + x) ∂ν ∂ρ = ∫⁻ y, ν ((fun x => y + x) ⁻¹' B) ∂ρ := by
        congr 1; funext y
        rw [← lintegral_indicator_one (measurable_const_add y hB)]
        rfl
    _ ≤ ∫⁻ _y, C * volume B ∂ρ := by
        refine lintegral_mono fun y => ?_
        calc ν ((fun x => y + x) ⁻¹' B) ≤ (C • volume) ((fun x => y + x) ⁻¹' B) := hν _
          _ = C * volume B := by rw [Measure.smul_apply, smul_eq_mul, measure_preimage_add]
    _ = C * volume B := by rw [lintegral_const, measure_univ, mul_one]
    _ = (C • volume) B := by rw [Measure.smul_apply, smul_eq_mul]

theorem cubic_density : Claims.cubic_density := by
  intro N a h Dinf hs i j hij
  haveI := cubic_prob hs
  haveI := cubic_unif_prob hs
  set S1 : Finset (Fin N) := {i, j}
  set P : (Fin N → ℝ) → ℝ := fun u => termT a i u + termT a j u
  set R : (Fin N → ℝ) → ℝ := fun u => ∑ k ∈ S1ᶜ, termT a k u
  have hSPR : sumS a = P + R := by
    funext u
    simp only [sumS, Pi.add_apply, P, R]
    rw [← Finset.sum_add_sum_compl S1, Finset.sum_pair hij]
  have hiid : iIndepFun (fun k u => termT a k u) (cubicLaw a) :=
    iIndepFun_pi (X := fun k (x : ℝ) => (x / dK a) ^ 2) (μ := fun k => unifSym (a k))
      fun k => ((measurable_id.div_const _).pow_const 2).aemeasurable
  have hind0 := hiid.indepFun_finset S1 S1ᶜ disjoint_compl_right (fun k => measurable_termT a k)
  have hφ : Measurable fun v : S1 → ℝ => ∑ k, v k := Finset.measurable_sum _ fun k _ => measurable_pi_apply k
  have hψ : Measurable fun v : (S1ᶜ : Finset (Fin N)) → ℝ => ∑ k, v k :=
    Finset.measurable_sum _ fun k _ => measurable_pi_apply k
  have hind : IndepFun P R (cubicLaw a) := by
    have := hind0.comp hφ hψ
    convert this using 1
    · funext u
      simp only [Function.comp, P]
      rw [Finset.sum_coe_sort S1 (fun k => termT a k u), Finset.sum_pair hij]
    · funext u
      simp only [Function.comp, R]
      rw [Finset.sum_coe_sort S1ᶜ (fun k => termT a k u)]
  have hPm : Measurable P := (measurable_termT a i).add (measurable_termT a j)
  have hRm : Measurable R := Finset.measurable_sum _ fun k _ => measurable_termT a k
  rw [hSPR, hind.map_add_eq_map_conv_map hPm hRm]
  exact conv_le_of_le (law_pair hs hij)

end Dens

theorem cubic_bracket_width : Claims.cubic_bracket_width := by
  intro N a h Dinf hs τh hτ
  haveI := cubic_prob hs
  refine ⟨width_first hs _, fun i j hij => ?_⟩
  have hδ := deltaG_nonneg hs
  have hδN := deltaG_le hs
  set x := sOf a Dinf τh
  set C := Real.pi / (4 * om a i * om a j)
  have hC : 0 ≤ C := div_nonneg Real.pi_pos.le (by have := om_pos hs i; have := om_pos hs j; positivity)
  have hset : {u | x - deltaG a h < sumS a u ∧ sumS a u ≤ x + deltaG a h} =
      sumS a ⁻¹' Ioc (x - deltaG a h) (x + deltaG a h) := rfl
  have hle : (cubicLaw a) {u | x - deltaG a h < sumS a u ∧ sumS a u ≤ x + deltaG a h} ≤
      ENNReal.ofReal (C * (2 * deltaG a h)) := by
    rw [hset, ← Measure.map_apply (measurable_sumS a) measurableSet_Ioc]
    calc (cubicLaw a).map (sumS a) (Ioc (x - deltaG a h) (x + deltaG a h))
        ≤ (ENNReal.ofReal C • volume) (Ioc (x - deltaG a h) (x + deltaG a h)) :=
          cubic_density N a h Dinf hs i j hij _
      _ = ENNReal.ofReal (C * (2 * deltaG a h)) := by
          rw [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul, ← ENNReal.ofReal_mul hC]
          congr 2; ring
  calc (cubicLaw a).real {u | x - deltaG a h < sumS a u ∧ sumS a u ≤ x + deltaG a h}
      ≤ C * (2 * deltaG a h) := ENNReal.toReal_le_of_le_ofReal (by positivity) hle
    _ ≤ 2 * N * h * C := by nlinarith

theorem cubic_width_density : Claims.cubic_width_density := by
  intro N a h Dinf hs τh hτ C hC
  haveI := cubic_prob hs
  have hδ := deltaG_nonneg hs
  have hδN := deltaG_le hs
  set x := sOf a Dinf τh
  have hset : {u | x - deltaG a h < sumS a u ∧ sumS a u ≤ x + deltaG a h} =
      sumS a ⁻¹' Ioc (x - deltaG a h) (x + deltaG a h) := rfl
  rw [ofReal_measureReal, hset, ← Measure.map_apply (measurable_sumS a) measurableSet_Ioc]
  calc (cubicLaw a).map (sumS a) (Ioc (x - deltaG a h) (x + deltaG a h))
      ≤ (C • volume) (Ioc (x - deltaG a h) (x + deltaG a h)) := hC _
    _ = C * ENNReal.ofReal (2 * deltaG a h) := by
        rw [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul]; congr 2; ring
    _ ≤ C * ENNReal.ofReal (2 * N * h) := by
        gcongr C * ?_
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (2 * N * h) * C := mul_comm _ _

end StatFormal.OTFD.Wave8c
