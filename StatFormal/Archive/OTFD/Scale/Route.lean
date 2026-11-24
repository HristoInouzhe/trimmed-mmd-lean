import StatFormal.Archive.OTFD.Scale.Statements
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim

/-!
# otfd A: the probability scale `Υ` (helpers, untrusted)

Source: `otfd/papers/A_sieves/main.tex:1195-1220` (`Υ`, `c_K`, `ρ_K`, with the 2026-10-13
hypothesis `μ_K{g_K = ρ_K} = 0`), `supplement.tex:4870-4880` (the two facts used).

Setting: `E` a finite-dimensional real normed space, `g` a norm on `E` (`IsGauge`: absolutely
homogeneous, subadditive, definite), `μ` a Borel probability measure,
`c(s) = μ{g ≤ s}` (`cK`). `ScaleHyp μ g` is the paper's assumption, with `[0, ρ_K)` written as
`{s | 0 ≤ s ∧ c s < 1}` and `μ{g = ρ_K} = 0` as "`μ{g = s} = 0` whenever `c s = 1`" (for
`s > ρ_K` this is automatic).

Main facts:
* `IsGauge.continuous`, `IsGauge.exists_le_mul_norm`, `IsGauge.exists_mul_norm_le` (norm
  equivalence, from convexity in finite dimension and compactness of the unit sphere);
* `continuousAt_cK_of_atom` (`c` is continuous at `s` when `μ{g = s} = 0`; via `cdf`), hence
  `ScaleHyp.continuous`;
* `g_ups` (`g(Υ r) = c(g r)`, so `Υ` takes values in `{g ≤ 1}`), `continuous_ups`;
* `measure_ups_ball` (**`Υ` maps the reference into the open ball**: `μ{c(g r) < 1} = 1`, i.e.
  `(Υ#μ){g < 1} = 1`; this is where the added hypothesis is used);
* `S_ups`, `ups_S`, `continuousOn_S` (`S = (Υ|_{c∘g<1})⁻¹` on `{g < 1}`, continuous).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.OTFD.Scale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsGauge

variable {g : E → ℝ} (hg : IsGauge g)
include hg

theorem zero : g 0 = 0 := by simpa using hg.smul 0 0

theorem neg (x : E) : g (-x) = g x := by simpa using hg.smul (-1) x

theorem nonneg (x : E) : 0 ≤ g x := by
  have := hg.add_le x (-x)
  rw [add_neg_cancel, hg.zero, hg.neg] at this
  linarith

theorem pos {x : E} (hx : x ≠ 0) : 0 < g x :=
  lt_of_le_of_ne (hg.nonneg x) fun h => hx (hg.eq_zero x h.symm)

theorem sub_le (x y : E) : g x - g y ≤ g (x - y) := by
  have := hg.add_le (x - y) y
  rw [sub_add_cancel] at this
  linarith

theorem convexOn : ConvexOn ℝ univ g :=
  ⟨convex_univ, fun x _ y _ a b ha hb _ => by
    calc g (a • x + b • y) ≤ g (a • x) + g (b • y) := hg.add_le _ _
      _ = a • g x + b • g y := by
        rw [hg.smul, hg.smul, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]⟩

variable [FiniteDimensional ℝ E]

theorem continuous : Continuous g := by
  have := hg.convexOn.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.1 this

theorem exists_le_mul_norm : ∃ b > 0, ∀ x, g x ≤ b * ‖x‖ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 (hg.continuous.continuousAt (x := 0)) 1
    one_pos
  refine ⟨2 / δ, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hg.zero]
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set t := δ / (2 * ‖x‖) with ht
  have htpos : 0 < t := by positivity
  have hy : dist (t • x) 0 < δ := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
    field_simp
    linarith
  have h1 := hball hy
  rw [Real.dist_eq, hg.zero, sub_zero, hg.smul, abs_of_pos htpos,
    abs_of_nonneg (mul_nonneg htpos.le (hg.nonneg x))] at h1
  rw [ht, div_mul_eq_mul_div, div_lt_one (by positivity)] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

theorem exists_mul_norm_le : ∃ a > 0, ∀ x, a * ‖x‖ ≤ g x := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, one_pos, fun x => by simp [Subsingleton.elim x 0, hg.zero]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hg.continuous.continuousOn
  have hx₀0 : x₀ ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨g x₀, hg.pos hx₀0, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hg.zero]
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have := hmin hmem
  simp only [mem_setOf_eq] at this
  rw [hg.smul, abs_of_pos (inv_pos.2 hxn)] at this
  rw [mul_comm]
  have := mul_le_mul_of_nonneg_left this hxn.le
  rwa [← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul] at this

end IsGauge

/-! ### The radial distribution function -/

variable [MeasurableSpace E] [BorelSpace E]

variable {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ}

theorem cK_mono : Monotone (cK μ g) := fun s t hst =>
  measureReal_mono fun x (hx : g x ≤ s) => (hx.trans hst : g x ≤ t)

theorem cK_nonneg (s : ℝ) : 0 ≤ cK μ g s := measureReal_nonneg

theorem cK_le_one (s : ℝ) : cK μ g s ≤ 1 :=
  (measureReal_mono (subset_univ _)).trans_eq probReal_univ

theorem cK_of_neg (hg : IsGauge g) {s : ℝ} (hs : s < 0) : cK μ g s = 0 := by
  have : {x | g x ≤ s} = ∅ := eq_empty_of_forall_notMem fun x hx =>
    absurd (lt_of_le_of_lt hx hs) (not_lt.2 (hg.nonneg x))
  simp [cK, this]

theorem cK_eq_cdf (hgm : Measurable g) : cK μ g = cdf (μ.map g) := by
  funext s
  rw [cdf_eq_real, map_measureReal_apply hgm measurableSet_Iic]
  rfl

theorem continuousAt_cK_of_atom (hgm : Measurable g) {s : ℝ} (h : μ {x | g x = s} = 0) :
    ContinuousAt (cK μ g) s := by
  rw [cK_eq_cdf hgm]
  set f := cdf (μ.map g)
  have hsing : (μ.map g) {s} = 0 := by
    rw [Measure.map_apply hgm (measurableSet_singleton s)]; exact h
  have h1 := f.measure_singleton s
  rw [measure_cdf, hsing, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have h2 : Function.leftLim f s ≤ f s := Monotone.leftLim_le f.mono le_rfl
  have hl : Function.leftLim f s = f s := le_antisymm h2 (by linarith)
  refine continuousAt_iff_continuous_left'_right'.2
    ⟨(f.mono.continuousWithinAt_Iio_iff_leftLim_eq).2 hl, ?_⟩
  exact (f.right_continuous s).mono Ioi_subset_Ici_self

theorem ScaleHyp.continuous [FiniteDimensional ℝ E] (hg : IsGauge g) (h : ScaleHyp μ g) :
    Continuous (cK μ g) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  by_cases hs : s < 0
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact (cK_of_neg hg ht).symm
  rcases (cK_le_one (μ := μ) (g := g) s).lt_or_eq with hlt | heq
  · exact h.cont s (not_lt.1 hs) hlt
  · exact continuousAt_cK_of_atom hg.continuous.measurable (h.atom s heq)

/-! ### The map `Υ` -/

theorem ups_zero (hg : IsGauge g) : ups μ g 0 = 0 := by simp [ups]

theorem g_ups (hg : IsGauge g) (h : ScaleHyp μ g) (r : E) : g (ups μ g r) = cK μ g (g r) := by
  by_cases hr : r = 0
  · simp [hr, ups, hg.zero, h.zero]
  have hpos := hg.pos hr
  rw [ups, hg.smul, abs_of_nonneg (div_nonneg (cK_nonneg _) hpos.le), div_mul_cancel₀ _ hpos.ne']

theorem g_ups_le_one (hg : IsGauge g) (h : ScaleHyp μ g) (r : E) : g (ups μ g r) ≤ 1 := by
  rw [g_ups hg h]; exact cK_le_one _

theorem continuous_ups [FiniteDimensional ℝ E] (hg : IsGauge g) (h : ScaleHyp μ g) :
    Continuous (ups μ g) := by
  have hc := h.continuous hg
  have hgc := hg.continuous
  obtain ⟨a, ha, hle⟩ := hg.exists_mul_norm_le
  refine continuous_iff_continuousAt.2 fun r => ?_
  by_cases hr : r = 0
  · subst hr
    rw [ContinuousAt, ups_zero hg]
    have hlim : Tendsto (fun r => cK μ g (g r) / a) (𝓝 0) (𝓝 0) := by
      have := ((hc.comp hgc).tendsto 0).div_const a
      simpa [Function.comp, hg.zero, h.zero] using this
    refine squeeze_zero_norm (fun r => ?_) hlim
    by_cases hr : r = 0
    · simp [hr, ups, cK_nonneg, ha.le, div_nonneg]
    have hpos := hg.pos hr
    rw [ups, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (cK_nonneg _) hpos.le)]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos ha]
    have := hle r
    have h0 := cK_nonneg (μ := μ) (g := g) (g r)
    nlinarith
  · exact (((hc.comp hgc).continuousAt.div hgc.continuousAt (hg.pos hr).ne').smul
      continuousAt_id)

/-- **`Υ` maps the reference into the open ball**: `μ{c(g r) < 1} = 1`, i.e.
`(Υ#μ){g < 1} = 1` (by `g_ups`). Uses the added hypothesis `ScaleHyp.atom`. -/
theorem measure_ups_ball [FiniteDimensional ℝ E] (hg : IsGauge g) (h : ScaleHyp μ g) :
    μ {r | cK μ g (g r) < 1} = 1 := by
  have hc := h.continuous hg
  have hgm : Measurable g := hg.continuous.measurable
  have hcompl : {r | cK μ g (g r) < 1}ᶜ = {r | cK μ g (g r) = 1} := by
    ext r; simp only [mem_compl_iff, mem_setOf_eq, not_lt]
    exact ⟨fun h1 => le_antisymm (cK_le_one _) h1, fun h1 => h1.ge⟩
  have hmeas : MeasurableSet {r | cK μ g (g r) < 1} :=
    measurableSet_lt (hc.measurable.comp hgm) measurable_const
  suffices μ {r | cK μ g (g r) = 1} = 0 by
    rw [← prob_compl_eq_zero_iff hmeas, hcompl]; exact this
  set A := {s | cK μ g s = 1} with hA
  by_cases hAe : A = ∅
  · have : {r | cK μ g (g r) = 1} = ∅ := eq_empty_of_forall_notMem fun r hr => by
      have : g r ∈ A := hr
      rw [hAe] at this; exact this
    rw [this, measure_empty]
  have hAne : A.Nonempty := nonempty_iff_ne_empty.2 hAe
  have hAbdd : BddBelow A := ⟨0, fun s (hs : cK μ g s = 1) => by
    by_contra hneg; rw [not_le] at hneg
    rw [cK_of_neg hg hneg] at hs; exact zero_ne_one hs⟩
  have hAcl : IsClosed A := isClosed_eq hc continuous_const
  set ρ := sInf A with hρ
  have hρA : cK μ g ρ = 1 := hAcl.csInf_mem hAne hAbdd
  have hset : {r | cK μ g (g r) = 1} ⊆ {r | g r = ρ} ∪ {r | ρ < g r} := by
    intro r hr
    have : ρ ≤ g r := csInf_le hAbdd hr
    rcases this.eq_or_lt with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1
  have hup : μ {r | ρ < g r} = 0 := by
    have hmeas' : MeasurableSet {r | g r ≤ ρ} := measurableSet_le hgm measurable_const
    have : {r | ρ < g r} = {r | g r ≤ ρ}ᶜ := by ext r; simp
    rw [this, prob_compl_eq_zero_iff hmeas']
    have h1 : μ.real {r | g r ≤ ρ} = 1 := hρA
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h1
    exact h1
  refine le_antisymm ((measure_mono hset).trans ((measure_union_le _ _).trans ?_)) bot_le
  rw [h.atom ρ hρA, hup, add_zero]

/-! ### The inverse `S` on the open ball -/

theorem cinv_nonneg (y : ℝ) : 0 ≤ cinv μ g y := by
  unfold cinv
  by_cases hne : {s | 0 ≤ s ∧ y ≤ cK μ g s}.Nonempty
  · exact le_csInf hne fun s hs => hs.1
  · rw [not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]

theorem exists_cK_gt [FiniteDimensional ℝ E] (hg : IsGauge g) {y : ℝ} (hy : y < 1) :
    ∃ s, 0 ≤ s ∧ y < cK μ g s := by
  have hgm : Measurable g := hg.continuous.measurable
  have hlim : Tendsto (cK μ g) atTop (𝓝 1) := by rw [cK_eq_cdf hgm]; exact tendsto_cdf_atTop (μ.map g)
  obtain ⟨s, hs1, hs2⟩ := ((hlim.eventually (lt_mem_nhds hy)).and (eventually_ge_atTop 0)).exists
  exact ⟨s, hs2, hs1⟩

section Inverse

variable [FiniteDimensional ℝ E] (hg : IsGauge g) (h : ScaleHyp μ g)
include hg h

theorem cK_pos {s : ℝ} (hs : 0 < s) : 0 < cK μ g s := by
  rcases (cK_le_one (μ := μ) (g := g) s).lt_or_eq with hlt | heq
  · have := h.mono ⟨le_rfl, by rw [h.zero]; norm_num⟩ ⟨hs.le, hlt⟩ hs
    rwa [h.zero] at this
  · rw [heq]; norm_num

theorem cinv_of_nonpos {y : ℝ} (hy : y ≤ 0) : cinv μ g y = 0 := by
  have : {s | 0 ≤ s ∧ y ≤ cK μ g s} = Ici 0 := by
    ext s
    simp only [mem_setOf_eq, mem_Ici]
    exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, hy.trans (cK_nonneg _)⟩⟩
  rw [cinv, this, csInf_Ici]

theorem cK_cinv {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) : cK μ g (cinv μ g y) = y := by
  have hc := h.continuous hg
  set T := {s | 0 ≤ s ∧ y ≤ cK μ g s} with hT
  obtain ⟨s₁, hs₁0, hs₁⟩ := exists_cK_gt (μ := μ) hg hy1
  have hne : T.Nonempty := ⟨s₁, hs₁0, hs₁.le⟩
  have hbdd : BddBelow T := ⟨0, fun s hs => hs.1⟩
  have hcl : IsClosed T := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le continuous_const hc)
  have hmem : cinv μ g y ∈ T := hcl.csInf_mem hne hbdd
  refine le_antisymm ?_ hmem.2
  by_contra hlt
  rw [not_le] at hlt
  set s₀ := cinv μ g y with hs₀
  rcases hmem.1.eq_or_lt with h0 | hpos
  · rw [← h0, h.zero] at hlt; linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := s₀))
    (cK μ g s₀ - y) (by linarith)
  set t := max 0 (s₀ - δ / 2) with ht
  have ht0 : 0 ≤ t := le_max_left _ _
  have hts : t < s₀ := max_lt hpos (by linarith)
  have hdist : dist t s₀ < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : s₀ - δ / 2 ≤ t := le_max_right _ _
    linarith
  have h1 := hball hdist
  rw [Real.dist_eq] at h1
  have h2 : y ≤ cK μ g t := by linarith [neg_abs_le (cK μ g t - cK μ g s₀)]
  have : s₀ ≤ t := csInf_le hbdd ⟨ht0, h2⟩
  linarith

theorem cinv_unique {y s : ℝ} (hs0 : 0 ≤ s) (hcs : cK μ g s = y) (hy1 : y < 1) :
    cinv μ g y = s := by
  have hy0 : 0 ≤ y := hcs ▸ cK_nonneg s
  have h1 := cK_cinv hg h hy0 hy1
  exact h.mono.injOn ⟨cinv_nonneg y, by rw [h1]; exact hy1⟩ ⟨hs0, by rw [hcs]; exact hy1⟩
    (h1.trans hcs.symm)

theorem continuousAt_cinv {y : ℝ} (hy : y < 1) : ContinuousAt (cinv μ g) y := by
  refine Metric.continuousAt_iff.2 fun ε hε => ?_
  set s := cinv μ g y with hsdef
  have hs0 : 0 ≤ s := cinv_nonneg y
  set u := cK μ g (s + ε / 2) with hudef
  have hu1 : u ≤ 1 := cK_le_one _
  have hyu : y < u := by
    by_cases hy0 : y ≤ 0
    · have := cK_pos hg h (μ := μ) (s := s + ε / 2) (by linarith)
      linarith
    · rw [not_le] at hy0
      have hcs := cK_cinv hg h hy0.le hy
      rcases (cK_le_one (μ := μ) (g := g) (s + ε / 2)).lt_or_eq with hlt | heq
      · have := h.mono ⟨hs0, by rw [hcs]; exact hy⟩ ⟨by linarith, hlt⟩ (by linarith : s < s + ε / 2)
        rw [hcs] at this; exact this
      · rw [hudef, heq]; exact hy
  -- the upper half, valid for every `y'`
  have hupper : ∀ y', y' < u → cinv μ g y' < s + ε / 2 := by
    intro y' hy'
    by_cases hy'0 : y' ≤ 0
    · rw [cinv_of_nonpos hg h hy'0]; linarith
    · rw [not_le] at hy'0
      have hy'1 : y' < 1 := lt_of_lt_of_le hy' hu1
      have hct := cK_cinv hg h hy'0.le hy'1
      by_contra hge
      rw [not_lt] at hge
      have := cK_mono (μ := μ) (g := g) hge
      rw [hct] at this; linarith
  by_cases hlow : s < ε / 2
  · refine ⟨u - y, by linarith, fun {y'} hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have hy' : y' < u := by linarith [le_abs_self (y' - y)]
    have h1 := hupper y' hy'
    have h2 := cinv_nonneg (μ := μ) (g := g) y'
    rw [abs_lt]; constructor <;> linarith
  · rw [not_lt] at hlow
    have hspos : 0 < s := by linarith
    have hy0 : 0 < y := by
      by_contra hy0; rw [not_lt] at hy0
      rw [hsdef, cinv_of_nonpos hg h hy0] at hspos; exact lt_irrefl _ hspos
    have hcs := cK_cinv hg h hy0.le hy
    set l := cK μ g (s - ε / 2) with hldef
    have hly : l < y := by
      have hm := h.mono ⟨by linarith, lt_of_le_of_lt (cK_mono (by linarith)) (hcs ▸ hy)⟩
        ⟨hs0, by rw [hcs]; exact hy⟩ (by linarith : s - ε / 2 < s)
      rw [hcs] at hm; exact hm
    have hl0 : 0 ≤ l := cK_nonneg _
    refine ⟨min (u - y) (y - l), lt_min (by linarith) (by linarith), fun {y'} hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have hd1 : |y' - y| < u - y := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : |y' - y| < y - l := lt_of_lt_of_le hd (min_le_right _ _)
    have hy'u : y' < u := by linarith [le_abs_self (y' - y)]
    have hy'l : l < y' := by linarith [neg_abs_le (y' - y)]
    have h1 := hupper y' hy'u
    have hy'1 : y' < 1 := lt_of_lt_of_le hy'u hu1
    have hct := cK_cinv hg h (by linarith) hy'1
    have h2 : s - ε / 2 < cinv μ g y' := by
      by_contra hle; rw [not_lt] at hle
      have := cK_mono (μ := μ) (g := g) hle
      rw [hct] at this; linarith
    rw [abs_lt]; constructor <;> linarith

theorem g_Sinv (w : E) : g (Sinv μ g w) = cinv μ g (g w) := by
  by_cases hw : w = 0
  · simp [hw, Sinv, hg.zero, cinv_of_nonpos hg h le_rfl]
  have hpos := hg.pos hw
  rw [Sinv, hg.smul, abs_of_nonneg (div_nonneg (cinv_nonneg _) hpos.le),
    div_mul_cancel₀ _ hpos.ne']

theorem S_ups {r : E} (hr : cK μ g (g r) < 1) : Sinv μ g (ups μ g r) = r := by
  by_cases hr0 : r = 0
  · simp [hr0, ups, Sinv]
  have hpos := hg.pos hr0
  have hy := g_ups hg h r
  have hypos : 0 < cK μ g (g r) := cK_pos hg h hpos
  have hcinv : cinv μ g (cK μ g (g r)) = g r := cinv_unique hg h hpos.le rfl hr
  rw [Sinv, hy, hcinv, ups, smul_smul]
  rw [show g r / cK μ g (g r) * (cK μ g (g r) / g r) = 1 by field_simp, one_smul]

theorem ups_S {w : E} (hw : g w < 1) :
    ups μ g (Sinv μ g w) = w ∧ cK μ g (g (Sinv μ g w)) < 1 := by
  by_cases hw0 : w = 0
  · simp [hw0, ups, Sinv, hg.zero, h.zero]
  have hpos := hg.pos hw0
  have hcs := cK_cinv hg h hpos.le hw
  have hgS := g_Sinv hg h w
  have hs0 : cinv μ g (g w) ≠ 0 := by
    intro h0; rw [h0, h.zero] at hcs; exact hpos.ne' hcs.symm
  refine ⟨?_, by rw [hgS, hcs]; exact hw⟩
  rw [ups, hgS, hcs, Sinv, smul_smul]
  rw [show g w / cinv μ g (g w) * (cinv μ g (g w) / g w) = 1 by field_simp, one_smul]

theorem continuousOn_Sinv : ContinuousOn (Sinv μ g) {w | g w < 1} := by
  have hgc := hg.continuous
  obtain ⟨a, ha, hle⟩ := hg.exists_mul_norm_le
  intro w hw
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hw0 : w = 0
  · subst hw0
    rw [ContinuousAt, show Sinv μ g 0 = 0 by simp [Sinv]]
    have hlim : Tendsto (fun w => cinv μ g (g w) / a) (𝓝 0) (𝓝 0) := by
      have h1 := ((continuousAt_cinv hg h (y := g 0) (by rw [hg.zero]; norm_num)).comp
        hgc.continuousAt).tendsto.div_const a
      simpa [Function.comp, hg.zero, cinv_of_nonpos hg h le_rfl] using h1
    refine squeeze_zero_norm (fun w' => ?_) hlim
    by_cases hw' : w' = 0
    · simp [hw', Sinv, div_nonneg (cinv_nonneg _) ha.le]
    have hpos := hg.pos hw'
    rw [Sinv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (cinv_nonneg _) hpos.le),
      div_mul_eq_mul_div, div_le_div_iff₀ hpos ha]
    have := hle w'
    have h0 := cinv_nonneg (μ := μ) (g := g) (g w')
    nlinarith
  · exact (((continuousAt_cinv hg h hw).comp hgc.continuousAt).div hgc.continuousAt
      (hg.pos hw0).ne').smul continuousAt_id

end Inverse

end StatFormal.OTFD.Scale
