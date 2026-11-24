import StatFormal.Wave31th.RouteChart
import StatFormal.Wave31th.RouteDensity

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Wave 31th, route: the core on `ι → ℝ` (untrusted proof file)

`core_pi`: let `f : (ι → ℝ) → ℝ` be `C¹` with a compact thin band `{|f − t| ≤ r₀}`, the level set `L = {f = t}` nonempty with `∇f ≠ 0` on it,
`p` continuous on an open `U ⊇ L` and positive on `L`. Then the law of `f` under `p·λ` has on `[t−r,t+r]` a density in `[c, C]`.

Route: at each `x ∈ L` a coordinate `i` with `∂_i f(x) ≠ 0` and a neighbourhood on which `m |∂_i f| ≤ p ≤ M |∂_i f|`
(`local_chart`, from `chart_bounds`); `L` is compact (closed in the band), so finitely many chart regions `R_x` cover it; the band
`{|f − t| ≤ r}` lies in `⋃ R_x` for small `r` (`exists_band_subset`: the minimum of `|f − t|` on the compact band minus `⋃ R_x`);
for Borel `A ⊆ [t−r,t+r]`, `P(f⁻¹A) ≤ Σ_x P(f⁻¹A ∩ R_x) ≤ (Σ_x M_x B_x) λ(A)` and `P(f⁻¹A) ≥ P(f⁻¹A ∩ R_{x₁}) ≥ m_{x₁} B_{x₁} λ(A)`;
`qdensity_of_bounds` turns these two-sided bounds into a density.
-/

noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace StatFormal.Wave31th.Chart

open StatFormal.Wave12c StatFormal.Wave31th

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A chart at a point of the level set. -/
lemma local_chart {f p : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} {t : ℝ} (hf : ContDiff ℝ 1 f) (hU : IsOpen U)
    (hp : ContinuousOn p U) {x : ι → ℝ} (hxL : f x = t) (hxU : x ∈ U) (hpx : 0 < p x)
    (hdx : ∃ i, fderiv ℝ f x (Pi.single i 1) ≠ 0) :
    ∃ (R : Set (ι → ℝ)) (ε : ℝ) (B : ℝ≥0∞) (m M : ℝ), IsOpen R ∧ x ∈ R ∧ 0 < ε ∧ 0 < B ∧ B ≠ ∞ ∧
      0 < m ∧ 0 ≤ M ∧
      ∀ A : Set ℝ, MeasurableSet A →
        ENNReal.ofReal m * B * volume (A ∩ Ioo (t - ε) (t + ε)) ≤
            (volume.withDensity fun y => ENNReal.ofReal (p y)) (f ⁻¹' A ∩ R) ∧
        (volume.withDensity fun y => ENNReal.ofReal (p y)) (f ⁻¹' A ∩ R) ≤
            ENNReal.ofReal M * B * volume (A ∩ Ioo (t - ε) (t + ε)) := by
  obtain ⟨i, hi⟩ := hdx
  set g : (ι → ℝ) → ℝ := fun y => fderiv ℝ f y (Pi.single i 1) with hg
  have hgc : Continuous g := (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have ha : 0 < |g x| := abs_pos.2 hi
  have hpc : ContinuousAt p x := hp.continuousAt (hU.mem_nhds hxU)
  have hN : {y | y ∈ U ∧ |g x| / 2 < |g y| ∧ |g y| < 2 * |g x| ∧ p x / 2 < p y ∧ p y < 2 * p x} ∈ 𝓝 x := by
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hxU
    have hab : ContinuousAt (fun y => |g y|) x := (continuous_abs.comp hgc).continuousAt
    have h2 : ∀ᶠ y in 𝓝 x, |g x| / 2 < |g y| :=
      continuousAt_const.eventually_lt hab (by show |g x| / 2 < |g x|; linarith)
    have h2' : ∀ᶠ y in 𝓝 x, |g y| < 2 * |g x| :=
      hab.eventually_lt continuousAt_const (by show |g x| < 2 * |g x|; linarith)
    have h3 : ∀ᶠ y in 𝓝 x, p x / 2 < p y := continuousAt_const.eventually_lt hpc (by linarith)
    have h4 : ∀ᶠ y in 𝓝 x, p y < 2 * p x := hpc.eventually_lt continuousAt_const (by linarith)
    filter_upwards [h1, h2, h2', h3, h4] with y hy1 hy2 hy2' hy3 hy4
    exact ⟨hy1, hy2, hy2', hy3, hy4⟩
  have hbd : ∀ y ∈ {y | y ∈ U ∧ |g x| / 2 < |g y| ∧ |g y| < 2 * |g x| ∧ p x / 2 < p y ∧ p y < 2 * p x},
      (p x / (4 * |g x|)) * |g y| ≤ p y ∧ p y ≤ (4 * p x / |g x|) * |g y| := by
    rintro y ⟨-, hy2, hy2', hy3, hy4⟩
    constructor
    · calc (p x / (4 * |g x|)) * |g y| ≤ (p x / (4 * |g x|)) * (2 * |g x|) := by gcongr
        _ = p x / 2 := by field_simp; ring
        _ ≤ p y := hy3.le
    · calc p y ≤ 2 * p x := hy4.le
        _ = (4 * p x / |g x|) * (|g x| / 2) := by field_simp; ring
        _ ≤ (4 * p x / |g x|) * |g y| := by gcongr
  obtain ⟨R, ε, B, hRo, hxR, -, hε, hB, hBtop, hbound⟩ :=
    chart_bounds hf i hi hN (m := p x / (4 * |g x|)) (M := 4 * p x / |g x|) (by positivity) (by positivity) hbd
  refine ⟨R, ε, B, p x / (4 * |g x|), 4 * p x / |g x|, hRo, hxR, hε, hB, hBtop, by positivity, by positivity, ?_⟩
  rw [← hxL]
  exact hbound

/-- The band `{|f − t| ≤ r₂}` lies in an open set containing the level set, for small `r₂`. -/
lemma exists_band_subset {f : (ι → ℝ) → ℝ} (hfc : Continuous f) {t r₀ : ℝ} (hr₀ : 0 < r₀)
    (hband : IsCompact {x | |f x - t| ≤ r₀}) {W : Set (ι → ℝ)} (hW : IsOpen W)
    (hLW : {x | f x = t} ⊆ W) : ∃ r₂ > 0, ∀ z, |f z - t| ≤ r₂ → z ∈ W := by
  set K := {x | |f x - t| ≤ r₀} ∩ Wᶜ with hK
  have hKc : IsCompact K := hband.inter_right hW.isClosed_compl
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨r₀, hr₀, fun z hz => ?_⟩
    by_contra hzW
    have : z ∈ K := ⟨hz, hzW⟩
    rw [hKe] at this
    exact this
  · obtain ⟨z₀, hz₀K, hmin⟩ := hKc.exists_isMinOn hKne
      (show Continuous fun z => |f z - t| by fun_prop).continuousOn
    have hm : 0 < |f z₀ - t| := by
      rw [abs_pos, sub_ne_zero]
      intro h0
      exact hz₀K.2 (hLW h0)
    refine ⟨min r₀ (|f z₀ - t| / 2), by positivity, fun z hz => ?_⟩
    by_contra hzW
    have hzK : z ∈ K := ⟨le_trans hz (min_le_left _ _), hzW⟩
    have h1 : |f z₀ - t| ≤ |f z - t| := isMinOn_iff.1 hmin z hzK
    have h2 := min_le_right r₀ (|f z₀ - t| / 2)
    linarith

/-- The core on `ι → ℝ`. -/
theorem core_pi {f p : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} {t : ℝ} (hf : ContDiff ℝ 1 f)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hband : IsCompact {x | |f x - t| ≤ r₀})
    (hne : ∃ x, f x = t) (hd : ∀ x, f x = t → ∃ i, fderiv ℝ f x (Pi.single i 1) ≠ 0)
    (hU : IsOpen U) (hLU : {x | f x = t} ⊆ U) (hp : ContinuousOn p U) (hpos : ∀ x, f x = t → 0 < p x) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
      QDensity (volume.withDensity fun x => ENNReal.ofReal (p x)) f t r c C := by
  classical
  have hfc : Continuous f := hf.continuous
  set L := {x | f x = t} with hLdef
  have hLc : IsCompact L := hband.of_isClosed_subset (isClosed_eq hfc continuous_const) (fun x hx => by
    have hx' : f x = t := hx
    show |f x - t| ≤ r₀
    rw [hx', sub_self, abs_zero]
    exact hr₀.le)
  set P : Measure (ι → ℝ) := volume.withDensity fun x => ENNReal.ofReal (p x) with hP
  have hloc : ∀ x, ∃ (R : Set (ι → ℝ)) (ε : ℝ) (B : ℝ≥0∞) (m M : ℝ), x ∈ L →
      (IsOpen R ∧ x ∈ R ∧ 0 < ε ∧ 0 < B ∧ B ≠ ∞ ∧ 0 < m ∧ 0 ≤ M ∧
        ∀ A : Set ℝ, MeasurableSet A →
          ENNReal.ofReal m * B * volume (A ∩ Ioo (t - ε) (t + ε)) ≤ P (f ⁻¹' A ∩ R) ∧
          P (f ⁻¹' A ∩ R) ≤ ENNReal.ofReal M * B * volume (A ∩ Ioo (t - ε) (t + ε))) := by
    intro x
    by_cases hx : x ∈ L
    · obtain ⟨R, ε, B, m, M, h⟩ := local_chart hf hU hp hx (hLU hx) (hpos x hx) (hd x hx)
      exact ⟨R, ε, B, m, M, fun _ => h⟩
    · exact ⟨∅, 1, 1, 1, 0, fun h => absurd h hx⟩
  choose R ε B m M hRM using hloc
  obtain ⟨F, hFL, hcov⟩ := hLc.elim_nhds_subcover R
    (fun x hx => ((hRM x hx).1).mem_nhds ((hRM x hx).2.1))
  set W := ⋃ x ∈ F, R x with hW
  have hWo : IsOpen W := isOpen_biUnion fun x hx => (hRM x (hFL x hx)).1
  obtain ⟨r₂, hr₂, hr₂W⟩ := exists_band_subset hfc hr₀ hband hWo hcov
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨x₁, hx₁F, -⟩ : ∃ x ∈ F, x₀ ∈ R x := by
    have := hcov hx₀
    simpa [hW] using this
  obtain ⟨xm, hxmF, hxm⟩ := F.exists_min_image ε ⟨x₁, hx₁F⟩
  have hε₀ : 0 < ε xm := (hRM xm (hFL xm hxmF)).2.2.1
  set r := min r₂ (ε xm / 2) with hrdef
  have hr : 0 < r := lt_min hr₂ (by positivity)
  have hrε : ∀ x ∈ F, r < ε x := fun x hx =>
    lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le (by linarith) (hxm x hx))
  have hAsub : ∀ x ∈ F, ∀ A : Set ℝ, A ⊆ Icc (t - r) (t + r) → A ∩ Ioo (t - ε x) (t + ε x) = A := by
    intro x hx A hA
    refine inter_eq_left.2 fun a ha => ?_
    obtain ⟨h1, h2⟩ := hA ha
    have := hrε x hx
    exact ⟨by linarith, by linarith⟩
  have hcover : ∀ A : Set ℝ, A ⊆ Icc (t - r) (t + r) → f ⁻¹' A ⊆ ⋃ x ∈ F, (f ⁻¹' A ∩ R x) := by
    intro A hA z hz
    obtain ⟨h1, h2⟩ := hA hz
    have hzb : |f z - t| ≤ r₂ := by
      rw [abs_le]
      have := min_le_left r₂ (ε xm / 2)
      constructor <;> linarith
    have hzW : z ∈ W := hr₂W z hzb
    simp only [hW, mem_iUnion, exists_prop] at hzW
    obtain ⟨x, hxF, hzx⟩ := hzW
    simp only [mem_iUnion, exists_prop]
    exact ⟨x, hxF, hz, hzx⟩
  -- the constants
  have hfinU : ∑ x ∈ F, ENNReal.ofReal (M x) * B x ≠ ∞ := by
    refine ne_of_lt (ENNReal.sum_lt_top.2 fun x hx => ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (hRM x (hFL x hx)).2.2.2.2.1)
  have hfinL : ENNReal.ofReal (m x₁) * B x₁ ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (hRM x₁ (hFL x₁ hx₁F)).2.2.2.2.1)).ne
  have hposL : ENNReal.ofReal (m x₁) * B x₁ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (hRM x₁ (hFL x₁ hx₁F)).2.2.2.2.2.1).ne'
      (hRM x₁ (hFL x₁ hx₁F)).2.2.2.1.ne'
  set c' : ℝ := (ENNReal.ofReal (m x₁) * B x₁).toReal with hc'
  set C' : ℝ := (∑ x ∈ F, ENNReal.ofReal (M x) * B x).toReal with hC'
  have hc'pos : 0 < c' := ENNReal.toReal_pos hposL hfinL
  have hc'e : ENNReal.ofReal c' = ENNReal.ofReal (m x₁) * B x₁ := ENNReal.ofReal_toReal hfinL
  have hC'e : ENNReal.ofReal C' = ∑ x ∈ F, ENNReal.ofReal (M x) * B x := ENNReal.ofReal_toReal hfinU
  have hbd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - r) (t + r) →
      ENNReal.ofReal c' * volume A ≤ P (f ⁻¹' A) ∧ P (f ⁻¹' A) ≤ ENNReal.ofReal C' * volume A := by
    intro A hA hAI
    constructor
    · rw [hc'e]
      have h1 := ((hRM x₁ (hFL x₁ hx₁F)).2.2.2.2.2.2.2 A hA).1
      rw [hAsub x₁ hx₁F A hAI] at h1
      exact h1.trans (measure_mono inter_subset_left)
    · rw [hC'e, Finset.sum_mul]
      calc P (f ⁻¹' A) ≤ P (⋃ x ∈ F, (f ⁻¹' A ∩ R x)) := measure_mono (hcover A hAI)
        _ ≤ ∑ x ∈ F, P (f ⁻¹' A ∩ R x) := measure_biUnion_finset_le _ _
        _ ≤ ∑ x ∈ F, ENNReal.ofReal (M x) * B x * volume A := by
            refine Finset.sum_le_sum fun x hx => ?_
            have h1 := ((hRM x (hFL x hx)).2.2.2.2.2.2.2 A hA).2
            rwa [hAsub x hx A hAI] at h1
  have hQ := qdensity_of_bounds (t := t) (r := r) (c := c') (C := C') hfc.measurable hc'pos hbd
  exact ⟨r, c', max c' C', hr, hc'pos, le_max_left _ _, hQ⟩

end StatFormal.Wave31th.Chart
