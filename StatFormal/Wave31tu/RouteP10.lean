import StatFormal.Wave31tu.RouteP10Setup
import StatFormal.Wave31tu.RouteP9
import StatFormal.Wave31tr.Proofs
import StatFormal.Wave30tz.Proofs

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y10 `lap_clip` (Lemma S4.21 `lem:lapclip`, S4 :1088-1132)

The fitted Laplace witness clips itself: with `P̃, Q̃` the empirical laws of the fitting batches (no `x_i` equal to a `y_j`),
`α ∈ (0,1)` and a minimizer `(w, v)` of `eq:qp`: `D̄̂ > 0`, `û ≤ f̂ ≤ t̂` on `ℝ`, `ĝ = t̂ − û = osc(f̂) > 0`, the order statistics
of ranks `≥ ⌈n′(1−α)⌉` at the `X`'s equal `t̂` and those of ranks `≤ ⌊m′α⌋ + 1` at the `Y`'s equal `û`, every genuine quantile is `t̂`,
resp. `û`, the plain ramp is `(f̂ − û)/ĝ`, `φ̂ = f̂/ĝ` has `osc = 1`, `‖φ̂‖ = 1/ĝ ≥ ½` (the least representer norm),
`L̃(φ̂) − α = D̄̂‖φ̂‖`, `φ̂` maximizes `(L̃(φ) − α)/‖φ‖` over `osc(φ) ≤ 1`, and the own-term order statistics and genuine quantiles lie
within `1/(n′D̄̂)`, resp. `1/(m′D̄̂)`, of `t̂`, `û`.

Route (printed): the empirical laws are a pair to which the population results apply — 31tr T42 `excess_laplace` in its general
form (G) at `P̃, Q̃` (self-clipping `u ≤ f⋆ ≤ t` and the equality of Proposition 5.10(i)), with `t̂`, `û` the least `(1−α)`- and
greatest `α`-quantiles of the values (`Lib/EmpiricalQuantile`), the gap `t̂ − û ≥ D > 0` (certified `pop_ramp_rkhs`; `D > 0` by
`eq:zeroeq`, `TV(P̃,Q̃) = 1`, `RouteP10Setup`); Lemma S4.20 (`RouteP9.ratio_le_uPath`) at `P̃, Q̃`; the own terms
`w_i/D̂ ∈ [0, 1/(n′(1−α)D̂)]` and the certified `order_stat_shift`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration
  StatFormal.Wave30tz StatFormal.Wave30tq StatFormal.EmpiricalQuantile

/-- Y10 `lap_clip`. -/
theorem lap_clip_route : Claims.lap_clip := by
  intro H _ _ _ _ σ φ n m x y α w v hσ hφ hn hm hxy hα0 hα1 hQP
  intro F t u D φh
  obtain ⟨hsm, hnorm, -⟩ := laplace_feature_facts hσ hφ
  have hP := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  have hQ := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  have hw := hQP.1
  have hv := hQP.2.1
  have hDeq : D = Demp φ x y α := StatFormal.PaperRun.qpVal_eq_Demp hsm hα0.le hα1 hn hm hQP
  have hDpos' := dpop_empirical_pos hσ hφ hn hm x y hxy hα0.le hα1
  have hDD : D = Dpop φ (empirical x) (empirical y) α := hDeq
  have hDpos : 0 < D := hDD ▸ hDpos'
  have ha : wsum φ x w ∈ region φ α (empirical x) := wsum_mem_region hsm x hw
  have hb : wsum φ y v ∈ region φ α (empirical y) := wsum_mem_region hsm y hv
  have hab : ‖wsum φ x w - wsum φ y v‖ = Dpop φ (empirical x) (empirical y) α := hDD
  have hFm : Measurable F := ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).measurable
  have ht : IsLeast {q | IsQuantileAt (empirical x) F (1 - α) q} t :=
    isLeast_quantileAt_empirical hn x hFm (by linarith) (by linarith)
  have hu : IsGreatest {q | IsQuantileAt (empirical y) F α q} u :=
    isGreatest_quantileAt_empirical hm y hFm hα0.le hα1
  have hDφ : ∀ z z' : ℝ, ‖φ z - φ z'‖ ≤ 2 := fun z z' =>
    (norm_sub_le _ _).trans (by rw [hnorm, hnorm]; norm_num)
  have hgap := (StatFormal.Wave30tz.pop_ramp_rkhs ℝ H (empirical x) (empirical y) φ 1 2 α (wsum φ x w) (wsum φ y v)
    t u hsm (fun z => (hnorm z).le) hDφ hα0.le hα1 ha hb hab hDpos' ht hu).1
  have htu : 0 < t - u := lt_of_lt_of_le hDpos' hgap
  obtain ⟨hband, hid, -, -⟩ := StatFormal.Wave31tr.excess_laplace.1 H σ φ (empirical x) (empirical y) α
    (wsum φ x w) (wsum φ y v) t u hσ hsm hφ hα0.le hα1 hDpos' ha hb hab ht.1 hu.1 (by linarith)
  have hband' : ∀ z, u ≤ F z ∧ F z ≤ t := hband
  -- ranks
  have hp0 : 0 < 1 - α := by linarith
  have hr1 : 1 ≤ ⌈(n : ℝ) * (1 - α)⌉₊ := rank_ceil_pos hn hp0
  have hr2 : ⌈(n : ℝ) * (1 - α)⌉₊ ≤ ⌊(n : ℝ) * (1 - α)⌋₊ + 1 := rank_ceil_le_floor_succ _ _
  have hr3 : ⌊(n : ℝ) * (1 - α)⌋₊ + 1 ≤ n := rank_floor_succ_le hn hp0.le (by linarith)
  have hs1 : 1 ≤ ⌈(m : ℝ) * α⌉₊ := rank_ceil_pos hm hα0
  have hs2 : ⌈(m : ℝ) * α⌉₊ ≤ ⌊(m : ℝ) * α⌋₊ + 1 := rank_ceil_le_floor_succ _ _
  have hs3 : ⌊(m : ℝ) * α⌋₊ + 1 ≤ m := rank_floor_succ_le hm hα0.le hα1
  -- (d) the order statistics
  have hX : ∀ r : ℕ, ⌈(n : ℝ) * (1 - α)⌉₊ ≤ r → r ≤ n → ordStat (fun i => F (x i)) r = t := fun r h1 h2 =>
    le_antisymm (ordStat_le_of_forall_le _ (hr1.trans h1) h2 fun i => (hband' (x i)).2)
      (ordStat_mono_rank _ hr1 h1 h2)
  have hY : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊(m : ℝ) * α⌋₊ + 1 → ordStat (fun j => F (y j)) r = u := fun r h1 h2 =>
    le_antisymm (ordStat_mono_rank _ h1 h2 hs3)
      (le_ordStat_of_forall_le _ h1 (h2.trans hs3) fun j => (hband' (y j)).1)
  -- attained values
  obtain ⟨i₀, hi₀⟩ := exists_eq_ordStat (fun i => F (x i)) hr1 (hr2.trans hr3)
  obtain ⟨j₀, hj₀⟩ := exists_eq_ordStat (fun j => F (y j)) (by omega : 1 ≤ ⌊(m : ℝ) * α⌋₊ + 1) hs3
  have hti : F (x i₀) = t := hi₀
  have huj : F (y j₀) = u := hj₀
  have hsupinf := iSup_iInf_of_attained hband' hti huj
  -- (c) the oscillation
  have hosc : Wave31to.oscFn F = t - u := by unfold Wave31to.oscFn; rw [hsupinf.1, hsupinf.2]
  -- (e) genuine quantiles
  have hqX : ∀ q, IsEmpQuantile (fun i => F (x i)) (1 - α) q → q = t := fun q hq => by
    obtain ⟨h1, h2⟩ := empQuantile_bracket _ hn hp0 (by linarith) hq
    rw [hX _ hr2 hr3] at h2
    exact le_antisymm h2 h1
  have hqY : ∀ q, IsEmpQuantile (fun j => F (y j)) α q → q = u := fun q hq => by
    obtain ⟨h1, h2⟩ := empQuantile_bracket _ hm hα0 hα1 hq
    rw [hY (⌊(m : ℝ) * α⌋₊ + 1) (by omega) le_rfl] at h2
    rw [hY _ hs1 hs2] at h1
    exact le_antisymm h2 h1
  -- (f) the plain ramp
  have hramp : ramp F t u = fun z => (F z - u) / (t - u) := by
    funext z
    simp only [ramp, clip]
    rw [max_eq_left (hband' z).1, min_eq_left (hband' z).2]
  -- (g) the normalized witness
  have hwit : ∀ z, Wave31to.wit φ φh z = (t - u)⁻¹ * F z := fun z => by
    show ⟪(t - u)⁻¹ • witness φ x y w v, φ z⟫_ℝ = _
    rw [real_inner_smul_left]; rfl
  have hinv : 0 < (t - u)⁻¹ := inv_pos.mpr htu
  have hbandw : ∀ z, (t - u)⁻¹ * u ≤ Wave31to.wit φ φh z ∧ Wave31to.wit φ φh z ≤ (t - u)⁻¹ * t := fun z => by
    rw [hwit]; exact ⟨mul_le_mul_of_nonneg_left (hband' z).1 hinv.le, mul_le_mul_of_nonneg_left (hband' z).2 hinv.le⟩
  have hsupinfw := iSup_iInf_of_attained hbandw (z₁ := x i₀) (z₂ := y j₀) (by rw [hwit, hti]) (by rw [hwit, huj])
  have hoscw : Wave31to.oscFn (Wave31to.wit φ φh) = 1 := by
    unfold Wave31to.oscFn; rw [hsupinfw.1, hsupinfw.2, ← mul_sub, inv_mul_cancel₀ htu.ne']
  have hnw : ‖witness φ x y w v‖ = 1 := by
    unfold witness
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hDpos]
    exact inv_mul_cancel₀ hDpos.ne'
  have hnφh : ‖φh‖ = 1 / (t - u) := by
    show ‖(t - u)⁻¹ • witness φ x y w v‖ = _
    rw [norm_smul, hnw, Real.norm_eq_abs, abs_of_pos hinv, mul_one, one_div]
  have hwitle : ∀ z, |Wave31to.wit φ φh z| ≤ ‖φh‖ := fun z =>
    (abs_real_inner_le_norm φh (φ z)).trans (by rw [hnorm, mul_one])
  have hhalf : 1 / 2 ≤ ‖φh‖ := by
    have h1 := hwitle (x i₀)
    have h2 := hwitle (y j₀)
    rw [hwit, hti] at h1
    rw [hwit, huj] at h2
    have h3 : (t - u)⁻¹ * t - (t - u)⁻¹ * u = 1 := by rw [← mul_sub, inv_mul_cancel₀ htu.ne']
    have h4 : (t - u)⁻¹ * t - (t - u)⁻¹ * u ≤ |(t - u)⁻¹ * t| + |(t - u)⁻¹ * u| :=
      (sub_le_sub (le_abs_self _) (neg_abs_le _)).trans_eq (by ring)
    linarith
  have hrep : ∀ g' : H, (∀ z, ⟪g', φ z⟫_ℝ = Wave31to.wit φ φh z) → ‖φh‖ ≤ ‖g'‖ := fun g' hg' =>
    norm_le_of_rep (witness_orth φ x y w v (t - u)⁻¹) hg'
  -- (h) the identity `L̃(φ̂) − α = D̄̂ N̂`
  have hwint : ∀ μ : Measure ℝ, IsFiniteMeasure μ → Integrable (Wave31to.wit φ φh) μ := fun μ _ =>
    Integrable.of_bound ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).aestronglyMeasurable ‖φh‖
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hwitle z)
  have hramp' : ∀ z, ramp F t u z = Wave31to.wit φ φh z - u / (t - u) := fun z => by
    rw [hramp, hwit]; field_simp
  have hint : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      ∫ z, ramp F t u z ∂μ = (∫ z, Wave31to.wit φ φh z ∂μ) - u / (t - u) := fun μ _ => by
    simp_rw [hramp']
    rw [integral_sub (hwint μ inferInstance) (integrable_const _), integral_const]
    simp
  have hid' : (∫ z, ramp F t u z ∂(empirical x)) - (∫ z, ramp F t u z ∂(empirical y)) - α =
      (1 - α) * Dpop φ (empirical x) (empirical y) α / (t - u) := hid
  rw [hint _ hP, hint _ hQ] at hid'
  have hlin : linL (empirical x) (empirical y) (Wave31to.wit φ φh) - α = (1 - α) * D * ‖φh‖ := by
    unfold linL
    rw [hnφh, hDD]
    have : (1 - α) * Dpop φ (empirical x) (empirical y) α * (1 / (t - u)) =
        (1 - α) * Dpop φ (empirical x) (empirical y) α / (t - u) := by ring
    rw [this, ← hid']; ring
  -- (i) the maximizing property
  have hmax : ∀ g' : H, g' ≠ 0 → Wave31to.oscFn (Wave31to.wit φ g') ≤ 1 →
      (linL (empirical x) (empirical y) (Wave31to.wit φ g') - α) / ‖g'‖ ≤
        (linL (empirical x) (empirical y) (Wave31to.wit φ φh) - α) / ‖φh‖ := by
    intro g' hg' hosc'
    have h := ratio_le_uPath (P := empirical x) (Q := empirical y) hsm (κ := 1) (fun z => (hnorm z).le) hα0.le hα1 hg' hosc'
    have hφhpos : 0 < ‖φh‖ := by linarith
    rw [hlin, mul_div_assoc, div_self hφhpos.ne', mul_one]
    unfold Wave31ti.uPath at h
    rw [← hDD] at h
    exact h
  -- (j), (k) the own terms
  have hownX : ∀ i, ownX φ x y w v i = F (x i) - w i / D := fun i => by
    unfold ownX; rw [hnorm]; simp only [one_pow, mul_one]; rfl
  have hownY : ∀ j, ownY φ x y w v j = F (y j) + v j / D := fun j => by
    unfold ownY; rw [hnorm]; simp only [one_pow, mul_one]; rfl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcX : ∀ i, 0 ≤ w i / D ∧ w i / D ≤ 1 / (n * ((1 - α) * D)) := fun i => by
    refine ⟨div_nonneg (hw.1 i).1 hDpos.le, ?_⟩
    have := (hw.1 i).2
    rw [div_le_iff₀ hDpos]
    calc w i ≤ 1 / (n * (1 - α)) := this
      _ = 1 / (n * ((1 - α) * D)) * D := by field_simp
  have hcY : ∀ j, 0 ≤ v j / D ∧ v j / D ≤ 1 / (m * ((1 - α) * D)) := fun j => by
    refine ⟨div_nonneg (hv.1 j).1 hDpos.le, ?_⟩
    have := (hv.1 j).2
    rw [div_le_iff₀ hDpos]
    calc v j ≤ 1 / (m * (1 - α)) := this
      _ = 1 / (m * ((1 - α) * D)) * D := by field_simp
  have hOX : ∀ r : ℕ, ⌈(n : ℝ) * (1 - α)⌉₊ ≤ r → r ≤ n →
      t - 1 / (n * ((1 - α) * D)) ≤ ordStat (ownX φ x y w v) r ∧ ordStat (ownX φ x y w v) r ≤ t := by
    intro r h1 h2
    have hs := StatFormal.Wave30tz.order_stat_shift n (fun i => F (x i)) (ownX φ x y w v) (1 / (n * ((1 - α) * D))) r
      (hr1.trans h1) h2 (fun i => by rw [hownX]; constructor <;> linarith [hcX i])
    rw [hX r h1 h2] at hs
    exact hs
  have hOY : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊(m : ℝ) * α⌋₊ + 1 →
      u ≤ ordStat (ownY φ x y w v) r ∧ ordStat (ownY φ x y w v) r ≤ u + 1 / (m * ((1 - α) * D)) := by
    intro r h1 h2
    have hs := StatFormal.Wave30tz.order_stat_shift m (ownY φ x y w v) (fun j => F (y j)) (1 / (m * ((1 - α) * D))) r
      h1 (h2.trans hs3) (fun j => by rw [hownY]; constructor <;> linarith [hcY j])
    rw [hY r h1 h2] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hqOX : ∀ q, IsEmpQuantile (ownX φ x y w v) (1 - α) q → t - 1 / (n * ((1 - α) * D)) ≤ q ∧ q ≤ t := by
    intro q hq
    obtain ⟨h1, h2⟩ := empQuantile_bracket _ hn hp0 (by linarith) hq
    exact ⟨(hOX _ le_rfl (hr2.trans hr3)).1.trans h1, h2.trans (hOX _ hr2 hr3).2⟩
  have hqOY : ∀ q, IsEmpQuantile (ownY φ x y w v) α q → u ≤ q ∧ q ≤ u + 1 / (m * ((1 - α) * D)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := empQuantile_bracket _ hm hα0 hα1 hq
    exact ⟨(hOY _ hs1 hs2).1.trans h1, h2.trans (hOY _ (by omega) le_rfl).2⟩
  exact ⟨hDpos, hDeq, hband', hosc, htu, hX, hY, hqX, hqY, hramp, hoscw, hnφh, hhalf, hrep, hlin, hmax, hOX, hOY,
    hqOX, hqOY⟩

end StatFormal.Wave31tu.RouteP
