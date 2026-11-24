import StatFormal.Wave31tu.RouteP10Setup
import StatFormal.Wave31tu.RouteP9
import StatFormal.Wave31tu.RouteP7
import StatFormal.Wave31tr.Proofs
import StatFormal.Wave30tz.Proofs

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y11 `lap_pop` (the population ramp and `eq:lappop`, S4 :1134-1143; the order of `g⋆`, S4 :1342-1344)

At `α = α⋆ − ε ∈ (0, α⋆)`, with nearest points `a, b` of the regions, `f⋆ = (a − b)/‖a − b‖`, `t⋆` the least `(1−α)`-quantile and
`u⋆` the greatest `α`-quantile of `⟪f⋆, φ ·⟫`, `g⋆ = t⋆ − u⋆` and `φ⋆ = f⋆/g⋆`: `D_α > 0`, `g⋆ > 0`, `osc(φ⋆) ≤ 1`,
`‖φ⋆‖ = 1/g⋆` (the least representer norm), `L(φ⋆) − α = E_Pψ⋆ − E_Qψ⋆ − α = V(ε)/g⋆ ≤ ε`, `g⋆ ≥ V(ε)/ε`, `err(φ⋆) ≤ ε`,
`g⋆ ≤ osc(f⋆) ≤ 2`; under the two-sided bound, `‖φ⋆‖ ≤ c_V^{−1}ε^{−1/4}`, `g⋆ ≥ c_Vε^{1/4}` and `g⋆ ≤ c₂(2ε)^{5/4}/ε` (`2ε ≤ ε₀`).

Route (printed): 31tr T42 `excess_laplace` (G) (self-clipping and the equality), `pop_ramp_rkhs` (`g⋆ ≥ D_α > 0`, `D_α > 0` by
`eq:zeroeq` with the characteristic Laplace kernel), `L(ψ) ≤ α⋆` for `[0,1]`-valued `ψ` (`newapprox_err`), T40 (i-2)
`excess_i` (G) at `α′ = α⋆ − 2ε`, Y7 (`RouteP7.lap_const_route`) for `V(ε) ≥ c_Vε^{5/4}`, and the least representer norm
(Bochner integrals of the features lie in the closed span: `RouteP9.inner_region`).
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Concentration
  StatFormal.Wave30tz StatFormal.Wave30tq

/-- An element of a region is orthogonal to everything orthogonal to the features. -/
theorem region_orth {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) {P : Measure 𝒳} [IsProbabilityMeasure P]
    {α : ℝ} {a : H} (ha : a ∈ region φ α P) {d : H} (hd : ∀ z, ⟪d, φ z⟫_ℝ = 0) : ⟪d, a⟫_ℝ = 0 := by
  obtain ⟨g, hgm, hgb, -, rfl⟩ := ha
  rw [inner_region P hφ hκ hgm hgb d]
  simp [hd]

/-- Y11 `lap_pop`. -/
theorem lap_pop_route : Claims.lap_pop := by
  intro H _ _ _ _ σ φ P Q _ _ ε a b t u hσ hφ hε hεtv htv1 ha hb hab ht hu
  intro α f φs
  obtain ⟨hsm, hnorm, hchar⟩ := laplace_feature_facts hσ hφ
  have hκ : ∀ z, ‖φ z‖ ≤ 1 := fun z => (hnorm z).le
  have hα0 : 0 < α := by show 0 < tvDist P Q - ε; linarith
  have hα1 : α < 1 := by show tvDist P Q - ε < 1; linarith
  have hαtv : α < tvDist P Q := by show tvDist P Q - ε < tvDist P Q; linarith
  -- `D_α > 0`
  have hDpos : 0 < Dpop φ P Q α := by
    have hz := StatFormal.TrimmedMMD.ZeroSet.zeroeq ℝ H P Q φ 1 α hsm hκ hchar hα0.le hα1
    have h0 : 0 ≤ Dpop φ P Q α := Real.sInf_nonneg fun _ ⟨_, _, _, _, hr⟩ => hr ▸ norm_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (hz.1 h.symm) (not_le.mpr hαtv)
  have hDφ : ∀ z z' : ℝ, ‖φ z - φ z'‖ ≤ 2 := fun z z' =>
    (norm_sub_le _ _).trans (by rw [hnorm, hnorm]; norm_num)
  have hgap := (StatFormal.Wave30tz.pop_ramp_rkhs ℝ H P Q φ 1 2 α a b t u hsm hκ hDφ hα0.le hα1 ha hb hab hDpos ht hu).1
  have htu : 0 < t - u := lt_of_lt_of_le hDpos hgap
  obtain ⟨hband, hid, -, -⟩ := StatFormal.Wave31tr.excess_laplace.1 H σ φ P Q α a b t u hσ hsm hφ hα0.le hα1 hDpos
    ha hb hab ht.1 hu.1 (by linarith)
  have hband' : ∀ z, u ≤ Wave31to.wit φ f z ∧ Wave31to.wit φ f z ≤ t := hband
  have hfn : ‖f‖ = 1 := by
    show ‖‖a - b‖⁻¹ • (a - b)‖ = 1
    rw [norm_smul, norm_inv, norm_norm, hab, inv_mul_cancel₀ hDpos.ne']
  have hinv : 0 < (t - u)⁻¹ := inv_pos.mpr htu
  have hwit : ∀ z, Wave31to.wit φ φs z = (t - u)⁻¹ * Wave31to.wit φ f z := fun z => by
    show ⟪(t - u)⁻¹ • f, φ z⟫_ℝ = _
    rw [real_inner_smul_left]; rfl
  -- `osc(φ⋆) ≤ 1`
  have hoscs : Wave31to.oscFn (Wave31to.wit φ φs) ≤ 1 := by
    unfold Wave31to.oscFn
    have h1 : (⨆ z, Wave31to.wit φ φs z) ≤ (t - u)⁻¹ * t :=
      ciSup_le fun z => by rw [hwit]; exact mul_le_mul_of_nonneg_left (hband' z).2 hinv.le
    have h2 : (t - u)⁻¹ * u ≤ ⨅ z, Wave31to.wit φ φs z :=
      le_ciInf fun z => by rw [hwit]; exact mul_le_mul_of_nonneg_left (hband' z).1 hinv.le
    have h3 : (t - u)⁻¹ * t - (t - u)⁻¹ * u = 1 := by rw [← mul_sub, inv_mul_cancel₀ htu.ne']
    linarith
  have hns : ‖φs‖ = 1 / (t - u) := by
    show ‖(t - u)⁻¹ • f‖ = _
    rw [norm_smul, hfn, Real.norm_eq_abs, abs_of_pos hinv, mul_one, one_div]
  -- the least representer norm
  have hrep : ∀ g' : H, (∀ z, ⟪g', φ z⟫_ℝ = Wave31to.wit φ φs z) → ‖φs‖ ≤ ‖g'‖ := by
    intro g' hg'
    refine norm_le_of_rep (fun d hd => ?_) hg'
    show ⟪(t - u)⁻¹ • (‖a - b‖⁻¹ • (a - b)), d⟫_ℝ = 0
    rw [real_inner_comm, inner_smul_right, inner_smul_right, inner_sub_right, region_orth hsm hκ ha hd,
      region_orth hsm hκ hb hd]
    ring
  -- the ramp and the integrals
  have hramp : ∀ z, ramp (Wave31to.wit φ f) t u z = Wave31to.wit φ φs z - u / (t - u) := fun z => by
    simp only [ramp, clip]
    rw [max_eq_left (hband' z).1, min_eq_left (hband' z).2, hwit]
    field_simp
  have hwm : Measurable (Wave31to.wit φ φs) :=
    ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).measurable
  have hwb : ∀ z, |Wave31to.wit φ φs z| ≤ ‖φs‖ := fun z =>
    (abs_real_inner_le_norm φs (φ z)).trans (by rw [hnorm, mul_one])
  have hint : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      ∫ z, ramp (Wave31to.wit φ f) t u z ∂μ = (∫ z, Wave31to.wit φ φs z ∂μ) - u / (t - u) := fun μ _ => by
    simp_rw [hramp]
    rw [integral_sub (Integrable.of_bound hwm.aestronglyMeasurable ‖φs‖ (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hwb z)) (integrable_const _), integral_const]
    simp
  have hlin : linL P Q (Wave31to.wit φ φs) - α =
      (∫ z, ramp (Wave31to.wit φ f) t u z ∂P) - (∫ z, ramp (Wave31to.wit φ f) t u z ∂Q) - α := by
    rw [hint P inferInstance, hint Q inferInstance]; unfold linL; ring
  have hid' : (∫ z, ramp (Wave31to.wit φ f) t u z ∂P) - (∫ z, ramp (Wave31to.wit φ f) t u z ∂Q) - α =
      Wave31ti.uPath φ P Q α / (t - u) := hid
  -- `L(ψ⋆) ≤ α⋆`
  have hrm : Measurable (ramp (Wave31to.wit φ f) t u) := by
    have : Measurable (Wave31to.wit φ f) := ((continuous_const.inner continuous_id).comp_stronglyMeasurable hsm).measurable
    unfold ramp clip
    exact ((this.max measurable_const).min measurable_const).sub_const _ |>.div_const _
  have hr01 : ∀ z, 0 ≤ ramp (Wave31to.wit φ f) t u z ∧ ramp (Wave31to.wit φ f) t u z ≤ 1 := fun z => by
    simp only [ramp, clip]
    rw [max_eq_left (hband' z).1, min_eq_left (hband' z).2]
    exact ⟨div_nonneg (by linarith [(hband' z).1]) htu.le, (div_le_one htu).mpr (by linarith [(hband' z).2])⟩
  have hLle : (∫ z, ramp (Wave31to.wit φ f) t u z ∂P) - (∫ z, ramp (Wave31to.wit φ f) t u z ∂Q) ≤ tvDist P Q := by
    have h := integral_sub_le_mul_tvDist_of_nonneg (μ := P) (ν := Q) hrm zero_le_one (fun z => (hr01 z).1)
      (fun z => (hr01 z).2)
    linarith
  have hαdef : α = tvDist P Q - ε := rfl
  have hVle : Wave31ti.uPath φ P Q α / (t - u) ≤ ε := by rw [← hid']; linarith
  have hVnn : 0 ≤ Wave31ti.uPath φ P Q α := mul_nonneg (by linarith) hDpos.le
  have hVε : Wave31ti.uPath φ P Q α / ε ≤ t - u := by
    rw [div_le_iff₀ hε]; rw [div_le_iff₀ htu] at hVle; linarith
  have herr : errL P Q (Wave31to.wit φ φs) ≤ ε := by
    unfold errL
    have h1 := hlin.trans hid'
    have h2 : 0 ≤ Wave31ti.uPath φ P Q α / (t - u) := div_nonneg hVnn htu.le
    linarith
  -- `g⋆ ≤ osc(f⋆) ≤ 2`
  have hwfb : ∀ z, |Wave31to.wit φ f z| ≤ 1 := fun z =>
    (abs_real_inner_le_norm f (φ z)).trans (by rw [hnorm, hfn, mul_one])
  have hbdA : BddAbove (range (Wave31to.wit φ f)) := ⟨1, by rintro _ ⟨z, rfl⟩; exact (abs_le.mp (hwfb z)).2⟩
  have hbdB : BddBelow (range (Wave31to.wit φ f)) := ⟨-1, by rintro _ ⟨z, rfl⟩; exact (abs_le.mp (hwfb z)).1⟩
  have hsup : t ≤ ⨆ z, Wave31to.wit φ f z := by
    by_contra hlt
    push Not at hlt
    have hall : {z | Wave31to.wit φ f z < t} = univ := by
      ext z; simp only [mem_setOf_eq, mem_univ, iff_true]; exact (le_ciSup hbdA z).trans_lt hlt
    have := ht.1.1
    rw [show (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) = Wave31to.wit φ f from rfl, hall, probReal_univ] at this
    linarith
  have hinf : (⨅ z, Wave31to.wit φ f z) ≤ u := by
    by_contra hlt
    push Not at hlt
    have hnone : {z | Wave31to.wit φ f z ≤ u} = ∅ := by
      ext z; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]; exact hlt.trans_le (ciInf_le hbdB z)
    have := hu.1.2
    rw [show (fun x => ⟪‖a - b‖⁻¹ • (a - b), φ x⟫_ℝ) = Wave31to.wit φ f from rfl, hnone, measureReal_empty] at this
    linarith
  have hosc1 : t - u ≤ Wave31to.oscFn (Wave31to.wit φ f) := by unfold Wave31to.oscFn; linarith
  have hosc2 : Wave31to.oscFn (Wave31to.wit φ f) ≤ 2 := by
    unfold Wave31to.oscFn
    have h1 : (⨆ z, Wave31to.wit φ f z) ≤ 1 := ciSup_le fun z => (abs_le.mp (hwfb z)).2
    have h2 : -1 ≤ ⨅ z, Wave31to.wit φ f z := le_ciInf fun z => (abs_le.mp (hwfb z)).1
    linarith
  refine ⟨hDpos, htu, hoscs, hns, hrep, hlin, hid', hVle, hVε, herr, hosc1, hosc2, ?_⟩
  -- the order of `g⋆` under the two-sided bound
  intro c₁ c₂ ε₀ hTS
  have hconst := lap_const_route H φ 1 P Q c₁ c₂ ε₀ hsm hκ htv1 hTS
  obtain ⟨-, -, -, -, hcV, -, hsand, hcVe, -⟩ := hconst
  have hcVε : cV (tvDist P Q) c₁ ε₀ * ε ^ (5 / 4 : ℝ) ≤ Wave31ti.uPath φ P Q α := hcVe ε ⟨hε, hεtv.le⟩
  have h54 : ε ^ (5 / 4 : ℝ) = ε ^ (1 / 4 : ℝ) * ε := by
    rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add hε, Real.rpow_one]
  have hlow : cV (tvDist P Q) c₁ ε₀ * ε ^ (1 / 4 : ℝ) ≤ t - u := by
    refine le_trans ?_ hVε
    rw [le_div_iff₀ hε]
    calc cV (tvDist P Q) c₁ ε₀ * ε ^ (1 / 4 : ℝ) * ε = cV (tvDist P Q) c₁ ε₀ * ε ^ (5 / 4 : ℝ) := by rw [h54]; ring
      _ ≤ _ := hcVε
  have hq0 : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
  refine ⟨?_, hlow, fun h2ε => ?_⟩
  · rw [hns, Real.rpow_neg hε.le, one_div, ← mul_inv]
    exact inv_anti₀ (mul_pos hcV hq0) hlow
  · -- the supporting line at `α` (T40 (i-2)) evaluated at `α′ = α⋆ − 2ε`
    obtain ⟨-, -, -, hε₀α, hTwo⟩ := hTS
    have hline := (StatFormal.Wave31tr.excess_i.1 ℝ H P Q φ 1 α a b t u hsm hκ hα0.le hα1 hDpos ha hb hab ht.1 hu.1).2
      (tvDist P Q - 2 * ε) ⟨by linarith, by linarith⟩
    have h2e : 2 * ε ∈ Ioc (0 : ℝ) ε₀ := ⟨by linarith, h2ε⟩
    have hD2 := (hTwo (2 * ε) h2e).2
    have hs2 := (hsand (2 * ε) ⟨h2e.1.le, h2e.2.trans hε₀α⟩).2
    have hαe : tvDist P Q - 2 * ε - α = -ε := by rw [hαdef]; ring
    rw [hαe] at hline
    have hpath : (1 - (tvDist P Q - 2 * ε)) * Dpop φ P Q (tvDist P Q - 2 * ε) = Wave31ti.uPath φ P Q (tvDist P Q - 2 * ε) :=
      rfl
    have hpathα : (1 - α) * Dpop φ P Q α = Wave31ti.uPath φ P Q α := rfl
    rw [hpath, hpathα] at hline
    rw [le_div_iff₀ hε]
    nlinarith
end StatFormal.Wave31tu.RouteP
