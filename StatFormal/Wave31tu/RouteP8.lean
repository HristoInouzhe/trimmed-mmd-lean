import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tq.Proofs
import StatFormal.Wave31tq.RouteM21
import StatFormal.Lib.MomentTrim.Construction

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y8 `condR_facts` (`eq:condR` around Theorem 5.11; §5 :324-325, abs :12-13, §1 :85-86, S4 :1071-1073)

Under the crossing hypotheses (`IsCross`, `p(x₀) > 0`):
(b) `eq:condR` for some `r⋆, c⋆` iff `|p − q| ≥ c(p + q)` a.e. off every neighbourhood of `x₀` ("`p/q` stays away from one");
(c) shrinking `r⋆` keeps `eq:condR` with the same `c⋆`; `p + q` is bounded near `x₀` after shrinking; off `[x₀ − r⋆, x₀ + r⋆]`,
`p + q ≤ |p − q|/(c⋆r⋆)`, so `P + Q` inherits the exponential tails of `|P − Q|`;
(d) `eq:condR` holds on no interval where `p = q` unless `p + q = 0` a.e. there.

Route: near `x₀`, `|p − q| ≥ (ℓ₀/2)|x − x₀|` (the derivative at the crossing) and `p + q ≤ B` (continuity on a compact interval)
give `c₀|x − x₀|(p + q) ≤ |p − q|` (`near_bound`, the route lemma (a) of the approved prose); the tails through
`absPQ = |p − q|·Leb` (31tq Q1 `tv_density`).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.Wave31tq

/-- Under `IsCross`, `p + q` is bounded on `[x₀ − r, x₀ + r]` for some `r ∈ (0, 1]`. -/
theorem cross_sum_bounded {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) :
    ∃ r > 0, ∃ B > 0, ∀ x, |x - x₀| ≤ r → p x + q x ≤ B := by
  obtain ⟨-, -, -, -, -, -, ⟨r, hr, hpc, hqc⟩, -⟩ := hc
  have hsub : Icc (x₀ - r / 2) (x₀ + r / 2) ⊆ Ioo (x₀ - r) (x₀ + r) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hpc.add hqc).mono hsub)
  refine ⟨r / 2, half_pos hr, max C 1, lt_max_of_lt_right one_pos, fun x hx => ?_⟩
  have hx' : x ∈ Icc (x₀ - r / 2) (x₀ + r / 2) := ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩
  have := hC x hx'
  rw [Real.norm_eq_abs] at this
  exact ((le_abs_self _).trans this).trans (le_max_left _ _)

/-- The route lemma (a): under `IsCross`, `c₀|x − x₀|(p x + q x) ≤ |p x − q x|` for `|x − x₀| < r₀`, some `r₀, c₀ > 0`. -/
theorem near_bound {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) :
    ∃ r₀ > 0, ∃ c₀ > 0, ∀ x, |x - x₀| < r₀ → c₀ * |x - x₀| * (p x + q x) ≤ |p x - q x| := by
  have hpq := RouteM.cross_zero hc
  obtain ⟨r, hr, B, hB, hbd⟩ := cross_sum_bounded hc
  obtain ⟨-, -, hp0, hq0, -, -, -, -, -, hd, hℓ⟩ := hc
  obtain ⟨δ, hδ, hder⟩ := StatFormal.MomentTrim.exists_deriv_bound hd (by simp [hpq]) (half_pos hℓ)
  refine ⟨min δ r, lt_min hδ hr, ℓ₀ / 2 / B, div_pos (half_pos hℓ) hB, fun x hx => ?_⟩
  have h1 := hder x (hx.trans_le (min_le_left _ _))
  have h2 := hbd x (hx.le.trans (min_le_right _ _))
  have hlow : ℓ₀ / 2 * |x - x₀| ≤ |p x - q x| := by
    have h3 : |ℓ₀ * (x - x₀)| ≤ |p x - q x - ℓ₀ * (x - x₀)| + |p x - q x| := by
      have := abs_sub (p x - q x) (p x - q x - ℓ₀ * (x - x₀))
      simp only [sub_sub_cancel] at this; linarith
    rw [abs_mul, abs_of_pos hℓ] at h3
    linarith
  have hs0 : 0 ≤ p x + q x := add_nonneg (hp0 x) (hq0 x)
  have ha : 0 ≤ |x - x₀| := abs_nonneg _
  calc ℓ₀ / 2 / B * |x - x₀| * (p x + q x) ≤ ℓ₀ / 2 / B * |x - x₀| * B :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (div_pos (half_pos hℓ) hB).le ha)
    _ = ℓ₀ / 2 * |x - x₀| := by field_simp
    _ ≤ _ := hlow

/-- Y8 `condR_facts`. -/
theorem condR_facts_route : Claims.condR_facts := by
  intro P Q _ _ p q x₀ ℓ₀ hc hpx
  have hc' := hc
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -⟩ := hc'
  have hs0 : ∀ x, 0 ≤ p x + q x := fun x => add_nonneg (hp0 x) (hq0 x)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- (b) ⇒
    rintro ⟨rs, cs, hrs, hrs1, hcs, hae⟩ r hr
    refine ⟨cs * min rs r, mul_pos hcs (lt_min hrs hr), hae.mono fun x hx hxr => ?_⟩
    have hm : min rs r ≤ min rs |x - x₀| := min_le_min le_rfl hxr
    calc cs * min rs r * (p x + q x) ≤ cs * min rs |x - x₀| * (p x + q x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hcs.le) (hs0 x)
      _ ≤ _ := hx
  · -- (b) ⇐
    intro H
    obtain ⟨r₀, hr₀, c₀, hc₀, hnear⟩ := near_bound hc
    obtain ⟨c₁, hc₁, hfar⟩ := H r₀ hr₀
    refine ⟨min r₀ 1, min c₀ c₁, lt_min hr₀ one_pos, min_le_right _ _, lt_min hc₀ hc₁, hfar.mono fun x hx => ?_⟩
    have hcs0 : 0 ≤ min c₀ c₁ := (lt_min hc₀ hc₁).le
    have hm0 : 0 ≤ min (min r₀ 1) |x - x₀| := le_min (lt_min hr₀ one_pos).le (abs_nonneg _)
    rcases lt_or_ge |x - x₀| r₀ with hlt | hge
    · calc min c₀ c₁ * min (min r₀ 1) |x - x₀| * (p x + q x) ≤ c₀ * |x - x₀| * (p x + q x) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 hc₀.le) (hs0 x)
        _ ≤ _ := hnear x hlt
    · have hm1 : min (min r₀ 1) |x - x₀| ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
      calc min c₀ c₁ * min (min r₀ 1) |x - x₀| * (p x + q x) ≤ c₁ * 1 * (p x + q x) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (min_le_right _ _) hm1 hm0 hc₁.le) (hs0 x)
        _ = c₁ * (p x + q x) := by ring
        _ ≤ _ := hx hge
  · intro rs cs hR
    obtain ⟨hrs, hrs1, hcs, hae⟩ := hR
    have hcsrs : 0 < cs * rs := mul_pos hcs hrs
    -- (c)(iii): off the interval
    have hoff : ∀ᵐ x ∂volume, rs ≤ |x - x₀| → p x + q x ≤ |p x - q x| / (cs * rs) := by
      filter_upwards [hae] with x hx hxr
      rw [min_eq_left hxr] at hx
      rw [le_div_iff₀ hcsrs]; linarith
    refine ⟨fun rs' hrs' => ⟨hrs'.1, hrs'.2.trans hrs1, hcs, hae.mono fun x hx => ?_⟩, ?_, hoff, ?_, ?_⟩
    · -- (c)(i)
      calc cs * min rs' |x - x₀| * (p x + q x) ≤ cs * min rs |x - x₀| * (p x + q x) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_min hrs'.2 le_rfl) hcs.le) (hs0 x)
        _ ≤ _ := hx
    · -- (c)(ii)
      obtain ⟨r, hr, B, -, hbd⟩ := cross_sum_bounded hc
      refine ⟨min rs r, ⟨lt_min hrs hr, min_le_left _ _⟩, B, fun z hz => hbd z ?_⟩
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2, min_le_right rs r]
    · -- (d)
      intro a b _ hab
      have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ x₀ := by
        rw [ae_iff]; simp [measure_singleton]
      filter_upwards [hab, hae, hne] with x hx1 hx2 hx3 hxI
      have hpq := hx1 hxI
      rw [hpq, sub_self, abs_zero] at hx2
      have hpos : 0 < cs * min rs |x - x₀| := mul_pos hcs (lt_min hrs (abs_pos.mpr (sub_ne_zero.mpr hx3)))
      have : q x + q x ≤ 0 := by
        by_contra h; push Not at h; nlinarith [mul_pos hpos h]
      rw [hpq]; linarith [hq0 x]
    · -- (e): the tails of `P + Q`
      intro C' hET
      obtain ⟨hC', hET⟩ := hET
      have habs : absPQ P Q = volume.withDensity (fun x => ENNReal.ofReal |p x - q x|) :=
        (StatFormal.Wave31tq.tv_density.2 ℝ P Q p q hpm hqm hp0 hq0 hP hQ).1
      have hsum : ∀ S : Set ℝ, MeasurableSet S → (P + Q) S = ∫⁻ x in S, ENNReal.ofReal (p x + q x) := by
        intro S hS
        rw [Measure.add_apply, hP, hQ, withDensity_apply _ hS, withDensity_apply _ hS, ← lintegral_add_left]
        · refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_add (hp0 x) (hq0 x)]
        · exact hpm.ennreal_ofReal
      have hmeasS : ∀ t : ℝ, MeasurableSet {x : ℝ | t < |x - x₀|} := fun t =>
        measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub measurable_const))
      have htail : ∀ t, rs ≤ t → (P + Q) {x | t < |x - x₀|} ≤ ENNReal.ofReal (C' * Real.exp (-t / C') / (cs * rs)) := by
        intro t ht
        rw [hsum _ (hmeasS t)]
        have hpt : ∀ᵐ x ∂(volume.restrict {x : ℝ | t < |x - x₀|}),
            ENNReal.ofReal (p x + q x) ≤ ENNReal.ofReal |p x - q x| * ENNReal.ofReal (cs * rs)⁻¹ := by
          rw [ae_restrict_iff' (hmeasS t)]
          filter_upwards [hoff] with x hx hxS
          rw [← ENNReal.ofReal_mul (abs_nonneg _), ← div_eq_mul_inv]
          exact ENNReal.ofReal_le_ofReal (hx (ht.trans hxS.le))
        calc ∫⁻ x in {x | t < |x - x₀|}, ENNReal.ofReal (p x + q x)
            ≤ ∫⁻ x in {x | t < |x - x₀|}, ENNReal.ofReal |p x - q x| * ENNReal.ofReal (cs * rs)⁻¹ := lintegral_mono_ae hpt
          _ = (∫⁻ x in {x | t < |x - x₀|}, ENNReal.ofReal |p x - q x|) * ENNReal.ofReal (cs * rs)⁻¹ :=
              lintegral_mul_const _ ((continuous_abs.measurable.comp (hpm.sub hqm)).ennreal_ofReal)
          _ = absPQ P Q {x | t < |x - x₀|} * ENNReal.ofReal (cs * rs)⁻¹ := by
              rw [habs, withDensity_apply _ (hmeasS t)]
          _ ≤ ENNReal.ofReal (C' * Real.exp (-t / C')) * ENNReal.ofReal (cs * rs)⁻¹ :=
              by gcongr; exact hET t (lt_of_lt_of_le hrs ht)
          _ = ENNReal.ofReal (C' * Real.exp (-t / C') / (cs * rs)) := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hC'.le (Real.exp_pos _).le), ← div_eq_mul_inv]
      refine ⟨htail, ?_⟩
      -- (f): a `SumTail` constant
      set C'' := max (max C' (C' / (cs * rs))) (2 * Real.exp (rs / C')) with hC''
      have hC''1 : C' ≤ C'' := (le_max_left _ _).trans (le_max_left _ _)
      have hC''2 : C' / (cs * rs) ≤ C'' := (le_max_right _ _).trans (le_max_left _ _)
      have hC''3 : 2 * Real.exp (rs / C') ≤ C'' := le_max_right _ _
      have hC''pos : 0 < C'' := lt_of_lt_of_le hC' hC''1
      refine ⟨C'', hC''pos, fun t ht => ?_⟩
      have hexp : Real.exp (-t / C') ≤ Real.exp (-t / C'') := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left ht.le hC' hC''1
      rcases le_or_gt rs t with hrt | hrt
      · refine (htail t hrt).trans (ENNReal.ofReal_le_ofReal ?_)
        calc C' * Real.exp (-t / C') / (cs * rs) = C' / (cs * rs) * Real.exp (-t / C') := by ring
          _ ≤ C'' * Real.exp (-t / C'') := mul_le_mul hC''2 hexp (Real.exp_pos _).le hC''pos.le
      · have htot : (P + Q) {x | t < |x - x₀|} ≤ 2 := by
          calc (P + Q) {x | t < |x - x₀|} ≤ (P + Q) univ := measure_mono (subset_univ _)
            _ = 2 := by rw [Measure.add_apply, measure_univ, measure_univ]; norm_num
        refine htot.trans ?_
        have h2 : (2 : ℝ) ≤ C'' * Real.exp (-t / C'') := by
          have he1 : Real.exp (-rs / C') ≤ Real.exp (-t / C'') := by
            refine (Real.exp_le_exp.mpr ?_).trans hexp
            rw [neg_div, neg_div, neg_le_neg_iff]
            exact div_le_div_of_nonneg_right hrt.le hC'.le
          calc (2 : ℝ) = 2 * Real.exp (rs / C') * Real.exp (-rs / C') := by
                rw [mul_assoc, ← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero, mul_one]
            _ ≤ C'' * Real.exp (-t / C'') := mul_le_mul hC''3 he1 (Real.exp_pos _).le hC''pos.le
        calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          _ ≤ _ := ENNReal.ofReal_le_ofReal h2

end StatFormal.Wave31tu.RouteP
