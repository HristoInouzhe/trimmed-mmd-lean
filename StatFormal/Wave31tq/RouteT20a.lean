import StatFormal.Wave31tq.RouteT18
import StatFormal.Lib.MomentTrim.Construction
import StatFormal.Lib.MomentTrim.OneSided
import StatFormal.Lib.MomentTrim.Signed
import StatFormal.Lib.FourierTaylor.MomentDecay

/-!
# Wave 31tq, route T (Q20, main part): the moment-cancelling trimmings as measures (untrusted)

From the density-level construction `MomentTrim.exists_moment_trimming` (Lib/MomentTrim/Construction) to the measures of
Proposition S4.15: `P′ = f_P dx ≤ P`, `Q′ = f_Q dx ≤ Q` of mass `1 − α⋆ + ε(w)` (with `∫ min(p, q) = 1 − α⋆` from Q1(b),
`Claims.tv_density`, a hypothesis), and `ν = P′ − Q′ = h₊dx − h₋dx` (`P′ + h₋dx = Q′ + h₊dx`), so that
`|ν| ≤ h₊dx + h₋dx` (minimality of the Jordan decomposition), `supp ν ⊆ [x₀ − Tw, x₀ + Tw]` and the moments through the
Jordan parts are those of `h₊ − h₋` (`MomentTrim.integral_jordan_sub'`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- A probability measure with Lebesgue density `p ≥ 0` has `p` integrable and `∫ p = 1`. -/
theorem density_integrable {P : Measure ℝ} [IsProbabilityMeasure P] {p : ℝ → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) : Integrable p ∧ ∫ x, p x = 1 := by
  have hl : ∫⁻ x, ENNReal.ofReal (p x) = 1 := by
    have h := measure_univ (μ := P)
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  refine ⟨⟨hpm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hp0), hl]; exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hp0) hpm.aestronglyMeasurable, hl, ENNReal.toReal_one]

/-- `∫ min(p, q) = 1 − α⋆` (from Q1(b): `α⋆ = ∫ (p − q)₊`). -/
theorem integral_min_eq (h1 : Claims.tv_density) {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = volume.withDensity (fun x => ENNReal.ofReal (q x))) :
    ∫ x, min (p x) (q x) = 1 - StatFormal.Distances.tvDist P Q := by
  obtain ⟨hpi, hp1⟩ := density_integrable hpm hp0 hP
  obtain ⟨hqi, _⟩ := density_integrable hqm hq0 hQ
  have htv : StatFormal.Distances.tvDist P Q = ∫ x, max (p x - q x) 0 :=
    (h1.2 ℝ P Q p q hpm hqm hp0 hq0 hP hQ).2.2.2.1
  have hpos : Integrable (fun x => max (p x - q x) 0) := (hpi.sub hqi).pos_part
  have e : ∀ x, min (p x) (q x) = p x - max (p x - q x) 0 := fun x => by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  simp_rw [e]
  rw [integral_sub hpi hpos, hp1, htv]

/-- `volume.withDensity (ofReal ∘ f)` for an integrable `f ≥ 0` has total mass `ofReal (∫ f)`. -/
theorem withDensity_univ_ofReal {f : ℝ → ℝ} (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) univ = ENNReal.ofReal (∫ x, f x) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)]

/-- The integrals of `(x − x₀)^j` against `h dx` for `h ≥ 0` measurable. -/
theorem integral_pow_withDensity {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (x₀ : ℝ) (j : ℕ) :
    ∫ x, (x - x₀) ^ j ∂(volume.withDensity (fun x => ENNReal.ofReal (h x))) = ∫ x, (x - x₀) ^ j * h x := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (h x)) hm.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (h0 x), smul_eq_mul, mul_comm]

/-- `h dx` vanishes off `[a, b]` when `h` does. -/
theorem withDensity_compl_eq_zero {h : ℝ → ℝ} {a b : ℝ} (hs : ∀ x, x ∉ Icc a b → h x = 0) :
    volume.withDensity (fun x => ENNReal.ofReal (h x)) (Icc a b)ᶜ = 0 := by
  rw [withDensity_apply _ measurableSet_Icc.compl, setLIntegral_congr_fun measurableSet_Icc.compl
    (g := fun _ => 0) (fun x hx => by simp only [hs x hx, ENNReal.ofReal_zero]), lintegral_zero]

/-- **A trimming pair as measures.** `P′ = f_P dx ≤ P`, `Q′ = f_Q dx ≤ Q` of mass `1 − α⋆ + e`, and `ν = P′ − Q′` has
`|ν| ≤ M`, support in `[x₀ − W, x₀ + W]` and vanishing moments of order `< N` through its Jordan parts. -/
theorem pair_measures (h1 : Claims.tv_density) {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ W M : ℝ} {N : ℕ} (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    {fP fQ hp hm : ℝ → ℝ} {e : ℝ} (ht : IsTrimmingPair p q x₀ W M N fP fQ hp hm e) :
    ∃ (P' Q' : FiniteMeasure ℝ), (P' : Measure ℝ) ≤ P ∧ (Q' : Measure ℝ) ≤ Q ∧
      (P' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
      (Q' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
      ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation univ ≤ ENNReal.ofReal M ∧
      ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation (Icc (x₀ - W) (x₀ + W))ᶜ = 0 ∧
      ∀ j < N, sMoment ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure) x₀ j = 0 := by
  obtain ⟨hpi, _⟩ := density_integrable hpm hp0 hP
  obtain ⟨hqi, _⟩ := density_integrable hqm hq0 hQ
  have hmin := integral_min_eq h1 hpm hqm hp0 hq0 hP hQ
  have hfPi : Integrable fP := hpi.mono' ht.meas_fP.aestronglyMeasurable (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.fP_nonneg x)]; exact ht.fP_le x)
  have hfQi : Integrable fQ := hqi.mono' ht.meas_fQ.aestronglyMeasurable (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.fQ_nonneg x)]; exact ht.fQ_le x)
  have iP : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (fP x))) := isFiniteMeasure_withDensity_ofReal hfPi.2
  have iQ : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (fQ x))) := isFiniteMeasure_withDensity_ofReal hfQi.2
  have iHp : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (hp x))) := isFiniteMeasure_withDensity_ofReal ht.int_hp.2
  have iHm : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (hm x))) := isFiniteMeasure_withDensity_ofReal ht.int_hm.2
  set μP := volume.withDensity (fun x => ENNReal.ofReal (fP x)) with hμP
  set μQ := volume.withDensity (fun x => ENNReal.ofReal (fQ x)) with hμQ
  set Hp := volume.withDensity (fun x => ENNReal.ofReal (hp x)) with hHp
  set Hm := volume.withDensity (fun x => ENNReal.ofReal (hm x)) with hHm
  refine ⟨⟨μP, iP⟩, ⟨μQ, iQ⟩, ?_⟩
  change μP ≤ P ∧ μQ ≤ Q ∧ μP univ = _ ∧ μQ univ = _ ∧
    (μP.toSignedMeasure - μQ.toSignedMeasure).totalVariation univ ≤ _ ∧
    (μP.toSignedMeasure - μQ.toSignedMeasure).totalVariation _ = 0 ∧
    ∀ j < N, sMoment (μP.toSignedMeasure - μQ.toSignedMeasure) x₀ j = 0
  -- the signed measure through the parts `h₊, h₋`
  have hadd : μP + Hm = Hp + μQ := by
    rw [hμP, hHm, hHp, hμQ, ← withDensity_add_left ht.meas_fP.ennreal_ofReal,
      ← withDensity_add_left ht.meas_hp.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (ht.fP_nonneg x) (ht.hm_nonneg x), ← ENNReal.ofReal_add (ht.hp_nonneg x) (ht.fQ_nonneg x),
      ht.add_eq x, add_comm]
  have hν : μP.toSignedMeasure - μQ.toSignedMeasure = Hp.toSignedMeasure - Hm.toSignedMeasure :=
    toSignedMeasure_sub_eq_of_add_eq μP μQ Hp Hm hadd
  have hHpc := withDensity_compl_eq_zero (fun x hx => (ht.support x hx).1)
  have hHmc := withDensity_compl_eq_zero (fun x hx => (ht.support x hx).2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hμP, hP]
    exact withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (ht.fP_le x))
  · rw [hμQ, hQ]
    exact withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (ht.fQ_le x))
  · rw [hμP, withDensity_univ_ofReal hfPi ht.fP_nonneg, ht.mass_fP, hmin]
  · rw [hμQ, withDensity_univ_ofReal hfQi ht.fQ_nonneg, ht.mass_fQ, hmin]
  · rw [hν]
    refine (Measure.le_iff'.mp (totalVariation_le_of_eq_sub _ Hp Hm rfl) univ).trans ?_
    rw [Measure.add_apply, hHp, hHm, withDensity_univ_ofReal ht.int_hp ht.hp_nonneg,
      withDensity_univ_ofReal ht.int_hm ht.hm_nonneg, ← ENNReal.ofReal_add (integral_nonneg ht.hp_nonneg)
        (integral_nonneg ht.hm_nonneg)]
    exact ENNReal.ofReal_le_ofReal ht.mass_h
  · rw [hν]
    refine le_antisymm ?_ bot_le
    refine (Measure.le_iff'.mp (totalVariation_le_of_eq_sub _ Hp Hm rfl) _).trans ?_
    rw [Measure.add_apply, hHpc, hHmc, add_zero]
  · intro j hj
    unfold sMoment
    rw [integral_jordan_sub' _ Hp Hm hν (FourierTaylor.integrable_pow_sub hHpc j) (FourierTaylor.integrable_pow_sub hHmc j),
      hHp, hHm, integral_pow_withDensity ht.meas_hp ht.hp_nonneg, integral_pow_withDensity ht.meas_hm ht.hm_nonneg,
      ht.moments j hj, sub_self]

/-- **The main part of Proposition S4.15 at a fixed scale, as measures.** -/
theorem trimming_measures (h1 : Claims.tv_density) {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ T w : ℝ} {N : ℕ} (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    {fP fQ hp hm : ℝ → ℝ} {e : ℝ} (ht : IsMomentTrimming p q x₀ ℓ₀ N T w fP fQ hp hm e) :
    ∃ (P' Q' : FiniteMeasure ℝ), (P' : Measure ℝ) ≤ P ∧ (Q' : Measure ℝ) ≤ Q ∧
      ℓ₀ * w ^ 2 / 8 ≤ e ∧ (P' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
      (Q' : Measure ℝ) univ = ENNReal.ofReal (1 - StatFormal.Distances.tvDist P Q + e) ∧
      ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal (2 * ℓ₀ * w ^ 2) ∧
      ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure).totalVariation
        (Icc (x₀ - T * w) (x₀ + T * w))ᶜ = 0 ∧
      ∀ j < N, sMoment ((P' : Measure ℝ).toSignedMeasure - (Q' : Measure ℝ).toSignedMeasure) x₀ j = 0 := by
  obtain ⟨P', Q', h1', h2', h3', h4', h5', h6', h7'⟩ := pair_measures h1 hpm hqm hp0 hq0 hP hQ ht.toPair
  exact ⟨P', Q', h1', h2', ht.e_ge, h3', h4', h5', h6', h7'⟩

end StatFormal.Wave31tq.RouteT
