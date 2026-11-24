import StatFormal.Wave31tq.Statements
import StatFormal.Lib.TVMeasure.Basic

/-!
# Wave 31tq, route A: Q1 `tv_density` (untrusted proof file)

(a) On any measurable space, with `M = P + Q` and the frozen densities `densP, densQ` (real versions of `dP/dM`, `dQ/dM`):
`P = densP · M`, `Q = densQ · M` (`TVMeasure.eq_withDensity_add_left/right`), so `|P − Q| = |densP − densQ| · M`
(`TVMeasure.totalVariation_eq_withDensity_abs`, from Mathlib's Jordan decomposition `(P − Q, Q − P)` of `P − Q`), the frozen
`errFn` is `∫ |1_A − f| d|P − Q|` (`TVMeasure.integral_withDensity_ofReal`), `|P − Q|(𝒳) = 2α⋆` (`Lib/Distances/TV`),
`|P − Q| = (P − P ∧ Q) + (Q − P ∧ Q)` and `(P ∧ Q)(𝒳) = 1 − α⋆`.
(b) For Lebesgue densities the same library lemmas with `μ = volume`; `α⋆ = (P − P ∧ Q)(V) = ∫ (p − q)₊`; for `G` with `q ≤ p` a.e. on
`G` and `p ≤ q` a.e. off `G`, `|P − Q|(A ∖ G) = |P − Q|(G ∖ A) = 0` (each of `(P − Q)`, `(Q − P)` vanishes there, by one of the two
density representations), so `1_A = 1_G` `|P − Q|`-a.e.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace StatFormal.Wave31tq.RouteA

open StatFormal.TVMeasure StatFormal.Wave31to

section General

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem densP_measurable (P Q : Measure 𝒳) : Measurable (densP P Q) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem densQ_measurable (P Q : Measure 𝒳) : Measurable (densQ P Q) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem densP_nonneg (P Q : Measure 𝒳) (x : 𝒳) : 0 ≤ densP P Q x := ENNReal.toReal_nonneg

theorem densQ_nonneg (P Q : Measure 𝒳) (x : 𝒳) : 0 ≤ densQ P Q x := ENNReal.toReal_nonneg

theorem eq_densP (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    P = (P + Q).withDensity (fun x => ENNReal.ofReal (densP P Q x)) :=
  eq_withDensity_add_left P Q

theorem eq_densQ (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Q = (P + Q).withDensity (fun x => ENNReal.ofReal (densQ P Q x)) :=
  eq_withDensity_add_right P Q

theorem measurableSet_setA (P Q : Measure 𝒳) : MeasurableSet (setA P Q) :=
  measurableSet_lt (densQ_measurable P Q) (densP_measurable P Q)

/-- `|P − Q| = |p − q| · (P + Q)` with the frozen densities. -/
theorem absPQ_eq_dens (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    absPQ P Q = (P + Q).withDensity (fun x => ENNReal.ofReal |densP P Q x - densQ P Q x|) :=
  totalVariation_eq_withDensity_abs (densP_measurable P Q) (densQ_measurable P Q) (densP_nonneg P Q) (densQ_nonneg P Q)
    (eq_densP P Q) (eq_densQ P Q)

/-- The frozen `errFn` is `∫ |1_A − f| d|P − Q|`. -/
theorem errFn_eq_integral_absPQ (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] (f : 𝒳 → ℝ) :
    errFn P Q f = ∫ x, |(setA P Q).indicator (fun _ => (1 : ℝ)) x - f x| ∂(absPQ P Q) := by
  have h1 := densP_measurable P Q
  have h2 := densQ_measurable P Q
  rw [absPQ_eq_dens, integral_withDensity_ofReal (by fun_prop) (fun _ => abs_nonneg _)]
  rfl

/-- `|P − Q|(S) = (P − Q)(S) + (Q − P)(S)`. -/
theorem absPQ_apply (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] (S : Set 𝒳) :
    absPQ P Q S = (P - Q) S + (Q - P) S := by
  rw [absPQ, totalVariation_sub_eq, Measure.add_apply]

end General

/-- Q1 (b), the error functional for Lebesgue-type densities: if `P = p · μ`, `Q = q · μ`, `q ≤ p` a.e. on `G` and `p ≤ q`
a.e. off `G`, then `1_A = 1_G` `|P − Q|`-a.e. -/
theorem indicator_setA_ae_eq {𝒳 : Type*} [MeasurableSpace 𝒳] {μ P Q : Measure 𝒳} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {p q : 𝒳 → ℝ} (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (p x))) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (q x)))
    {G : Set 𝒳} (hG : MeasurableSet G) (hon : ∀ᵐ x ∂μ, x ∈ G → q x ≤ p x) (hoff : ∀ᵐ x ∂μ, x ∉ G → p x ≤ q x) :
    ∀ᵐ x ∂(absPQ P Q), (setA P Q).indicator (fun _ => (1 : ℝ)) x = G.indicator (fun _ => (1 : ℝ)) x := by
  have hA := measurableSet_setA P Q
  have h1 : absPQ P Q (setA P Q \ G) = 0 := by
    rw [absPQ_apply,
      sub_apply_eq_zero_of_ae_le hp hq hq0 hP hQ (hA.diff hG) (hoff.mono fun x hx hxS => hx hxS.2),
      sub_apply_eq_zero_of_ae_le (densQ_measurable P Q) (densP_measurable P Q) (densP_nonneg P Q) (eq_densQ P Q)
        (eq_densP P Q) (hA.diff hG) (Eventually.of_forall fun x hxS => le_of_lt hxS.1), add_zero]
  have h2 : absPQ P Q (G \ setA P Q) = 0 := by
    rw [absPQ_apply,
      sub_apply_eq_zero_of_ae_le hq hp hp0 hQ hP (hG.diff hA) (hon.mono fun x hx hxS => hx hxS.1),
      sub_apply_eq_zero_of_ae_le (densP_measurable P Q) (densQ_measurable P Q) (densQ_nonneg P Q) (eq_densP P Q)
        (eq_densQ P Q) (hG.diff hA) (Eventually.of_forall fun x hxS => not_lt.1 hxS.2), zero_add]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  simp only [mem_ofPred_eq] at hx
  by_cases hxA : x ∈ setA P Q <;> by_cases hxG : x ∈ G <;> simp_all

theorem tv_density_route : Claims.tv_density := by
  refine ⟨fun 𝒳 _ P Q _ _ => ?_, fun V _ _ _ _ _ P Q _ _ p q hp hq hp0 hq0 hP hQ => ?_⟩
  · exact ⟨absPQ_eq_dens P Q, fun f _ _ => errFn_eq_integral_absPQ P Q f, totalVariation_univ_eq P Q,
      totalVariation_eq_sub_inf P Q, inf_univ_eq P Q⟩
  · have hTV : absPQ P Q = volume.withDensity (fun x => ENNReal.ofReal |p x - q x|) :=
      totalVariation_eq_withDensity_abs hp hq hp0 hq0 hP hQ
    have hsub : P - P ⊓ Q = volume.withDensity (fun x => ENNReal.ofReal (max (p x - q x) 0)) := by
      rw [sub_inf_eq_sub_of_withDensity hp hq hp0 hq0 hP hQ, sub_eq_withDensity_ofReal hp hq hq0 hP hQ]
      congr 1
      ext x
      simp
    refine ⟨hTV, inf_eq_withDensity_min hp hq hP hQ, hsub, ?_, ?_⟩
    · have ht0 := Distances.tvDist_nonneg P Q
      have ht1 := Distances.tvDist_le_one (μ := P) (ν := Q)
      have : IsFiniteMeasure (P ⊓ Q) := isFiniteMeasure_of_le P inf_le_left
      have huniv : (P - P ⊓ Q) univ = ENNReal.ofReal (Distances.tvDist P Q) := by
        rw [Measure.sub_apply MeasurableSet.univ inf_le_left, measure_univ, inf_univ_eq, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1
        ring
      have hl : ∫⁻ x, ENNReal.ofReal (max (p x - q x) 0) = (P - P ⊓ Q) univ := by
        rw [hsub, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => max (p x - q x) 0)
        (Eventually.of_forall fun x => le_max_right _ _) (by fun_prop), hl, huniv, ENNReal.toReal_ofReal ht0]
    · intro G f hG hf _ hon hoff
      rw [errFn_eq_integral_absPQ P Q f,
        integral_congr_ae (g := fun x => |G.indicator (fun _ => (1 : ℝ)) x - f x|)
          ((indicator_setA_ae_eq hp hq hp0 hq0 hP hQ hG hon hoff).mono fun x hx => by
          simp only [hx]),
        hTV, integral_withDensity_ofReal (by fun_prop) (fun _ => abs_nonneg _)]

end StatFormal.Wave31tq.RouteA
