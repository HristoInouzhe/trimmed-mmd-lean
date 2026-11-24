import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Mixtures with disjoint component supports have a constant density ratio where both densities are positive (library, untrusted)

Let `R, P₀, Q₀` be measures concentrated on measurable sets `SR, SP, SQ` (`R(SRᶜ) = P₀(SPᶜ) = Q₀(SQᶜ) = 0`), with `SR` disjoint from
`SP` and from `SQ`, and let `p, q ≥ 0` be densities (with respect to a σ-finite `μ`) of the mixtures `(1−b)R + bP₀` and
`(1−c)R + cQ₀`, `b, c ≤ 1`. Then (`mixture_densities`) `p = 0` a.e. off `SR ∪ SP`, `q = 0` a.e. off `SR ∪ SQ`, and
`(1−c)p = (1−b)q` a.e. on `SR`, since both mixtures restrict to multiples of `R` on `SR`. If moreover `SP` and `SQ` are disjoint,
`μ` charges open sets and `p, q` are continuous and positive on an open set `W`, then a.e. point of `W` lies in `SR`, and
(`mixture_ratio_eqOn`) `(1−c)p = (1−b)q` everywhere on `W`: the density ratio `p/q` is the constant `(1−b)/(1−c)` there.

General facts used: a density vanishes a.e. on a null set of its law (`ae_eq_zero_of_withDensity_eq_zero`), and laws with
densities that are proportional on a set have proportional densities a.e. there (`ae_mul_eq_of_withDensity`).

Used for the two-point pairs `((1−b)R + bP₀, (1−c)R + cQ₀)` of Proposition 5.8 of the trimmed-mmd paper: they do not cross as in
Proposition 5.5 (S4 :1383-1384).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.CrossExamples

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A nonnegative density vanishes a.e. on a measurable set that its law does not charge. -/
theorem ae_eq_zero_of_withDensity_eq_zero {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {S : Set α}
    (hS : MeasurableSet S) (h : μ.withDensity (fun x => ENNReal.ofReal (f x)) S = 0) : ∀ᵐ x ∂μ, x ∈ S → f x = 0 := by
  rw [withDensity_apply _ hS, setLIntegral_eq_zero_iff hS hf.ennreal_ofReal] at h
  filter_upwards [h] with x hx hxS
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 (hx hxS)) (hf0 x)

/-- **Proportional laws have proportional densities.** If `ofReal a · P(A ∩ S) = ofReal b · Q(A ∩ S)` for every measurable `S`,
where `P = f·μ`, `Q = g·μ` (`f, g ≥ 0` measurable, `μ` σ-finite) and `a, b ≥ 0`, then `a f = b g` a.e. on `A`. -/
theorem ae_mul_eq_of_withDensity [SigmaFinite μ] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {A : Set α} (hA : MeasurableSet A)
    (h : ∀ S, MeasurableSet S → ENNReal.ofReal a * μ.withDensity (fun x => ENNReal.ofReal (f x)) (A ∩ S) =
      ENNReal.ofReal b * μ.withDensity (fun x => ENNReal.ofReal (g x)) (A ∩ S)) :
    ∀ᵐ x ∂μ, x ∈ A → a * f x = b * g x := by
  have hF : Measurable (A.indicator fun x => ENNReal.ofReal (a * f x)) :=
    (measurable_const.mul hf).ennreal_ofReal.indicator hA
  have hG : Measurable (A.indicator fun x => ENNReal.ofReal (b * g x)) :=
    (measurable_const.mul hg).ennreal_ofReal.indicator hA
  have key : (A.indicator fun x => ENNReal.ofReal (a * f x)) =ᵐ[μ] (A.indicator fun x => ENNReal.ofReal (b * g x)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hF hG fun S hS _ => ?_
    rw [setLIntegral_indicator hA, setLIntegral_indicator hA]
    have e1 : ∫⁻ x in A ∩ S, ENNReal.ofReal (a * f x) ∂μ = ENNReal.ofReal a * ∫⁻ x in A ∩ S, ENNReal.ofReal (f x) ∂μ := by
      simp_rw [ENNReal.ofReal_mul ha]
      exact lintegral_const_mul _ hf.ennreal_ofReal
    have e2 : ∫⁻ x in A ∩ S, ENNReal.ofReal (b * g x) ∂μ = ENNReal.ofReal b * ∫⁻ x in A ∩ S, ENNReal.ofReal (g x) ∂μ := by
      simp_rw [ENNReal.ofReal_mul hb]
      exact lintegral_const_mul _ hg.ennreal_ofReal
    rw [e1, e2, ← withDensity_apply _ (hA.inter hS), ← withDensity_apply _ (hA.inter hS)]
    exact h S hS
  filter_upwards [key] with x hx hxA
  simp only [indicator_of_mem hxA] at hx
  exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg ha (hf0 x)) (mul_nonneg hb (hg0 x))).1 hx

/-- **Densities of mixtures with disjoint component supports.** For measures `R, P₀, Q₀` concentrated on measurable sets `SR, SP, SQ`
with `SR` disjoint from `SP` and `SQ`, and densities `p, q ≥ 0` (w.r.t. a σ-finite `μ`) of `(1−b)R + bP₀` and `(1−c)R + cQ₀`
(`b, c ≤ 1`): `p = 0` a.e. off `SR ∪ SP`, `q = 0` a.e. off `SR ∪ SQ`, and `(1−c)p = (1−b)q` a.e. on `SR`. -/
theorem mixture_densities [SigmaFinite μ] {R P₀ Q₀ : Measure α} {SR SP SQ : Set α} {b c : ℝ} {p q : α → ℝ}
    (hSR : MeasurableSet SR) (hSP : MeasurableSet SP) (hSQ : MeasurableSet SQ) (hRP : Disjoint SR SP) (hRQ : Disjoint SR SQ)
    (hR : R SRᶜ = 0) (hP : P₀ SPᶜ = 0) (hQ : Q₀ SQᶜ = 0) (hb1 : b ≤ 1) (hc1 : c ≤ 1)
    (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hPd : ENNReal.ofReal (1 - b) • R + ENNReal.ofReal b • P₀ = μ.withDensity (fun x => ENNReal.ofReal (p x)))
    (hQd : ENNReal.ofReal (1 - c) • R + ENNReal.ofReal c • Q₀ = μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    (∀ᵐ x ∂μ, x ∉ SR ∪ SP → p x = 0) ∧ (∀ᵐ x ∂μ, x ∉ SR ∪ SQ → q x = 0) ∧
      ∀ᵐ x ∂μ, x ∈ SR → (1 - c) * p x = (1 - b) * q x := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 : μ.withDensity (fun x => ENNReal.ofReal (p x)) (SR ∪ SP)ᶜ = 0 := by
      rw [← hPd, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        measure_mono_null (compl_subset_compl.2 subset_union_left) hR,
        measure_mono_null (compl_subset_compl.2 subset_union_right) hP]
      simp
    exact ae_eq_zero_of_withDensity_eq_zero hp hp0 (hSR.union hSP).compl h0
  · have h0 : μ.withDensity (fun x => ENNReal.ofReal (q x)) (SR ∪ SQ)ᶜ = 0 := by
      rw [← hQd, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        measure_mono_null (compl_subset_compl.2 subset_union_left) hR,
        measure_mono_null (compl_subset_compl.2 subset_union_right) hQ]
      simp
    exact ae_eq_zero_of_withDensity_eq_zero hq hq0 (hSR.union hSQ).compl h0
  · refine ae_mul_eq_of_withDensity hp hq hp0 hq0 (by linarith) (by linarith) hSR fun S _ => ?_
    have hP0 : P₀ (SR ∩ S) = 0 :=
      measure_mono_null (fun x hx => hRP.notMem_of_mem_left hx.1) hP
    have hQ0 : Q₀ (SR ∩ S) = 0 :=
      measure_mono_null (fun x hx => hRQ.notMem_of_mem_left hx.1) hQ
    rw [← hPd, ← hQd, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, hP0, hQ0]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring

/-- **A constant density ratio where both densities are positive.** In the setting of `mixture_densities`, with moreover `SP`, `SQ`
disjoint and `μ` positive on nonempty open sets: if `p, q` are continuous and positive on an open set `W`, then `(1−c)p = (1−b)q`
everywhere on `W`. -/
theorem mixture_ratio_eqOn [TopologicalSpace α] [OpensMeasurableSpace α] [SigmaFinite μ] [μ.IsOpenPosMeasure]
    {R P₀ Q₀ : Measure α} {SR SP SQ : Set α} {b c : ℝ} {p q : α → ℝ}
    (hSR : MeasurableSet SR) (hSP : MeasurableSet SP) (hSQ : MeasurableSet SQ) (hRP : Disjoint SR SP) (hRQ : Disjoint SR SQ)
    (hPQ : Disjoint SP SQ) (hR : R SRᶜ = 0) (hP : P₀ SPᶜ = 0) (hQ : Q₀ SQᶜ = 0) (hb1 : b ≤ 1) (hc1 : c ≤ 1)
    (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hPd : ENNReal.ofReal (1 - b) • R + ENNReal.ofReal b • P₀ = μ.withDensity (fun x => ENNReal.ofReal (p x)))
    (hQd : ENNReal.ofReal (1 - c) • R + ENNReal.ofReal c • Q₀ = μ.withDensity (fun x => ENNReal.ofReal (q x)))
    {W : Set α} (hW : IsOpen W) (hpc : ContinuousOn p W) (hqc : ContinuousOn q W) (hpW : ∀ x ∈ W, 0 < p x)
    (hqW : ∀ x ∈ W, 0 < q x) :
    EqOn (fun x => (1 - c) * p x) (fun x => (1 - b) * q x) W := by
  obtain ⟨h1, h2, h3⟩ :=
    mixture_densities (μ := μ) hSR hSP hSQ hRP hRQ hR hP hQ hb1 hc1 hp hq hp0 hq0 hPd hQd
  have hae : (fun x => (1 - c) * p x) =ᵐ[μ.restrict W] (fun x => (1 - b) * q x) := by
    refine (ae_restrict_iff' hW.measurableSet).2 ?_
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxW
    by_cases hxR : x ∈ SR
    · exact hx3 hxR
    · exfalso
      have hxP : x ∈ SP := by
        by_contra hxP
        exact (hpW x hxW).ne' (hx1 fun h => h.elim hxR hxP)
      have hxQ : x ∈ SQ := by
        by_contra hxQ
        exact (hqW x hxW).ne' (hx2 fun h => h.elim hxR hxQ)
      exact hPQ.notMem_of_mem_left hxP hxQ
  exact Measure.eqOn_open_of_ae_eq hae hW (continuousOn_const.mul hpc) (continuousOn_const.mul hqc)

end StatFormal.CrossExamples
