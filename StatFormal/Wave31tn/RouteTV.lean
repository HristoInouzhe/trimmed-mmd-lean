import StatFormal.Wave31tn.Statements
import StatFormal.Wave31tb.RouteSeparated

/-!
# Wave 31tn route: the mixtures `mixAt R P₀ t` and their total variation (untrusted proof material)

* `mixAt_isProb`, `mixAt_real`, `mixAt_apply`: the mixture is a probability measure, `(1−t)R(A) + tP₀(A)`.
* `tv_mixAt`: with `R, P₀, Q₀` on pairwise disjoint measurable sets and `s, t ∈ [0,1]`,
  `TV((1−s)R + sP₀, (1−t)R + tQ₀) = max s t` (the difference on `A` is `(t−s)R(A) + sP₀(A) − tQ₀(A)`; `S_P` attains `s`, `S_Q`
  attains `−t`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tn

namespace RouteTV

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma mixAt_isProb (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsProbabilityMeasure (mixAt R P₀ t) :=
  StatFormal.Wave31tb.mix_isProb R P₀ h0 h1

lemma mixAt_real (R P₀ : Measure 𝒳) [IsFiniteMeasure R] [IsFiniteMeasure P₀] {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (A : Set 𝒳) :
    (mixAt R P₀ t).real A = (1 - t) * R.real A + t * P₀.real A :=
  StatFormal.Wave31tb.mix_real R P₀ h0 h1 A

lemma mixAt_apply (R P₀ : Measure 𝒳) (t : ℝ) (A : Set 𝒳) :
    mixAt R P₀ t A = ENNReal.ofReal (1 - t) * R A + ENNReal.ofReal t * P₀ A := by
  simp [mixAt, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

lemma real_le_one (μ : Measure 𝒳) [IsProbabilityMeasure μ] (A : Set 𝒳) : μ.real A ≤ 1 :=
  (measureReal_mono (subset_univ A)).trans_eq probReal_univ

lemma real_one_of_compl {μ : Measure 𝒳} [IsProbabilityMeasure μ] {S : Set 𝒳} (hS : MeasurableSet S)
    (h : μ Sᶜ = 0) : μ.real S = 1 := by
  rw [measureReal_def, (prob_compl_eq_zero_iff hS).1 h, ENNReal.toReal_one]

lemma real_zero_of_sub {μ : Measure 𝒳} {S T : Set 𝒳} (hST : S ⊆ Tᶜ) (h : μ Tᶜ = 0) : μ.real S = 0 := by
  rw [measureReal_def, measure_mono_null hST h, ENNReal.toReal_zero]

/-- `TV((1−s)R + sP₀, (1−t)R + tQ₀) = max s t`. -/
lemma tv_mixAt (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q₀]
    {SR SP SQ : Set 𝒳} (hSP : MeasurableSet SP) (hSQ : MeasurableSet SQ)
    (hRP : Disjoint SR SP) (hRQ : Disjoint SR SQ) (hPQ : Disjoint SP SQ)
    (hR : R SRᶜ = 0) (hP₀ : P₀ SPᶜ = 0) (hQ₀ : Q₀ SQᶜ = 0)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    StatFormal.Distances.tvDist (mixAt R P₀ s) (mixAt R Q₀ t) = max s t := by
  have := mixAt_isProb R P₀ hs0 hs1
  have := mixAt_isProb R Q₀ ht0 ht1
  apply le_antisymm
  · refine StatFormal.Distances.tvDist_le_of_forall fun A _ => ?_
    rw [mixAt_real R P₀ hs0 hs1, mixAt_real R Q₀ ht0 ht1]
    have hR1 := real_le_one R A
    have hP1 := real_le_one P₀ A
    have hQ1 := real_le_one Q₀ A
    have hR0 : 0 ≤ R.real A := measureReal_nonneg
    have hP0 : 0 ≤ P₀.real A := measureReal_nonneg
    have hQ0 : 0 ≤ Q₀.real A := measureReal_nonneg
    have hms := le_max_left s t
    have hmt := le_max_right s t
    rw [abs_le]
    constructor
    · rcases le_total s t with h | h <;> nlinarith
    · rcases le_total s t with h | h <;> nlinarith
  · rcases le_total t s with h | h
    · rw [max_eq_left h]
      have hA := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := mixAt R P₀ s) (ν := mixAt R Q₀ t) hSP
      rw [mixAt_real R P₀ hs0 hs1, mixAt_real R Q₀ ht0 ht1, real_one_of_compl hSP hP₀,
        real_zero_of_sub hRP.symm.subset_compl_right hR, real_zero_of_sub hPQ.subset_compl_right hQ₀] at hA
      have : (1 - s) * 0 + s * 1 - ((1 - t) * 0 + t * 0) = s := by ring
      rwa [this, abs_of_nonneg hs0] at hA
    · rw [max_eq_right h]
      have hA := StatFormal.Distances.abs_measureReal_sub_le_tvDist (μ := mixAt R P₀ s) (ν := mixAt R Q₀ t) hSQ
      rw [mixAt_real R P₀ hs0 hs1, mixAt_real R Q₀ ht0 ht1, real_one_of_compl hSQ hQ₀,
        real_zero_of_sub hRQ.symm.subset_compl_right hR, real_zero_of_sub hPQ.symm.subset_compl_right hP₀] at hA
      have : (1 - s) * 0 + s * 0 - ((1 - t) * 0 + t * 1) = -t := by ring
      rwa [this, abs_neg, abs_of_nonneg ht0] at hA

end RouteTV

end StatFormal.Wave31tn
