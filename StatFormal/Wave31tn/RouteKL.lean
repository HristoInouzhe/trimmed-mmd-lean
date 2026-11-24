import StatFormal.Wave31tn.RouteTV
import StatFormal.Lib.Distances.LeCam

/-!
# Wave 31tn route: `KL(P_{a,h} ‖ P_a) ≤ h²/(a(1−a))` and the `n`-sample total variation (untrusted proof material)

* `klFun_le_sq`: `klFun y = y log y + 1 − y ≤ (y − 1)²` for `y ≥ 0` (`log y ≤ y − 1`), so `KL ≤ χ²`;
* `klDiv_le_of_withDensity`: `KL(ν.withDensity g ‖ ν) ≤ ∫⁻ (g − 1)² dν` (Mathlib's `klDiv_eq_lintegral_klFun_of_ac`);
* `mixAt_eq_withDensity`: `P_{a,h} = P_a.withDensity g`, `g = (a+h)/a` on `S_P`, `(1−a−h)/(1−a)` off it;
* `kl_mixAt_le`: `KL(P_{a,h} ‖ P_a) ≤ h²/a + h²/(1−a) = h²/(a(1−a))` (the `χ²`-divergence, computed exactly);
* `tv_pi_mixAt_le`: `TV(P_{a,h}^n, P_a^n) ≤ √(n·KL/2) ≤ h√(n/(2a(1−a)))` (the library's Pinsker + tensorisation).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set InformationTheory
open scoped ENNReal

namespace StatFormal.Wave31tn

namespace RouteKL

open RouteTV

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

lemma klFun_le_sq {y : ℝ} (hy : 0 ≤ y) : klFun y ≤ (y - 1) ^ 2 := by
  rw [klFun_apply]
  rcases hy.eq_or_lt with rfl | hy
  · simp
  · have hl := Real.log_le_sub_one_of_pos hy
    nlinarith

lemma klDiv_le_of_withDensity {μ ν : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : 𝒳 → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hμ : μ = ν.withDensity fun x => ENNReal.ofReal (g x)) :
    klDiv μ ν ≤ ∫⁻ x, ENNReal.ofReal ((g x - 1) ^ 2) ∂ν := by
  have hac : μ ≪ ν := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hrn : μ.rnDeriv ν =ᵐ[ν] fun x => ENNReal.ofReal (g x) := by
    rw [hμ]; exact Measure.rnDeriv_withDensity ν hg.ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
      = ∫⁻ x, ENNReal.ofReal (klFun (g x)) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (hg0 x)]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((g x - 1) ^ 2) ∂ν :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_le_sq (hg0 x))

open Classical in
/-- The density ratio `g = b/a` on `S_P`, `(1−b)/(1−a)` off it (`b = a + h`). -/
def ratio (SP : Set 𝒳) (a b : ℝ) : 𝒳 → ℝ := fun x => if x ∈ SP then b / a else (1 - b) / (1 - a)

lemma ratio_measurable {SP : Set 𝒳} (hSP : MeasurableSet SP) (a b : ℝ) : Measurable (ratio SP a b) := by
  classical
  exact Measurable.ite hSP measurable_const measurable_const

lemma ratio_nonneg (SP : Set 𝒳) {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (x : 𝒳) :
    0 ≤ ratio SP a b x := by
  unfold ratio; split_ifs
  · positivity
  · exact div_nonneg (by linarith) (by linarith)

/-- `P_b = P_a.withDensity g`. -/
lemma mixAt_eq_withDensity (R P₀ : Measure 𝒳) {SR SP : Set 𝒳} (hSP : MeasurableSet SP) (hRP : Disjoint SR SP)
    (hR : R SRᶜ = 0) (hP₀ : P₀ SPᶜ = 0) {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    mixAt R P₀ b = (mixAt R P₀ a).withDensity fun x => ENNReal.ofReal (ratio SP a b x) := by
  have hRSP : R SP = 0 := measure_mono_null hRP.symm.subset_compl_right hR
  have hRae : ∀ᵐ x ∂R, x ∉ SP := measure_eq_zero_iff_ae_notMem.1 hRSP
  have hPae : ∀ᵐ x ∂P₀, x ∈ SP := ae_iff.2 hP₀
  ext A hA
  rw [withDensity_apply _ hA, mixAt_apply]
  unfold mixAt
  rw [Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul, Measure.restrict_smul,
    lintegral_smul_measure, lintegral_smul_measure]
  have h1 : ∫⁻ x in A, ENNReal.ofReal (ratio SP a b x) ∂R = ENNReal.ofReal ((1 - b) / (1 - a)) * R A := by
    rw [← setLIntegral_const]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hRae] with x hx
    simp [ratio, hx]
  have h2 : ∫⁻ x in A, ENNReal.ofReal (ratio SP a b x) ∂P₀ = ENNReal.ofReal (b / a) * P₀ A := by
    rw [← setLIntegral_const]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hPae] with x hx
    simp [ratio, hx]
  rw [h1, h2, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_mul ha0.le]
  have e1 : (1 - a) * ((1 - b) / (1 - a)) = 1 - b := by field_simp [show (1 - a) ≠ 0 by linarith]
  have e2 : a * (b / a) = b := by field_simp
  rw [e1, e2]

/-- `KL(P_b ‖ P_a) ≤ (b−a)²/(a(1−a))` (the `χ²`-divergence). -/
lemma kl_mixAt_le (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {SR SP : Set 𝒳}
    (hSP : MeasurableSet SP) (hRP : Disjoint SR SP) (hR : R SRᶜ = 0) (hP₀ : P₀ SPᶜ = 0)
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    klDiv (mixAt R P₀ b) (mixAt R P₀ a) ≤ ENNReal.ofReal ((b - a) ^ 2 / (a * (1 - a))) := by
  classical
  have := mixAt_isProb R P₀ hb0 hb1
  have := mixAt_isProb R P₀ ha0.le ha1.le
  refine (klDiv_le_of_withDensity (ratio_measurable hSP a b) (ratio_nonneg SP ha0 ha1 hb0 hb1)
    (mixAt_eq_withDensity R P₀ hSP hRP hR hP₀ ha0 ha1 hb0 hb1)).trans_eq ?_
  have hRSP : R SP = 0 := measure_mono_null hRP.symm.subset_compl_right hR
  have hRc : R SPᶜ = 1 := (prob_compl_eq_one_iff hSP).2 hRSP
  have hP1 : P₀ SP = 1 := (prob_compl_eq_zero_iff hSP).1 hP₀
  have hfun : (fun x => ENNReal.ofReal ((ratio SP a b x - 1) ^ 2)) =
      SP.piecewise (fun _ => ENNReal.ofReal ((b / a - 1) ^ 2)) (fun _ => ENNReal.ofReal (((1 - b) / (1 - a) - 1) ^ 2)) := by
    funext x
    by_cases hx : x ∈ SP <;> simp [ratio, hx, Set.piecewise]
  rw [hfun, lintegral_piecewise hSP.nullMeasurableSet, setLIntegral_const, setLIntegral_const, mixAt_apply, mixAt_apply,
    hRSP, hP1, hRc, hP₀]
  simp only [mul_zero, zero_add, mul_one, add_zero]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_add
    (mul_nonneg (sq_nonneg _) ha0.le) (mul_nonneg (sq_nonneg _) (by linarith))]
  congr 1
  have h1a : (1 - a) ≠ 0 := by linarith
  field_simp
  ring

/-- `TV(P_{a+h}^n, P_a^n) ≤ h√(n/(2a(1−a)))` for `h ∈ [0, 1−a]`. -/
lemma tv_pi_mixAt_le (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {SR SP : Set 𝒳}
    (hSP : MeasurableSet SP) (hRP : Disjoint SR SP) (hR : R SRᶜ = 0) (hP₀ : P₀ SPᶜ = 0)
    {a h : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 - a) (n : ℕ) :
    StatFormal.Distances.tvDist (Measure.pi fun _ : Fin n => mixAt R P₀ (a + h))
      (Measure.pi fun _ : Fin n => mixAt R P₀ a) ≤ h * √(n / (2 * a * (1 - a))) := by
  have := mixAt_isProb R P₀ (t := a + h) (by linarith) (by linarith)
  have := mixAt_isProb R P₀ ha0.le ha1.le
  have hkl := kl_mixAt_le R P₀ hSP hRP hR hP₀ ha0 ha1 (b := a + h) (by linarith) (by linarith)
  have hX : 0 ≤ (a + h - a) ^ 2 / (a * (1 - a)) := div_nonneg (sq_nonneg _) (mul_nonneg ha0.le (by linarith))
  have hne : klDiv (mixAt R P₀ (a + h)) (mixAt R P₀ a) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hle : (klDiv (mixAt R P₀ (a + h)) (mixAt R P₀ a)).toReal ≤ (a + h - a) ^ 2 / (a * (1 - a)) :=
    ENNReal.toReal_le_of_le_ofReal hX hkl
  refine (StatFormal.Distances.tvDist_pi_le_sqrt_klDiv _ _ n hne).trans ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc √(n * (klDiv (mixAt R P₀ (a + h)) (mixAt R P₀ a)).toReal / 2)
      ≤ √(n * ((a + h - a) ^ 2 / (a * (1 - a))) / 2) :=
        Real.sqrt_le_sqrt (by gcongr)
    _ = h * √(n / (2 * a * (1 - a))) := by
        have : (n : ℝ) * ((a + h - a) ^ 2 / (a * (1 - a))) / 2 = h ^ 2 * (n / (2 * a * (1 - a))) := by
          have h1a : (1 - a) ≠ 0 := by linarith
          field_simp
          ring
        rw [this, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh0]

end RouteKL

end StatFormal.Wave31tn
