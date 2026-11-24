import StatFormal.Wave31tn.RouteKL

/-!
# Wave 31tn route: S1 `prop:lower2pt` (untrusted proof material)

* (a) from `RouteTV.tv_mixAt` (`TV = max s t`).
* (b) Le Cam: `{α̃ ≤ a}` has null probability `≥ 1 − δ`; the data laws differ only in the perturbed sample, so (the randomiser and
  the other sample are common factors, `tvDist_prod_left_le`/`_right_le`) their TV is at most `TV(P_{a,h}^n, P_a^n) ≤ h√(n/(2a(1−a)))`
  (`RouteKL.tv_pi_mixAt_le`: `KL ≤ χ² = h²/(a(1−a))`, Pinsker, tensorisation); on `{α̃ ≤ a}` the error at the perturbed pair, whose
  TV is `a + h`, is `≥ h`.
* (c) from (b) at `h = ((1−δ)/2)√(2a(1−a)/N)`, `N` the smaller sample size: `h√(N/(2a(1−a))) = (1−δ)/2`; at `δ = 1` trivial.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tn

namespace RouteS1

open RouteTV RouteKL StatFormal.Wave30tp

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma sampleLaw_isProb {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n m : ℕ) : IsProbabilityMeasure (sampleLaw P Q n m) := by
  unfold sampleLaw; infer_instance

/-- The Le Cam step with a common randomiser: `(μ₁ ⊗ ρ)(A) ≥ (μ₀ ⊗ ρ)(A) − TV(μ₁, μ₀)`. -/
lemma lecam_step {μ1 μ0 : Measure α} [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ0] (ρ : Measure β)
    [IsProbabilityMeasure ρ] {A : Set (α × β)} (hA : MeasurableSet A) {δ c : ℝ}
    (h0 : 1 - δ ≤ (μ0.prod ρ).real A) (hc : StatFormal.Distances.tvDist μ1 μ0 ≤ c) :
    1 - δ - c ≤ (μ1.prod ρ).real A := by
  have h1 := StatFormal.Distances.measureReal_ge_sub_tvDist (μ := μ1.prod ρ) (ν := μ0.prod ρ) hA
  have h2 := StatFormal.Distances.tvDist_prod_left_le (μ := μ1) (ν := μ0) ρ
  linarith

theorem lower2pt_tv_route : Claims.lower2pt_tv := by
  intro 𝒳 _ R P₀ Q₀ _ _ _ SR SP SQ a h _ hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hh0 hh1
  have ht := fun s t (hs0 : (0 : ℝ) ≤ s) (hs1 : s ≤ 1) (ht0 : (0 : ℝ) ≤ t) (ht1 : t ≤ 1) =>
    tv_mixAt R P₀ Q₀ hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ hs0 hs1 ht0 ht1
  refine ⟨?_, ?_, ?_⟩
  · rw [ht a a ha0.le ha1.le ha0.le ha1.le, max_self]
  · rw [ht (a + h) a (by linarith) (by linarith) ha0.le ha1.le, max_eq_left (by linarith)]
  · rw [ht a (a + h) ha0.le ha1.le (by linarith) (by linarith), max_eq_right (by linarith)]

theorem lower2pt_route : Claims.lower2pt := by
  intro 𝒳 _ R P₀ Q₀ _ _ _ SR SP SQ a δ n m Ξ _ ρ _ T hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hT hval h hh0 hh1
  have := mixAt_isProb R P₀ ha0.le ha1.le
  have := mixAt_isProb R Q₀ ha0.le ha1.le
  have := mixAt_isProb R P₀ (t := a + h) (by linarith) (by linarith)
  have := mixAt_isProb R Q₀ (t := a + h) (by linarith) (by linarith)
  have hTV := lower2pt_tv_route 𝒳 R P₀ Q₀ SR SP SQ a h hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hh0.le hh1
  have hA : MeasurableSet {z : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ | T z ≤ a} := measurableSet_le hT measurable_const
  have := sampleLaw_isProb (mixAt R P₀ a) (mixAt R Q₀ a) n m
  have h0 : 1 - δ ≤ ((sampleLaw (mixAt R P₀ a) (mixAt R Q₀ a) n m).prod ρ).real {z | T z ≤ a} := by
    have hc : {z : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ | T z ≤ a} = {z | a < T z}ᶜ := by ext z; simp
    rw [hc, probReal_compl_eq_one_sub (measurableSet_lt measurable_const hT)]
    linarith
  have hsubP : {z : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ | T z ≤ a} ⊆
      {z | h ≤ StatFormal.Distances.tvDist (mixAt R P₀ (a + h)) (mixAt R Q₀ a) - T z} := by
    intro z hz; simp only [mem_setOf_eq] at hz ⊢; rw [hTV.2.1]; linarith
  have hsubQ : {z : ((Fin n → 𝒳) × (Fin m → 𝒳)) × Ξ | T z ≤ a} ⊆
      {z | h ≤ StatFormal.Distances.tvDist (mixAt R P₀ a) (mixAt R Q₀ (a + h)) - T z} := by
    intro z hz; simp only [mem_setOf_eq] at hz ⊢; rw [hTV.2.2]; linarith
  constructor
  · have := sampleLaw_isProb (mixAt R P₀ (a + h)) (mixAt R Q₀ a) n m
    have hc : StatFormal.Distances.tvDist (sampleLaw (mixAt R P₀ (a + h)) (mixAt R Q₀ a) n m)
        (sampleLaw (mixAt R P₀ a) (mixAt R Q₀ a) n m) ≤ h * √(n / (2 * a * (1 - a))) :=
      (StatFormal.Distances.tvDist_prod_left_le (Measure.pi fun _ : Fin m => mixAt R Q₀ a)).trans
        (tv_pi_mixAt_le R P₀ hSP hRP hR hP₀ ha0 ha1 hh0.le hh1.le n)
    exact (lecam_step ρ hA h0 hc).trans (measureReal_mono hsubP)
  · have := sampleLaw_isProb (mixAt R P₀ a) (mixAt R Q₀ (a + h)) n m
    have hc : StatFormal.Distances.tvDist (sampleLaw (mixAt R P₀ a) (mixAt R Q₀ (a + h)) n m)
        (sampleLaw (mixAt R P₀ a) (mixAt R Q₀ a) n m) ≤ h * √(m / (2 * a * (1 - a))) :=
      (StatFormal.Distances.tvDist_prod_right_le (Measure.pi fun _ : Fin n => mixAt R P₀ a)).trans
        (tv_pi_mixAt_le R Q₀ hSQ hRQ hR hQ₀ ha0 ha1 hh0.le hh1.le m)
    exact (lecam_step ρ hA h0 hc).trans (measureReal_mono hsubQ)

theorem lower2pt_c_route : Claims.lower2pt_c := by
  intro 𝒳 _ R P₀ Q₀ _ _ _ SR SP SQ a δ n m Ξ _ ρ _ T hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hδ0 hδ1 hn hm hT hval hh1
  rcases hδ1.lt_or_eq with hδ | hδ
  · set h := hStar δ a (min n m) with hhdef
    have hN : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast le_min hn hm
    have h1a : 0 < 1 - a := by linarith
    have hq : 0 < 2 * a * (1 - a) / ((min n m : ℕ) : ℝ) := by positivity
    have hh0 : 0 < h := by
      rw [hhdef, hStar]; exact mul_pos (by linarith) (Real.sqrt_pos.2 hq)
    have hb := lower2pt_route 𝒳 R P₀ Q₀ SR SP SQ a δ n m Ξ ρ T hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hT hval h hh0 hh1
    have key : ∀ k : ℕ, (k : ℝ) = ((min n m : ℕ) : ℝ) → h * √(k / (2 * a * (1 - a))) = (1 - δ) / 2 := by
      intro k hk
      rw [hhdef, hStar, hk, mul_assoc, ← Real.sqrt_mul hq.le]
      have hN0 : ((min n m : ℕ) : ℝ) ≠ 0 := by linarith
      have h1a' : (1 - a) ≠ 0 := by linarith
      have ha' : a ≠ 0 := by linarith
      rw [show 2 * a * (1 - a) / ((min n m : ℕ) : ℝ) * (((min n m : ℕ) : ℝ) / (2 * a * (1 - a))) = 1 by
        field_simp]
      simp
    refine ⟨fun hnm => ?_, fun hmn => ?_⟩
    · have := hb.1
      rw [key n (by rw [min_eq_left hnm])] at this
      linarith
    · have := hb.2
      rw [key m (by rw [min_eq_right hmn])] at this
      linarith
  · subst hδ
    simp only [sub_self, zero_div]
    exact ⟨fun _ => measureReal_nonneg, fun _ => measureReal_nonneg⟩

end RouteS1

end StatFormal.Wave31tn
