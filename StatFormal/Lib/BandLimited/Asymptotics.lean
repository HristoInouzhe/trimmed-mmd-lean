import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A cubic tail at a dilated point is eventually below a linear function (library, untrusted)

If `T(t) ≤ K/t³` for `t ≥ t₀ > 0`, then for every `A, s, κ > 0` there is `ε₂ > 0` with `T(√(A/ε)·s) ≤ κε` for all
`ε ∈ (0, ε₂]`: the argument `u = √(A/ε)s` is `≥ t₀` once `ε ≤ As²/t₀²`, and `K/u³ = Kε/(A s³ √(A/ε)) ≤ κε` once
`√(A/ε) ≥ K/(κAs³)`. This is the step "`b̄(Ω_ε t) ≤ 16π/(3(Ω_ε t)³) = O(ε^{3/2})`" of the proof of Theorem S4.13 of the
trimmed-MMD paper, with `Ω_ε = √(ℓπ²/(2θε))`.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.BandLimited

/-- **Cubic tails at `√(A/ε)·s` are `o(ε)`**, in the explicit form: `T(√(A/ε)s) ≤ κε` for `ε ∈ (0, ε₂]`. -/
theorem cubic_tail_small {T : ℝ → ℝ} {K t₀ : ℝ} (ht₀ : 0 < t₀) (hT : ∀ t, t₀ ≤ t → T t ≤ K / t ^ 3)
    {A s κ : ℝ} (hA : 0 < A) (hs : 0 < s) (hκ : 0 < κ) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε, 0 < ε → ε ≤ ε₂ → T (√(A / ε) * s) ≤ κ * ε := by
  set K' : ℝ := |K| + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  refine ⟨min (A * s ^ 2 / t₀ ^ 2) (A * (κ * A * s ^ 3) ^ 2 / K' ^ 2), by positivity, fun ε hε hεle => ?_⟩
  have hε1 : ε ≤ A * s ^ 2 / t₀ ^ 2 := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ A * (κ * A * s ^ 3) ^ 2 / K' ^ 2 := hεle.trans (min_le_right _ _)
  set r := √(A / ε) with hr
  have hAε : 0 < A / ε := div_pos hA hε
  have hr0 : 0 < r := Real.sqrt_pos.2 hAε
  have hr2 : r ^ 2 = A / ε := Real.sq_sqrt hAε.le
  have hu0 : 0 < r * s := mul_pos hr0 hs
  -- `t₀ ≤ r s`
  have hu : t₀ ≤ r * s := by
    rw [← pow_le_pow_iff_left₀ ht₀.le hu0.le two_ne_zero, mul_pow, hr2]
    rw [le_div_iff₀ (by positivity)] at hε1
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  -- `K'/(κ A s³) ≤ r`
  have hrK : K' ≤ κ * A * s ^ 3 * r := by
    have h1 : K' ^ 2 ≤ (κ * A * s ^ 3 * r) ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hε2
      rw [mul_pow, hr2, mul_div_assoc', le_div_iff₀ hε]
      nlinarith
    exact (pow_le_pow_iff_left₀ hK'0.le (by positivity) two_ne_zero).1 h1
  calc T (r * s) ≤ K / (r * s) ^ 3 := hT _ hu
    _ ≤ K' / (r * s) ^ 3 := by
        gcongr
        rw [hK']; linarith [le_abs_self K]
    _ ≤ κ * ε := by
        rw [div_le_iff₀ (by positivity)]
        have : κ * ε * (r * s) ^ 3 = κ * A * s ^ 3 * r := by
          have : ε * r ^ 2 = A := by rw [hr2]; field_simp
          calc κ * ε * (r * s) ^ 3 = κ * s ^ 3 * r * (ε * r ^ 2) := by ring
            _ = κ * A * s ^ 3 * r := by rw [this]; ring
        rw [this]; exact hrK

end StatFormal.BandLimited
