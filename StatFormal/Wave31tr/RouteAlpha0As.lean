import StatFormal.Lib.Alpha0Witness.SLLN
import StatFormal.Wave31tr.Statements

/-!
# Wave 31tr, chunk M2: T15 `alpha0_fit_uniform_as` (untrusted route)

On the intersection of the two strong-law events (`Alpha0Witness.ae_tendsto_sampleMean` for `φ ∘ X_i` and `φ ∘ Y_j`, Mathlib's
Etemadi strong law), the empirical mean embeddings of the prefixes converge to `μ_P`, `μ_Q`; at `α = 0` every exact minimizer is
the uniform pair (`isQPMin_zero_iff`), whose witness is the normalized difference (`witness_unif`); the normalized differences
converge uniformly against `φ` (`abs_inner_normalize_sub_le_of_tendsto`). The prefix-size statement follows pathwise.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteAlpha0

open StatFormal.Wave30tz StatFormal.Alpha0Witness

theorem alpha0_fit_uniform_as_route : Claims.alpha0_fit_uniform_as := by
  intro 𝒳 H _ _ _ _ _ _ _ Ω _ ℙ _ P Q _ _ X Y φ κ hX hY hiX hiY hlX hlY hφ hκ hpos
  filter_upwards [ae_tendsto_sampleMean hX hiX hlX hφ hκ, ae_tendsto_sampleMean hY hiY hlY hφ hκ] with ω hωX hωY
  have key := abs_inner_normalize_sub_le_of_tendsto hωX hωY hpos hκ
  have part1 : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → ∀ (w : Fin n → ℝ) (v : Fin m → ℝ),
      IsQPMin φ 0 (fun i : Fin n => X i ω) (fun j : Fin m => Y j ω) w v →
        ∀ z, |⟪witness φ (fun i : Fin n => X i ω) (fun j : Fin m => Y j ω) w v, φ z⟫_ℝ -
          ⟪(‖(∫ x, φ x ∂P) - ∫ x, φ x ∂Q‖)⁻¹ • ((∫ x, φ x ∂P) - ∫ x, φ x ∂Q), φ z⟫_ℝ| ≤ ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := key ε hε
    refine ⟨max N₀ 1, fun n m hn hm w v hmin z => ?_⟩
    obtain ⟨rfl, rfl⟩ := (isQPMin_zero_iff φ (le_of_max_le_right hn) (le_of_max_le_right hm) _ _ w v).1 hmin
    rw [witness_unif]
    exact hN₀ n m (le_of_max_le_left hn) (le_of_max_le_left hm) z
  refine ⟨part1, fun a b hab ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := part1 ε hε
  obtain ⟨N₁, hN₁⟩ := hab N₀
  exact ⟨N₁, fun n m hn hm w v hmin z => hN₀ (a n m) (b n m) (hN₁ n m hn hm).1 (hN₁ n m hn hm).2 w v hmin z⟩

end StatFormal.Wave31tr.RouteAlpha0
