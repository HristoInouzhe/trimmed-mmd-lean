import StatFormal.Wave31tu.Statements
import StatFormal.Wave31ti.Proofs

set_option linter.style.longLine false

/-!
# Wave31tu, chunk P: Y7 `lap_const` (S4 :1061-1071, the constants paragraph)

Under the two-sided bound `c₁ε^{5/4} ≤ D_{α⋆−ε} ≤ c₂ε^{5/4}` on `(0, ε₀]` (`TwoSided54`), `α⋆ < 1`: `ρ₀, κ₀ ∈ (0,1)`, `c_V > 0`,
`V(ε) = (1−α⋆+ε)D_{α⋆−ε}` is nondecreasing on `[0, α⋆]`, `(1−α⋆)D_{α⋆−ε} ≤ V(ε) ≤ D_{α⋆−ε}`, `V(ε) ≥ c_Vε^{5/4}` on `(0, α⋆]`, and
`ρ₀V(2ε) ≤ V(ε)` for `ε < ε₀/2`.

Route (printed): the certified `Wave31ti.pathconvex` (the path `α ↦ (1−α)D_α` is nonincreasing on `[0,1)`), `D_α ≥ 0`, and the
two-sided bound; for `ε > ε₀` the lower bound is carried from `ε₀` by monotonicity.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteP

open StatFormal.Distances StatFormal.TrimmedMMD.Unconditional

/-- `(1 − α⋆)D_{α⋆−ε} ≤ V(ε) ≤ D_{α⋆−ε}` for `ε ∈ [0, α⋆]` (any laws, any feature map). -/
theorem uPath_sandwich {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H)
    (P Q : Measure 𝒳) {αs e : ℝ} (he : e ∈ Icc (0 : ℝ) αs) :
    (1 - αs) * Dpop φ P Q (αs - e) ≤ Wave31ti.uPath φ P Q (αs - e) ∧
      Wave31ti.uPath φ P Q (αs - e) ≤ Dpop φ P Q (αs - e) := by
  have hD := Wave31ti.Dpop_nonneg0 φ P Q (αs - e)
  unfold Wave31ti.uPath
  constructor
  · exact mul_le_mul_of_nonneg_right (by linarith [he.1]) hD
  · have : (1 - (αs - e)) * Dpop φ P Q (αs - e) ≤ 1 * Dpop φ P Q (αs - e) :=
      mul_le_mul_of_nonneg_right (by linarith [he.2]) hD
    linarith

/-- Y7 `lap_const`. -/
theorem lap_const_route : Claims.lap_const := by
  intro H _ _ _ _ φ κ P Q _ _ c₁ c₂ ε₀ hφ hκ hα1 hTS
  obtain ⟨hc₁, hc₁₂, hε₀, hε₀α, hTwo⟩ := hTS
  set αs := tvDist P Q with hαs
  have hαpos : 0 < αs := lt_of_lt_of_le hε₀ hε₀α
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  have h1α : 0 < 1 - αs := by linarith
  have h2p : (1 : ℝ) < 2 ^ (5 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hrho0 : 0 < rho0 αs c₁ c₂ := by
    unfold rho0; exact div_pos (mul_pos h1α hc₁) (mul_pos (by linarith) hc₂)
  have hrho1 : rho0 αs c₁ c₂ < 1 := by
    unfold rho0
    rw [div_lt_one (mul_pos (by linarith) hc₂)]
    calc (1 - αs) * c₁ ≤ 1 * c₂ := mul_le_mul (by linarith) hc₁₂ hc₁.le (by norm_num)
      _ < 2 ^ (5 / 4 : ℝ) * c₂ := by rw [one_mul]; exact lt_mul_of_one_lt_left hc₂ h2p
  have hsec : 0 < (1 - αs) * c₁ * (ε₀ / 2) ^ (5 / 4 : ℝ) / (2 * αs) :=
    div_pos (mul_pos (mul_pos h1α hc₁) (Real.rpow_pos_of_pos (by linarith) _)) (by linarith)
  have hk0 : 0 < kappa0 αs c₁ c₂ ε₀ := lt_min hrho0 hsec
  have hk1 : kappa0 αs c₁ c₂ ε₀ < 1 := lt_of_le_of_lt (min_le_left _ _) hrho1
  have hcV : 0 < cV αs c₁ ε₀ := by
    unfold cV; exact mul_pos (mul_pos h1α hc₁) (Real.rpow_pos_of_pos (div_pos hε₀ hαpos) _)
  have hanti := ((Wave31ti.pathconvex ℝ H P Q φ κ hφ hκ).2)
  have hmono : MonotoneOn (fun e => Wave31ti.uPath φ P Q (αs - e)) (Icc 0 αs) := by
    intro e he e' he' hle
    exact hanti ⟨by linarith [he'.2], by linarith [he'.1]⟩ ⟨by linarith [he.2], by linarith [he.1]⟩ (by linarith)
  have hsand := fun e (he : e ∈ Icc (0 : ℝ) αs) => uPath_sandwich φ P Q (αs := αs) he
  -- the lower bound on `(0, ε₀]`
  have hlow : ∀ e ∈ Ioc (0 : ℝ) ε₀, (1 - αs) * c₁ * e ^ (5 / 4 : ℝ) ≤ Wave31ti.uPath φ P Q (αs - e) := by
    intro e he
    have h1 := (hsand e ⟨he.1.le, he.2.trans hε₀α⟩).1
    have h2 := (hTwo e he).1
    calc (1 - αs) * c₁ * e ^ (5 / 4 : ℝ) = (1 - αs) * (c₁ * e ^ (5 / 4 : ℝ)) := by ring
      _ ≤ (1 - αs) * Dpop φ P Q (αs - e) := mul_le_mul_of_nonneg_left h2 h1α.le
      _ ≤ _ := h1
  have hcVe : ∀ e ∈ Ioc (0 : ℝ) αs, cV αs c₁ ε₀ * e ^ (5 / 4 : ℝ) ≤ Wave31ti.uPath φ P Q (αs - e) := by
    intro e he
    have hr1 : (ε₀ / αs) ^ (5 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one (div_pos hε₀ hαpos).le ((div_le_one hαpos).mpr hε₀α) (by norm_num)
    have he54 : 0 ≤ e ^ (5 / 4 : ℝ) := Real.rpow_nonneg he.1.le _
    rcases le_or_gt e ε₀ with hle | hlt
    · calc cV αs c₁ ε₀ * e ^ (5 / 4 : ℝ) = (1 - αs) * c₁ * e ^ (5 / 4 : ℝ) * (ε₀ / αs) ^ (5 / 4 : ℝ) := by
            unfold cV; ring
        _ ≤ (1 - αs) * c₁ * e ^ (5 / 4 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hr1 (mul_nonneg (mul_pos h1α hc₁).le he54)
        _ ≤ _ := by rw [mul_one]; exact hlow e ⟨he.1, hle⟩
    · have hm := hmono ⟨hε₀.le, hε₀α⟩ ⟨he.1.le, he.2⟩ hlt.le
      have hl0 := hlow ε₀ ⟨hε₀, le_rfl⟩
      have hpow : e ^ (5 / 4 : ℝ) ≤ αs ^ (5 / 4 : ℝ) := Real.rpow_le_rpow he.1.le he.2 (by norm_num)
      have hdiv : (ε₀ / αs) ^ (5 / 4 : ℝ) * αs ^ (5 / 4 : ℝ) = ε₀ ^ (5 / 4 : ℝ) := by
        rw [Real.div_rpow hε₀.le hαpos.le]
        field_simp [(Real.rpow_pos_of_pos hαpos (5 / 4 : ℝ)).ne']
      calc cV αs c₁ ε₀ * e ^ (5 / 4 : ℝ) ≤ cV αs c₁ ε₀ * αs ^ (5 / 4 : ℝ) := mul_le_mul_of_nonneg_left hpow hcV.le
        _ = (1 - αs) * c₁ * ε₀ ^ (5 / 4 : ℝ) := by unfold cV; rw [← hdiv]; ring
        _ ≤ Wave31ti.uPath φ P Q (αs - ε₀) := hl0
        _ ≤ _ := hm
  have hrho : ∀ e ∈ Ioo (0 : ℝ) (ε₀ / 2),
      rho0 αs c₁ c₂ * Wave31ti.uPath φ P Q (αs - 2 * e) ≤ Wave31ti.uPath φ P Q (αs - e) := by
    intro e he
    have h2e : 2 * e ∈ Ioc (0 : ℝ) ε₀ := ⟨by linarith [he.1], by linarith [he.2]⟩
    have hup := (hsand (2 * e) ⟨h2e.1.le, h2e.2.trans hε₀α⟩).2
    have hD2 := (hTwo (2 * e) h2e).2
    have hmul : (2 * e) ^ (5 / 4 : ℝ) = 2 ^ (5 / 4 : ℝ) * e ^ (5 / 4 : ℝ) := Real.mul_rpow (by norm_num) he.1.le
    have hl := hlow e ⟨he.1, by linarith [he.2]⟩
    calc rho0 αs c₁ c₂ * Wave31ti.uPath φ P Q (αs - 2 * e)
        ≤ rho0 αs c₁ c₂ * (c₂ * (2 * e) ^ (5 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hup.trans hD2) hrho0.le
      _ = (1 - αs) * c₁ * e ^ (5 / 4 : ℝ) := by
          unfold rho0; rw [hmul]; field_simp [(lt_trans one_pos h2p).ne', hc₂.ne']
      _ ≤ _ := hl
  exact ⟨hrho0, hrho1, hk0, hk1, hcV, hmono, hsand, hcVe, hrho⟩

end StatFormal.Wave31tu.RouteP
