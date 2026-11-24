import StatFormal.Wave31tu.RouteFMain

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: Y15 (c) `lap_fitted_fraction` (§5 :290-291, S4 :1034-1036)

"The fitted ramp keeps a fixed fraction of the excess of the population ramp": in case (i) or (ii) of Proposition S4.27, the fitted
excess is at least `κ₀ε/2` (`lap_fitted_of`), and the population excess at the same level is `V(ε)/g⋆ ≤ ε` (frozen Y11 `lap_pop`,
`eq:lappop`), so `(κ₀/2)(E_Pψ⋆ − E_Qψ⋆ − α) ≤ E_Pψ − E_Qψ − α` (`κ₀ > 0` by Y7 `lap_const`).
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteF

open StatFormal.FixedPoint

/-- **Y15 (c)**: the fitted ramp keeps the fraction `κ₀/2` of the population excess. -/
theorem lap_fitted_fraction_of (h6 : Claims.lap_err) (h7 : Claims.lap_const) (h9 : Claims.lap_ratio)
    (h10 : Claims.lap_clip) (h11 : Claims.lap_pop) (h12 : Claims.lap_compare) (h13 : Claims.lap_dev)
    (h14 : Claims.lap_own) : Claims.lap_fitted_fraction := by
  intro H _ _ _ _ φ P Q _ _ p q x₀ ℓ₀ c₁ c₂ ε₀ c K ε n m x y w v t u a b ts us hφ hcross hpx0 h54 htv hn hm hxy hc hK
    hIx hIy hcase hεα hqp hcut ha hb hab hts hus
  have hfit := lap_fitted_of h6 h7 h9 h10 h11 h12 h13 h14 H φ P Q p q x₀ ℓ₀ c₁ c₂ ε₀ c K n m x y hφ hcross hpx0 h54 htv
    hn hm hxy hc hK hIx hIy
  obtain ⟨-, hsm, hκ1⟩ := laplace1_facts hφ
  obtain ⟨-, -, hκ0, -, hcv, -, -, -, -⟩ := h7 H φ 1 P Q c₁ c₂ ε₀ hsm hκ1 htv h54
  have hnm : 1 ≤ min n m := le_min hn hm
  obtain ⟨hε, hexc⟩ : 0 < ε ∧ StatFormal.Wave31tu.kappa0 (StatFormal.Distances.tvDist P Q) c₁ c₂ ε₀ * ε / 2 ≤
      (∫ z, StatFormal.Wave30tq.ramp (fitF φ x y w v) t u z ∂P) -
        (∫ z, StatFormal.Wave30tq.ramp (fitF φ x y w v) t u z ∂Q) - (StatFormal.Distances.tvDist P Q - ε) := by
    rcases hcase with ⟨rs, cs, pbar, hR, hpbar, hfitI⟩ | hfitII
    · exact ⟨(epsFitI_pos hκ0 hcv hnm).trans_le hfitI, ((hfit.1 rs cs pbar hR hpbar ε hfitI hεα w v hqp).1 t u hcut).2⟩
    · exact ⟨(epsFitII_pos hκ0 hcv hnm).trans_le hfitII, (hfit.2 ε hfitII hεα w v hqp t u hcut).2⟩
  obtain ⟨-, -, -, -, -, -, hpop, hpopε, -⟩ := h11 H 1 φ P Q ε a b ts us one_pos hφ hε hεα htv ha hb hab hts hus
  rw [hpop]
  calc StatFormal.Wave31tu.kappa0 (StatFormal.Distances.tvDist P Q) c₁ c₂ ε₀ / 2 *
        (Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) / (ts - us))
      ≤ StatFormal.Wave31tu.kappa0 (StatFormal.Distances.tvDist P Q) c₁ c₂ ε₀ / 2 * ε :=
        mul_le_mul_of_nonneg_left hpopε (by positivity)
    _ = StatFormal.Wave31tu.kappa0 (StatFormal.Distances.tvDist P Q) c₁ c₂ ε₀ * ε / 2 := by ring
    _ ≤ _ := hexc

end StatFormal.Wave31tu.RouteF
