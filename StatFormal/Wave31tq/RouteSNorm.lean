import StatFormal.Wave31tq.Statements
import StatFormal.Lib.MollifierNorm.Sobolev

/-!
# Wave 31tq, route S: Lemma S4.9, the norm of a mollified indicator (untrusted proof file)

Q10 `newsobnorm`: `c_d > 0` (`JBall.sSup_jBall_Ici_one_lt_one`); `0 ≤ f_w ≤ 1`, `f_w ∈ C_c^∞` (L8, `FourierOps.mollify_smooth_facts`);
the Sobolev bound from `Lib/MollifierNorm/Sobolev.lean` (`sobolevS_mollify_le`: Plancherel, the averaged translation identity,
dyadic shells) after the angular change of variables `sobolevA = sobolevS` (`sobolevA_eq_sobolevS`, from
`MollifierNorm.lintegral_comp_inv_smul`); a negative translation constant forces `Leb(E) = 0`
(`MollifierNorm.volume_eq_zero_of_translation_neg`), and then the bound at `Π = 0` gives `0`.
-/

noncomputable section
open MeasureTheory Set Metric FourierTransform
open scoped ENNReal ContDiff symmDiff

namespace StatFormal.Wave31tq.RouteS

open StatFormal.Wave31tp

/-- The angular Sobolev functional equals Mathlib's: `sobolevA s f = sobolevS s f` (substitution `ξ = 2πη`). -/
theorem sobolevA_eq_sobolevS {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (s : ℝ) (f : V → ℂ) : sobolevA s f = sobolevS s f := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set G : V → ℝ≥0∞ := fun η => ‖ft2 f η‖ₑ ^ 2 * ENNReal.ofReal ((1 + ‖(2 * Real.pi) • η‖ ^ 2) ^ s) with hG
  have h1 : ∀ ξ : V, ‖ft2A f ξ‖ₑ ^ 2 * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) = G ((2 * Real.pi)⁻¹ • ξ) := by
    intro ξ; simp only [G, ft2A, smul_inv_smul₀ hpi.ne']
  have h2 : ∀ η : V, G η = ‖ft2 f η‖ₑ ^ 2 * ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖η‖ ^ 2) ^ s) := by
    intro η
    simp only [G, norm_smul, Real.norm_of_nonneg hpi.le]
    congr 3; ring
  unfold sobolevA sobolevS
  simp_rw [h1]
  rw [MollifierNorm.lintegral_comp_inv_smul G hpi, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  simp_rw [h2]

theorem newsobnorm_route : Claims.newsobnorm := by
  intro d _ V _ _ _ _ _ hd s Per E b m hs hE hEb htr hb hb0 hb1 hbs hm
  have hcd : 0 < cJ d := by
    unfold cJ; linarith [StatFormal.JBall.sSup_jBall_Ici_one_lt_one (d := d)]
  refine ⟨hcd, fun w hw => ?_⟩
  obtain ⟨hsm, hcs, h01, -⟩ := FourierOps.mollify_smooth_facts hE hEb hb hb0 hb1 hbs hw
  refine ⟨h01, hsm, hcs, fun hw1 => ?_⟩
  rw [sobolevA_eq_sobolevS]
  have hr : 0 < 1 - (2 : ℝ) ^ (1 - 2 * s) := sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  have hy : 0 < 1 - (2 : ℝ) ^ (-(4 * (m : ℝ) + 1 - 2 * s)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  rcases le_or_gt 0 Per with hPer | hPer
  · refine (MollifierNorm.sobolevS_mollify_le hd hs hE hEb hPer htr hb hb0 hb1 hbs hm hw hw1).trans ?_
    rw [← ENNReal.ofReal_add (by positivity)]
    · refine le_of_eq (congrArg ENNReal.ofReal ?_)
      unfold sobConst cJ lapC
      field_simp
    · have : 0 < (2 : ℝ) ^ (3 * s) := by positivity
      have : 0 < w ^ (1 - 2 * s) := Real.rpow_pos_of_pos hw _
      have : 0 ≤ Per / (2 * (1 - sSup (jBall d '' Ici 1))) := div_nonneg hPer (by unfold cJ at hcd; linarith)
      positivity
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hd]; exact Nat.pos_of_neZero d)
    have hE0 : volume E = 0 := MollifierNorm.volume_eq_zero_of_translation_neg hEb hPer htr
    have htr0 : ∀ h : V, volume (E ∆ ((· - h) ⁻¹' E)) ≤ ENNReal.ofReal (0 * ‖h‖) := by
      intro h; rw [zero_mul, ENNReal.ofReal_zero]
      exact (htr h).trans (ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonpos_of_nonneg hPer.le (norm_nonneg _))).le
    refine (MollifierNorm.sobolevS_mollify_le hd hs hE hEb le_rfl htr0 hb hb0 hb1 hbs hm hw hw1).trans ?_
    simp [hE0]

end StatFormal.Wave31tq.RouteS
