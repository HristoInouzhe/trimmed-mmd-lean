import StatFormal.Archive.OTFD.Wave22b.Statements
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Route — T `lem:exp` (`eq:L`, `eq:expbounds`) (untrusted)

* The segment `v + s(w − v) = (1 − s)v + sw` stays in the closed `b`-ball (convexity), so the integrand of the length
  bound is at most `L_b ‖w − v‖` and the integral over `[0,1]` is at most `L_b ‖w − v‖`; integrate squares over `t`
  (`lintegral_const_mul''`) and take suprema.
* `L_b < ∞`: `(t, v) ↦ d(Exp_{m(t)})_v` is continuous on the compact `T × B̄(0, b)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.OTFD.Wave22b

section ExpProofs
variable {T V W M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [PseudoEMetricSpace M]

lemma segment_norm_le {v w : V} {b s : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖v + s • (w - v)‖ ≤ b := by
  have : v + s • (w - v) = (1 - s) • v + s • w := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  calc ‖(1 - s) • v + s • w‖ ≤ ‖(1 - s) • v‖ + ‖s • w‖ := norm_add_le _ _
    _ = (1 - s) * ‖v‖ + s * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2]), Real.norm_of_nonneg hs.1]
    _ ≤ (1 - s) * b + s * b := add_le_add (mul_le_mul_of_nonneg_left hv (by linarith [hs.2]))
        (mul_le_mul_of_nonneg_left hw hs.1)
    _ = b := by ring

lemma exp_pointwise {Ex : T → V → M} {D : T → V → V →L[ℝ] W} {b : ℝ} (hL : LengthBound Ex D) (t : T) {v w : V}
    (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) : edist (Ex t v) (Ex t w) ≤ Lb D b * ‖v - w‖ₑ := by
  refine (hL t v w).trans ?_
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, ‖D t (v + s • (w - v)) (w - v)‖ₑ ≤ Lb D b * ‖v - w‖ₑ := by
    intro s hs
    refine ((D t (v + s • (w - v))).le_opENorm (w - v)).trans ?_
    rw [enorm_sub_rev]
    refine mul_le_mul_left ?_ _
    exact le_iSup₂_of_le (f := fun (t : T) (v : V) => ⨆ (_ : v ∈ Metric.closedBall (0 : V) b), ‖D t v‖ₑ) t
      (v + s • (w - v)) (le_iSup_of_le (by rw [mem_closedBall_zero_iff]; exact segment_norm_le hv hw hs) le_rfl)
  calc ∫⁻ s in Icc (0 : ℝ) 1, ‖D t (v + s • (w - v)) (w - v)‖ₑ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, Lb D b * ‖v - w‖ₑ :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono fun s hs => hb s hs)
    _ = Lb D b * ‖v - w‖ₑ := by rw [setLIntegral_const, Real.volume_Icc]; simp

end ExpProofs

theorem exp_bounds : Claims.exp_bounds := by
  intro T V W M _ _ _ _ _ _ lam Ex D b v w hL hv hw hmeas
  have hp : ∀ t, edist (Ex t (v t)) (Ex t (w t)) ≤ Lb D b * ‖v t - w t‖ₑ := fun t => exp_pointwise hL t (hv t) (hw t)
  refine ⟨hp, ?_, ?_⟩
  · calc ∫⁻ t, edist (Ex t (v t)) (Ex t (w t)) ^ 2 ∂lam ≤ ∫⁻ t, Lb D b ^ 2 * ‖v t - w t‖ₑ ^ 2 ∂lam := by
          refine lintegral_mono fun t => ?_
          rw [← mul_pow]; exact pow_le_pow_left' (hp t) 2
      _ = Lb D b ^ 2 * ∫⁻ t, ‖v t - w t‖ₑ ^ 2 ∂lam := lintegral_const_mul'' _ (hmeas.pow_const 2)
  · exact iSup_le fun t => (hp t).trans (by gcongr; exact le_iSup (fun t => ‖v t - w t‖ₑ) t)

theorem exp_bounds_embed : Claims.exp_bounds_embed := by
  intro T V W M H _ _ _ _ _ _ _ Ex D ι b Λ h h' hL hι hb hb'
  refine iSup_le fun t => (exp_pointwise hL t (hb t) (hb' t)).trans ?_
  gcongr
  have : ι h t - ι h' t = ι (h - h') t := by rw [map_sub]; rfl
  rw [this, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hι _ t)

theorem exp_Lb_finite : Claims.exp_Lb_finite := by
  intro T V W _ _ _ _ _ _ _ D b hD
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : V) b)).exists_bound_of_continuousOn hD.continuousOn
  refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun t => iSup₂_le fun v hv => ?_) ENNReal.ofReal_lt_top
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC (t, v) ⟨mem_univ _, hv⟩)

end StatFormal.OTFD.Wave22b
