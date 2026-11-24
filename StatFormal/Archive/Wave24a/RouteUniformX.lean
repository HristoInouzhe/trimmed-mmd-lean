import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.Wave21b.RouteCondBand
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Route — C `cor:conditional-uniform-x` (untrusted)

Quantitative gradient bound (`grad_bound`): if `ξ` is a subgradient of `g` at `u` tested on `B̄(u,h)`, `|g − χ| ≤ η`
there, `∇χ = Q` on `B̄(u,h)` with `‖Q − Q(u)‖ ≤ ε`, then `‖ξ − Q(u)‖ ≤ ε + 2η/h` (test the subgradient inequality at
`u + h e`, `e = (ξ − Q u)/‖ξ − Q u‖`, and apply the mean value theorem to `s ↦ χ(u + s e)`). Joint continuity on the
compact `S_r × D₀` gives one `δ` for every query (Heine–Cantor); take `h = min(r, δ/2)` and `η = εh/4`. The bands
follow from the certified Wave 21b `cond_band_two_sided` at each query.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24a

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma grad_bound {χ g : E → ℝ} {Q : E → E} {u ξ : E} {h ε η : ℝ} (hh : 0 < h)
    (hgrad : ∀ y ∈ closedBall u h, HasGradientAt χ (Q y) y)
    (hQ : ∀ y ∈ closedBall u h, ‖Q y - Q u‖ ≤ ε)
    (hsub : ∀ y ∈ closedBall u h, g u + ⟪ξ, y - u⟫ ≤ g y)
    (happ : ∀ y ∈ closedBall u h, |g y - χ y| ≤ η) :
    ‖ξ - Q u‖ ≤ ε + 2 * η / h := by
  have hu : u ∈ closedBall u h := mem_closedBall_self hh.le
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hQ u hu)
  have hη : 0 ≤ η := (abs_nonneg _).trans (happ u hu)
  set d := ξ - Q u with hd
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 h0
  set e := ‖d‖⁻¹ • d with he
  have hen : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn.ne']
  have hde : ⟪d, e⟫ = ‖d‖ := by
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hline : ∀ s ∈ Icc (0 : ℝ) h, u + s • e ∈ closedBall u h := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hen, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    exact hs.2
  set φ : ℝ → ℝ := fun s => χ (u + s • e)
  have hφd : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt φ ⟪Q (u + s • e), e⟫ s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => u + s • e) e s := by
      simpa using ((hasDerivAt_id s).smul_const e).const_add u
    have h2 := ((hasGradientAt_iff_hasFDerivAt.1 (hgrad _ (hline s hs))).comp_hasDerivAt s h1)
    rw [InnerProductSpace.toDual_apply_apply] at h2
    exact h2
  have hφc : ContinuousOn φ (Icc 0 h) := fun s hs => (hφd s hs).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope φ (fun s => ⟪Q (u + s • e), e⟫) hh hφc
    (fun s hs => hφd s (Ioo_subset_Icc_self hs))
  have hcm := hline c (Ioo_subset_Icc_self hc)
  have hslope : χ (u + h • e) - χ u = h * ⟪Q (u + c • e), e⟫ := by
    have : φ h - φ 0 = h * ⟪Q (u + c • e), e⟫ := by
      rw [hcd, sub_zero]; field_simp
    simpa [φ] using this
  have hQc : ⟪Q (u + c • e), e⟫ ≤ ⟪Q u, e⟫ + ε := by
    have h1 : ⟪Q (u + c • e) - Q u, e⟫ ≤ ε := by
      refine (real_inner_le_norm _ _).trans ?_
      rw [hen, mul_one]; exact hQ _ hcm
    rw [inner_sub_left] at h1; linarith
  have hy := hline h ⟨hh.le, le_rfl⟩
  have hs := hsub _ hy
  rw [add_sub_cancel_left, inner_smul_right] at hs
  have ha1 := abs_le.1 (happ _ hy)
  have ha2 := abs_le.1 (happ u hu)
  have hξ : ⟪ξ, e⟫ = ‖d‖ + ⟪Q u, e⟫ := by
    rw [← hde, hd, inner_sub_left]; ring
  have key : h * ‖d‖ ≤ h * ε + 2 * η := by
    have := mul_le_mul_of_nonneg_left hQc hh.le
    nlinarith
  rw [show ε + 2 * η / h = (h * ε + 2 * η) / h by field_simp]
  rw [le_div_iff₀ hh]; linarith

end

theorem conditional_uniform_x_maps : Claims.conditional_uniform_x_maps := by
  intro K X _ D0 S O r χ Q g T hD0 hS hr hO hSO hgrad hQc hsub hconv η hη
  set C := cthickening r S with hC
  have hCc : IsCompact C := hS.cthickening
  have hCO : C ×ˢ D0 ⊆ O ×ˢ D0 := prod_mono hSO le_rfl
  have hU := (hCc.prod hD0).uniformContinuousOn_of_continuous (hQc.mono hCO)
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, hδU⟩ := hU (η / 2) (by positivity)
  set h := min r (δ / 2) with hh
  have hh0 : 0 < h := lt_min hr (by positivity)
  have hball : ∀ u ∈ S, closedBall u h ⊆ C := fun u hu =>
    (closedBall_subset_cthickening hu h).trans (cthickening_mono (min_le_left _ _) S)
  filter_upwards [hconv (η / 2 * h / 4) (by positivity)] with n hn x hx u hu
  have hb := grad_bound (χ := χ x) (g := g n x) (Q := Q x) (u := u) (ξ := T n x u) (ε := η / 2)
    (η := η / 2 * h / 4) hh0 (fun y hy => hgrad x hx y (hSO (hball u hu hy)))
    (fun y hy => by
      have := hδU (y, x) ⟨hball u hu hy, hx⟩ (u, x) ⟨hball u hu (mem_closedBall_self hh0.le), hx⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact (mem_closedBall.1 hy).trans_lt ((min_le_right _ _).trans_lt (by linarith)))
      rw [dist_eq_norm] at this
      exact this.le)
    (fun y hy => hsub n x hx u hu y (hball u hu hy)) (fun y hy => hn x hx y (hball u hu hy))
  calc ‖T n x u - Q x u‖ ≤ η / 2 + 2 * (η / 2 * h / 4) / h := hb
    _ = 3 * η / 4 := by field_simp; ring
    _ ≤ η := by linarith

theorem conditional_uniform_x : Claims.conditional_uniform_x := by
  intro K X 𝒯 _ D0 μ A S O r δ EK χ Q g T e hD0 hS hr hO hSO hgrad hQc hsub hconv he hA η hη
  have hη' : 0 < η / (|EK| + 1) := by positivity
  filter_upwards [conditional_uniform_x_maps K X D0 S O r χ Q g T hD0 hS hr hO hSO hgrad hQc hsub hconv _ hη']
    with n hn x hx p hp0 hp1 t v hv
  have hQS : ContinuousOn (Q x) S := by
    have : ContinuousOn (fun u => Q x u) O :=
      (hQc.comp (continuousOn_id.prodMk continuousOn_const) (fun u hu => ⟨hu, hx⟩) :)
    exact this.mono ((self_subset_cthickening S).trans hSO)
  obtain ⟨a, b, ha, hb, hab⟩ := StatFormal.Wave21b.cond_band_two_sided K 𝒯 μ A S (Q x) (T n x) e δ
    (η / (|EK| + 1)) EK hQS (fun u hu => hn x hx u hu) he hA p hp0 hp1 t v hv
  refine ⟨a, b, ha, hb, hab.trans ?_⟩
  calc EK * (η / (|EK| + 1)) ≤ |EK| * (η / (|EK| + 1)) := by gcongr; exact le_abs_self EK
    _ ≤ (|EK| + 1) * (η / (|EK| + 1)) := by gcongr; linarith
    _ = η := by field_simp

example : Claims.conditional_uniform_x_maps := conditional_uniform_x_maps
example : Claims.conditional_uniform_x := conditional_uniform_x

end StatFormal.Wave24a
