import StatFormal.Archive.OTFD.Wave1.Statements

/-!
# Route — Lipschitz hypersurfaces: closedness and transversal lines (untrusted)

For `w ≠ 0` put `a(x) = ⟪x, w⟫/‖w‖²` and `p(x) = x − a(x) w` (the projection onto `Z = (ℝw)^⊥`). Then
`x ∈ A_w ⟺ a(x) = τ(p x)`, so `A_w` is closed, and a line `x + s u` with `a(u) > L ‖p u‖` meets `A_w` at most once
(`otfd A`, proof of `lem:app-block-Pl`).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP2b

open StatFormal.OTFD.Wave1 (PellClass IsLipHyp lipHyp)

section Geom
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `a(x) = ⟪x, w⟫/‖w‖²`, the coordinate of `x` along `w`. -/
def acoef (w x : H) : ℝ := ⟪x, w⟫_ℝ / ‖w‖ ^ 2

/-- `p(x) = x − a(x) w`, the orthogonal projection onto `(ℝw)^⊥`. -/
def pZ (w x : H) : H := x - acoef w x • w

lemma acoef_add (w x y : H) : acoef w (x + y) = acoef w x + acoef w y := by
  simp [acoef, inner_add_left, add_div]

lemma acoef_smul (w x : H) (s : ℝ) : acoef w (s • x) = s * acoef w x := by
  simp [acoef, real_inner_smul_left, mul_div_assoc]

lemma acoef_self {w : H} (hw : w ≠ 0) : acoef w w = 1 := by
  have : (‖w‖ ^ 2 : ℝ) ≠ 0 := by positivity
  simp [acoef, div_self this]

lemma pZ_add (w x y : H) : pZ w (x + y) = pZ w x + pZ w y := by
  simp only [pZ, acoef_add, add_smul]; abel

lemma pZ_smul (w x : H) (s : ℝ) : pZ w (s • x) = s • pZ w x := by
  simp only [pZ, acoef_smul, smul_sub, mul_smul]

lemma inner_pZ {w : H} (hw : w ≠ 0) (x : H) : ⟪pZ w x, w⟫_ℝ = 0 := by
  have : (‖w‖ ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [pZ, acoef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp
  ring

lemma acoef_of_inner_zero {w z : H} (hz : ⟪z, w⟫_ℝ = 0) : acoef w z = 0 := by
  simp [acoef, hz]

lemma mem_lipHyp_iff {w : H} (hw : w ≠ 0) (τ : H → ℝ) (x : H) :
    x ∈ lipHyp w τ ↔ acoef w x = τ (pZ w x) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have ha : acoef w (z + τ z • w) = τ z := by
      rw [acoef_add, acoef_smul, acoef_of_inner_zero hz, acoef_self hw]; ring
    have hp : pZ w (z + τ z • w) = z := by simp only [pZ, ha, add_sub_cancel_right]
    rw [hp, ha]
  · intro h
    refine ⟨pZ w x, inner_pZ hw x, ?_⟩
    rw [← h]; simp [pZ]

lemma norm_pZ_le {w : H} (hw : w ≠ 0) (y : H) : ‖pZ w y‖ ≤ 2 * ‖y‖ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : ‖acoef w y • w‖ ≤ ‖y‖ := by
    rw [norm_smul, acoef, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖w‖ ^ 2)]
    have hcs := abs_real_inner_le_norm y w
    calc |⟪y, w⟫_ℝ| / ‖w‖ ^ 2 * ‖w‖ ≤ ‖y‖ * ‖w‖ / ‖w‖ ^ 2 * ‖w‖ := by gcongr
      _ = ‖y‖ := by field_simp
  calc ‖pZ w y‖ ≤ ‖y‖ + ‖acoef w y • w‖ := norm_sub_le _ _
    _ ≤ 2 * ‖y‖ := by linarith

lemma isClosed_lipHyp {w : H} (hw : w ≠ 0) {τ : H → ℝ} {L : ℝ≥0}
    (hτ : LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) : IsClosed (lipHyp w τ) := by
  have he : lipHyp w τ = {x | acoef w x = τ (pZ w x)} := by ext x; exact mem_lipHyp_iff hw τ x
  rw [he]
  have hpc : Continuous (pZ w) := by unfold pZ acoef; fun_prop
  have hac : Continuous (acoef w) := by unfold acoef; fun_prop
  have hτc : Continuous (fun x => τ (pZ w x)) :=
    hτ.continuousOn.comp_continuous hpc (fun x => inner_pZ hw x)
  exact isClosed_eq hac hτc

lemma lipHyp_line_subsingleton {w : H} (hw : w ≠ 0) {τ : H → ℝ} {L : ℝ≥0}
    (hτ : LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) {u : H} (hu : (L : ℝ) * ‖pZ w u‖ < acoef w u) (x : H) :
    {s : ℝ | x + s • u ∈ lipHyp w τ}.Subsingleton := by
  intro s hs t ht
  simp only [mem_ofPred_eq, mem_lipHyp_iff hw] at hs ht
  rw [acoef_add, acoef_smul, pZ_add, pZ_smul] at hs ht
  have hd := hτ.dist_le_mul (pZ w x + s • pZ w u) (by simp [inner_add_left, real_inner_smul_left, inner_pZ hw])
    (pZ w x + t • pZ w u) (by simp [inner_add_left, real_inner_smul_left, inner_pZ hw])
  rw [← hs, ← ht, Real.dist_eq, dist_eq_norm] at hd
  have e1 : acoef w x + s * acoef w u - (acoef w x + t * acoef w u) = (s - t) * acoef w u := by ring
  have e2 : pZ w x + s • pZ w u - (pZ w x + t • pZ w u) = (s - t) • pZ w u := by
    rw [sub_smul]; abel
  rw [e1, e2, abs_mul, norm_smul, Real.norm_eq_abs] at hd
  by_contra hne
  have hpos : 0 < |s - t| := abs_pos.2 (sub_ne_zero.2 hne)
  have hau : 0 < acoef w u := lt_of_le_of_lt (by positivity) hu
  rw [abs_of_pos hau] at hd
  nlinarith [mul_lt_mul_of_pos_left hu hpos]

end Geom

end StatFormal.WaveP2b
