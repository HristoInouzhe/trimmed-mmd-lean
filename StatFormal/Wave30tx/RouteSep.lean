import StatFormal.Wave30tx.Statements

/-!
# Route: `lem:sepmargin (v2)` (untrusted proof material)

* `inner_nonneg_of_min'`: if `‖d‖² ≤ ‖d + s v‖²` for every `s ∈ (0,1]` then `⟨d, v⟩ ≥ 0`.
* `inner_ge_of_isMinNorm`: the first-order condition of the projection of the origin onto a convex set,
  `‖d‖² ≤ ⟨d, z⟩` for every `z ∈ K`.
* `sepmargin`: the claim.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace StatFormal.Wave30tx.RSep

open StatFormal.TrimmedMMD.Projection StatFormal.Wave30tx

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If `‖d‖² ≤ ‖d + s v‖²` for every `s ∈ (0,1]`, then `⟨d, v⟩ ≥ 0`. -/
theorem inner_nonneg_of_min' {d v : H}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖d‖ ^ 2 ≤ ‖d + s • v‖ ^ 2) : 0 ≤ ⟪d, v⟫_ℝ := by
  by_contra hc
  push Not at hc
  set c := ⟪d, v⟫_ℝ
  set N := ‖v‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  set s := min 1 (-c / (N + 1))
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsN : s * N ≤ -c := by
    have h1 : s ≤ -c / (N + 1) := min_le_right _ _
    have h2 : s * N ≤ -c / (N + 1) * N := mul_le_mul_of_nonneg_right h1 hN
    have h3 : -c / (N + 1) * N ≤ -c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have key := h s hs0 hs1
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at key
  have : 0 ≤ s * (2 * c + s * N) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).1 this
  linarith

/-- First-order condition: for a minimum-norm element `d` of a convex `K`, `‖d‖² ≤ ⟨d, z⟩` on `K`. -/
theorem inner_ge_of_isMinNorm {K : Set H} {d : H} (hK : Convex ℝ K) (hd : IsMinNorm K d) {z : H}
    (hz : z ∈ K) : ‖d‖ ^ 2 ≤ ⟪d, z⟫_ℝ := by
  have key : 0 ≤ ⟪d, z - d⟫_ℝ := by
    refine inner_nonneg_of_min' fun s hs0 hs1 => ?_
    have hmem : d + s • (z - d) ∈ K := by
      have := hK hd.1 hz (by linarith : (0 : ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]; abel
    exact pow_le_pow_left₀ (norm_nonneg _) (hd.2 _ hmem) 2
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at key
  linarith

/-- The first-order condition in the direction `f* = d/‖d‖`: `‖d‖ ≤ ⟨f*, z⟩` on `K`. -/
theorem norm_le_inner_dir {K : Set H} {d : H} (hK : Convex ℝ K) (hd : IsMinNorm K d)
    (hD : 0 < ‖d‖) {z : H} (hz : z ∈ K) : ‖d‖ ≤ ⟪‖d‖⁻¹ • d, z⟫_ℝ := by
  have h := inner_ge_of_isMinNorm hK hd hz
  rw [real_inner_smul_left, le_inv_mul_iff₀ hD]
  nlinarith

/-- For unit vectors, `⟨u, f⟩ = 1 − ‖u − f‖²/2`. -/
theorem inner_unit {u f : H} (hu : ‖u‖ = 1) (hf : ‖f‖ = 1) : ⟪u, f⟫_ℝ = 1 - ‖u - f‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, hu, hf]; ring

/-- `‖d‖⁻¹ • d` is a unit vector. -/
theorem norm_dir {d : H} (hD : 0 < ‖d‖) : ‖‖d‖⁻¹ • d‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']

/-- The identity `‖d' − d‖² = (‖d'‖ − ‖d‖)² + ‖d'‖‖d‖‖d'/‖d'‖ − d/‖d‖‖²`. -/
theorem norm_sub_sq_dir {d d' : H} (hD : 0 < ‖d‖) (hD' : 0 < ‖d'‖) :
    ‖d' - d‖ ^ 2 = (‖d'‖ - ‖d‖) ^ 2 + ‖d'‖ * ‖d‖ * ‖‖d'‖⁻¹ • d' - ‖d‖⁻¹ • d‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_dir hD, norm_dir hD', real_inner_smul_left,
    real_inner_smul_right]
  field_simp
  ring

theorem sepmargin : Claims.sepmargin := by
  intro H _ _ K dstar hK hd hD D fstar
  have hfnorm : ‖fstar‖ = 1 := norm_dir hD
  have hfd : ⟪fstar, dstar⟫_ℝ = D := by
    change ⟪‖dstar‖⁻¹ • dstar, dstar⟫_ℝ = ‖dstar‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hfoc : ∀ z ∈ K, D ≤ ⟪fstar, z⟫_ℝ := fun z hz => norm_le_inner_dir hK hd hD hz
  have h1 : ∀ f : H, sepK K f ≤ ((⟪f, dstar⟫_ℝ : ℝ) : EReal) := fun f => iInf₂_le dstar hd.1
  have h2 : sepK K fstar = (D : EReal) := by
    apply le_antisymm
    · simpa [hfd] using h1 fstar
    · exact le_iInf₂ fun z hz => EReal.coe_le_coe_iff.2 (hfoc z hz)
  refine ⟨h1, h2, ⟨⟨fstar, by simp [hfnorm], h2⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    refine (h1 f).trans (EReal.coe_le_coe_iff.2 ?_)
    have hf' : ‖f‖ ≤ 1 := by simpa using hf
    calc ⟪f, dstar⟫_ℝ ≤ ‖f‖ * ‖dstar‖ := real_inner_le_norm _ _
      _ ≤ 1 * D := by gcongr
      _ = D := one_mul _
  · intro u hu
    have hds : dstar = D • fstar := by
      change dstar = ‖dstar‖ • (‖dstar‖⁻¹ • dstar)
      rw [smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
    have hle : sepK K u ≤ ((D - D / 2 * ‖u - fstar‖ ^ 2 : ℝ) : EReal) := by
      refine (h1 u).trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
      rw [hds, real_inner_smul_right, inner_unit hu hfnorm]; ring
    rw [h2]
    calc ((D / 2 * ‖u - fstar‖ ^ 2 : ℝ) : EReal)
        = (D : EReal) - ((D - D / 2 * ‖u - fstar‖ ^ 2 : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; congr 1; ring
      _ ≤ (D : EReal) - sepK K u := EReal.sub_le_sub le_rfl hle
  · intro d' hd'
    exact norm_sub_sq_dir hD hd'

end StatFormal.Wave30tx.RSep
