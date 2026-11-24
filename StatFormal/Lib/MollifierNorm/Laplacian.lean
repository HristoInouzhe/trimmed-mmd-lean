import StatFormal.Lib.FourierOps.Laplacian

/-!
# Real and complex Laplacians; the decay constant `C_b = ‖Δ^m b‖_{L¹}` (library, untrusted)

Mathlib's Laplacian `Δ` (`InnerProductSpace.instLaplacian`) acts on functions `V → F` for every normed space `F`. For a smooth
real function `b : V → ℝ` the Laplacian commutes with the real-to-complex embedding (`ContDiffAt.laplacian_CLM_comp_left` with
`Complex.ofRealCLM`), and so do its iterates, since the Laplacian of a smooth function is smooth (it is a finite sum of
second derivatives along an orthonormal basis). Hence the Fourier decay bound of `FourierOps.norm_fourier_le_laplacian`, stated
for `V → ℂ`, holds with the real constant `C_b = ∫ |Δ^m b|`:
`‖𝓕 b(ξ)‖ ≤ C_b (4π²‖ξ‖²)^{−m}` for `ξ ≠ 0`, for `b ∈ C_c^∞(V; ℝ)` (Folland, *Real Analysis*, Thm 8.22).
-/

noncomputable section
open MeasureTheory FourierTransform Laplacian
open scoped ContDiff

namespace StatFormal.MollifierNorm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian of a smooth function is smooth. -/
theorem contDiff_laplacian {f : V → F} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine ContDiff.sum fun i _ => ?_
  have h2 : ContDiff ℝ ∞ (iteratedFDeriv ℝ 2 f) := hf.iteratedFDeriv_right (by norm_num)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => V) F
    ![(stdOrthonormalBasis ℝ V) i, (stdOrthonormalBasis ℝ V) i]).contDiff.comp h2

/-- Iterated Laplacians of a smooth function are smooth. -/
theorem contDiff_laplacian_iterate {f : V → F} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ ((Δ : (V → F) → (V → F))^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact contDiff_laplacian ih

/-- The Laplacian commutes with the embedding `ℝ → ℂ`: `Δ (b : ℂ) = (Δ b : ℂ)` for smooth real `b`. -/
theorem laplacian_ofReal {f : V → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ (fun x => (f x : ℂ)) = fun x => ((Δ f) x : ℂ) := by
  funext x
  have h := (hf.contDiffAt (x := x)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)
  exact h.laplacian_CLM_comp_left (l := Complex.ofRealCLM)

/-- Iterated Laplacians commute with the embedding `ℝ → ℂ`. -/
theorem laplacian_iterate_ofReal (k : ℕ) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) :
    (Δ : (V → ℂ) → (V → ℂ))^[k] (fun x => (f x : ℂ)) = fun x => (((Δ : (V → ℝ) → (V → ℝ))^[k] f) x : ℂ) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, laplacian_ofReal hf]
    exact ih (contDiff_laplacian hf)

variable [MeasurableSpace V] [BorelSpace V]

/-- **Fourier decay with the real constant** `C_b = ∫ |Δ^m b|`: for `b ∈ C_c^∞(V; ℝ)` and `ξ ≠ 0`,
`‖𝓕 b(ξ)‖ ≤ C_b ((4π²‖ξ‖²)⁻¹)^m`. -/
theorem norm_fourier_ofReal_le_laplacian {b : V → ℝ} (hb : ContDiff ℝ ∞ b) (hbs : HasCompactSupport b) (m : ℕ)
    {ξ : V} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun x => (b x : ℂ)) ξ‖ ≤
      (∫ x, |((Δ : (V → ℝ) → (V → ℝ))^[m] b) x|) * ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹) ^ m := by
  have hbc : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp hb
  have hbcs : HasCompactSupport (fun x => (b x : ℂ)) := hbs.comp_left Complex.ofReal_zero
  have h := FourierOps.norm_fourier_le_laplacian hbc hbcs m hξ
  rw [laplacian_iterate_ofReal m hb] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

end StatFormal.MollifierNorm
