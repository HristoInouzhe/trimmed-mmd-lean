import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierL2.Agree

/-!
# Translations and the L² modulus of continuity (library, untrusted)

For `f ∈ L¹ ∩ L²` on a finite-dimensional real inner-product space `V` and `h ∈ V`, the Fourier transform turns translation into
a phase, `𝓕 (f(· + h))(ξ) = 𝐞(⟪h, ξ⟫) 𝓕 f(ξ)` (Mathlib's `VectorFourier.fourierIntegral_comp_add_right`), so Plancherel's identity
(`FourierL2.plancherel_L1L2`) for `f(· + h) − f` gives `∫ |𝓕 f|² |𝐞(⟪h, ξ⟫) − 1|² = ‖f(· + h) − f‖₂²` (Stein–Weiss, Ch. I §§1–2).
For an indicator, `|1_E(x + h) − 1_E(x)|² = 1_{E ∆ (E − h)}(x)`, so the L² modulus is the measure of a symmetric difference,
and translation invariance of Lebesgue measure gives `vol (E ∆ (E − h)) = vol (E ∆ (E + h))`.
-/

noncomputable section
open MeasureTheory FourierTransform Set
open scoped InnerProductSpace RealInnerProductSpace symmDiff

set_option linter.unusedSectionVars false

namespace StatFormal.FourierOps

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Translation becomes a phase**: `𝓕 (f(· + h))(ξ) = 𝐞(⟪h, ξ⟫) 𝓕 f(ξ)`; no integrability needed. -/
theorem fourier_comp_add_right (f : V → ℂ) (h ξ : V) :
    𝓕 (fun x => f (x + h)) ξ = (𝐞 ⟪h, ξ⟫ : ℂ) * 𝓕 f ξ := by
  have := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ V) f h) ξ
  simp only [Circle.smul_def] at this
  exact this

/-- The Fourier transform of the increment `f(· + h) − f` of an integrable `f`. -/
theorem fourier_increment {f : V → ℂ} (hf : Integrable f) (h ξ : V) :
    𝓕 (fun x => f (x + h) - f x) ξ = ((𝐞 ⟪h, ξ⟫ : ℂ) - 1) * 𝓕 f ξ := by
  have hfh : Integrable (fun x => f (x + h)) := hf.comp_add_right h
  calc 𝓕 (fun x => f (x + h) - f x) ξ = 𝓕 (fun x => f (x + h)) ξ - 𝓕 f ξ := by
        simp only [Real.fourier_eq, smul_sub]
        exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hfh)
          ((Real.fourierIntegral_convergent_iff ξ).2 hf)
    _ = ((𝐞 ⟪h, ξ⟫ : ℂ) - 1) * 𝓕 f ξ := by rw [fourier_comp_add_right]; ring

/-- **Plancherel for translations**: for `f ∈ L¹ ∩ L²`, `∫ |𝓕 f|² |𝐞(⟪h, ξ⟫) − 1|² = ∫ |f(x + h) − f(x)|²`. -/
theorem integral_norm_fourier_sq_mul_phase {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) (h : V) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 * ‖(𝐞 ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 = ∫ x, ‖f (x + h) - f x‖ ^ 2 := by
  have hg1 : Integrable (fun x => f (x + h) - f x) := (hf1.comp_add_right h).sub hf1
  have hg2 : MemLp (fun x => f (x + h) - f x) 2 :=
    (hf2.comp_measurePreserving (measurePreserving_add_right volume h)).sub hf2
  have hP := (FourierL2.plancherel_L1L2 hg1 hg2 hg1 hg2).2.1
  rw [← hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [fourier_increment hf1 h ξ, norm_mul, mul_pow]
  ring

/-- The squared increment of an indicator is the indicator of a symmetric difference:
`|1_E(x + h) − 1_E(x)|² = 1_{E ∆ (E − h)}(x)`, with `E − h = (· + h) ⁻¹' E`. -/
theorem norm_indicator_increment_sq (E : Set V) (h x : V) :
    ‖E.indicator (fun _ => (1 : ℂ)) (x + h) - E.indicator (fun _ => (1 : ℂ)) x‖ ^ 2 =
      (E ∆ ((· + h) ⁻¹' E)).indicator (1 : V → ℝ) x := by
  by_cases hx : x ∈ E <;> by_cases hxh : x + h ∈ E <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hxh, Set.mem_symmDiff]

/-- **The L² modulus of an indicator**: `∫ |1_E(x + h) − 1_E(x)|² = vol (E ∆ (E − h))` (as a real number). -/
theorem integral_norm_indicator_increment_sq {E : Set V} (hE : MeasurableSet E) (h : V) :
    ∫ x, ‖E.indicator (fun _ => (1 : ℂ)) (x + h) - E.indicator (fun _ => (1 : ℂ)) x‖ ^ 2 =
      (volume (E ∆ ((· + h) ⁻¹' E))).toReal := by
  have hm : MeasurableSet (E ∆ ((· + h) ⁻¹' E)) := hE.symmDiff (measurable_add_const h hE)
  simp_rw [norm_indicator_increment_sq]
  rw [integral_indicator_one hm, measureReal_def]

/-- Translation invariance of the symmetric-difference measure: `vol (E ∆ (E − h)) = vol (E ∆ (E + h))`. -/
theorem volume_symmDiff_add_eq_sub (E : Set V) (h : V) :
    volume (E ∆ ((· + h) ⁻¹' E)) = volume (E ∆ ((· - h) ⁻¹' E)) := by
  rw [← measure_preimage_add_right volume (-h) (E ∆ ((· + h) ⁻¹' E)), preimage_symmDiff, symmDiff_comm]
  congr 2
  · ext x; simp
  · ext x; simp [sub_eq_add_neg]

end StatFormal.FourierOps
