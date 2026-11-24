import StatFormal.Lib.ChiSquare.Whitening
import TauCeti.Probability.Distributions.Gaussian.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Route — a centred Gaussian with injective covariance on a finite-dimensional space is absolutely continuous
(untrusted)

Whitening (`Foundations/ChiSquare`, `map_whiten`): `W#ν = N(0, I_n)`. The linear isomorphism
`G x = Σ_i √λ_i x_i b_i` inverts `W` (`G(W z) = Σ_i ⟪b_i, z⟫ b_i = z`), so `ν = G#(γ^n)`; `γ^n ≪ Leb^n` (Tau Ceti
`pi_gaussianReal_eq_withDensity`) and `G#Leb^n` is a Haar measure on `E`, hence `≪ volume`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP2b

open StatFormal.ChiSquare

section AC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The colouring isomorphism `G x = Σ_i √λ_i x_i b_i`. -/
def colourEquiv (ν : Measure E) [IsGaussian ν] (hm : ∫ z, z ∂ν = 0)
    (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) :
    (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E :=
  (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (eigval ν i))
    (Real.sqrt_pos.2 (eigval_pos ν hm hinj i)).ne').trans (eigB ν).toBasis.equivFun.symm

lemma colourEquiv_apply (ν : Measure E) [IsGaussian ν] (hm : ∫ z, z ∂ν = 0)
    (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) (x : Fin (Module.finrank ℝ E) → ℝ) :
    colourEquiv ν hm hinj x = ∑ i, (Real.sqrt (eigval ν i) * x i) • eigB ν i := by
  show (eigB ν).repr.symm _ = _
  rw [← OrthonormalBasis.sum_repr_symm]
  simp

lemma colourEquiv_whiten (ν : Measure E) [IsGaussian ν] (hm : ∫ z, z ∂ν = 0)
    (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) (z : E) :
    colourEquiv ν hm hinj (WithLp.ofLp (whiten ν z)) = z := by
  rw [colourEquiv_apply]
  conv_rhs => rw [← (eigB ν).sum_repr' z]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : Real.sqrt (eigval ν i) ≠ 0 := (Real.sqrt_pos.2 (eigval_pos ν hm hinj i)).ne'
  congr 1
  rw [show (WithLp.ofLp (whiten ν z)) i = whiten ν z i from rfl, whiten_apply]
  field_simp

theorem gaussian_ac (ν : Measure E) [IsGaussian ν] (hm : ∫ z, z ∂ν = 0)
    (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) : ν ≪ volume := by
  set G := colourEquiv ν hm hinj
  have hGc : Continuous G := G.toContinuousLinearEquiv.continuous
  have hW : Measurable (whiten ν) := (whiten ν).continuous.measurable
  have h1 : ν.map (fun z => G (WithLp.ofLp (whiten ν z))) = ν := by
    have : (fun z => G (WithLp.ofLp (whiten ν z))) = id := by
      funext z; exact colourEquiv_whiten ν hm hinj z
    rw [this, Measure.map_id]
  have h2 : ν.map (fun z => G (WithLp.ofLp (whiten ν z))) =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map G := by
    rw [show (fun z => G (WithLp.ofLp (whiten ν z))) = G ∘ (WithLp.ofLp ∘ whiten ν) from rfl,
      ← Measure.map_map hGc.measurable ((WithLp.measurable_ofLp _ _).comp hW),
      ← Measure.map_map (WithLp.measurable_ofLp _ _) hW, map_whiten ν hm hinj,
      ← map_pi_eq_stdGaussian, Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _)]
    have : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin (Module.finrank ℝ E) → ℝ) → _) = id := by
      funext x; rfl
    rw [this, Measure.map_id]
  have hν : ν = (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map G := h1.symm.trans h2
  rw [hν]
  have h2 : (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) ≪
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => (volume : Measure ℝ)) := by
    rw [TauCeti.Probability.pi_gaussianReal_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  refine (h2.map hGc.measurable).trans ?_
  have : (Measure.pi fun _ : Fin (Module.finrank ℝ E) => (volume : Measure ℝ)).map G =
      (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)).map G := by rw [volume_pi]
  rw [this]
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

end AC

end StatFormal.WaveP2b
