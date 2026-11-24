import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierL2.Agree

/-!
# Wave 31tp, route F: Fourier analysis on `V` (untrusted proof file)

L2 (`ft2_ae`) and L1 (`plancherel`) from `StatFormal.Lib.FourierL2.Agree` (tempered-distribution identification of the L² and
integral transforms, then Mathlib's unitary L² transform).
-/

noncomputable section
open MeasureTheory FourierTransform

namespace StatFormal.Wave31tp.RouteF

theorem ft2_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] {f : V → ℂ} (hf : MemLp f 2) :
    ft2 f = ⇑(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure V)) := by
  classical
  simp only [ft2, dif_pos hf]

theorem ft2_ae_route : Claims.ft2_ae := by
  intro V _ _ _ _ _ f hf1 hf2
  refine ⟨?_, FourierL2.fourierInv_toLp_ae hf1 hf2⟩
  rw [ft2_eq hf2]
  exact FourierL2.fourier_toLp_ae hf1 hf2

theorem plancherel_route : Claims.plancherel := by
  intro V _ _ _ _ _ f g hf1 hf2 hg1 hg2
  exact FourierL2.plancherel_L1L2 hf1 hf2 hg1 hg2

end StatFormal.Wave31tp.RouteF
