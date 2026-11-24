import StatFormal.Wave31tr.Statements
import StatFormal.Lib.KernelFacts.Line
import StatFormal.Wave31tc.RouteCore
import StatFormal.Wave31th.RouteGauss

/-!
# Wave 31tr, chunk M1: `gauss_qdens_formula`, `gauss_qdens_Q_Qprime` (T13)

`ψ v = φ (v 0)` on `ℝ¹` has the Gaussian Gram function (`KernelFacts.gauss_gram_line`), so the certified `Wave31th.gaussian_regular`
at `d = 1` gives `witFn g ψ` `C¹` with decay as `‖v‖ → ∞`; `witFn g φ = witFn g ψ ∘ lineEmb` is then `C¹` and tends to `0` at `±∞`
(`KernelFacts.contDiff_comp_lineEmb`, `tendsto_comp_lineEmb_atTop/atBot`), discharging the two regularity hypotheses of the
certified `Wave31tc.qdens_formula` and `Wave31tc.qdens_Q_Qprime`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tr.RouteMisc1

open StatFormal.KernelFacts

/-- For the Gaussian kernel on `ℝ`, every witness `x ↦ ⟪g, φ x⟫` is `C¹` and tends to `0` at `±∞`. -/
lemma gauss_line_regular {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {σ : ℝ} (hσ : 0 < σ)
    {φ : ℝ → H} (hk : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) (g : H) :
    ContDiff ℝ 1 (StatFormal.Wave12c.witFn g φ) ∧ Tendsto (StatFormal.Wave12c.witFn g φ) atTop (𝓝 0) ∧
      Tendsto (StatFormal.Wave12c.witFn g φ) atBot (𝓝 0) := by
  set ψ : EuclideanSpace ℝ (Fin 1) → H := fun v => φ (v 0) with hψ
  obtain ⟨hC, hT⟩ := StatFormal.Wave31th.gaussian_regular 1 H ψ σ hσ (gauss_gram_line hk) g
  have heq : StatFormal.Wave12c.witFn g φ = StatFormal.Wave12c.witFn g ψ ∘ lineEmb := by
    funext x; simp [StatFormal.Wave12c.witFn, ψ]
  rw [heq]
  exact ⟨contDiff_comp_lineEmb hC, tendsto_comp_lineEmb_atTop hT, tendsto_comp_lineEmb_atBot hT⟩

theorem gauss_qdens_formula_route : Claims.gauss_qdens_formula := by
  intro H _ _ _ σ φ g p U t hσ hk ht hex hder hU hLU hp hpos
  obtain ⟨hC, hT, hB⟩ := gauss_line_regular hσ hk g
  exact StatFormal.Wave31tc.qdens_formula _ p U t hC hT hB ht hex hder hU hLU hp hpos

theorem gauss_qdens_Q_Qprime_route : Claims.gauss_qdens_Q_Qprime := by
  intro H _ _ _ σ φ dstar p q U V tα uα hσ hk ht hex hder hU hLU hp hpos hu hexu hderu hV hLV hq hqpos
  obtain ⟨hC, hT, hB⟩ := gauss_line_regular hσ hk dstar
  exact StatFormal.Wave31tc.qdens_Q_Qprime H φ dstar p q U V tα uα hC hT hB ht hex hder hU hLU hp hpos hu hexu hderu hV hLV
    hq hqpos

end StatFormal.Wave31tr.RouteMisc1
