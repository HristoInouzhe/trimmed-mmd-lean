import StatFormal.Wave31tp.Statements
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Bessel potentials by Gaussian subordination: the integrand, continuity, positivity (library, untrusted)

On a finite-dimensional real inner-product space `V` of dimension `d = finrank ℝ V`, the Bessel potential (Matérn profile)
`G_s(x) = Γ(s)⁻¹ ∫₀^∞ t^{s−1} e^{−t} (4πt)^{−d/2} e^{−‖x‖²/(4t)} dt` (`Wave31tp.besselPot`; Stein, *Singular Integrals*, V.3.1,
with `α = 2s`) is, for `s > d/2`:

* well defined: the integrand (`integrand`) is integrable on `(0, ∞)` for every `x` (`integrableOn_integrand`), since it is
  dominated by its value at `x = 0`, which is `(4π)^{−d/2} t^{(s − d/2) − 1} e^{−t}` (`integrand_zero_eq`), a Gamma integrand;
* continuous (`continuous_besselPot`), by dominated convergence with the same bound;
* positive (`besselPot_pos`) and maximal at the origin (`besselPot_le_zero`).

The case `d = 0` is included (then `s > 0` and `G_s ≡ 1`). The Fourier side is in `Lib/Matern/Fourier.lean`.
-/

noncomputable section
open MeasureTheory Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatFormal.Matern

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The subordination integrand `t^{s−1} e^{−t} (4πt)^{−d/2} e^{−‖x‖²/(4t)}`, `d = finrank ℝ V`. -/
def integrand (s : ℝ) (x : V) (t : ℝ) : ℝ :=
  t ^ (s - 1) * Real.exp (-t) * (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- `besselPot` unfolds to `Γ(s)⁻¹` times the integral of `integrand` over `(0, ∞)`. -/
lemma besselPot_eq (s : ℝ) (x : V) : besselPot s x = (Real.Gamma s)⁻¹ * ∫ t in Ioi (0 : ℝ), integrand s x t := rfl

/-- The integrand is positive for `t > 0`. -/
lemma integrand_pos (s : ℝ) (x : V) {t : ℝ} (ht : 0 < t) : 0 < integrand s x t := by
  unfold integrand
  positivity

/-- For `t > 0` the integrand is largest at `x = 0` (`e^{−‖x‖²/(4t)} ≤ 1`). -/
lemma integrand_le_zero (s : ℝ) (x : V) {t : ℝ} (ht : 0 < t) : integrand s x t ≤ integrand s (0 : V) t := by
  unfold integrand
  have hc : 0 ≤ t ^ (s - 1) * Real.exp (-t) * (4 * Real.pi * t) ^ (-(Module.finrank ℝ V : ℝ) / 2) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [Real.exp_le_exp, norm_zero]
  have : 0 ≤ ‖x‖ ^ 2 / (4 * t) := by positivity
  rw [neg_div, neg_div]
  simpa using this

/-- At `x = 0` the integrand is a Gamma integrand: `(4π)^{−d/2} e^{−t} t^{(s − d/2) − 1}` for `t > 0`. -/
lemma integrand_zero_eq (s : ℝ) {t : ℝ} (ht : 0 < t) :
    integrand s (0 : V) t = (4 * Real.pi) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
      (Real.exp (-t) * t ^ ((s - (Module.finrank ℝ V : ℝ) / 2) - 1)) := by
  simp only [integrand, norm_zero]
  rw [Real.mul_rpow (by positivity) ht.le,
    show s - (Module.finrank ℝ V : ℝ) / 2 - 1 = (s - 1) + (-(Module.finrank ℝ V : ℝ) / 2) by ring, Real.rpow_add ht]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- The integrand is jointly measurable in `(x, t)`. -/
lemma measurable_integrand (s : ℝ) : Measurable (Function.uncurry (integrand (V := V) s)) := by
  unfold Function.uncurry integrand
  fun_prop

/-- The integrand is measurable in `t` for each `x`. -/
lemma measurable_integrand_t (s : ℝ) (x : V) : Measurable (integrand s x) :=
  (measurable_integrand (V := V) s).comp measurable_prodMk_left

/-- The integrand at `x = 0` is integrable on `(0, ∞)` when `s > d/2`. -/
lemma integrableOn_integrand_zero {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) :
    IntegrableOn (integrand s (0 : V)) (Ioi 0) :=
  IntegrableOn.congr_fun ((Real.GammaIntegral_convergent (by linarith : 0 < s - (Module.finrank ℝ V : ℝ) / 2)).const_mul
    ((4 * Real.pi) ^ (-(Module.finrank ℝ V : ℝ) / 2))) (fun _ ht => (integrand_zero_eq s ht).symm)
    measurableSet_Ioi

/-- The domination `|integrand s x t| ≤ integrand s 0 t`, almost everywhere on `(0, ∞)`. -/
lemma norm_integrand_le (s : ℝ) (x : V) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ‖integrand s x t‖ ≤ integrand s (0 : V) t := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (integrand_pos s x ht)]
  exact integrand_le_zero s x ht

/-- **The subordination integral converges**: for `s > d/2` the integrand is integrable on `(0, ∞)` for every `x`. -/
theorem integrableOn_integrand {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (x : V) :
    IntegrableOn (integrand s x) (Ioi 0) :=
  Integrable.mono' (integrableOn_integrand_zero hs) (measurable_integrand_t s x).aestronglyMeasurable
    (norm_integrand_le s x)

/-- **Continuity of the Bessel potential** `G_s`, `s > d/2` (dominated convergence). -/
theorem continuous_besselPot {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) : Continuous (besselPot (V := V) s) := by
  have h : Continuous fun x : V => ∫ t in Ioi (0 : ℝ), integrand s x t :=
    continuous_of_dominated (fun x => (measurable_integrand_t s x).aestronglyMeasurable) (norm_integrand_le s)
      (integrableOn_integrand_zero hs) (ae_of_all _ fun t => by unfold integrand; fun_prop)
  exact continuous_const.mul h

/-- `0 < Γ(s)` for `s > d/2 ≥ 0`. -/
lemma Gamma_pos {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) : 0 < Real.Gamma s :=
  Real.Gamma_pos_of_pos (lt_of_le_of_lt (by positivity) hs)

/-- **Positivity of the Bessel potential**: `0 < G_s(x)` for `s > d/2`. -/
theorem besselPot_pos {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (x : V) : 0 < besselPot s x := by
  refine mul_pos (inv_pos.2 (Gamma_pos hs)) ?_
  show 0 < ∫ t in Ioi (0 : ℝ), integrand s x t
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => (integrand_pos s x ht).le))
    (integrableOn_integrand hs x)]
  have : Function.support (integrand s x) ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.2 fun t ht => (integrand_pos s x ht).ne'
  rw [this, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **The Bessel potential is maximal at the origin**: `G_s(x) ≤ G_s(0)` for `s > d/2`. -/
theorem besselPot_le_zero {s : ℝ} (hs : (Module.finrank ℝ V : ℝ) / 2 < s) (x : V) :
    besselPot s x ≤ besselPot s (0 : V) :=
  mul_le_mul_of_nonneg_left (setIntegral_mono_on (integrableOn_integrand hs x) (integrableOn_integrand_zero hs)
    measurableSet_Ioi fun _ ht => integrand_le_zero s x ht) (inv_nonneg.2 (Gamma_pos hs).le)

end StatFormal.Matern
