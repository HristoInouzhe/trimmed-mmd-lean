import StatFormal.Lib.DiffEntropy.Basic

/-!
# Gaussian maximum-entropy bounds for the differential entropy on `ℝᵈ`

Lebesgue measure on `ℝᵈ = EuclideanSpace ℝ (Fin d)` (`volume`), on `ℝᵈ × ℝᵈ` the product `volume.prod volume`
(definitionally the product `volume`). `p_s(u) = ∏ᵢ φ_s(uᵢ)` is the `N(0, s I_d)` density (`gdens d s`; the same
formula as `SchrodingerPathD.gdens`, re-proved here so that this library imports Mathlib only).

* `lintegral_gdens_shift`: `∫ p_s(x − a) dx = 1` (`s > 0`).
* `negPart_integrable_P2`: for `ρ ≪ Leb` with `∫ ‖x‖² dρ < ∞` the negative part of `log dρ/dLeb` is integrable,
  i.e. the differential entropy is `< +∞` in the extended sense (so it is either finite or `−∞`).
* `relEnt_le_gauss`: `Ent(ρ) ≤ (d/2) log(2πs) + ∫ ‖x − a‖² dρ / (2s)` for all `s > 0`, `a`.
* `relEnt_le_cov`: with `a = E X`, `V = E‖X − EX‖² = tr Cov(ρ)`: `Ent(ρ) ≤ (d/2) log(2πe V/d)` (`d ≥ 1`, `V > 0`).
* `negPart_integrable_P2_prod`: the same negative-part statement on `ℝᵈ × ℝᵈ` for a measure whose marginals are
  in `𝒫₂`.
-/

noncomputable section
open MeasureTheory Set InformationTheory Filter
open scoped ENNReal

set_option linter.style.longLine false

namespace StatFormal.DiffEntropy

local notation "E" d => EuclideanSpace ℝ (Fin d)

open ProbabilityTheory

variable {d : ℕ}

/-- `p_s(u) = ∏ᵢ φ_s(uᵢ)`, the Lebesgue density of `N(0, s I_d)`. -/
def gdens (d : ℕ) (s : ℝ) (u : E d) : ℝ := ∏ i, gaussianPDFReal 0 s.toNNReal (u i)

lemma gdens_pos {s : ℝ} (hs : 0 < s) (u : E d) : 0 < gdens d s u := by
  have hv : s.toNNReal ≠ 0 := by simpa using hs
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 _ _ hv

lemma measurable_gdens (s : ℝ) : Measurable (gdens d s) := by
  unfold gdens
  exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 _).comp (by fun_prop)

lemma log_gaussPDF_zero {s : ℝ} (hs : 0 < s) (u : ℝ) :
    Real.log (gaussianPDFReal 0 s.toNNReal u) = -(Real.log (2 * Real.pi * s) / 2) - u ^ 2 / (2 * s) := by
  have hv : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.le
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_inv, hv,
    Real.log_sqrt (by positivity)]
  ring

lemma log_gdens {s : ℝ} (hs : 0 < s) (u : E d) :
    Real.log (gdens d s u) = -(d * Real.log (2 * Real.pi * s) / 2) - ‖u‖ ^ 2 / (2 * s) := by
  have hv : s.toNNReal ≠ 0 := by simpa using hs
  rw [gdens, Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 _ _ hv).ne')]
  simp_rw [log_gaussPDF_zero hs]
  rw [Finset.sum_sub_distrib, EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma lintegral_gdens {s : ℝ} (hs : 0 < s) : ∫⁻ x, ENNReal.ofReal (gdens d s x) ∂(volume : Measure (E d)) = 1 := by
  have hv : s.toNNReal ≠ 0 := by simpa using hs
  rw [← (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp (measurable_gdens s).ennreal_ofReal]
  simp only [gdens, PiLp.toLp_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [volume_pi, integral_fintype_prod_eq_prod (f := fun _ x => gaussianPDFReal 0 s.toNNReal x)]
    simp [integral_gaussianPDFReal_eq_one 0 hv]
  · rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ x => gaussianPDFReal 0 s.toNNReal x)
      (fun i => integrable_gaussianPDFReal 0 _)
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 _ _

lemma lintegral_gdens_shift {s : ℝ} (hs : 0 < s) (a : E d) :
    ∫⁻ x, ENNReal.ofReal (gdens d s (x - a)) ∂(volume : Measure (E d)) = 1 := by
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (gdens d s x)) a, lintegral_gdens hs]

lemma integrable_normsq_sub {ρ : Measure (E d)} [IsFiniteMeasure ρ] (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ)
    (a : E d) : Integrable (fun x : E d => ‖x - a‖ ^ 2) ρ := by
  refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * ‖a‖ ^ 2))) (by fun_prop)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := norm_sub_le x a
  have h0 : 0 ≤ ‖x - a‖ := norm_nonneg _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x‖ - ‖a‖), norm_nonneg x, norm_nonneg a]

lemma log_gdens_shift {s : ℝ} (hs : 0 < s) (a x : E d) :
    Real.log (gdens d s (x - a)) = -(d * Real.log (2 * Real.pi * s) / 2) - ‖x - a‖ ^ 2 / (2 * s) :=
  log_gdens hs _

lemma integrable_log_gdens {ρ : Measure (E d)} [IsFiniteMeasure ρ] (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ)
    {s : ℝ} (hs : 0 < s) (a : E d) : Integrable (fun x => Real.log (gdens d s (x - a))) ρ := by
  simp_rw [log_gdens_shift hs]
  exact (integrable_const _).sub ((integrable_normsq_sub h2 a).div_const _)

lemma integral_log_gdens {ρ : Measure (E d)} [IsProbabilityMeasure ρ] (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ)
    {s : ℝ} (hs : 0 < s) (a : E d) :
    ∫ x, Real.log (gdens d s (x - a)) ∂ρ = -(d * Real.log (2 * Real.pi * s) / 2) - (∫ x, ‖x - a‖ ^ 2 ∂ρ) / (2 * s) := by
  simp_rw [log_gdens_shift hs]
  rw [integral_sub (integrable_const _) ((integrable_normsq_sub h2 a).div_const _), integral_const,
    integral_div]
  simp

/-- In `𝒫₂`, `Ent(ρ) < +∞`: the negative part of `log dρ/dLeb` is `ρ`-integrable. -/
theorem negPart_integrable_P2 {ρ : Measure (E d)} [IsProbabilityMeasure ρ] (hρ : ρ ≪ volume)
    (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ) :
    Integrable (fun x => max (-llr ρ volume x) 0) ρ :=
  gibbs_negPart hρ (show Measurable (fun x : E d => gdens d 1 (x - 0)) from (measurable_gdens 1).comp (measurable_sub_const 0)) (fun x => gdens_pos one_pos _)
    (lintegral_gdens_shift one_pos 0).le (integrable_log_gdens h2 one_pos 0)

/-- Gaussian bound: `Ent(ρ) ≤ (d/2) log(2πs) + ∫ ‖x − a‖² dρ / (2s)`. -/
theorem relEnt_le_gauss {ρ : Measure (E d)} [IsProbabilityMeasure ρ] (hρ : FiniteEnt ρ volume)
    (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ) {s : ℝ} (hs : 0 < s) (a : E d) :
    relEnt ρ volume ≤ d * Real.log (2 * Real.pi * s) / 2 + (∫ x, ‖x - a‖ ^ 2 ∂ρ) / (2 * s) := by
  have := gibbs_le hρ (show Measurable (fun x : E d => gdens d s (x - a)) from (measurable_gdens s).comp (measurable_sub_const a)) (fun x => gdens_pos hs _)
    (lintegral_gdens_shift hs a).le (integrable_log_gdens h2 hs a)
  rw [integral_log_gdens h2 hs a] at this
  linarith

/-- Gaussian maximum-entropy bound: `Ent(ρ) ≤ (d/2) log(2πe · V/d)`, `V = ∫ ‖x − m‖² dρ = tr Cov(ρ)`,
`m = ∫ x dρ`. -/
theorem relEnt_le_cov {ρ : Measure (E d)} [IsProbabilityMeasure ρ] (hρ : FiniteEnt ρ volume)
    (h2 : Integrable (fun x : E d => ‖x‖ ^ 2) ρ) (hd : 0 < d) (hV : 0 < ∫ x, ‖x - ∫ y, y ∂ρ‖ ^ 2 ∂ρ) :
    relEnt ρ volume ≤
      d / 2 * Real.log (2 * Real.pi * Real.exp 1 * ((∫ x, ‖x - ∫ y, y ∂ρ‖ ^ 2 ∂ρ) / d)) := by
  set V := ∫ x, ‖x - ∫ y, y ∂ρ‖ ^ 2 ∂ρ
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hs : 0 < V / d := div_pos hV hdR
  have h := relEnt_le_gauss hρ h2 hs (∫ y, y ∂ρ)
  have hrw : V / (2 * (V / d)) = d / 2 := by field_simp
  rw [hrw] at h
  rw [show 2 * Real.pi * Real.exp 1 * (V / d) = Real.exp 1 * (2 * Real.pi * (V / d)) by ring,
    Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  nlinarith

/-- On `ℝᵈ × ℝᵈ`: a measure `≪ Leb` whose marginals have finite second moments has an integrable negative part of
`log dπ/dLeb` (Gibbs against `p₁(x) p₁(y)`). -/
theorem negPart_integrable_P2_prod {π : Measure ((E d) × (E d))} [IsProbabilityMeasure π]
    (hπ : π ≪ (volume : Measure (E d)).prod volume)
    (h1 : Integrable (fun z : (E d) × (E d) => ‖z.1‖ ^ 2) π) (h2 : Integrable (fun z : (E d) × (E d) => ‖z.2‖ ^ 2) π) :
    Integrable (fun z => max (-llr π ((volume : Measure (E d)).prod volume) z) 0) π := by
  have hg : Measurable fun z : (E d) × (E d) => gdens d 1 z.1 * gdens d 1 z.2 :=
    ((measurable_gdens 1).comp measurable_fst).mul ((measurable_gdens 1).comp measurable_snd)
  refine gibbs_negPart hπ hg (fun z => mul_pos (gdens_pos one_pos _) (gdens_pos one_pos _)) ?_ ?_
  · have : (fun z : (E d) × (E d) => ENNReal.ofReal (gdens d 1 z.1 * gdens d 1 z.2)) =
        fun z => ENNReal.ofReal (gdens d 1 z.1) * ENNReal.ofReal (gdens d 1 z.2) := by
      funext z; rw [ENNReal.ofReal_mul (gdens_pos one_pos _).le]
    rw [this, lintegral_prod_mul (f := fun x : E d => ENNReal.ofReal (gdens d 1 x))
      (g := fun x : E d => ENNReal.ofReal (gdens d 1 x)) (measurable_gdens 1).ennreal_ofReal.aemeasurable
      (measurable_gdens 1).ennreal_ofReal.aemeasurable, lintegral_gdens one_pos, one_mul]
  · have e : (fun z : (E d) × (E d) => Real.log (gdens d 1 z.1 * gdens d 1 z.2)) =
        fun z => (-(d * Real.log (2 * Real.pi * 1) / 2) - ‖z.1‖ ^ 2 / (2 * 1)) +
          (-(d * Real.log (2 * Real.pi * 1) / 2) - ‖z.2‖ ^ 2 / (2 * 1)) := by
      funext z
      rw [Real.log_mul (gdens_pos one_pos _).ne' (gdens_pos one_pos _).ne', log_gdens one_pos, log_gdens one_pos]
    rw [e]
    exact ((integrable_const _).sub (h1.div_const _)).add ((integrable_const _).sub (h2.div_const _))

end StatFormal.DiffEntropy
