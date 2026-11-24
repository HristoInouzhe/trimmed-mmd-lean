import StatFormal.Lib.FourierTaylor.Taylor
import StatFormal.Wave31tp.Statements

/-!
# Fourier transforms of measures with matching moments (library, untrusted)

Let `ρ₁, ρ₂` be finite measures on `ℝ` carried by `[x₀ − W, x₀ + W]` whose moments `∫ (x − x₀)^j` agree for `j < N`. Then
`‖ftMeas ρ₁ ξ − ftMeas ρ₂ ξ‖ ≤ (ρ₁(ℝ) + ρ₂(ℝ)) · min{1, (2π|ξ|W)^N / N!}` (the classical moment-decay estimate behind Durrett,
Thm 3.3.20; eq:newmomentdecay of the trimmed-mmd supplement).

Route: `𝐞(−xξ) = 𝐞(−x₀ξ) · e^{it}` with `t = −2πξ(x − x₀)`; the Taylor polynomial of `e^{it}` of order `N` integrates to a
combination of the moments `∫ (x − x₀)^j dρ`, and the remainder is bounded by `|t|^N / N! ≤ (2π|ξ|W)^N / N!` on the interval
(`norm_expIRem_le`). The `1` in the minimum is the trivial bound `‖ftMeas ρ ξ‖ ≤ ρ(ℝ)`.

* `norm_ftMeas_sub_moments_le`: one measure, `ftMeas ρ ξ` minus its moment expansion is at most `ρ(ℝ) (2π|ξ|W)^N / N!`;
* `norm_ftMeas_sub_le_of_moments`: the two-measure estimate with the minimum.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Complex Real
open scoped Nat FourierTransform InnerProductSpace

namespace StatFormal.FourierTaylor

open StatFormal.Wave31tp

/-- The trivial bound: the Fourier transform of a finite measure is bounded by its mass. -/
lemma norm_ftMeas_le_mass (ρ : Measure ℝ) [IsFiniteMeasure ρ] (ξ : ℝ) : ‖ftMeas ρ ξ‖ ≤ ρ.real univ := by
  unfold ftMeas
  simpa using norm_integral_le_of_norm_le_const (μ := ρ) (C := 1) (ae_of_all _ fun x => by simp)

/-- The phase factorisation `𝐞(−xξ) = 𝐞(−x₀ξ) · e^{it}`, `t = −2πξ(x − x₀)`. -/
lemma fourierChar_phase (x x₀ ξ : ℝ) :
    (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) = (𝐞 (-(x₀ * ξ)) : ℂ) * Complex.exp (((-2 * π * ξ * (x - x₀) : ℝ) : ℂ) * I) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The Taylor coefficients of `x ↦ e^{−2πiξ(x − x₀)}` in powers of `x − x₀`. -/
lemma taylor_term (x x₀ ξ : ℝ) (j : ℕ) :
    (((-2 * π * ξ * (x - x₀) : ℝ) : ℂ) * I) ^ j / (j.factorial : ℂ) =
      (-2 * π * ξ * I) ^ j / (j ! : ℂ) * (((x - x₀) ^ j : ℝ) : ℂ) := by
  push_cast
  rw [div_mul_eq_mul_div, ← mul_pow]
  ring_nf

variable {ρ : Measure ℝ} [IsFiniteMeasure ρ] {x₀ W : ℝ}

omit [IsFiniteMeasure ρ] in
lemma ae_mem_Icc (hρ : ρ (Icc (x₀ - W) (x₀ + W))ᶜ = 0) : ∀ᵐ x ∂ρ, x ∈ Icc (x₀ - W) (x₀ + W) :=
  mem_ae_iff.mpr hρ

/-- Polynomial moments of a finite measure carried by a compact interval are integrable. -/
lemma integrable_pow_sub (hρ : ρ (Icc (x₀ - W) (x₀ + W))ᶜ = 0) (j : ℕ) :
    Integrable (fun x => (x - x₀) ^ j) ρ := by
  refine Integrable.of_bound (by fun_prop : Continuous fun x : ℝ => (x - x₀) ^ j).aestronglyMeasurable (W ^ j) ?_
  filter_upwards [ae_mem_Icc hρ] with x hx
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩) j

/-- **One measure.** `ftMeas ρ ξ` minus its order-`N` moment expansion
`𝐞(−x₀ξ) Σ_{j<N} (−2πiξ)^j / j! · ∫ (x − x₀)^j dρ` has norm at most `ρ(ℝ) · (2π|ξ|W)^N / N!`, when `ρ` is carried by
`[x₀ − W, x₀ + W]`. -/
theorem norm_ftMeas_sub_moments_le (hρ : ρ (Icc (x₀ - W) (x₀ + W))ᶜ = 0) (N : ℕ) (ξ : ℝ) :
    ‖ftMeas ρ ξ - (𝐞 (-(x₀ * ξ)) : ℂ) * ∑ j ∈ Finset.range N,
        (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ : ℝ) : ℂ)‖ ≤
      ρ.real univ * ((2 * π * |ξ| * W) ^ N / (N ! : ℝ)) := by
  set e₀ : ℂ := (𝐞 (-(x₀ * ξ)) : ℂ)
  set P : ℝ → ℂ := fun x => ∑ j ∈ Finset.range N, (-2 * π * ξ * I) ^ j / (j ! : ℂ) * (((x - x₀) ^ j : ℝ) : ℂ)
  have hPi : Integrable P ρ := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact ((integrable_pow_sub hρ j).ofReal).const_mul _
  have hchar : Integrable (fun x : ℝ => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ)) ρ := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun x => by simp)
    exact (Continuous.aestronglyMeasurable (by
      simp only [Real.fourierChar_apply]; fun_prop))
  have hsum : e₀ * ∑ j ∈ Finset.range N, (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ : ℝ) : ℂ) =
      ∫ x, e₀ * P x ∂ρ := by
    rw [integral_const_mul, integral_finsetSum _ fun j _ => ((integrable_pow_sub hρ j).ofReal).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hsum, ftMeas, ← integral_sub hchar (hPi.const_mul _), mul_comm]
  refine norm_integral_le_of_norm_le_const ?_
  filter_upwards [ae_mem_Icc hρ] with x hx
  have hrem : (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) - e₀ * P x = e₀ * expIRem N (-2 * π * ξ * (x - x₀)) := by
    have hP : P x = ∑ j ∈ Finset.range N, (((-2 * π * ξ * (x - x₀) : ℝ) : ℂ) * I) ^ j / (j.factorial : ℂ) :=
      Finset.sum_congr rfl fun j _ => (taylor_term x x₀ ξ j).symm
    rw [fourierChar_phase x x₀ ξ, hP]
    unfold expIRem
    ring
  rw [hrem, norm_mul, Circle.norm_coe, one_mul]
  refine (norm_expIRem_le N _).trans ?_
  gcongr
  have hx' : |x - x₀| ≤ W := abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
  have : 0 ≤ 2 * π * |ξ| := by positivity
  nlinarith

/-- **Moment decay** (eq:newmomentdecay). If `ρ₁, ρ₂` are finite measures on `ℝ` carried by `[x₀ − W, x₀ + W]` with equal
moments `∫ (x − x₀)^j` for every `j < N`, then
`‖ftMeas ρ₁ ξ − ftMeas ρ₂ ξ‖ ≤ (ρ₁(ℝ) + ρ₂(ℝ)) · min{1, (2π|ξ|W)^N / N!}`. -/
theorem norm_ftMeas_sub_le_of_moments (ρ₁ ρ₂ : Measure ℝ) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] {x₀ W : ℝ} {N : ℕ}
    (h₁ : ρ₁ (Icc (x₀ - W) (x₀ + W))ᶜ = 0) (h₂ : ρ₂ (Icc (x₀ - W) (x₀ + W))ᶜ = 0)
    (hmom : ∀ j < N, ∫ x, (x - x₀) ^ j ∂ρ₁ = ∫ x, (x - x₀) ^ j ∂ρ₂) (ξ : ℝ) :
    ‖ftMeas ρ₁ ξ - ftMeas ρ₂ ξ‖ ≤
      (ρ₁.real univ + ρ₂.real univ) * min 1 ((2 * π * |ξ| * W) ^ N / (N ! : ℝ)) := by
  rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
  refine le_min ((norm_sub_le _ _).trans (add_le_add (norm_ftMeas_le_mass ρ₁ ξ) (norm_ftMeas_le_mass ρ₂ ξ))) ?_
  have hS : ∑ j ∈ Finset.range N, (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ₁ : ℝ) : ℂ) =
      ∑ j ∈ Finset.range N, (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ₂ : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun j hj => by rw [hmom j (Finset.mem_range.mp hj)]
  have e : ftMeas ρ₁ ξ - ftMeas ρ₂ ξ =
      (ftMeas ρ₁ ξ - (𝐞 (-(x₀ * ξ)) : ℂ) * ∑ j ∈ Finset.range N,
        (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ₁ : ℝ) : ℂ)) -
      (ftMeas ρ₂ ξ - (𝐞 (-(x₀ * ξ)) : ℂ) * ∑ j ∈ Finset.range N,
        (-2 * π * ξ * I) ^ j / (j ! : ℂ) * ((∫ x, (x - x₀) ^ j ∂ρ₂ : ℝ) : ℂ)) := by
    rw [hS]; ring
  rw [e, add_mul]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_ftMeas_sub_moments_le h₁ N ξ) (norm_ftMeas_sub_moments_le h₂ N ξ))

end StatFormal.FourierTaylor
