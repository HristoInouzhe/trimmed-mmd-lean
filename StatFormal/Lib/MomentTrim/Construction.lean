import StatFormal.Lib.MomentTrim.Solver
import StatFormal.Lib.MomentTrim.Pair
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Moment-cancelling trimmings of a crossing density pair (library, untrusted)

Let `p, q ≥ 0` be integrable on `ℝ`, continuous near `x₀`, with `e = p − q` differentiable at `x₀`, `e′(x₀) = ℓ₀ > 0` and
`p(x₀) = q(x₀) > 0`. For every `N ≥ 1` there are `T ≥ 1`, `w_N > 0` such that for `0 < w ≤ w_N` there are densities
`f_P ≤ p`, `f_Q ≤ q` and `h₊, h₋ ≥ 0` with `f_P + h₋ = f_Q + h₊`, `h±` carried by `[x₀ − Tw, x₀ + Tw]`, `∫ h₊ + ∫ h₋ ≤ 2ℓ₀w²`,
equal moments `∫ (x − x₀)^j h₊ = ∫ (x − x₀)^j h₋` for `j < N`, and `∫ f_P = ∫ f_Q = ∫ min(p, q) + ε(w)` with `ε(w) ≥ ℓ₀w²/8`.
This is the construction in the proof of Proposition S4.15 of the trimmed-mmd supplement (S4 :799-827), general in the density
pair: the excess `e` is added on `(x₀ − w, x₀ + w)` and its first `N` moments are cancelled by a polynomial density
`g(x) = S_{Tw}(m)(x − x₀)` on `[x₀ − Tw, x₀ + Tw]` (`Lib/MomentTrim/Solver`, the map `𝒢_T`), removed from the common part;
`f_P = min(p, q) + e 1_{(x₀, x₀+w]} − g₋`, `f_Q = min(p, q) − e 1_{(x₀−w, x₀]} − g₊`, `h₊ = e 1_{(x₀, x₀+w]} + g₊`,
`h₋ = −e 1_{(x₀−w, x₀]} + g₋`.

The printed route bounds `G_w = 𝒢_T[M(w)]` through its uniform convergence to `G₀`; here the same bound is obtained directly
from the explicit operator-norm bound of the solver (`abs_solL_le`) and the first-order estimate
`|∫_{x₀−w}^{x₀+w} (x − x₀)^j (e(x) − ℓ₀(x − x₀)) dx| ≤ 2ηw^{j+2}` (the uniform convergence `F_w(t) → t`, `η` from the little-o of
`e` at `x₀`). Constants: `K = solK N`, `T = 32(KN + 1)`, `η = ℓ₀/T`.

* `exists_deriv_bound`, `exists_half_lower`: the little-o and continuity estimates;
* `IsMomentTrimming`: the bundle of properties;
* `momentTrimming_of_small`: the construction at a fixed `w` under the smallness conditions;
* `exists_moment_trimming`: the existence of `T`, `w_N`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Interval

namespace StatFormal.MomentTrim

/-! ### Local estimates at `x₀` -/

/-- **First-order estimate.** If `e(x₀) = 0` and `e′(x₀) = ℓ₀`, then for every `η > 0`, `|e(x) − ℓ₀(x − x₀)| ≤ η|x − x₀|` near `x₀`. -/
theorem exists_deriv_bound {e : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hd : HasDerivAt e ℓ₀ x₀) (he : e x₀ = 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → |e x - ℓ₀ * (x - x₀)| ≤ η * |x - x₀| := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp hd).def hη
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h1 := hball (y := x - x₀) (by rwa [Real.dist_eq, sub_zero])
  have hx' : x₀ + (x - x₀) = x := by ring
  rw [hx', he, sub_zero, smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm (x - x₀)] at h1
  exact h1

/-- **Continuity at a positive value.** If `f` is continuous on `(x₀ − r₀, x₀ + r₀)` and `f(x₀) > 0`, then `f > f(x₀)/2` near `x₀`. -/
theorem exists_half_lower {f : ℝ → ℝ} {x₀ r₀ : ℝ} (hr₀ : 0 < r₀) (hf : ContinuousOn f (Ioo (x₀ - r₀) (x₀ + r₀)))
    (hpos : 0 < f x₀) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x₀ / 2 < f x := by
  have hc : ContinuousAt f x₀ := hf.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc (f x₀ / 2) (half_pos hpos)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h1 := h (x := x) (by rwa [Real.dist_eq])
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.1]

/-! ### Elementary integrals -/

lemma integral_lin_right (c x₀ w : ℝ) : ∫ x in x₀..(x₀ + w), c * (x - x₀) = c * w ^ 2 / 2 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x), integral_id]
  ring

lemma integral_lin_left (c x₀ w : ℝ) : ∫ x in (x₀ - w)..x₀, c * (x₀ - x) = c * w ^ 2 / 2 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun x => x), integral_id]
  ring

lemma integral_sub_symm (x₀ w : ℝ) : ∫ x in (x₀ - w)..(x₀ + w), (x - x₀) ^ 1 = 0 := by
  simp only [pow_one]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x), integral_id]
  ring

/-- A function that vanishes off `[a, b]`, times a polynomial weight, is integrable. -/
theorem integrable_pow_mul_of_support {h : ℝ → ℝ} (hh : Integrable h) {a b : ℝ} (hs : ∀ x, x ∉ Icc a b → h x = 0)
    (x₀ : ℝ) (j : ℕ) : Integrable (fun x => (x - x₀) ^ j * h x) := by
  have e : (fun x => (x - x₀) ^ j * h x) = (Icc a b).indicator (fun x => (x - x₀) ^ j * h x) := by
    funext x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hs x hx, mul_zero]
  rw [e]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact IntegrableOn.continuousOn_mul (by fun_prop) hh.integrableOn isCompact_Icc

/-! ### The construction -/

/-- The properties of the moment-cancelling trimming at scale `w`: densities `fP ≤ p`, `fQ ≤ q` of the trimmings and `hp, hm` of
the Jordan-type parts of their difference (`fP + hm = fQ + hp`). -/
structure IsMomentTrimming (p q : ℝ → ℝ) (x₀ ℓ₀ : ℝ) (N : ℕ) (T w : ℝ) (fP fQ hp hm : ℝ → ℝ) (e : ℝ) : Prop where
  meas_fP : Measurable fP
  meas_fQ : Measurable fQ
  meas_hp : Measurable hp
  meas_hm : Measurable hm
  fP_nonneg : ∀ x, 0 ≤ fP x
  fQ_nonneg : ∀ x, 0 ≤ fQ x
  hp_nonneg : ∀ x, 0 ≤ hp x
  hm_nonneg : ∀ x, 0 ≤ hm x
  fP_le : ∀ x, fP x ≤ p x
  fQ_le : ∀ x, fQ x ≤ q x
  add_eq : ∀ x, fP x + hm x = fQ x + hp x
  support : ∀ x, x ∉ Icc (x₀ - T * w) (x₀ + T * w) → hp x = 0 ∧ hm x = 0
  int_hp : Integrable hp
  int_hm : Integrable hm
  mass_h : (∫ x, hp x) + ∫ x, hm x ≤ 2 * ℓ₀ * w ^ 2
  moments : ∀ j < N, ∫ x, (x - x₀) ^ j * hp x = ∫ x, (x - x₀) ^ j * hm x
  mass_fP : ∫ x, fP x = (∫ x, min (p x) (q x)) + e
  mass_fQ : ∫ x, fQ x = (∫ x, min (p x) (q x)) + e
  e_ge : ℓ₀ * w ^ 2 / 8 ≤ e

/-- A moment-cancelling trimming is a trimming pair at scale `Tw` with `M = 2ℓ₀w²`. -/
theorem IsMomentTrimming.toPair {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} {N : ℕ} {T w : ℝ} {fP fQ hp hm : ℝ → ℝ} {e : ℝ}
    (h : IsMomentTrimming p q x₀ ℓ₀ N T w fP fQ hp hm e) :
    IsTrimmingPair p q x₀ (T * w) (2 * ℓ₀ * w ^ 2) N fP fQ hp hm e :=
  ⟨h.meas_fP, h.meas_fQ, h.meas_hp, h.meas_hm, h.fP_nonneg, h.fQ_nonneg, h.hp_nonneg, h.hm_nonneg, h.fP_le, h.fQ_le,
    h.add_eq, h.support, h.int_hp, h.int_hm, h.mass_h, h.moments, h.mass_fP, h.mass_fQ⟩

/-- The moment vector `m_j = −∫_{x₀−w}^{x₀+w} (x − x₀)^j e(x) dx` of the added excess. -/
def momVec (e : ℝ → ℝ) (x₀ w : ℝ) (N : ℕ) : Fin N → ℝ :=
  fun j => -∫ x in (x₀ - w)..(x₀ + w), (x - x₀) ^ (j : ℕ) * e x

/-- The correcting polynomial density `g(x) = S_{Tw}(m)(x − x₀)` on `[x₀ − Tw, x₀ + Tw]`. -/
def corr (e : ℝ → ℝ) (x₀ w T : ℝ) (N : ℕ) : ℝ → ℝ :=
  (Icc (x₀ - T * w) (x₀ + T * w)).indicator (fun x => solL N (T * w) (momVec e x₀ w N) (x - x₀))

section Corr

variable {e : ℝ → ℝ} {x₀ ℓ₀ T w η : ℝ} {N : ℕ}

/-- The moment vector is small: `(Tw)^{−j} |m_j| ≤ 2w²(ℓ₀/T + η)`. -/
theorem momVec_bound (hℓ : 0 < ℓ₀) (hw : 0 < w) (hT : 1 ≤ T) (hη : 0 ≤ η)
    (hcont : ContinuousOn e (Icc (x₀ - w) (x₀ + w)))
    (hderiv : ∀ x, |x - x₀| ≤ w → |e x - ℓ₀ * (x - x₀)| ≤ η * |x - x₀|) (j : Fin N) :
    ((T * w) ^ (j : ℕ))⁻¹ * |momVec e x₀ w N j| ≤ 2 * w ^ 2 * (ℓ₀ / T + η) := by
  have hT0 : 0 < T := by linarith
  have hab : x₀ - w ≤ x₀ + w := by linarith
  have hIcc : ∀ x ∈ Ι (x₀ - w) (x₀ + w), |x - x₀| ≤ w := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    exact abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hi1 : IntervalIntegrable (fun x => (x - x₀) ^ (j : ℕ) * (e x - ℓ₀ * (x - x₀))) volume (x₀ - w) (x₀ + w) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (by fun_prop : Continuous fun x : ℝ => (x - x₀) ^ (j : ℕ)).continuousOn.mul
      (hcont.sub (by fun_prop : Continuous fun x : ℝ => ℓ₀ * (x - x₀)).continuousOn)
  have hi2 : IntervalIntegrable (fun x => ℓ₀ * (x - x₀) ^ ((j : ℕ) + 1)) volume (x₀ - w) (x₀ + w) :=
    (by fun_prop : Continuous fun x : ℝ => ℓ₀ * (x - x₀) ^ ((j : ℕ) + 1)).intervalIntegrable _ _
  have hsplit : ∫ x in (x₀ - w)..(x₀ + w), (x - x₀) ^ (j : ℕ) * e x =
      (∫ x in (x₀ - w)..(x₀ + w), (x - x₀) ^ (j : ℕ) * (e x - ℓ₀ * (x - x₀))) +
        ∫ x in (x₀ - w)..(x₀ + w), ℓ₀ * (x - x₀) ^ ((j : ℕ) + 1) := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    congr 1; funext x; ring
  have hlen : |x₀ + w - (x₀ - w)| = 2 * w := by rw [abs_of_pos (by linarith)]; ring
  -- the remainder
  have hR : |∫ x in (x₀ - w)..(x₀ + w), (x - x₀) ^ (j : ℕ) * (e x - ℓ₀ * (x - x₀))| ≤ w ^ (j : ℕ) * (η * w) * (2 * w) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - w) (b := x₀ + w)
      (f := fun x => (x - x₀) ^ (j : ℕ) * (e x - ℓ₀ * (x - x₀))) (C := w ^ (j : ℕ) * (η * w)) (fun x hx => by
        have hx' := hIcc x hx
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx' _)
          ((hderiv x hx').trans (mul_le_mul_of_nonneg_left hx' hη)) (abs_nonneg _) (pow_nonneg hw.le _))
    rwa [Real.norm_eq_abs, hlen] at this
  -- the main term
  have hM : |∫ x in (x₀ - w)..(x₀ + w), ℓ₀ * (x - x₀) ^ ((j : ℕ) + 1)| ≤
      (if (j : ℕ) = 0 then 0 else ℓ₀ * w ^ ((j : ℕ) + 1) * (2 * w)) := by
    split_ifs with hj
    · rw [hj, intervalIntegral.integral_const_mul, zero_add, integral_sub_symm, mul_zero, abs_zero]
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - w) (b := x₀ + w)
        (f := fun x => ℓ₀ * (x - x₀) ^ ((j : ℕ) + 1)) (C := ℓ₀ * w ^ ((j : ℕ) + 1)) (fun x hx => by
          have hx' := hIcc x hx
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hℓ]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx' _) hℓ.le)
      rwa [Real.norm_eq_abs, hlen] at this
  have hm : |momVec e x₀ w N j| ≤ w ^ (j : ℕ) * (η * w) * (2 * w) +
      (if (j : ℕ) = 0 then 0 else ℓ₀ * w ^ ((j : ℕ) + 1) * (2 * w)) := by
    unfold momVec
    rw [abs_neg, hsplit]
    exact (abs_add_le _ _).trans (add_le_add hR hM)
  have hTw : 0 < (T * w) ^ (j : ℕ) := pow_pos (by positivity) _
  rw [inv_mul_le_iff₀ hTw]
  refine hm.trans ?_
  have hTj : T ^ (j : ℕ) * w ^ (j : ℕ) = (T * w) ^ (j : ℕ) := (mul_pow T w _).symm
  have hT1 : 1 ≤ T ^ (j : ℕ) := one_le_pow₀ hT
  split_ifs with hj
  · rw [hj, pow_zero, pow_zero, one_mul, add_zero]
    have : 0 ≤ ℓ₀ / T := div_nonneg hℓ.le hT0.le
    nlinarith [sq_nonneg w]
  · have hTT : T ≤ T ^ (j : ℕ) := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ (j : ℕ) := pow_le_pow_right₀ hT (Nat.one_le_iff_ne_zero.mpr hj)
    rw [← hTj, pow_succ]
    have hwj : 0 ≤ w ^ (j : ℕ) := pow_nonneg hw.le _
    have hℓT : ℓ₀ ≤ T ^ (j : ℕ) * (ℓ₀ / T) := by
      rw [mul_div_assoc', le_div_iff₀ hT0, mul_comm (T ^ (j : ℕ))]
      exact mul_le_mul_of_nonneg_left hTT hℓ.le
    have hηT : η ≤ T ^ (j : ℕ) * η := le_mul_of_one_le_left hη hT1
    have hw2 : 0 ≤ w ^ (j : ℕ) * w ^ 2 := by positivity
    calc w ^ (j : ℕ) * (η * w) * (2 * w) + ℓ₀ * (w ^ (j : ℕ) * w) * (2 * w)
        = 2 * (w ^ (j : ℕ) * w ^ 2) * (η + ℓ₀) := by ring
      _ ≤ 2 * (w ^ (j : ℕ) * w ^ 2) * (T ^ (j : ℕ) * η + T ^ (j : ℕ) * (ℓ₀ / T)) := by
          gcongr
      _ = T ^ (j : ℕ) * w ^ (j : ℕ) * (2 * w ^ 2 * (ℓ₀ / T + η)) := by ring

/-- **Sup bound of the correction.** If `K N (ℓ₀/T + η) ≤ ℓ₀/16`, then `|g| ≤ ℓ₀w/(8T)` everywhere. -/
theorem abs_corr_le (hℓ : 0 < ℓ₀) (hw : 0 < w) (hT : 1 ≤ T) (hη : 0 ≤ η)
    (hKN : solK N * N * (ℓ₀ / T + η) ≤ ℓ₀ / 16)
    (hcont : ContinuousOn e (Icc (x₀ - w) (x₀ + w)))
    (hderiv : ∀ x, |x - x₀| ≤ w → |e x - ℓ₀ * (x - x₀)| ≤ η * |x - x₀|) (x : ℝ) :
    |corr e x₀ w T N x| ≤ ℓ₀ * w / (8 * T) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < T * w := by positivity
  have hrhs : 0 ≤ ℓ₀ * w / (8 * T) := by positivity
  unfold corr
  by_cases hx : x ∈ Icc (x₀ - T * w) (x₀ + T * w)
  · rw [indicator_of_mem hx]
    have hxt : |x - x₀| ≤ T * w := abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine (abs_solL_le N hL _ hxt).trans ?_
    have hsum : ∑ j : Fin N, ((T * w) ^ (j : ℕ))⁻¹ * |momVec e x₀ w N j| ≤ N * (2 * w ^ 2 * (ℓ₀ / T + η)) := by
      calc ∑ j : Fin N, ((T * w) ^ (j : ℕ))⁻¹ * |momVec e x₀ w N j| ≤ ∑ _j : Fin N, 2 * w ^ 2 * (ℓ₀ / T + η) :=
            Finset.sum_le_sum fun j _ => momVec_bound hℓ hw hT hη hcont hderiv j
        _ = N * (2 * w ^ 2 * (ℓ₀ / T + η)) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hK := solK_nonneg N
    calc (T * w)⁻¹ * solK N * ∑ j : Fin N, ((T * w) ^ (j : ℕ))⁻¹ * |momVec e x₀ w N j|
        ≤ (T * w)⁻¹ * solK N * (N * (2 * w ^ 2 * (ℓ₀ / T + η))) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (inv_nonneg.mpr hL.le) hK)
      _ = (T * w)⁻¹ * (2 * w ^ 2) * (solK N * N * (ℓ₀ / T + η)) := by ring
      _ ≤ (T * w)⁻¹ * (2 * w ^ 2) * (ℓ₀ / 16) :=
          mul_le_mul_of_nonneg_left hKN (mul_nonneg (inv_nonneg.mpr hL.le) (by positivity))
      _ = ℓ₀ * w / (8 * T) := by field_simp; ring
  · rw [indicator_of_notMem hx, abs_zero]
    exact hrhs

lemma continuous_corr_piece (e : ℝ → ℝ) (x₀ w T : ℝ) (N : ℕ) :
    Continuous (fun x => solL N (T * w) (momVec e x₀ w N) (x - x₀)) :=
  (continuous_solL N _ _).comp (continuous_id.sub continuous_const)

lemma integrable_corr (e : ℝ → ℝ) (x₀ w T : ℝ) (N : ℕ) : Integrable (corr e x₀ w T N) :=
  ((continuous_corr_piece e x₀ w T N).integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma measurable_corr (e : ℝ → ℝ) (x₀ w T : ℝ) (N : ℕ) : Measurable (corr e x₀ w T N) :=
  (continuous_corr_piece e x₀ w T N).measurable.indicator measurableSet_Icc

lemma corr_eq_zero (e : ℝ → ℝ) (x₀ w T : ℝ) (N : ℕ) {x : ℝ} (hx : x ∉ Icc (x₀ - T * w) (x₀ + T * w)) :
    corr e x₀ w T N x = 0 := by
  unfold corr; rw [indicator_of_notMem hx]

/-- **L¹ bound of the correction.** `∫ |g| ≤ ℓ₀w²/4`. -/
theorem integral_abs_corr_le (hℓ : 0 < ℓ₀) (hw : 0 < w) (hT : 1 ≤ T) (hη : 0 ≤ η)
    (hKN : solK N * N * (ℓ₀ / T + η) ≤ ℓ₀ / 16)
    (hcont : ContinuousOn e (Icc (x₀ - w) (x₀ + w)))
    (hderiv : ∀ x, |x - x₀| ≤ w → |e x - ℓ₀ * (x - x₀)| ≤ η * |x - x₀|) :
    ∫ x, |corr e x₀ w T N x| ≤ ℓ₀ * w ^ 2 / 4 := by
  have hT0 : 0 < T := by linarith
  have hle : ∀ x, |corr e x₀ w T N x| ≤ (Icc (x₀ - T * w) (x₀ + T * w)).indicator (fun _ => ℓ₀ * w / (8 * T)) x := by
    intro x
    by_cases hx : x ∈ Icc (x₀ - T * w) (x₀ + T * w)
    · rw [indicator_of_mem hx]; exact abs_corr_le hℓ hw hT hη hKN hcont hderiv x
    · rw [indicator_of_notMem hx, corr_eq_zero e x₀ w T N hx, abs_zero]
  have hint : Integrable ((Icc (x₀ - T * w) (x₀ + T * w)).indicator (fun _ => ℓ₀ * w / (8 * T))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine (integral_mono (integrable_corr e x₀ w T N).abs hint hle).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by nlinarith), smul_eq_mul]
  field_simp; ring

/-- **Moments of the correction.** `∫ (x − x₀)^j g(x) dx = m_j` for `j < N`. -/
theorem integral_pow_mul_corr (hL : 0 < T * w) (j : Fin N) :
    ∫ x, (x - x₀) ^ (j : ℕ) * corr e x₀ w T N x = momVec e x₀ w N j := by
  have e1 : (fun x => (x - x₀) ^ (j : ℕ) * corr e x₀ w T N x) =
      (Icc (x₀ - T * w) (x₀ + T * w)).indicator (fun x => (x - x₀) ^ (j : ℕ) * solL N (T * w) (momVec e x₀ w N) (x - x₀)) := by
    funext x; unfold corr; rw [indicator_mul_right]
  rw [e1, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun t => t ^ (j : ℕ) * solL N (T * w) (momVec e x₀ w N) t)]
  have h1 : x₀ - T * w - x₀ = -(T * w) := by ring
  have h2 : x₀ + T * w - x₀ = T * w := by ring
  rw [h1, h2, solL_moments N hL]

end Corr

/-- **The construction at a fixed scale `w`.** Under the smallness conditions at `w` (the first-order estimate of `e = p − q` with
`η ≤ ℓ₀/4` on `[x₀ − w, x₀ + w]`, `min(p, q) ≥ ℓ₀w/8` on `[x₀ − Tw, x₀ + Tw]`, and `K N (ℓ₀/T + η) ≤ ℓ₀/16`), the trimming
densities exist. -/
theorem momentTrimming_of_small {p q : ℝ → ℝ} {x₀ ℓ₀ T w η : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpi : Integrable p) (hℓ : 0 < ℓ₀) (hw : 0 < w) (hT : 1 ≤ T) (hη : 0 ≤ η) (hη4 : η ≤ ℓ₀ / 4)
    (hKN : solK N * N * (ℓ₀ / T + η) ≤ ℓ₀ / 16)
    (hcont : ContinuousOn (fun x => p x - q x) (Icc (x₀ - w) (x₀ + w)))
    (hderiv : ∀ x, |x - x₀| ≤ w → |(p x - q x) - ℓ₀ * (x - x₀)| ≤ η * |x - x₀|)
    (hmin : ∀ x, |x - x₀| ≤ T * w → ℓ₀ * w / 8 ≤ min (p x) (q x)) :
    ∃ fP fQ hp hm : ℝ → ℝ, ∃ e : ℝ, IsMomentTrimming p q x₀ ℓ₀ N T w fP fQ hp hm e := by
  set E : ℝ → ℝ := fun x => p x - q x with hE
  have hT0 : 0 < T := by linarith
  have hL : 0 < T * w := by positivity
  have hwL : w ≤ T * w := le_mul_of_one_le_left hw.le hT
  have hEm : Measurable E := hpm.sub hqm
  -- linear bounds of `E` on both sides of `x₀`
  have hEr : ∀ x ∈ Icc x₀ (x₀ + w), (ℓ₀ - η) * (x - x₀) ≤ E x ∧ E x ≤ (ℓ₀ + η) * (x - x₀) := by
    intro x hx
    have hx' : |x - x₀| ≤ w := abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hderiv x hx'
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hEl : ∀ x ∈ Icc (x₀ - w) x₀, (ℓ₀ - η) * (x₀ - x) ≤ -E x ∧ -E x ≤ (ℓ₀ + η) * (x₀ - x) := by
    intro x hx
    have hx' : |x - x₀| ≤ w := abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hderiv x hx'
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), abs_le] at h
    constructor <;> linarith [h.1, h.2]
  -- the added excess on each side
  set aP : ℝ → ℝ := (Ioc x₀ (x₀ + w)).indicator E with haP
  set aQ : ℝ → ℝ := (Ioc (x₀ - w) x₀).indicator (fun x => -E x) with haQ
  have haP0 : ∀ x, 0 ≤ aP x := by
    intro x
    by_cases hx : x ∈ Ioc x₀ (x₀ + w)
    · rw [haP, indicator_of_mem hx]
      exact le_trans (mul_nonneg (by linarith) (by linarith [hx.1])) (hEr x (Ioc_subset_Icc_self hx)).1
    · rw [haP, indicator_of_notMem hx]
  have haQ0 : ∀ x, 0 ≤ aQ x := by
    intro x
    by_cases hx : x ∈ Ioc (x₀ - w) x₀
    · rw [haQ, indicator_of_mem hx]
      exact le_trans (mul_nonneg (by linarith) (by linarith [hx.2])) (hEl x (Ioc_subset_Icc_self hx)).1
    · rw [haQ, indicator_of_notMem hx]
  have hcontP : ContinuousOn E (Icc x₀ (x₀ + w)) := hcont.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hcontQ : ContinuousOn (fun x => -E x) (Icc (x₀ - w) x₀) := (hcont.mono (Icc_subset_Icc le_rfl (by linarith))).neg
  have haPi : Integrable aP := (hcontP.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have haQi : Integrable aQ := (hcontQ.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have haPm : Measurable aP := hEm.indicator measurableSet_Ioc
  have haQm : Measurable aQ := hEm.neg.indicator measurableSet_Ioc
  have hIaP : ∫ x, aP x = ∫ x in x₀..(x₀ + w), E x := by
    rw [haP, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have hIaQ : ∫ x, aQ x = ∫ x in (x₀ - w)..x₀, -E x := by
    rw [haQ, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have hEiP : IntervalIntegrable E volume x₀ (x₀ + w) := hcontP.intervalIntegrable_of_Icc (by linarith)
  have hEiQ : IntervalIntegrable (fun x => -E x) volume (x₀ - w) x₀ := hcontQ.intervalIntegrable_of_Icc (by linarith)
  have hlinP : ∀ c : ℝ, IntervalIntegrable (fun x => c * (x - x₀)) volume x₀ (x₀ + w) := fun c =>
    (by fun_prop : Continuous fun x : ℝ => c * (x - x₀)).intervalIntegrable _ _
  have hlinQ : ∀ c : ℝ, IntervalIntegrable (fun x => c * (x₀ - x)) volume (x₀ - w) x₀ := fun c =>
    (by fun_prop : Continuous fun x : ℝ => c * (x₀ - x)).intervalIntegrable _ _
  have haP_lo : (ℓ₀ - η) * w ^ 2 / 2 ≤ ∫ x, aP x := by
    rw [hIaP, ← integral_lin_right]
    exact intervalIntegral.integral_mono_on (by linarith) (hlinP _) hEiP fun x hx => (hEr x hx).1
  have haP_hi : ∫ x, aP x ≤ (ℓ₀ + η) * w ^ 2 / 2 := by
    rw [hIaP, ← integral_lin_right (ℓ₀ + η) x₀ w]
    exact intervalIntegral.integral_mono_on (by linarith) hEiP (hlinP _) fun x hx => (hEr x hx).2
  have haQ_hi : ∫ x, aQ x ≤ (ℓ₀ + η) * w ^ 2 / 2 := by
    rw [hIaQ, ← integral_lin_left (ℓ₀ + η) x₀ w]
    exact intervalIntegral.integral_mono_on (by linarith) hEiQ (hlinQ _) fun x hx => (hEl x hx).2
  -- the correction `g` and its parts
  set g := corr E x₀ w T N with hg
  have hgb : ∀ x, |g x| ≤ ℓ₀ * w / (8 * T) := abs_corr_le hℓ hw hT hη hKN hcont hderiv
  have hgi : Integrable g := integrable_corr E x₀ w T N
  have hgm : Measurable g := measurable_corr E x₀ w T N
  have hgl1 : ∫ x, |g x| ≤ ℓ₀ * w ^ 2 / 4 := integral_abs_corr_le hℓ hw hT hη hKN hcont hderiv
  have hgsmall : ∀ x, |g x| ≤ ℓ₀ * w / 8 := fun x =>
    (hgb x).trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith))
  have hgsupp : ∀ x, x ∉ Icc (x₀ - T * w) (x₀ + T * w) → g x = 0 := fun x hx => corr_eq_zero E x₀ w T N hx
  set gp : ℝ → ℝ := fun x => max (g x) 0 with hgp
  set gn : ℝ → ℝ := fun x => max (-g x) 0 with hgn
  have hgp0 : ∀ x, 0 ≤ gp x := fun x => le_max_right _ _
  have hgn0 : ∀ x, 0 ≤ gn x := fun x => le_max_right _ _
  have hgp_le : ∀ x, gp x ≤ |g x| := fun x => max_le (le_abs_self _) (abs_nonneg _)
  have hgn_le : ∀ x, gn x ≤ |g x| := fun x => max_le (neg_le_abs _) (abs_nonneg _)
  have hgpi : Integrable gp := hgi.pos_part
  have hgni : Integrable gn := hgi.neg_part
  have hgpm : Measurable gp := hgm.max measurable_const
  have hgnm : Measurable gn := hgm.neg.max measurable_const
  have hgsum : ∀ x, gp x + gn x = |g x| := fun x => by
    simp only [hgp, hgn]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h, zero_add]
  have hgdiff : ∀ x, gp x - gn x = g x := fun x => by
    simp only [hgp, hgn]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  -- the common part dominates the correction
  have hmin_g : ∀ x, |g x| ≤ min (p x) (q x) := by
    intro x
    by_cases hx : x ∈ Icc (x₀ - T * w) (x₀ + T * w)
    · have hxt : |x - x₀| ≤ T * w := abs_sub_le_iff.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
      exact (hgsmall x).trans (hmin x hxt)
    · rw [hgsupp x hx, abs_zero]; exact le_min (hp0 x) (hq0 x)
  have hmni : Integrable (fun x => min (p x) (q x)) :=
    hpi.mono' (hpm.min hqm).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 x) (hq0 x))]; exact min_le_left _ _)
  -- the difference `h₊ − h₋ = e 1_{(x₀−w, x₀+w]} + g`
  have hdiff : ∀ x, aP x - aQ x = (Ioc (x₀ - w) (x₀ + w)).indicator E x := by
    intro x
    by_cases h1 : x ∈ Ioc x₀ (x₀ + w)
    · have h2 : x ∉ Ioc (x₀ - w) x₀ := fun h => by linarith [h.2, h1.1]
      have h3 : x ∈ Ioc (x₀ - w) (x₀ + w) := ⟨by linarith [h1.1], h1.2⟩
      rw [haP, haQ, indicator_of_mem h1, indicator_of_notMem h2, indicator_of_mem h3, sub_zero]
    · by_cases h2 : x ∈ Ioc (x₀ - w) x₀
      · have h3 : x ∈ Ioc (x₀ - w) (x₀ + w) := ⟨h2.1, by linarith [h2.2]⟩
        rw [haP, haQ, indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem h3, zero_sub, neg_neg]
      · have h3 : x ∉ Ioc (x₀ - w) (x₀ + w) := by
          rintro ⟨ha, hb⟩
          by_cases hc : x ≤ x₀
          · exact h2 ⟨ha, hc⟩
          · exact h1 ⟨lt_of_not_ge hc, hb⟩
        rw [haP, haQ, indicator_of_notMem h1, indicator_of_notMem h2, indicator_of_notMem h3, sub_zero]
  have hIcc_sub : Ioc x₀ (x₀ + w) ⊆ Icc (x₀ - T * w) (x₀ + T * w) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIcc_subQ : Ioc (x₀ - w) x₀ ⊆ Icc (x₀ - T * w) (x₀ + T * w) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsuppP : ∀ x, x ∉ Icc (x₀ - T * w) (x₀ + T * w) → aP x + gp x = 0 := by
    intro x hx
    rw [haP, indicator_of_notMem (fun h => hx (hIcc_sub h))]
    simp only [hgp, hgsupp x hx, max_self, add_zero]
  have hsuppQ : ∀ x, x ∉ Icc (x₀ - T * w) (x₀ + T * w) → aQ x + gn x = 0 := by
    intro x hx
    rw [haQ, indicator_of_notMem (fun h => hx (hIcc_subQ h))]
    simp only [hgn, hgsupp x hx, neg_zero, max_self, add_zero]
  have hpi' : Integrable (fun x => aP x + gp x) := haPi.add hgpi
  have hmi' : Integrable (fun x => aQ x + gn x) := haQi.add hgni
  -- vanishing moments
  have hmom : ∀ j < N, ∫ x, (x - x₀) ^ j * (aP x + gp x) = ∫ x, (x - x₀) ^ j * (aQ x + gn x) := by
    intro j hj
    have i1 := integrable_pow_mul_of_support hpi' hsuppP x₀ j
    have i2 := integrable_pow_mul_of_support hmi' hsuppQ x₀ j
    have hIE : Integrable ((Ioc (x₀ - w) (x₀ + w)).indicator E) :=
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
    have i3 := integrable_pow_mul_of_support hIE (a := x₀ - w) (b := x₀ + w) (fun x hx => by
      rw [indicator_of_notMem (fun h => hx (Ioc_subset_Icc_self h))]) x₀ j
    have i4 := integrable_pow_mul_of_support hgi hgsupp x₀ j
    rw [← sub_eq_zero, ← integral_sub i1 i2]
    have e1 : (fun x => (x - x₀) ^ j * (aP x + gp x) - (x - x₀) ^ j * (aQ x + gn x)) =
        fun x => (x - x₀) ^ j * (Ioc (x₀ - w) (x₀ + w)).indicator E x + (x - x₀) ^ j * g x := by
      funext x
      rw [← hdiff x, ← hgdiff x]; ring
    rw [e1, integral_add i3 i4]
    have e2 : ∫ x, (x - x₀) ^ j * (Ioc (x₀ - w) (x₀ + w)).indicator E x = -momVec E x₀ w N ⟨j, hj⟩ := by
      have e3 : (fun x => (x - x₀) ^ j * (Ioc (x₀ - w) (x₀ + w)).indicator E x) =
          (Ioc (x₀ - w) (x₀ + w)).indicator (fun x => (x - x₀) ^ j * E x) := by
        funext x; rw [indicator_mul_right]
      rw [e3, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      simp only [momVec, neg_neg]
    rw [e2, integral_pow_mul_corr (e := E) (x₀ := x₀) hL ⟨j, hj⟩]
    ring
  have hmom0 := hmom 0 hN
  simp only [pow_zero, one_mul] at hmom0
  rw [integral_add haPi hgpi, integral_add haQi hgni] at hmom0
  have hgn_int : ∫ x, gn x ≤ ℓ₀ * w ^ 2 / 4 := (integral_mono hgni hgi.abs hgn_le).trans hgl1
  have hgpn_int : (∫ x, gp x) + ∫ x, gn x ≤ ℓ₀ * w ^ 2 / 4 := by
    rw [← integral_add hgpi hgni]
    exact (le_of_eq (integral_congr_ae (ae_of_all _ hgsum))).trans hgl1
  refine ⟨fun x => min (p x) (q x) + aP x - gn x, fun x => min (p x) (q x) + aQ x - gp x,
    fun x => aP x + gp x, fun x => aQ x + gn x, (∫ x, aP x) - ∫ x, gn x, ?_⟩
  refine
    { meas_fP := ((hpm.min hqm).add haPm).sub hgnm
      meas_fQ := ((hpm.min hqm).add haQm).sub hgpm
      meas_hp := haPm.add hgpm
      meas_hm := haQm.add hgnm
      fP_nonneg := fun x => by linarith [haP0 x, hgn_le x, hmin_g x]
      fQ_nonneg := fun x => by linarith [haQ0 x, hgp_le x, hmin_g x]
      hp_nonneg := fun x => add_nonneg (haP0 x) (hgp0 x)
      hm_nonneg := fun x => add_nonneg (haQ0 x) (hgn0 x)
      fP_le := fun x => ?_
      fQ_le := fun x => ?_
      add_eq := fun x => by ring
      support := fun x hx => ⟨hsuppP x hx, hsuppQ x hx⟩
      int_hp := hpi'
      int_hm := hmi'
      mass_h := ?_
      moments := hmom
      mass_fP := ?_
      mass_fQ := ?_
      e_ge := ?_ }
  · by_cases hx : x ∈ Ioc x₀ (x₀ + w)
    · have : aP x = p x - q x := by rw [haP, indicator_of_mem hx]
      linarith [min_le_right (p x) (q x), hgn0 x]
    · have : aP x = 0 := by rw [haP, indicator_of_notMem hx]
      linarith [min_le_left (p x) (q x), hgn0 x]
  · by_cases hx : x ∈ Ioc (x₀ - w) x₀
    · have : aQ x = -(p x - q x) := by rw [haQ, indicator_of_mem hx]
      linarith [min_le_left (p x) (q x), hgp0 x]
    · have : aQ x = 0 := by rw [haQ, indicator_of_notMem hx]
      linarith [min_le_right (p x) (q x), hgp0 x]
  · rw [integral_add haPi hgpi, integral_add haQi hgni]
    nlinarith [sq_nonneg w]
  · have i1 : Integrable (fun x => min (p x) (q x) + aP x) := hmni.add haPi
    rw [integral_sub i1 hgni, integral_add hmni haPi]; ring
  · have i1 : Integrable (fun x => min (p x) (q x) + aQ x) := hmni.add haQi
    rw [integral_sub i1 hgpi, integral_add hmni haQi]; linarith
  · nlinarith [sq_nonneg w]

/-- **Existence of the moment-cancelling trimmings** (the main part of Proposition S4.15, general in the density pair). -/
theorem exists_moment_trimming {p q : ℝ → ℝ} {x₀ r₀ ℓ₀ : ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p) (hr₀ : 0 < r₀)
    (hpc : ContinuousOn p (Ioo (x₀ - r₀) (x₀ + r₀))) (hqc : ContinuousOn q (Ioo (x₀ - r₀) (x₀ + r₀)))
    (hd : HasDerivAt (fun x => p x - q x) ℓ₀ x₀) (hℓ : 0 < ℓ₀) (hpq : p x₀ = q x₀) (hpos : 0 < p x₀)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ T wN : ℝ, 1 ≤ T ∧ 0 < wN ∧ ∀ w ∈ Ioc (0 : ℝ) wN,
      ∃ fP fQ hp hm : ℝ → ℝ, ∃ e : ℝ, IsMomentTrimming p q x₀ ℓ₀ N T w fP fQ hp hm e := by
  have hK := solK_nonneg N
  set D : ℝ := 32 * (solK N * N + 1) with hDdef
  have hKN0 : 0 ≤ solK N * N := mul_nonneg hK (Nat.cast_nonneg N)
  have hD : 32 ≤ D := by rw [hDdef]; linarith
  have hD0 : 0 < D := by linarith
  set η : ℝ := ℓ₀ / D with hηdef
  have hη : 0 < η := div_pos hℓ hD0
  have hη4 : η ≤ ℓ₀ / 4 := div_le_div_of_nonneg_left hℓ.le (by norm_num) (by linarith)
  have hKN : solK N * N * (ℓ₀ / D + η) ≤ ℓ₀ / 16 := by
    rw [hηdef, show ℓ₀ / D + ℓ₀ / D = 2 * ℓ₀ / D by ring, ← mul_div_assoc, div_le_div_iff₀ hD0 (by norm_num), hDdef]
    nlinarith [mul_nonneg hKN0 hℓ.le]
  have he0 : (fun x => p x - q x) x₀ = 0 := by simp [hpq]
  obtain ⟨δ₁, hδ₁, hder⟩ := exists_deriv_bound hd he0 hη
  obtain ⟨δp, hδp, hpl⟩ := exists_half_lower hr₀ hpc hpos
  obtain ⟨δq, hδq, hql⟩ := exists_half_lower hr₀ hqc (hpq ▸ hpos)
  set wN : ℝ := min (min (δ₁ / 2) (min δp δq / (2 * D))) (min (r₀ / (2 * D)) (4 * p x₀ / ℓ₀)) with hwN
  have hwN0 : 0 < wN := lt_min (lt_min (by positivity) (div_pos (lt_min hδp hδq) (by positivity)))
    (lt_min (by positivity) (by positivity))
  refine ⟨D, wN, by linarith, hwN0, fun w hw => ?_⟩
  have hw0 : 0 < w := hw.1
  have hw1 : w ≤ δ₁ / 2 := hw.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hw2 : w ≤ min δp δq / (2 * D) := hw.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hw3 : w ≤ r₀ / (2 * D) := hw.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hw4 : w ≤ 4 * p x₀ / ℓ₀ := hw.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDw2 : D * w ≤ min δp δq / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [le_div_iff₀ (by positivity)] at hw2
    linarith
  have hDw3 : D * w ≤ r₀ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hw3
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hwD : w ≤ D * w := le_mul_of_one_le_left hw0.le (by linarith)
  have hδmin : min δp δq / 2 < δp ∧ min δp δq / 2 < δq :=
    ⟨by linarith [min_le_left δp δq], by linarith [min_le_right δp δq]⟩
  refine momentTrimming_of_small hN hpm hqm hp0 hq0 hpi hℓ hw0 (by linarith) hη.le hη4 hKN ?_ ?_ ?_
  · refine (hpc.sub hqc).mono fun x hx => ⟨?_, ?_⟩
    · linarith [hx.1, hr₀]
    · linarith [hx.2, hr₀]
  · intro x hx
    exact hder x (by linarith)
  · intro x hx
    have h1 := hpl x (by linarith [hδmin.1])
    have h2 := hql x (by linarith [hδmin.2])
    rw [← hpq] at h2
    have h3 : ℓ₀ * w / 8 ≤ p x₀ / 2 := by
      rw [le_div_iff₀ hℓ] at hw4
      linarith
    exact le_min (by linarith) (by linarith)

end StatFormal.MomentTrim
