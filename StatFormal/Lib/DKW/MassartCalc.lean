import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.IntermediateValue

/-!
# The calculus behind Massart's constant: a single exponential tilt for all levels

For `0 < ε < 1` there is ONE `λ > 0` such that for every `p ∈ (ε, 1]`
`log(1 + λ) + 2ε² ≤ p log(1 + λ/(p − ε))`  (`exists_lambda`).

This is the saddle-point step of the discrete-time martingale proof of the Dvoretzky–Kiefer–Wolfowitz–Massart
inequality (J.-Y. Le Boudec, *An elementary proof of the DKWM inequality*, arXiv:2607.04387, Lemmas 3–6; the
continuous-time version is H. W. J. Reeve, arXiv:2403.16651). Sion's minimax theorem is NOT used: the saddle point is
produced directly.
* `shape`: for fixed `ε, λ > 0`, `φ(y) = (y + ε) log(1 + λ/y)` has `φ'' ∝ y(2ε − λ) + ελ`, and `φ' > 0` wherever
  `y(λ − 2ε) ≥ ελ` (by `log(1 + z) > 2z/(2 + z)`); hence a critical point of `φ` on `(0, ∞)` is its global minimum.
* `D(p) = φ'(p − ε)` at `λ = ε/(1 − p)` changes sign on `(ε, 1)` (explicit points), so by the intermediate value
  theorem some `p₀` is critical for `λ₀ = ε/(1 − p₀)`.
* At `(p₀, λ₀)`: `φ(p₀ − ε) − log(1 + λ₀) = kl(p₀ ‖ p₀ − ε) ≥ 2ε²` (Pinsker for Bernoulli laws, `pinsker`).
-/

noncomputable section
open Real Set

namespace StatFormal.DKW.Massart

/-- `2z/(2 + z) < log(1 + z)` for `z > 0`. -/
lemma two_div_lt_log {z : ℝ} (hz : 0 < z) : 2 * z / (2 + z) < Real.log (1 + z) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - 2 * x / (2 + x)
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (x ^ 2 / ((1 + x) * (2 + x) ^ 2)) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by positivity
    have h2 : (2 + x) ≠ 0 := by positivity
    have hl := ((hasDerivAt_id x).const_add 1).log h1
    have hq := ((hasDerivAt_id x).const_mul 2).div ((hasDerivAt_id x).const_add 2) h2
    exact (hl.sub hq).congr_deriv (by simp only [id]; field_simp; ring)
  have hmono : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(hd x hx'.le).deriv]
      positivity
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz.le) hz
  simp only [f, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at h
  linarith

/-- `log(1 + z) ≤ z/2` for `z ≥ 4`. -/
lemma log_one_add_le_half {z : ℝ} (hz : 4 ≤ z) : Real.log (1 + z) ≤ z / 2 := by
  have h1 : 1 + z ≤ Real.exp (z / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ z / 2 by linarith)
    nlinarith
  calc Real.log (1 + z) ≤ Real.log (Real.exp (z / 2)) := Real.log_le_log (by linarith) h1
    _ = z / 2 := Real.log_exp _

/-- `log a − log b ≤ a/b − 1`. -/
lemma log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a - Real.log b ≤ a / b - 1 := by
  rw [← Real.log_div ha.ne' hb.ne']
  exact Real.log_le_sub_one_of_pos (div_pos ha hb)

/-! ### The shape of `φ(y) = (y + ε) log(1 + λ/y)` -/

/-- `φ(y) = (y + ε) log(1 + λ/y)`. -/
def phi (e l y : ℝ) : ℝ := (y + e) * Real.log (1 + l / y)

/-- `φ'(y) = log(1 + λ/y) − (y + ε)λ/(y(y + λ))`. -/
def psi (e l y : ℝ) : ℝ := Real.log (1 + l / y) - (y + e) * l / (y * (y + l))

lemma hasDerivAt_log_one_add_div {l y : ℝ} (hl : 0 < l) (hy : 0 < y) :
    HasDerivAt (fun x => Real.log (1 + l / x)) (-(l / (y * (y + l)))) y := by
  have hd := ((hasDerivAt_const y l).div (hasDerivAt_id y) hy.ne').const_add 1
  have hne : (1 + l / y) ≠ 0 := by positivity
  exact (hd.log hne).congr_deriv (by simp only [id, Pi.div_apply]; field_simp; ring)

lemma hasDerivAt_phi {e l y : ℝ} (hl : 0 < l) (hy : 0 < y) : HasDerivAt (phi e l) (psi e l y) y := by
  have h := ((hasDerivAt_id y).add_const e).mul (hasDerivAt_log_one_add_div hl hy)
  have : y * (y + l) ≠ 0 := by positivity
  exact h.congr_deriv (by simp only [psi, id]; field_simp; ring)

lemma hasDerivAt_psi {e l y : ℝ} (hl : 0 < l) (hy : 0 < y) :
    HasDerivAt (psi e l) (l * (y * (2 * e - l) + e * l) / (y * (y + l)) ^ 2) y := by
  have hne : y * (y + l) ≠ 0 := by positivity
  have h2 := (((hasDerivAt_id y).add_const e).mul_const l).div
      ((hasDerivAt_id y).mul ((hasDerivAt_id y).add_const l)) hne
  exact ((hasDerivAt_log_one_add_div hl hy).sub h2).congr_deriv (by simp only [id, Pi.mul_apply]; field_simp; ring)

lemma psi_pos_of {e l y : ℝ} (he : 0 < e) (hl : 0 < l) (hy : 0 < y) (h : e * l ≤ y * (l - 2 * e)) :
    0 < psi e l y := by
  have hlog := two_div_lt_log (show 0 < l / y by positivity)
  have heq : 2 * (l / y) / (2 + l / y) = 2 * l / (2 * y + l) := by
    field_simp
  have hle : (y + e) * l / (y * (y + l)) ≤ 2 * l / (2 * y + l) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hl hy]
  simp only [psi]
  linarith

/-- A critical point of `φ` on `(0, ∞)` is a global minimum there. -/
lemma shape {e l y0 y : ℝ} (he : 0 < e) (hl : 0 < l) (hy0 : 0 < y0) (h0 : psi e l y0 = 0) (hy : 0 < y) :
    phi e l y0 ≤ phi e l y := by
  have hS0 : y0 * (l - 2 * e) < e * l := by
    by_contra hc
    push_neg at hc
    have := psi_pos_of he hl hy0 hc
    linarith
  have hinc : ∀ a b : ℝ, 0 < a → a < b → b * (l - 2 * e) < e * l → psi e l a < psi e l b := by
    intro a b ha hab hb
    have hmono : StrictMonoOn (psi e l) (Icc a b) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc a b)
      · exact fun x hx => (hasDerivAt_psi hl (ha.trans_le hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := ha.trans hx.1
        rw [(hasDerivAt_psi hl hx0).deriv]
        have hpos : 0 < x * (2 * e - l) + e * l := by
          rcases le_or_gt 0 (l - 2 * e) with hc | hc
          · nlinarith [mul_le_mul_of_nonneg_right hx.2.le hc]
          · nlinarith [mul_pos hx0 (neg_pos.2 hc), mul_pos he hl]
        positivity
    exact hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hcont : ∀ a b : ℝ, 0 < a → ContinuousOn (phi e l) (Icc a b) := fun a b ha x hx =>
    (hasDerivAt_phi hl (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hdiff : ∀ a b : ℝ, 0 < a → DifferentiableOn ℝ (phi e l) (interior (Icc a b)) := by
    intro a b ha x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_phi hl (ha.trans hx.1)).differentiableAt.differentiableWithinAt
  rcases lt_trichotomy y y0 with h | h | h
  · have hanti : AntitoneOn (phi e l) (Icc y y0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc y y0) (hcont y y0 hy) (hdiff y y0 hy)
      intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_phi hl (hy.trans hx.1)).deriv]
      have := hinc x y0 (hy.trans hx.1) hx.2 hS0
      linarith
    exact hanti ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
  · rw [h]
  · have hmono : MonotoneOn (phi e l) (Icc y0 y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc y0 y) (hcont y0 y hy0) (hdiff y0 y hy0)
      intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_phi hl (hy0.trans hx.1)).deriv]
      by_cases hxS : x * (l - 2 * e) < e * l
      · have := hinc y0 x hy0 hx.1 hxS
        linarith
      · push_neg at hxS
        exact (psi_pos_of he hl (hy0.trans hx.1) hxS).le
    exact hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le

/-! ### Pinsker's inequality for Bernoulli laws -/

/-- Pinsker: `2(p − q)² ≤ kl(p ‖ q) = p log(p/q) + (1 − p) log((1 − p)/(1 − q))` for `0 < q < p < 1`. -/
lemma pinsker {p q : ℝ} (hq : 0 < q) (hqp : q < p) (hp : p < 1) :
    2 * (p - q) ^ 2 ≤ p * (Real.log p - Real.log q) + (1 - p) * (Real.log (1 - p) - Real.log (1 - q)) := by
  let f : ℝ → ℝ := fun x => p * (Real.log p - Real.log x) + (1 - p) * (Real.log (1 - p) - Real.log (1 - x)) -
    2 * (p - x) ^ 2
  have hd : ∀ x : ℝ, 0 < x → x < 1 →
      HasDerivAt f ((p - x) * (4 * x * (1 - x) - 1) / (x * (1 - x))) x := by
    intro x hx0 hx1
    have h1 : x ≠ 0 := hx0.ne'
    have h2 : (1 - x) ≠ 0 := by linarith
    have hA := ((hasDerivAt_log h1).const_sub (Real.log p)).const_mul p
    have hB := ((((hasDerivAt_id x).const_sub 1).log h2).const_sub (Real.log (1 - p))).const_mul (1 - p)
    have hC := (((hasDerivAt_id x).const_sub p).pow 2).const_mul 2
    exact ((hA.add hB).sub hC).congr_deriv (by simp only [id]; field_simp; ring)
  have hanti : AntitoneOn f (Icc q p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q p)
    · exact fun x hx => (hd x (hq.trans_le hx.1) (hx.2.trans_lt hp)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (hq.trans hx.1) (hx.2.trans hp)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hq.trans hx.1
      have hx1 : x < 1 := hx.2.trans hp
      rw [(hd x hx0 hx1).deriv]
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.2])
        nlinarith [sq_nonneg (2 * x - 1)]
      · exact (mul_pos hx0 (by linarith)).le
  have h := hanti ⟨le_rfl, hqp.le⟩ ⟨hqp.le, le_rfl⟩ hqp.le
  simp only [f, sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at h
  linarith

/-! ### The saddle point -/

/-- `D(p) = φ'(p − ε)` at the tilt `λ = ε/(1 − p)`. -/
def Dfun (e p : ℝ) : ℝ := psi e (e / (1 - p)) (p - e)

lemma one_add_lam_div {e p : ℝ} (hep : e < p) (hp : p < 1) :
    1 + e / (1 - p) / (p - e) = p * (1 - p + e) / ((1 - p) * (p - e)) := by
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : (p - e) ≠ 0 := by linarith
  field_simp
  ring

lemma log_one_add_lam_div {e p : ℝ} (he : 0 < e) (hep : e < p) (hp : p < 1) :
    Real.log (1 + e / (1 - p) / (p - e)) =
      Real.log p + Real.log (1 - p + e) - Real.log (1 - p) - Real.log (p - e) := by
  have hp0 : 0 < p := he.trans hep
  rw [one_add_lam_div hep hp, Real.log_div (by
      have : 0 < 1 - p + e := by linarith
      have : 0 < 1 - p := by linarith
      positivity) (by
      have : 0 < 1 - p := by linarith
      have : 0 < p - e := by linarith
      positivity),
    Real.log_mul hp0.ne' (by linarith), Real.log_mul (by linarith) (by linarith)]
  ring

lemma Dfun_eq {e p : ℝ} (he : 0 < e) (hep : e < p) (hp : p < 1) :
    Dfun e p = Real.log p + Real.log (1 - p + e) - Real.log (1 - p) - Real.log (p - e) -
      e / ((p - e) * (1 - p + e)) := by
  have hp0 : 0 < p := he.trans hep
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : (p - e) ≠ 0 := by linarith
  have h3 : (1 - p + e) ≠ 0 := by linarith
  have hsum : p - e + e / (1 - p) = p * (1 - p + e) / (1 - p) := by
    field_simp
    ring
  simp only [Dfun, psi]
  rw [log_one_add_lam_div he hep hp]
  congr 1
  rw [hsum, sub_add_cancel]
  field_simp

lemma Dfun_continuousOn {e a b : ℝ} (he : 0 < e) (hea : e < a) (hb : b < 1) :
    ContinuousOn (Dfun e) (Icc a b) := by
  have hcf : ContinuousOn (fun p => Real.log p + Real.log (1 - p + e) - Real.log (1 - p) -
      Real.log (p - e) - e / ((p - e) * (1 - p + e))) (Icc a b) := by
    have hm : ∀ p ∈ Icc a b, e < p ∧ p < 1 := fun p hp => ⟨hea.trans_le hp.1, hp.2.trans_lt hb⟩
    refine ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_) ?_) ?_
    · exact continuousOn_id.log fun p hp => ((he.trans (hm p hp).1)).ne'
    · exact (continuousOn_const.sub continuousOn_id |>.add continuousOn_const).log fun p hp =>
        ne_of_gt (show (0 : ℝ) < 1 - p + e by have := hm p hp; linarith)
    · exact (continuousOn_const.sub continuousOn_id).log fun p hp =>
        ne_of_gt (show (0 : ℝ) < 1 - p by have := hm p hp; linarith)
    · exact (continuousOn_id.sub continuousOn_const).log fun p hp =>
        ne_of_gt (show (0 : ℝ) < p - e by have := hm p hp; linarith)
    · refine continuousOn_const.div ((continuousOn_id.sub continuousOn_const).mul
        ((continuousOn_const.sub continuousOn_id).add continuousOn_const)) fun p hp => ?_
      have := hm p hp
      have h1 : 0 < p - e := by linarith
      have h2 : 0 < 1 - p + e := by linarith
      exact ne_of_gt (show (0 : ℝ) < (p - e) * (1 - p + e) from mul_pos h1 h2)
  refine hcf.congr fun p hp => ?_
  exact Dfun_eq he (hea.trans_le hp.1) (hp.2.trans_lt hb)

/-- `D < 0` just to the right of `ε`. -/
lemma Dfun_left_neg {e : ℝ} (he : 0 < e) (he1 : e < 1) : Dfun e (e + min e (1 - e) / 8) < 0 := by
  set y := min e (1 - e) / 8 with hy
  have hy0 : 0 < y := by
    have : 0 < min e (1 - e) := lt_min he (by linarith)
    positivity
  have hye : y ≤ e / 8 := by
    have := min_le_left e (1 - e); rw [hy]; linarith
  have hy1 : y ≤ (1 - e) / 8 := by
    have := min_le_right e (1 - e); rw [hy]; linarith
  rw [Dfun_eq he (by linarith) (by linarith)]
  have e1 : e + y - e = y := by ring
  have e2 : 1 - (e + y) + e = 1 - y := by ring
  have e3 : 1 - (e + y) = 1 - e - y := by ring
  rw [e1, e2, e3]
  -- `log(e + y) − log y = log(1 + e/y) ≤ e/(2y)`
  have hA : Real.log (e + y) - Real.log y ≤ e / y / 2 := by
    rw [← Real.log_div (by linarith) hy0.ne']
    have : (e + y) / y = 1 + e / y := by field_simp; ring
    rw [this]
    apply log_one_add_le_half
    rw [le_div_iff₀ hy0]; linarith
  have hB : Real.log (1 - y) - Real.log (1 - e - y) ≤ (1 - y) / (1 - e - y) - 1 :=
    log_sub_log_le (by linarith) (by linarith)
  have hB' : (1 - y) / (1 - e - y) - 1 = e / (1 - e - y) := by
    have : (1 - e - y) ≠ 0 := by linarith
    field_simp; ring
  have hC : e / y ≤ e / (y * (1 - y)) := by
    apply div_le_div_of_nonneg_left he.le (by nlinarith) (by nlinarith)
  have hD : e / (1 - e - y) < e / y / 2 := by
    rw [div_div, div_lt_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  nlinarith

/-- `D > 0` just to the left of `1`. -/
lemma Dfun_right_pos {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    0 < Dfun e (1 - e * (1 - e) / 2 * Real.exp (-(2 / (1 - e)))) := by
  set X := Real.exp (-(2 / (1 - e))) with hX
  set d := e * (1 - e) / 2 * X with hd
  have hX0 : 0 < X := Real.exp_pos _
  have hX1 : X < 1 := by
    rw [hX, Real.exp_lt_one_iff]
    have : 0 < 2 / (1 - e) := div_pos two_pos (by linarith)
    linarith
  have h1e : 0 < 1 - e := by linarith
  have hd0 : 0 < d := by positivity
  have hdle : d < (1 - e) / 2 := by
    rw [hd]
    have : e * (1 - e) / 2 * X < e * (1 - e) / 2 := by
      have : 0 < e * (1 - e) / 2 := by positivity
      nlinarith
    nlinarith
  rw [Dfun_eq he (by linarith) (by linarith)]
  have e2 : 1 - (1 - d) + e = d + e := by ring
  have e3 : 1 - (1 - d) = d := by ring
  have e4 : 1 - d - e = 1 - e - d := by ring
  rw [e2, e3, e4]
  -- first bracket `log(1 − d) − log(1 − e − d) > 0`
  have hA : 0 < Real.log (1 - d) - Real.log (1 - e - d) := by
    have := Real.log_lt_log (show 0 < 1 - e - d by linarith) (show 1 - e - d < 1 - d by linarith)
    linarith
  -- second bracket `log(d + e) − log d ≥ 2/(1 − e)`
  have hB : 2 / (1 - e) ≤ Real.log (d + e) - Real.log d := by
    rw [← Real.log_div (by linarith) hd0.ne']
    have hexp : Real.exp (2 / (1 - e)) ≤ (d + e) / d := by
      rw [le_div_iff₀ hd0]
      have hXinv : Real.exp (2 / (1 - e)) * X = 1 := by
        rw [hX, ← Real.exp_add]; simp
      have : Real.exp (2 / (1 - e)) * d = e * (1 - e) / 2 := by
        rw [hd]; linear_combination (e * (1 - e) / 2) * hXinv
      rw [this]
      nlinarith
    calc 2 / (1 - e) = Real.log (Real.exp (2 / (1 - e))) := (Real.log_exp _).symm
      _ ≤ Real.log ((d + e) / d) := Real.log_le_log (Real.exp_pos _) hexp
  -- third term `e/((1 − e − d)(d + e)) ≤ 2/(1 − e)`
  have hC : e / ((1 - e - d) * (d + e)) ≤ 2 / (1 - e) := by
    have h3 : 0 < 1 - e - d := by linarith
    have h4 : 0 < (1 - e - d) * (d + e) := by positivity
    rw [div_le_div_iff₀ h4 h1e]
    nlinarith [mul_pos hd0 he]
  linarith

/-- **The single tilt.** For `0 < ε < 1` there is `λ > 0` with `log(1 + λ) + 2ε² ≤ p log(1 + λ/(p − ε))` for every
`p ∈ (ε, 1]`. -/
theorem exists_lambda {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    ∃ l : ℝ, 0 < l ∧ ∀ p : ℝ, e < p → p ≤ 1 → Real.log (1 + l) + 2 * e ^ 2 ≤ p * Real.log (1 + l / (p - e)) := by
  set p1 := e + min e (1 - e) / 8 with hp1
  set p2 := 1 - e * (1 - e) / 2 * Real.exp (-(2 / (1 - e))) with hp2
  have h1e : 0 < 1 - e := by linarith
  have hmin : 0 < min e (1 - e) := lt_min he h1e
  have hp1e : e < p1 := by
    have : 0 < min e (1 - e) / 8 := by positivity
    linarith
  have hX0 : 0 < Real.exp (-(2 / (1 - e))) := Real.exp_pos _
  have hX1 : Real.exp (-(2 / (1 - e))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < 2 / (1 - e) := div_pos two_pos h1e
    linarith
  have hp21 : p2 < 1 := by
    have : 0 < e * (1 - e) / 2 * Real.exp (-(2 / (1 - e))) := by positivity
    linarith
  have hp12 : p1 ≤ p2 := by
    have : min e (1 - e) ≤ 1 - e := min_le_right _ _
    have : e * (1 - e) / 2 * Real.exp (-(2 / (1 - e))) ≤ e * (1 - e) / 2 := by
      have : 0 ≤ e * (1 - e) / 2 := by positivity
      nlinarith
    rw [hp1, hp2]; nlinarith
  have hcont := Dfun_continuousOn he hp1e hp21
  have hivt := intermediate_value_Icc hp12 hcont
  have h0mem : (0 : ℝ) ∈ Icc (Dfun e p1) (Dfun e p2) :=
    ⟨(Dfun_left_neg he he1).le, (Dfun_right_pos he he1).le⟩
  obtain ⟨p0, hp0, hD0⟩ := hivt h0mem
  have hp0e : e < p0 := hp1e.trans_le hp0.1
  have hp01 : p0 < 1 := hp0.2.trans_lt hp21
  set l := e / (1 - p0) with hl
  have hl0 : 0 < l := div_pos he (by linarith)
  refine ⟨l, hl0, fun p hp hp1' => ?_⟩
  have hsh := shape he hl0 (show 0 < p0 - e by linarith) hD0 (show 0 < p - e by linarith)
  have hphi : phi e l (p - e) = p * Real.log (1 + l / (p - e)) := by
    simp only [phi, sub_add_cancel]
  rw [← hphi]
  refine le_trans ?_ hsh
  -- value at the saddle point: `log(1 + λ₀) + kl(p₀ ‖ p₀ − ε)`
  have hval : phi e l (p0 - e) = Real.log (1 + l) +
      (p0 * (Real.log p0 - Real.log (p0 - e)) + (1 - p0) * (Real.log (1 - p0) - Real.log (1 - p0 + e))) := by
    have hlog1 : Real.log (1 + l) = Real.log (1 - p0 + e) - Real.log (1 - p0) := by
      rw [← Real.log_div (by linarith) (by linarith)]
      congr 1
      have : (1 - p0) ≠ 0 := by linarith
      rw [hl]; field_simp
    simp only [phi, sub_add_cancel]
    rw [hl, log_one_add_lam_div he hp0e hp01, ← hl, hlog1]
    ring
  rw [hval]
  have hpin := pinsker (show 0 < p0 - e by linarith) (show p0 - e < p0 by linarith) hp01
  have : p0 - (p0 - e) = e := by ring
  rw [this] at hpin
  have e5 : 1 - (p0 - e) = 1 - p0 + e := by ring
  rw [e5] at hpin
  linarith

end StatFormal.DKW.Massart
