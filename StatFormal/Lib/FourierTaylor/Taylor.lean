import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The sharp Taylor bound for `e^{it}` (library, untrusted)

For real `t` and `N : ℕ` the Taylor remainder `R_N(t) = e^{it} − Σ_{j<N} (it)^j / j!` satisfies
`‖R_N(t)‖ ≤ |t|^N / N!` (Durrett, *Probability: Theory and Examples*, Lemma 3.3.19; Feller II, XV.4).

Mathlib's `Complex.exp_bound` needs `‖x‖ ≤ 1`, and a mean-value bound with a constant derivative bound loses a factor `N`.
The proof here is a comparison with the boundary function `B(s) = s^N / N!`: `R_{N+1}(0) = 0` and `R_{N+1}' = i R_N`, so
on `[0, t]` the bound for `R_N` feeds `image_norm_le_of_norm_deriv_right_le_deriv_boundary`; negative `t` follows from
`R_N(−t) = conj R_N(t)`.

* `expIRem N t`: the remainder `R_N(t)`;
* `hasDerivAt_expIRem`: `R_{N+1}' = i R_N`;
* `norm_expIRem_le`: `‖R_N(t)‖ ≤ |t|^N / N!` for every real `t`.
-/

set_option linter.style.longLine false

noncomputable section
open Complex Set
open scoped Nat ComplexConjugate

namespace StatFormal.FourierTaylor

/-- The Taylor remainder of order `N` of `t ↦ e^{it}`: `e^{it} − Σ_{j<N} (it)^j / j!`. -/
def expIRem (N : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (t * I) - ∑ j ∈ Finset.range N, ((t : ℂ) * I) ^ j / (j.factorial : ℂ)

lemma expIRem_zero_left (t : ℝ) : expIRem 0 t = Complex.exp (t * I) := by
  simp [expIRem]

lemma expIRem_succ_zero (N : ℕ) : expIRem (N + 1) 0 = 0 := by
  simp [expIRem, Finset.sum_range_succ']

/-- The remainder of order `N + 1` has derivative `i` times the remainder of order `N`. -/
lemma hasDerivAt_expIRem (N : ℕ) (t : ℝ) :
    HasDerivAt (expIRem (N + 1)) (I * expIRem N t) t := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (s * I)) (Complex.exp (t * I) * I) t := by
    have h := ((hasDerivAt_id (t : ℂ)).mul_const I).cexp
    simpa using h.comp_ofReal
  have hterm : ∀ j ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => ((s : ℂ) * I) ^ (j + 1) / ((j + 1).factorial : ℂ))
        (I * (((t : ℂ) * I) ^ j / (j.factorial : ℂ))) t := by
    intro j _
    have h := ((((hasDerivAt_id (t : ℂ)).mul_const I).fun_pow (j + 1)).div_const
      (((j + 1).factorial : ℕ) : ℂ)).comp_ofReal
    refine h.congr_deriv ?_
    have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have h2 : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    simp only [id, one_mul]
    field_simp
  have hfun : expIRem (N + 1) = fun s : ℝ => Complex.exp (s * I) -
      (∑ j ∈ Finset.range N, ((s : ℂ) * I) ^ (j + 1) / ((j + 1).factorial : ℂ) + 1) := by
    funext s
    simp [expIRem, Finset.sum_range_succ']
  rw [hfun]
  convert hexp.sub ((HasDerivAt.fun_sum hterm).add_const 1) using 1
  simp only [expIRem, Finset.mul_sum, mul_sub]
  ring

/-- Conjugation reflects the remainder: `R_N(−t) = conj R_N(t)`. -/
lemma expIRem_neg (N : ℕ) (t : ℝ) : expIRem N (-t) = conj (expIRem N t) := by
  simp only [expIRem, map_sub, map_sum, map_div₀, map_pow, map_mul, ← Complex.exp_conj, conj_ofReal, conj_I,
    map_natCast, ofReal_neg, neg_mul, mul_neg]

/-- The Taylor bound on the half-line `t ≥ 0`, by comparison with the boundary function `s^N / N!`. -/
lemma norm_expIRem_le_of_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖expIRem N t‖ ≤ t ^ N / (N ! : ℝ) := by
  induction N generalizing t with
  | zero => simp [expIRem_zero_left, norm_exp_ofReal_mul_I]
  | succ N ih =>
    have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => s ^ (N + 1) / ((N + 1)! : ℝ)) (x ^ N / (N ! : ℝ)) x := by
      intro x
      convert (hasDerivAt_pow (N + 1) x).div_const ((N + 1)! : ℝ) using 1
      rw [Nat.factorial_succ]
      push_cast
      have : (N ! : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
      (f := expIRem (N + 1)) (f' := fun x => I * expIRem N x)
      (fun x _ => (hasDerivAt_expIRem N x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_expIRem N x).hasDerivWithinAt)
      (by simp [expIRem_succ_zero]) hB
      (fun x hx => by rw [norm_mul, norm_I, one_mul]; exact ih hx.1)
    exact key ⟨ht, le_rfl⟩

/-- **Taylor bound for `e^{it}`.** `‖e^{it} − Σ_{j<N} (it)^j / j!‖ ≤ |t|^N / N!` for every real `t` and `N : ℕ`. -/
theorem norm_expIRem_le (N : ℕ) (t : ℝ) : ‖expIRem N t‖ ≤ |t| ^ N / (N ! : ℝ) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_expIRem_le_of_nonneg N ht
  · have h := norm_expIRem_le_of_nonneg N (neg_nonneg.mpr ht)
    rwa [expIRem_neg, Complex.norm_conj, ← abs_of_nonpos ht] at h

/-- `norm_expIRem_le` unfolded: the statement with the Taylor polynomial written out. -/
theorem norm_exp_mul_I_sub_sum_le (t : ℝ) (N : ℕ) :
    ‖Complex.exp (t * I) - ∑ j ∈ Finset.range N, ((t : ℂ) * I) ^ j / (j.factorial : ℂ)‖ ≤
      |t| ^ N / (N.factorial : ℝ) :=
  norm_expIRem_le N t

end StatFormal.FourierTaylor
