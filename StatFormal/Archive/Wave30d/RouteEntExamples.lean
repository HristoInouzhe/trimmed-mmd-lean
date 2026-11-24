import StatFormal.Archive.Wave30d.RouteJointMinEnt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Route (wave 30d) — paper 2 `prop:jointmin`, entropic sets: non-vacuity and the unbounded-exponent regime (untrusted)

Both results are route lemmas (critic, 2026-10-20: not printed, so not targets); they witness that the targets
`jointmin_ent_group/cert/upper` are not vacuous (non-empty sets) and are not confined to a bounded exponent.

* `jointmin_ent_nonempty`: the product coupling `P̂ ⊗ ν` (`Measure.fst_prod`, `snd_prod`, `klDiv_self`) and Tonelli
  (`lintegral_prod_le`) over the discrete centre.
* `jointmin_ent_unbounded`: `K = ℝ`, `ν = N(0, s²)`, `λ = w² · 8s²/(8s² + ε)`: the exponent is `(z − x₀)²/(8s²)`
  (unbounded above), `E_ν e^{(z−x₀)²/(8s²)} ≤ e^{x₀²/(4s²)} E_ν e^{z²/(4s²)} < ∞` (Gaussian density times
  `e^{z²/(4s²)}` is `(2πs²)^{−1/2} e^{−z²/(4s²)}`, integrable by `integrable_exp_neg_mul_sq`), so `T(w, λ) < ∞`;
  `T⁰(w, λ) = ⊤` by the Wave 28e route `T0_cases` (`λ < w² = ‖(id⁻¹)ᵀ w‖²`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory Real
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30d

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a
open StatFormal.RobustEquality.Paper2.Alternating (centre)
open StatFormal.Foundations.GibbsUnbounded

/-- Non-vacuity of the entropic sets on `K = E` (route lemma, not a target; moved out of the draft statements by
the critic, 2026-10-20, as not printed): the reference itself belongs to the set as soon as the budget covers its
independent transport cost from the centre, `Σ_i a_i E_{z ∼ ν} ‖G(z − x_i)‖² ≤ r` (the coupling `P̂ ⊗ ν` has
`KL = 0`). -/
theorem jointmin_ent_nonempty (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] (n : ℕ) (G : E ≃L[ℝ] E) (ε r : ℝ) (ν : Measure E) [IsProbabilityMeasure ν] (a : Fin n → ℝ)
    (x : Fin n → E) (ha : ProbW a)
    (hcost : (∑ i, ENNReal.ofReal (a i) * ∫⁻ z, ENNReal.ofReal (‖G (z - x i)‖ ^ 2) ∂ν) ≤ ENNReal.ofReal r) :
    ν ∈ entBall G ε ν a x r := by
  have : IsProbabilityMeasure (centre a x) := centre_isProb' ha.1 ha.2 x
  refine ⟨inferInstance, ?_⟩
  refine iInf_le_of_le ((centre a x).prod ν) (iInf_le_of_le ⟨Measure.fst_prod, Measure.snd_prod⟩ ?_)
  rw [klDiv_self, mul_zero, add_zero]
  refine (lintegral_prod_le _).trans ?_
  rw [lintegral_centre]
  exact hcost

/-- The Gaussian exponential moment `E_{N(0,s²)} e^{z²/(4s²)} < ∞`. -/
lemma gauss_exp_moment {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, ENNReal.ofReal (exp (z ^ 2 / (4 * s ^ 2))) ∂(gaussianReal 0 (s ^ 2).toNNReal) ≠ ⊤ := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hv : (s ^ 2).toNNReal ≠ 0 := by simpa using hs.ne'
  have hvR : (((s ^ 2).toNNReal : ℝ≥0) : ℝ) = s ^ 2 := Real.coe_toNNReal _ hs2.le
  have hmeas : Measurable fun z : ℝ => ENNReal.ofReal (exp (z ^ 2 / (4 * s ^ 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [gaussianReal_of_var_ne_zero 0 hv, lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 _) hmeas]
  have e : ∀ z : ℝ, (gaussianPDF 0 (s ^ 2).toNNReal * fun z => ENNReal.ofReal (exp (z ^ 2 / (4 * s ^ 2)))) z =
      ENNReal.ofReal ((√(2 * π * s ^ 2))⁻¹ * exp (-(1 / (4 * s ^ 2)) * z ^ 2)) := fun z => by
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal, hvR]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    field_simp
    ring
  simp_rw [e]
  exact (((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (4 * s ^ 2))).const_mul
    (√(2 * π * s ^ 2))⁻¹).lintegral_lt_top).ne

/-- The entropic certificate beyond a bounded exponent (route lemma, not a target; moved out of the draft statements
by the critic, 2026-10-20, as not printed; evidence for paper note (1), the bounded-above hypothesis of `eq:gibbs`):
on `K = ℝ` with a Gaussian reference `N(0, s²)` and the ordinary cost, for every `w ≠ 0` there is a multiplier
`0 < λ < w²` at which the exponent `(f_{h_w}(x₀, ·) − λ c(x₀, ·))/(λε)` is unbounded above at every anchor, the
entropic `T(w, λ)` is FINITE, while the `ε = 0` term `T⁰(w, λ)` of the frozen `Paper2.Seminorm` is `+∞`. -/
theorem jointmin_ent_unbounded (n : ℕ) (ε s r w : ℝ) (a : Fin n → ℝ) (x : Fin n → ℝ) (ha : ProbW a) (hε : 0 < ε)
    (hs : 0 < s) (hw : w ≠ 0) :
    ∃ lam : ℝ, 0 < lam ∧ lam < w ^ 2 ∧
      (∀ z₀ : ℝ, ¬ BddAbove (Set.range fun z : ℝ =>
        (⟪w, z - z₀⟫ ^ 2 - lam * ‖(ContinuousLinearEquiv.refl ℝ ℝ) (z - z₀)‖ ^ 2) / (lam * ε))) ∧
      Tent (ContinuousLinearEquiv.refl ℝ ℝ) ε (gaussianReal 0 (s ^ 2).toNNReal) a x r w lam ≠ ⊤ ∧
      T0 (ContinuousLinearEquiv.refl ℝ ℝ) r a x w lam = ⊤ := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hw2 : 0 < w ^ 2 := by positivity
  set lam : ℝ := w ^ 2 * (8 * s ^ 2) / (8 * s ^ 2 + ε) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamw : lam < w ^ 2 := by
    rw [hlam, div_lt_iff₀ (by positivity)]; nlinarith
  set k : ℝ := 1 / (8 * s ^ 2) with hk
  have hk0 : 0 < k := by positivity
  -- the exponent is `k (z − z₀)²`
  have hexp : ∀ u : ℝ, (⟪w, u⟫ ^ 2 - lam * ‖(ContinuousLinearEquiv.refl ℝ ℝ) u‖ ^ 2) / (lam * ε) = k * u ^ 2 := by
    intro u
    have h1 : ⟪w, u⟫ = u * w := by simp [RCLike.inner_apply]
    have h2 : ‖(ContinuousLinearEquiv.refl ℝ ℝ) u‖ ^ 2 = u ^ 2 := by simp
    rw [h1, h2, hlam, hk]
    field_simp
    ring
  refine ⟨lam, hlam0, hlamw, fun z₀ => ?_, ?_, ?_⟩
  · rintro ⟨B, hB⟩
    set u : ℝ := (|B| + 1) / k + 1
    have hu1 : 1 ≤ u := by have : 0 ≤ (|B| + 1) / k := by positivity
                           linarith
    have hB' := hB ⟨z₀ + u, rfl⟩
    simp only [add_sub_cancel_left] at hB'
    rw [hexp] at hB'
    have hku : k * u = |B| + 1 + k := by
      simp only [u]; field_simp
    have : k * u ≤ k * u ^ 2 := by
      have : u ≤ u ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hk0.le
    linarith [le_abs_self B]
  · -- `T(w, λ) < ⊤`
    have hZ : ∀ i, ∫⁻ z, ENNReal.ofReal (exp ((⟪w, z - x i⟫ ^ 2 - lam * ‖(ContinuousLinearEquiv.refl ℝ ℝ)
        (z - x i)‖ ^ 2) / (lam * ε))) ∂(gaussianReal 0 (s ^ 2).toNNReal) ≠ ⊤ := fun i => by
      simp_rw [hexp]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gauss_exp_moment hs))
        (b := ENNReal.ofReal (exp (2 * k * x i ^ 2)) *
          ∫⁻ z, ENNReal.ofReal (exp (z ^ 2 / (4 * s ^ 2))) ∂(gaussianReal 0 (s ^ 2).toNNReal)) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun z => ?_
      rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
      have h4 : z ^ 2 / (4 * s ^ 2) = 2 * k * z ^ 2 := by rw [hk]; field_simp; ring
      rw [h4]
      nlinarith [sq_nonneg (z + x i)]
    set L : Fin n → EReal := fun i => ENNReal.log (∫⁻ z, ENNReal.ofReal (exp ((⟪w, z - x i⟫ ^ 2 -
      lam * ‖(ContinuousLinearEquiv.refl ℝ ℝ) (z - x i)‖ ^ 2) / (lam * ε))) ∂(gaussianReal 0 (s ^ 2).toNNReal))
    have hL : ∀ i, L i ≠ ⊤ := fun i => by
      simp only [L, ne_eq, ENNReal.log_eq_top_iff]; exact hZ i
    have hsum : ∑ i, ((a i : ℝ) : EReal) * L i ≤ ((∑ i, a i * (L i).toReal : ℝ) : EReal) := by
      rw [EReal.coe_finsetSum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left (EReal.le_coe_toReal (hL i)) (EReal.coe_nonneg.2 (ha.1 i))
    have hle : Tent (ContinuousLinearEquiv.refl ℝ ℝ) ε (gaussianReal 0 (s ^ 2).toNNReal) a x r w lam ≤
        ((lam * r + lam * ε * ∑ i, a i * (L i).toReal : ℝ) : EReal) := by
      unfold Tent
      rw [EReal.coe_add, EReal.coe_mul (lam * ε)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (EReal.coe_nonneg.2 (mul_pos hlam0 hε).le))
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  · -- `T⁰(w, λ) = ⊤`
    rw [StatFormal.Wave28e.T0_cases _ r ha x w hlam0]
    have hadj : ‖ContinuousLinearMap.adjoint (((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) w‖ ^ 2 =
        w ^ 2 := by
      simp [Real.norm_eq_abs, sq_abs, ContinuousLinearMap.adjoint_id]
    rw [hadj, if_neg (not_le.2 hlamw), EReal.coe_add_top]

end StatFormal.Wave30d
