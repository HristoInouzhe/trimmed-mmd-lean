import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Convex.Mul

/-!
# Pinelis' Bennett-type inequality in Hilbert space (independent summands)

Untrusted library code: no `Statements.lean` is involved.

Pinelis (1994), *Optimum bounds for the distributions of martingales in Banach spaces*, Ann. Probab. 22, Theorems 3.1 and 3.4,
in the special case of a real inner-product space (`(2,1)`-smooth, `D = 1`), independent summands (the coordinates of a
product measure) and the final sum. A self-contained proof:

* `cosh_sqrt_convex`: `w ↦ cosh √w` is convex on `[0, ∞)` (power series `Σ wⁿ/(2n)!`);
* `cosh_norm_add_le`: for `x, d ∈ H` and `λ ≥ 0`,
  `cosh(λ‖x + d‖) ≤ cosh(λ‖x‖)(e^{λ‖d‖} − λ‖d‖) + λ sinh(λ‖x‖)/‖x‖ · ⟪x, d⟫`
  (write `λ²‖x + d‖²` as a convex combination of `λ²(‖x‖ ± ‖d‖)²` and use the convexity of `cosh √·`);
* `integral_cosh_norm_add_le`: integrating over a mean-zero `d = η`, the linear term vanishes:
  `E cosh(λ‖x + η‖) ≤ cosh(λ‖x‖)(1 + E(e^{λ‖η‖} − 1 − λ‖η‖))`;
* `lintegral_cosh_norm_sum_le`: by induction over the coordinates (`lmarginal`),
  `E cosh(λ‖Σ_i η_i‖) ≤ ∏_i (1 + E(e^{λ‖η_i‖} − 1 − λ‖η_i‖))`;
* `pinelis_mgf_tail` (Theorem 3.1): `P(‖Σ η_i‖ ≥ r) ≤ 2e^{−λr} ∏_i (1 + E(e^{λ‖η_i‖} − 1 − λ‖η_i‖))`;
* `exp_sub_one_sub_le_sq` (Bennett): `e^{λy} − 1 − λy ≤ (y/a)²(e^{λa} − 1 − λa)` for `0 ≤ y ≤ a`, `λ ≥ 0`;
* `pinelis_tail` (Theorem 3.4): for `‖η_i‖ ≤ a` a.s. and `Σ E‖η_i‖² ≤ b²`,
  `P(‖Σ η_i‖ ≥ r) ≤ 2 exp(r/a − (r/a + b²/a²) log(1 + ra/b²))`.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped InnerProductSpace ENNReal

namespace StatFormal.Pinelis

/-! ### Scalar lemmas -/

/-- `cosh √w = Σ wⁿ/(2n)!` for `w ≥ 0`. -/
theorem hasSum_cosh_sqrt {w : ℝ} (hw : 0 ≤ w) :
    HasSum (fun n : ℕ => w ^ n / ((2 * n).factorial : ℝ)) (cosh √w) := by
  have h := Real.hasSum_cosh √w
  have e : ∀ n : ℕ, √w ^ (2 * n) = w ^ n := fun n => by rw [pow_mul, Real.sq_sqrt hw]
  simpa only [e] using h

/-- `w ↦ cosh √w` is convex on `[0, ∞)`. -/
theorem cosh_sqrt_convex {p q θ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    cosh √(θ * p + (1 - θ) * q) ≤ θ * cosh √p + (1 - θ) * cosh √q := by
  have hw : 0 ≤ θ * p + (1 - θ) * q := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have h1 := hasSum_cosh_sqrt hw
  have h2 := ((hasSum_cosh_sqrt hp).mul_left θ).add ((hasSum_cosh_sqrt hq).mul_left (1 - θ))
  refine hasSum_le (fun n => ?_) h1 h2
  have hc := (convexOn_pow (𝕜 := ℝ) n).2 (mem_Ici.2 hp) (mem_Ici.2 hq) hθ0 (by linarith : 0 ≤ 1 - θ)
    (by ring)
  simp only [smul_eq_mul] at hc
  have hf : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right hc hf.le

/-- `cosh y ≤ e^y − y` for `y ≥ 0`. -/
theorem cosh_le_exp_sub {y : ℝ} (hy : 0 ≤ y) : cosh y ≤ exp y - y := by
  have h1 := Real.cosh_add_sinh y
  have h2 := Real.self_le_sinh_iff.2 hy
  linarith

/-- `e^y − 1 − y ≥ 0`. -/
theorem exp_sub_one_sub_nonneg (y : ℝ) : 0 ≤ exp y - 1 - y := by
  linarith [add_one_le_exp y]

/-- **Bennett's pointwise lemma**: for `0 ≤ θ ≤ 1` and `u ≥ 0`, `e^{θu} − 1 − θu ≤ θ²(e^u − 1 − u)`. -/
theorem exp_mul_sub_le_sq {θ u : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    exp (θ * u) - 1 - θ * u ≤ θ ^ 2 * (exp u - 1 - u) := by
  have hs : ∀ y : ℝ, HasSum (fun n : ℕ => y ^ (n + 2) / ((n + 2).factorial : ℝ)) (exp y - 1 - y) := by
    intro y
    have h0 : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (exp y) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
    have h := (hasSum_nat_add_iff' 2).2 h0
    have h01 : ∑ i ∈ Finset.range 2, y ^ i / (i.factorial : ℝ) = 1 + y := by
      simp [Finset.sum_range_succ]
    rw [h01] at h
    convert h using 1
    · rw [Real.exp_eq_exp_ℝ]; ring
  refine hasSum_le (fun n => ?_) (hs (θ * u)) ((hs u).mul_left (θ ^ 2))
  have hf : (0 : ℝ) < ((n + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [mul_div_assoc', mul_pow]
  refine div_le_div_of_nonneg_right ?_ hf.le
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [pow_add]
  calc θ ^ n * θ ^ 2 ≤ 1 * θ ^ 2 := mul_le_mul_of_nonneg_right (pow_le_one₀ hθ0 hθ1) (by positivity)
    _ = θ ^ 2 := one_mul _

/-- **Bennett**: for `0 ≤ y ≤ a`, `a > 0`, `λ ≥ 0`, `e^{λy} − 1 − λy ≤ (y²/a²)(e^{λa} − 1 − λa)`. -/
theorem exp_sub_one_sub_le_sq {l y a : ℝ} (hl : 0 ≤ l) (hy0 : 0 ≤ y) (hya : y ≤ a) (ha : 0 < a) :
    exp (l * y) - 1 - l * y ≤ y ^ 2 / a ^ 2 * (exp (l * a) - 1 - l * a) := by
  have h := exp_mul_sub_le_sq (θ := y / a) (u := l * a) (div_nonneg hy0 ha.le)
    ((div_le_one ha).2 hya) (mul_nonneg hl ha.le)
  have e : y / a * (l * a) = l * y := by field_simp
  rw [e, div_pow] at h
  exact h

/-! ### The pointwise step in Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The pointwise step** (Hilbert case of Pinelis' smoothness argument): for `λ ≥ 0`,
`cosh(λ‖x + d‖) ≤ cosh(λ‖x‖)(e^{λ‖d‖} − λ‖d‖) + λ sinh(λ‖x‖)/‖x‖ · ⟪x, d⟫`. -/
theorem cosh_norm_add_le (x d : H) {l : ℝ} (hl : 0 ≤ l) :
    cosh (l * ‖x + d‖) ≤
      cosh (l * ‖x‖) * (exp (l * ‖d‖) - l * ‖d‖) + l * sinh (l * ‖x‖) / ‖x‖ * ⟪x, d⟫_ℝ := by
  by_cases hx : x = 0
  · subst hx
    simp only [zero_add, norm_zero, mul_zero, cosh_zero, one_mul, inner_zero_left, add_zero]
    exact cosh_le_exp_sub (mul_nonneg hl (norm_nonneg _))
  by_cases hd : d = 0
  · subst hd
    simp
  set r := ‖x‖ with hr
  set δ := ‖d‖ with hδ
  set p := ⟪x, d⟫_ℝ with hp
  have hr0 : 0 ≤ r := norm_nonneg _
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hrpos : 0 < r := norm_pos_iff.2 hx
  have hδpos : 0 < δ := norm_pos_iff.2 hd
  -- the convex combination
  have hpabs : |p| ≤ r * δ := abs_real_inner_le_norm x d
  set q := p / (r * δ) with hq
  have hrδ : 0 < r * δ := mul_pos hrpos hδpos
  have hpq : p = q * (r * δ) := by rw [hq]; field_simp
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hrδ]; exact (le_abs_self p).trans hpabs
  have hq2 : -1 ≤ q := by
    rw [hq, le_div_iff₀ hrδ]; linarith [neg_abs_le p]
  set θ := (1 + q) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hsq : ‖x + d‖ ^ 2 = r ^ 2 + 2 * p + δ ^ 2 := norm_add_sq_real x d
  have hcomb : (l * ‖x + d‖) ^ 2 = θ * (l * (r + δ)) ^ 2 + (1 - θ) * (l * (r - δ)) ^ 2 := by
    rw [mul_pow, hsq, hpq, hθ]; ring
  have hL : cosh (l * ‖x + d‖) = cosh √((l * ‖x + d‖) ^ 2) := by
    rw [Real.sqrt_sq (mul_nonneg hl (norm_nonneg _))]
  have hc := cosh_sqrt_convex (sq_nonneg (l * (r + δ))) (sq_nonneg (l * (r - δ))) hθ0 hθ1
  rw [← hcomb, ← hL, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, Real.cosh_abs, Real.cosh_abs] at hc
  rw [mul_add, mul_sub, Real.cosh_add, Real.cosh_sub] at hc
  -- the algebra
  set CA := cosh (l * r)
  set SA := sinh (l * r)
  set CB := cosh (l * δ)
  set SB := sinh (l * δ)
  have hSA : 0 ≤ SA := Real.sinh_nonneg_iff.2 (mul_nonneg hl hr0)
  have hCS : SA < CA := Real.sinh_lt_cosh _
  have hSB : l * δ ≤ SB := Real.self_le_sinh_iff.2 (mul_nonneg hl hδ0)
  have hexp : exp (l * δ) = CB + SB := (Real.cosh_add_sinh _).symm
  have hlin : l * SA / r * p = q * SA * (l * δ) := by
    rw [hpq]; field_simp
  rw [hexp, hlin]
  have hkey : 0 ≤ (SB - l * δ) * (CA - q * SA) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith
  have hθq : θ * (CA * CB + SA * SB) + (1 - θ) * (CA * CB - SA * SB) = CA * CB + q * SA * SB := by
    rw [hθ]; ring
  nlinarith [hc, hθq, hkey]

end Hilbert

/-! ### Integration: one coordinate, the product, the tails -/

section Prob

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem norm_le_exp_div {l y : ℝ} (hl : 0 < l) : y ≤ exp (l * y) / l := by
  rw [le_div_iff₀ hl]; linarith [add_one_le_exp (l * y)]

/-- Integrability consequences of `E e^{λ‖η‖} < ∞`. -/
theorem integrable_of_exp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {η : Ω → H}
    (hη : AEStronglyMeasurable η ν) {l : ℝ} (hl : 0 < l) (hexp : Integrable (fun ω => exp (l * ‖η ω‖)) ν) :
    Integrable (fun ω => ‖η ω‖) ν ∧ Integrable η ν := by
  have h1 : Integrable (fun ω => ‖η ω‖) ν :=
    Integrable.mono' (hexp.div_const l) hη.norm (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_norm]; exact norm_le_exp_div hl)
  exact ⟨h1, Integrable.mono' h1 hη (ae_of_all _ fun ω => le_rfl)⟩

/-- **One coordinate**: for a mean-zero `η` with `E e^{λ‖η‖} < ∞` (`λ > 0`) and any `x ∈ H`,
`E cosh(λ‖x + η‖) ≤ cosh(λ‖x‖)(1 + E(e^{λ‖η‖} − 1 − λ‖η‖))` (and the left side is integrable). -/
theorem integral_cosh_norm_add_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {η : Ω → H} (hη : AEStronglyMeasurable η ν) {l : ℝ} (hl : 0 < l)
    (hexp : Integrable (fun ω => exp (l * ‖η ω‖)) ν) (h0 : ∫ ω, η ω ∂ν = 0) (x : H) :
    Integrable (fun ω => cosh (l * ‖x + η ω‖)) ν ∧
      ∫ ω, cosh (l * ‖x + η ω‖) ∂ν ≤
        cosh (l * ‖x‖) * (1 + ∫ ω, (exp (l * ‖η ω‖) - 1 - l * ‖η ω‖) ∂ν) := by
  obtain ⟨hn, hi⟩ := integrable_of_exp hη hl hexp
  have hmeas : AEStronglyMeasurable (fun ω => cosh (l * ‖x + η ω‖)) ν :=
    (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.add continuous_id).norm))
      |>.comp_aestronglyMeasurable hη
  have hcI : Integrable (fun ω => cosh (l * ‖x + η ω‖)) ν := by
    refine Integrable.mono' (hexp.const_mul (exp (l * ‖x‖))) hmeas (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), ← Real.exp_add]
    have h1 := cosh_le_exp_sub (mul_nonneg hl.le (norm_nonneg (x + η ω)))
    have h2 : exp (l * ‖x + η ω‖) ≤ exp (l * ‖x‖ + l * ‖η ω‖) :=
      Real.exp_le_exp.2 (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hl.le)
    have h3 : 0 ≤ l * ‖x + η ω‖ := mul_nonneg hl.le (norm_nonneg _)
    linarith
  refine ⟨hcI, ?_⟩
  set c := l * sinh (l * ‖x‖) / ‖x‖
  have jE : Integrable (fun ω => exp (l * ‖η ω‖) - l * ‖η ω‖) ν := hexp.sub (hn.const_mul l)
  have jI : Integrable (fun ω => ⟪x, η ω⟫_ℝ) ν := hi.const_inner x
  have jR : Integrable (fun ω => cosh (l * ‖x‖) * (exp (l * ‖η ω‖) - l * ‖η ω‖) + c * ⟪x, η ω⟫_ℝ) ν :=
    (jE.const_mul _).add (jI.const_mul c)
  calc ∫ ω, cosh (l * ‖x + η ω‖) ∂ν
      ≤ ∫ ω, (cosh (l * ‖x‖) * (exp (l * ‖η ω‖) - l * ‖η ω‖) + c * ⟪x, η ω⟫_ℝ) ∂ν :=
        integral_mono hcI jR fun ω => cosh_norm_add_le x (η ω) hl.le
    _ = cosh (l * ‖x‖) * (1 + ∫ ω, (exp (l * ‖η ω‖) - 1 - l * ‖η ω‖) ∂ν) := by
        rw [integral_add (jE.const_mul _) (jI.const_mul c), integral_const_mul, integral_const_mul,
          integral_inner hi x, h0, inner_zero_right, mul_zero, add_zero]
        congr 1
        have j1 : Integrable (fun ω => exp (l * ‖η ω‖) - 1) ν := hexp.sub (integrable_const 1)
        rw [integral_sub j1 (hn.const_mul l), integral_sub hexp (integrable_const 1),
          integral_sub hexp (hn.const_mul l)]
        simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
        ring

theorem integral_exp_sub_nonneg {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ) (l : ℝ) :
    0 ≤ ∫ ω, (exp (l * f ω) - 1 - l * f ω) ∂ν :=
  integral_nonneg fun ω => exp_sub_one_sub_nonneg _

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

theorem stronglyMeasurable_sum_coord (η : ∀ i, Ω i → H) (hη : ∀ i, StronglyMeasurable (η i)) (s : Finset ι) :
    StronglyMeasurable (fun ω : ∀ i, Ω i => ∑ i ∈ s, η i (ω i)) :=
  Finset.stronglyMeasurable_fun_sum _ fun i _ => (hη i).comp_measurable (measurable_pi_apply i)

/-- **The product step** (Pinelis 1994, proof of Theorem 3.1, Hilbert case, independent summands):
`E cosh(λ‖Σ_i η_i‖) ≤ ∏_i (1 + E(e^{λ‖η_i‖} − 1 − λ‖η_i‖))` under `⊗_i μ_i`. -/
theorem lintegral_cosh_norm_sum_le (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : ∀ i, Ω i → H) (hη : ∀ i, StronglyMeasurable (η i)) {l : ℝ} (hl : 0 < l)
    (hexp : ∀ i, Integrable (fun ω => exp (l * ‖η i ω‖)) (μ i)) (h0 : ∀ i, ∫ ω, η i ω ∂(μ i) = 0) :
    ∫⁻ ω, ENNReal.ofReal (cosh (l * ‖∑ i, η i (ω i)‖)) ∂(Measure.pi μ) ≤
      ENNReal.ofReal (∏ i, (1 + ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))) := by
  classical
  set c : ι → ℝ := fun i => 1 + ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i) with hc
  have hc1 : ∀ i, 1 ≤ c i := fun i => by
    simp only [hc]; linarith [integral_exp_sub_nonneg (μ i) (fun ω => ‖η i ω‖) l]
  set F : (∀ i, Ω i) → ℝ≥0∞ := fun ω => ENNReal.ofReal (cosh (l * ‖∑ i, η i (ω i)‖)) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp
      (((stronglyMeasurable_sum_coord η hη univ).norm.measurable).const_mul l))
  have key : ∀ s : Finset ι, ∀ ω : ∀ i, Ω i,
      (∫⋯∫⁻_s, F ∂μ) ω ≤ ENNReal.ofReal ((∏ i ∈ s, c i) * cosh (l * ‖∑ i ∈ sᶜ, η i (ω i)‖)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ω
      simp [hF]
    | insert j s hj ih =>
      intro ω
      rw [lmarginal_insert _ hFm hj]
      set y : H := ∑ i ∈ (insert j s)ᶜ, η i (ω i) with hy
      have hsum : ∀ ξ : Ω j, ∑ i ∈ sᶜ, η i (Function.update ω j ξ i) = y + η j ξ := by
        intro ξ
        have hjs : j ∈ sᶜ := Finset.mem_compl.2 hj
        rw [← Finset.add_sum_erase _ _ hjs, hy, Finset.compl_insert, add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        · simp
      have hCs : 0 ≤ ∏ i ∈ s, c i := Finset.prod_nonneg fun i _ => (zero_le_one.trans (hc1 i))
      obtain ⟨hI, hle⟩ := integral_cosh_norm_add_le (μ j) (hη j).aestronglyMeasurable hl (hexp j) (h0 j) y
      calc ∫⁻ ξ, (∫⋯∫⁻_s, F ∂μ) (Function.update ω j ξ) ∂(μ j)
          ≤ ∫⁻ ξ, ENNReal.ofReal ((∏ i ∈ s, c i) * cosh (l * ‖y + η j ξ‖)) ∂(μ j) := by
            refine lintegral_mono fun ξ => (ih _).trans (le_of_eq ?_)
            rw [hsum]
        _ = ENNReal.ofReal (∏ i ∈ s, c i) * ∫⁻ ξ, ENNReal.ofReal (cosh (l * ‖y + η j ξ‖)) ∂(μ j) := by
            simp_rw [ENNReal.ofReal_mul hCs]
            rw [lintegral_const_mul]
            exact ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp
              ((((hη j).const_add y).norm.measurable).const_mul l))
        _ = ENNReal.ofReal (∏ i ∈ s, c i) * ENNReal.ofReal (∫ ξ, cosh (l * ‖y + η j ξ‖) ∂(μ j)) := by
            rw [ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun ξ => (Real.cosh_pos _).le)]
        _ ≤ ENNReal.ofReal (∏ i ∈ s, c i) * ENNReal.ofReal (cosh (l * ‖y‖) * c j) := by
            gcongr
        _ = ENNReal.ofReal ((∏ i ∈ insert j s, c i) * cosh (l * ‖y‖)) := by
            rw [← ENNReal.ofReal_mul hCs, Finset.prod_insert hj]
            congr 1; ring
  have hne : Nonempty (∀ i, Ω i) := ⟨fun i => (nonempty_of_isProbabilityMeasure (μ i)).some⟩
  obtain ⟨ω0⟩ := hne
  rw [lintegral_eq_lmarginal_univ ω0]
  refine (key univ ω0).trans (le_of_eq ?_)
  simp

/-- **Pinelis (1994) Theorem 3.1**, Hilbert case, independent summands, final sum:
`P(‖Σ_i η_i‖ ≥ r) ≤ 2e^{−λr} ∏_i (1 + E(e^{λ‖η_i‖} − 1 − λ‖η_i‖))`. -/
theorem pinelis_mgf_tail (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : ∀ i, Ω i → H) (hη : ∀ i, StronglyMeasurable (η i)) {l : ℝ} (hl : 0 < l)
    (hexp : ∀ i, Integrable (fun ω => exp (l * ‖η i ω‖)) (μ i)) (h0 : ∀ i, ∫ ω, η i ω ∂(μ i) = 0)
    {r : ℝ} (hr : 0 ≤ r) :
    Measure.pi μ {ω | r ≤ ‖∑ i, η i (ω i)‖} ≤
      ENNReal.ofReal (2 * exp (-(l * r)) * ∏ i, (1 + ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))) := by
  set C := ∏ i, (1 + ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i)) with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun i _ => by
    linarith [integral_exp_sub_nonneg (μ i) (fun ω => ‖η i ω‖) l]
  set F : (∀ i, Ω i) → ℝ≥0∞ := fun ω => ENNReal.ofReal (cosh (l * ‖∑ i, η i (ω i)‖)) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp
      (((stronglyMeasurable_sum_coord η hη univ).norm.measurable).const_mul l))
  have hcr : 0 < cosh (l * r) := Real.cosh_pos _
  have hsub : {ω : ∀ i, Ω i | r ≤ ‖∑ i, η i (ω i)‖} ⊆ {ω | ENNReal.ofReal (cosh (l * r)) ≤ F ω} := by
    intro ω hω
    simp only [mem_setOf_eq, hF] at hω ⊢
    refine ENNReal.ofReal_le_ofReal (Real.cosh_le_cosh.2 ?_)
    rw [abs_of_nonneg (mul_nonneg hl.le hr), abs_of_nonneg (mul_nonneg hl.le (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left hω hl.le
  have hmk := meas_ge_le_lintegral_div (μ := Measure.pi μ) hFm.aemeasurable (ENNReal.ofReal_pos.2 hcr).ne' ENNReal.ofReal_ne_top
  have hint := lintegral_cosh_norm_sum_le μ η hη hl hexp h0
  calc Measure.pi μ {ω | r ≤ ‖∑ i, η i (ω i)‖}
      ≤ Measure.pi μ {ω | ENNReal.ofReal (cosh (l * r)) ≤ F ω} := measure_mono hsub
    _ ≤ (∫⁻ ω, F ω ∂(Measure.pi μ)) / ENNReal.ofReal (cosh (l * r)) := hmk
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (cosh (l * r)) := by gcongr
    _ = ENNReal.ofReal (C / cosh (l * r)) := (ENNReal.ofReal_div_of_pos hcr).symm
    _ ≤ ENNReal.ofReal (2 * exp (-(l * r)) * C) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hcr]
        have h1 : 1 ≤ 2 * exp (-(l * r)) * cosh (l * r) := by
          rw [Real.cosh_eq, show 2 * exp (-(l * r)) * ((exp (l * r) + exp (-(l * r))) / 2) =
            exp (-(l * r)) * exp (l * r) + exp (-(l * r)) * exp (-(l * r)) by ring, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero]
          linarith [(exp_pos (-(l * r))).le, mul_pos (exp_pos (-(l * r))) (exp_pos (-(l * r)))]
        nlinarith

/-- `2e^{−λr} ∏ (1 + E_i) ≤ 2 exp(−λr + Σ E_i)` for `E_i ≥ 0`. -/
theorem two_exp_mul_prod_le {r l : ℝ} (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) :
    2 * exp (-(l * r)) * ∏ i, (1 + E i) ≤ 2 * exp (-(l * r) + ∑ i, E i) := by
  rw [Real.exp_add, Real.exp_sum, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => by linarith [hE i]) fun i _ => ?_) (by positivity)
  linarith [add_one_le_exp (E i)]

/-- **Pinelis (1994) Theorem 3.4**, Hilbert case (`D = 1`), independent summands, final sum: for `‖η_i‖ ≤ a` a.s.,
`Σ_i E‖η_i‖² ≤ b²`, `a, b² > 0` and `r ≥ 0`, `P(‖Σ_i η_i‖ ≥ r) ≤ 2 exp(r/a − (r/a + b²/a²) log(1 + ra/b²))`. -/
theorem pinelis_tail (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : ∀ i, Ω i → H) (hη : ∀ i, StronglyMeasurable (η i)) (h0 : ∀ i, ∫ ω, η i ω ∂(μ i) = 0)
    {a b2 r : ℝ} (ha : ∀ i, ∀ᵐ ω ∂(μ i), ‖η i ω‖ ≤ a) (hb : ∑ i, ∫ ω, ‖η i ω‖ ^ 2 ∂(μ i) ≤ b2)
    (ha0 : 0 < a) (hb0 : 0 < b2) (hr : 0 ≤ r) :
    Measure.pi μ {ω | r ≤ ‖∑ i, η i (ω i)‖} ≤
      ENNReal.ofReal (2 * exp (r / a - (r / a + b2 / a ^ 2) * log (1 + r * a / b2))) := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · subst hr0
    refine prob_le_one.trans ?_
    simp
  set Lg := log (1 + r * a / b2) with hLg
  have h1 : 0 < r * a / b2 := by positivity
  have hLg0 : 0 < Lg := Real.log_pos (by linarith)
  set l := Lg / a with hl
  have hl0 : 0 < l := div_pos hLg0 ha0
  have hla : l * a = Lg := by rw [hl]; field_simp
  have hexpLg : exp Lg = 1 + r * a / b2 := Real.exp_log (by linarith)
  have hexp : ∀ i, Integrable (fun ω => exp (l * ‖η i ω‖)) (μ i) := fun i =>
    Integrable.of_bound (Real.measurable_exp.comp ((hη i).norm.measurable.const_mul l)).aestronglyMeasurable
      (exp (l * a))
      ((ha i).mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hl0.le))
  have htail := pinelis_mgf_tail μ η hη hl0 hexp h0 hr
  set K := (exp (l * a) - 1 - l * a) / a ^ 2 with hK
  have hK0 : 0 ≤ K := div_nonneg (exp_sub_one_sub_nonneg _) (by positivity)
  have hEi : ∀ i, ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i) ≤ K * ∫ ω, ‖η i ω‖ ^ 2 ∂(μ i) := by
    intro i
    obtain ⟨hn, -⟩ := integrable_of_exp (hη i).aestronglyMeasurable hl0 (hexp i)
    have hsq : Integrable (fun ω => ‖η i ω‖ ^ 2) (μ i) :=
      Integrable.of_bound ((hη i).norm.pow 2).aestronglyMeasurable (a ^ 2)
        ((ha i).mono fun ω hω => by
          rw [Real.norm_eq_abs, abs_pow, abs_norm]
          exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
    rw [← integral_const_mul]
    refine integral_mono_ae ((hexp i).sub (integrable_const 1) |>.sub (hn.const_mul l)) (hsq.const_mul K)
      ((ha i).mono fun ω hω => ?_)
    have := exp_sub_one_sub_le_sq hl0.le (norm_nonneg (η i ω)) hω ha0
    rw [hK]
    calc exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖ ≤ ‖η i ω‖ ^ 2 / a ^ 2 * (exp (l * a) - 1 - l * a) := this
      _ = (exp (l * a) - 1 - l * a) / a ^ 2 * ‖η i ω‖ ^ 2 := by ring
  have hsumE : ∑ i, ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i) ≤ K * b2 := by
    calc _ ≤ ∑ i, K * ∫ ω, ‖η i ω‖ ^ 2 ∂(μ i) := Finset.sum_le_sum fun i _ => hEi i
      _ = K * ∑ i, ∫ ω, ‖η i ω‖ ^ 2 ∂(μ i) := (Finset.mul_sum _ _ _).symm
      _ ≤ K * b2 := mul_le_mul_of_nonneg_left hb hK0
  have hprod := two_exp_mul_prod_le (r := r) (l := l)
    (fun i => ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))
    (fun i => integral_exp_sub_nonneg (μ i) (fun ω => ‖η i ω‖) l)
  have hexpo : -(l * r) + K * b2 = r / a - (r / a + b2 / a ^ 2) * Lg := by
    rw [hK, hla, hexpLg, hl]
    field_simp
    ring
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  calc 2 * exp (-(l * r)) * ∏ i, (1 + ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i))
      ≤ 2 * exp (-(l * r) + ∑ i, ∫ ω, (exp (l * ‖η i ω‖) - 1 - l * ‖η i ω‖) ∂(μ i)) := hprod
    _ ≤ 2 * exp (-(l * r) + K * b2) := by gcongr
    _ = 2 * exp (r / a - (r / a + b2 / a ^ 2) * Lg) := by rw [hexpo]

end Prob

end StatFormal.Pinelis
