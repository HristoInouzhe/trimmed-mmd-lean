import StatFormal.Archive.Wave23d.Statements
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Route — R `prop:ball` (untrusted)

The region contains `u* = τ e_K`, so `β ≤ TD(u*) ≤ μ_K{z_K ≥ τ} = P(X_K ≥ τ)`. With `X_K = R Z_K/(K‖ζ‖)`,
`{X_K ≥ τ} ⊆ {|Z_K| ≥ τ s K} ∪ {‖ζ‖ < s}`. Chernoff (`mgf` of `N(0,1)`) gives `P(|Z| ≥ a) ≤ 2e^{−a²/2}`; on `{‖ζ‖ < s}`
every `|Z_k| < s k`, and the density bound `P(|Z| < y) ≤ 0.8 y` with independence gives `P(‖ζ‖ < s) ≤ 2^{−m}`,
`m = ⌊1/(1.6 s)⌋`. With `s = (τK)^{−2/3}` both terms are `≤ 2e^{−0.43(τK)^{2/3}}` (`log 2/1.6 > 0.43`).
Monotonicity of `τ_{K,p}`: `‖Π_K X‖ ≤ ‖Π_{K+1} X‖` pathwise, and Bessel gives `‖Π_K X‖ ≤ 1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset Real
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.Wave1 (truncK regionDepth tukeyDepth)

/-! ### Two Gaussian bounds -/

lemma gauss_tail {a : ℝ} (ha : 0 ≤ a) :
    gaussianReal 0 1 {x | a ≤ |x|} ≤ ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 2)) := by
  set μ := gaussianReal 0 1
  have hsub : {x : ℝ | a ≤ |x|} ⊆ {x | a ≤ id x} ∪ {x | id x ≤ -a} := by
    intro x hx
    simp only [mem_setOf_eq, id] at hx ⊢
    rcases le_or_gt 0 x with h | h
    · left; rwa [abs_of_nonneg h] at hx
    · right; rw [abs_of_neg h] at hx; show x ≤ -a; linarith
  have hmgf : ∀ t, mgf id μ t = Real.exp (t ^ 2 / 2) := by
    intro t; rw [mgf_id_gaussianReal]; simp
  have h1 : μ.real {x | a ≤ id x} ≤ Real.exp (-a ^ 2 / 2) := by
    have := measure_ge_le_exp_mul_mgf (X := id) (μ := μ) a ha (integrable_exp_mul_gaussianReal a)
    rw [hmgf, ← Real.exp_add] at this
    convert this using 2; ring
  have h2 : μ.real {x | id x ≤ -a} ≤ Real.exp (-a ^ 2 / 2) := by
    have := measure_le_le_exp_mul_mgf (X := id) (μ := μ) (-a) (by linarith : -a ≤ 0)
      (integrable_exp_mul_gaussianReal (-a))
    rw [hmgf, ← Real.exp_add] at this
    convert this using 2; ring
  calc μ {x | a ≤ |x|} ≤ μ ({x | a ≤ id x} ∪ {x | id x ≤ -a}) := measure_mono hsub
    _ ≤ μ {x | a ≤ id x} + μ {x | id x ≤ -a} := measure_union_le _ _
    _ = ENNReal.ofReal (μ.real {x | a ≤ id x}) + ENNReal.ofReal (μ.real {x | id x ≤ -a}) := by
      rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-a ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-a ^ 2 / 2)) :=
      add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring

lemma gauss_small {y : ℝ} (hy : 0 ≤ y) : gaussianReal 0 1 {x | |x| < y} ≤ ENNReal.ofReal (0.8 * y) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  have hset : {x : ℝ | |x| < y} = Ioo (-y) y := by ext x; simp [abs_lt]
  have hpdf : ∀ x, gaussianPDF 0 1 x ≤ ENNReal.ofReal (√(2 * π))⁻¹ := by
    intro x
    simp only [gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    have hpos : 0 < (√(2 * π))⁻¹ := by positivity
    nlinarith
  calc ∫⁻ x in {x | |x| < y}, gaussianPDF 0 1 x ≤ ∫⁻ _ in {x : ℝ | |x| < y}, ENNReal.ofReal (√(2 * π))⁻¹ :=
        lintegral_mono hpdf
    _ = ENNReal.ofReal (√(2 * π))⁻¹ * ENNReal.ofReal (2 * y) := by
      rw [setLIntegral_const, hset, Real.volume_Ioo]; congr 2; ring
    _ = ENNReal.ofReal ((√(2 * π))⁻¹ * (2 * y)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (0.8 * y) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hπ : (2.5 : ℝ) ≤ √(2 * π) := by
        rw [show (2.5 : ℝ) = √(2.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_d2])
      have : (√(2 * π))⁻¹ ≤ 0.4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
      nlinarith

/-! ### The setting -/

section Setting
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {e : ℕ → H} {Z : ℕ → Ω → ℝ}
  {ζ : Ω → H} {R : Ω → ℝ}

lemma continuous_truncK' (e : ℕ → H) (K : ℕ) : Continuous (truncK e K) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_const.inner continuous_id)

lemma measurable_ballX (hS : BallSetting P e Z ζ R) : Measurable (ballX R ζ) := by
  obtain ⟨-, -, -, -, hζ, -, hR, -⟩ := hS
  exact (hR.div hζ.norm).smul hζ

lemma measurable_truncK_ballX (hS : BallSetting P e Z ζ R) (K : ℕ) :
    Measurable fun ω => truncK e K (ballX R ζ ω) :=
  (continuous_truncK' e K).measurable.comp (measurable_ballX hS)

lemma norm_ballX_le (hS : BallSetting P e Z ζ R) (ω : Ω) : ‖ballX R ζ ω‖ ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, hR⟩ := hS
  unfold ballX
  rw [norm_smul, Real.norm_eq_abs]
  rcases eq_or_ne ‖ζ ω‖ 0 with h | h
  · rw [h]; simp
  · rw [abs_div, abs_norm, div_mul_cancel₀ _ h, abs_of_nonneg (hR ω).1]; exact (hR ω).2

lemma norm_truncK_sq (K : ℕ) (x : H) : ‖truncK e K x‖ ^ 2 = ∑ k : Fin K, ⟪e k, x⟫ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  congr 1; ext k; simp [truncK, Real.norm_eq_abs, sq_abs]

lemma norm_truncK_le (he : Orthonormal ℝ e) (K : ℕ) (x : H) : ‖truncK e K x‖ ≤ ‖x‖ := by
  have h := he.sum_inner_products_le (s := Finset.range K) x
  have h2 : ‖truncK e K x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_truncK_sq]
    calc ∑ k : Fin K, ⟪e k, x⟫ ^ 2 = ∑ k ∈ Finset.range K, ‖⟪e k, x⟫‖ ^ 2 := by
          rw [Finset.sum_range (fun k => ‖⟪e k, x⟫‖ ^ 2)]; congr 1; ext k; simp [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖x‖ ^ 2 := h
  nlinarith [norm_nonneg (truncK e K x), norm_nonneg x]

lemma norm_truncK_mono (K : ℕ) (x : H) : ‖truncK e K x‖ ≤ ‖truncK e (K + 1) x‖ := by
  have h : ‖truncK e K x‖ ^ 2 ≤ ‖truncK e (K + 1) x‖ ^ 2 := by
    rw [norm_truncK_sq, norm_truncK_sq, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc]
    linarith [sq_nonneg ⟪e (Fin.last K : ℕ), x⟫]
  nlinarith [norm_nonneg (truncK e K x), norm_nonneg (truncK e (K + 1) x)]

/-- `P(‖ζ‖ < s) ≤ 2^{−m}`, `m = ⌊1/(1.6 s)⌋`. -/
lemma small_ball (hS : BallSetting P e Z ζ R) {s : ℝ} (hs : 0 < s) :
    P {ω | ‖ζ ω‖ < s} ≤ (2⁻¹ : ℝ≥0∞) ^ ⌊1 / (1.6 * s)⌋₊ := by
  obtain ⟨he, hZm, hind, hlaw, -, hcoord, -, -⟩ := hS
  set m := ⌊1 / (1.6 * s)⌋₊
  set S : ℕ → Set ℝ := fun k => {x | |x| < s * ((k : ℝ) + 1)}
  have hSm : ∀ k, MeasurableSet (S k) := fun k => measurableSet_lt continuous_abs.measurable measurable_const
  have hsub : {ω | ‖ζ ω‖ < s} ⊆ ⋂ k ∈ Finset.range m, Z k ⁻¹' S k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [mem_iInter, Set.mem_preimage, S, Set.mem_ofPred_eq]
    intro k _
    have h1 : |⟪e k, ζ ω⟫| ≤ ‖ζ ω‖ := by
      have := abs_real_inner_le_norm (e k) (ζ ω); rwa [he.1 k, one_mul] at this
    rw [hcoord, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1), div_le_iff₀ (by positivity)] at h1
    exact h1.trans_lt (mul_lt_mul_of_pos_right hω (by positivity))
  calc P {ω | ‖ζ ω‖ < s} ≤ P (⋂ k ∈ Finset.range m, Z k ⁻¹' S k) := measure_mono hsub
    _ = ∏ k ∈ Finset.range m, P (Z k ⁻¹' S k) := hind.measure_inter_preimage_eq_mul _ fun k _ => hSm k
    _ ≤ ∏ _k ∈ Finset.range m, (2⁻¹ : ℝ≥0∞) := by
      refine Finset.prod_le_prod' fun k hk => ?_
      rw [← Measure.map_apply (hZm k) (hSm k), hlaw]
      refine (gauss_small (by positivity)).trans ?_
      have hkm : (k : ℝ) + 1 ≤ m := by
        have := Finset.mem_range.1 hk; exact_mod_cast this
      have hm : (m : ℝ) ≤ 1 / (1.6 * s) := Nat.floor_le (by positivity)
      have : 0.8 * (s * ((k : ℝ) + 1)) ≤ 2⁻¹ := by
        have h2 : s * ((k : ℝ) + 1) ≤ s * (1 / (1.6 * s)) := mul_le_mul_of_nonneg_left (hkm.trans hm) hs.le
        have h3 : s * (1 / (1.6 * s)) = 1 / 1.6 := by field_simp
        rw [h3] at h2; linarith
      calc ENNReal.ofReal (0.8 * (s * ((k : ℝ) + 1))) ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal this
        _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
    _ = (2⁻¹ : ℝ≥0∞) ^ m := by rw [Finset.prod_const, Finset.card_range]

/-- `2^{−⌊A/1.6⌋} ≤ 2 e^{−0.43 A}`. -/
lemma two_pow_floor_le {A : ℝ} (hA : 0 < A) :
    (2⁻¹ : ℝ≥0∞) ^ ⌊1 / (1.6 * (1 / A))⌋₊ ≤ ENNReal.ofReal (2 * Real.exp (-0.43 * A)) := by
  set m := ⌊1 / (1.6 * (1 / A))⌋₊
  have he : 1 / (1.6 * (1 / A)) = A / 1.6 := by field_simp
  have hm : A / 1.6 < m + 1 := by rw [← he]; exact Nat.lt_floor_add_one _
  have hconv : (2⁻¹ : ℝ≥0∞) ^ m = ENNReal.ofReal ((1 / 2) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : ((1 : ℝ) / 2) ^ m = Real.exp (m * -Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  rw [h1]
  have hl0 : 0 < Real.log 2 := by linarith
  calc Real.exp (m * -Real.log 2) ≤ Real.exp ((A / 1.6 - 1) * -Real.log 2) := by
        refine Real.exp_le_exp.2 ?_; nlinarith
    _ = 2 * Real.exp (-(Real.log 2 / 1.6) * A) := by
        rw [show (A / 1.6 - 1) * -Real.log 2 = Real.log 2 + -(Real.log 2 / 1.6) * A by ring, Real.exp_add,
          Real.exp_log (by norm_num)]
    _ ≤ 2 * Real.exp (-0.43 * A) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
        have : (0.43 : ℝ) ≤ Real.log 2 / 1.6 := by rw [le_div_iff₀ (by norm_num)]; linarith
        nlinarith

/-- The coordinate of `X` along `e_k`: `X_k = (R/‖ζ‖) Z_k/(k+1)`. -/
lemma inner_ballX (hS : BallSetting P e Z ζ R) (k : ℕ) (ω : Ω) :
    ⟪e k, ballX R ζ ω⟫ = R ω / ‖ζ ω‖ * (Z k ω / ((k : ℝ) + 1)) := by
  obtain ⟨-, -, -, -, -, hcoord, -, -⟩ := hS
  rw [ballX, inner_smul_right, hcoord]

/-- The main estimate at every radius `τ > 0`. -/
lemma ball_bound (hS : BallSetting P e Z ζ R) {K : ℕ} (hK : 0 < K) {τ : ℝ} (hτ : 0 < τ) :
    regionDepth (ballLawK P e ζ R K) (Metric.closedBall 0 τ) ≤
      ENNReal.ofReal (4 * Real.exp (-0.43 * (τ * K) ^ ((2 : ℝ) / 3))) := by
  set k0 : Fin K := ⟨K - 1, by omega⟩
  have hk0 : ((k0 : ℕ) : ℝ) + 1 = K := by
    simp only [k0]; rw [Nat.cast_sub (by omega)]; simp
  set u : EuclideanSpace ℝ (Fin K) := EuclideanSpace.single k0 τ
  have hu : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) τ := by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos hτ]
  set v : EuclideanSpace ℝ (Fin K) := EuclideanSpace.single k0 (-1)
  have hv : v ≠ 0 := by simp [v]
  have hset : {z : EuclideanSpace ℝ (Fin K) | ⟪v, z - u⟫ ≤ 0} = {z | τ ≤ z k0} := by
    ext z
    simp only [Set.mem_ofPred_eq, v, u, EuclideanSpace.inner_single_left, PiLp.sub_apply,
      EuclideanSpace.single_apply, if_pos rfl]
    simp
  have hmeas : MeasurableSet {z : EuclideanSpace ℝ (Fin K) | τ ≤ z k0} :=
    measurableSet_le measurable_const (PiLp.continuous_apply 2 _ k0).measurable
  -- the bound on the halfspace event
  set A : ℝ := (τ * K) ^ ((2 : ℝ) / 3)
  have hw : 0 < τ * K := mul_pos hτ (by exact_mod_cast hK)
  have hA : 0 < A := Real.rpow_pos_of_pos hw _
  have hA3 : A ^ 3 = (τ * K) ^ 2 := by
    simp only [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le, ← Real.rpow_natCast]; norm_num
  set s : ℝ := 1 / A
  have hs : 0 < s := by positivity
  have hinc : {ω | τ ≤ (truncK e K (ballX R ζ ω)) k0} ⊆
      Z k0 ⁻¹' {x | τ * s * K ≤ |x|} ∪ {ω | ‖ζ ω‖ < s} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    change τ ≤ ⟪e k0, ballX R ζ ω⟫ at hω
    rw [inner_ballX hS, hk0] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_le, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hz : 0 < ‖ζ ω‖ := hs.trans_le h2
    obtain ⟨-, -, -, -, -, -, -, hR⟩ := hS
    have hRZ : R ω * (Z k0 ω / K) ≤ |Z k0 ω| / K := by
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hK']
      calc R ω * Z k0 ω ≤ R ω * |Z k0 ω| := mul_le_mul_of_nonneg_left (le_abs_self _) (hR ω).1
        _ ≤ 1 * |Z k0 ω| := mul_le_mul_of_nonneg_right (hR ω).2 (abs_nonneg _)
        _ = |Z k0 ω| := one_mul _
    have : τ * ‖ζ ω‖ ≤ R ω * (Z k0 ω / K) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hz] at hω; linarith
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have : τ * s * K ≤ |Z k0 ω| := by
      have h3 : τ * s ≤ |Z k0 ω| / K := by nlinarith
      rwa [le_div_iff₀ hK'] at h3
    linarith
  have hZm := hS.2.1
  have hlaw := hS.2.2.2.1
  have hP1 : P (Z k0 ⁻¹' {x | τ * s * K ≤ |x|}) ≤ ENNReal.ofReal (2 * Real.exp (-A / 2)) := by
    rw [← Measure.map_apply (hZm k0) (measurableSet_le measurable_const continuous_abs.measurable), hlaw]
    refine (gauss_tail (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : (τ * s * K) ^ 2 = A := by
      have e1 : τ * s * K = (τ * K) / A := by simp only [s]; ring
      rw [e1, div_pow, ← hA3]; field_simp
    rw [this]
  have hP2 : P {ω | ‖ζ ω‖ < s} ≤ ENNReal.ofReal (2 * Real.exp (-0.43 * A)) :=
    (small_ball hS hs).trans (two_pow_floor_le hA)
  calc regionDepth (ballLawK P e ζ R K) (Metric.closedBall 0 τ)
      ≤ tukeyDepth (ballLawK P e ζ R K) u := iInf₂_le u hu
    _ ≤ ballLawK P e ζ R K {z | ⟪v, z - u⟫ ≤ 0} := iInf₂_le v hv
    _ = P {ω | τ ≤ (truncK e K (ballX R ζ ω)) k0} := by
      rw [hset, ballLawK, Measure.map_apply (measurable_truncK_ballX hS K) hmeas]; rfl
    _ ≤ P (Z k0 ⁻¹' {x | τ * s * K ≤ |x|} ∪ {ω | ‖ζ ω‖ < s}) := measure_mono hinc
    _ ≤ P (Z k0 ⁻¹' {x | τ * s * K ≤ |x|}) + P {ω | ‖ζ ω‖ < s} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-A / 2)) + ENNReal.ofReal (2 * Real.exp (-0.43 * A)) := add_le_add hP1 hP2
    _ ≤ ENNReal.ofReal (4 * Real.exp (-0.43 * A)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : Real.exp (-A / 2) ≤ Real.exp (-0.43 * A) := Real.exp_le_exp.2 (by linarith)
      linarith

end Setting

theorem ball_region_bound_thm : Claims.ball_region_bound := by
  intro H _ _ _ _ Ω _ P _ e Z ζ R hS K τ hK hτ
  exact ball_bound hS hK hτ

section Mono
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {e : ℕ → H} {Z : ℕ → Ω → ℝ}
  {ζ : Ω → H} {R : Ω → ℝ}

lemma ballLawK_closedBall (hS : BallSetting P e Z ζ R) (K : ℕ) (t : ℝ) :
    ballLawK P e ζ R K (Metric.closedBall 0 t) = P {ω | ‖truncK e K (ballX R ζ ω)‖ ≤ t} := by
  rw [ballLawK, Measure.map_apply (measurable_truncK_ballX hS K) Metric.isClosed_closedBall.measurableSet]
  congr 1; ext ω; simp [mem_closedBall_zero_iff]

lemma ballTau_set_one (hS : BallSetting P e Z ζ R) (K : ℕ) {p : ℝ} (hp1 : p ≤ 1) :
    (1 : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal p ≤ ballLawK P e ζ R K (Metric.closedBall 0 t)} := by
  refine ⟨zero_le_one, ?_⟩
  rw [ballLawK_closedBall hS]
  have : {ω | ‖truncK e K (ballX R ζ ω)‖ ≤ 1} = univ := by
    ext ω; simp only [Set.mem_ofPred_eq, mem_univ, iff_true]
    exact (norm_truncK_le hS.1 K _).trans (norm_ballX_le hS ω)
  rw [this, measure_univ]
  exact ENNReal.ofReal_le_one.2 hp1

lemma ballTau_mono_succ (hS : BallSetting P e Z ζ R) (K : ℕ) {p : ℝ} (hp1 : p ≤ 1) :
    ballTau (ballLawK P e ζ R K) p ≤ ballTau (ballLawK P e ζ R (K + 1)) p := by
  refine csInf_le_csInf ⟨0, fun t ht => ht.1⟩ ⟨1, ballTau_set_one hS (K + 1) hp1⟩ ?_
  rintro t ⟨ht0, ht⟩
  refine ⟨ht0, ht.trans ?_⟩
  rw [ballLawK_closedBall hS, ballLawK_closedBall hS]
  exact measure_mono fun ω hω => (norm_truncK_mono K _).trans hω

end Mono

theorem ball_tau_mono_thm : Claims.ball_tau_mono := by
  intro H _ _ _ _ Ω _ P _ e Z ζ R hS K p _ hp1
  exact ballTau_mono_succ hS K hp1

theorem ball_decay_thm : Claims.ball_decay := by
  intro H _ _ _ _ Ω _ P _ e Z ζ R hS K₀ p hK₀ _ hp1 hτ₀ K hK
  have hmono : Monotone fun K => ballTau (ballLawK P e ζ R K) p :=
    monotone_nat_of_le_succ fun K => ballTau_mono_succ hS K hp1
  have hle := hmono hK
  have hτ : 0 < ballTau (ballLawK P e ζ R K) p := hτ₀.trans_le hle
  refine (ball_bound hS (hK₀.trans_le hK) hτ).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have : (ballTau (ballLawK P e ζ R K₀) p * K) ^ ((2 : ℝ) / 3) ≤
      (ballTau (ballLawK P e ζ R K) p * K) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (mul_nonneg hτ₀.le hKpos) (mul_le_mul_of_nonneg_right hle hKpos) (by norm_num)
  linarith

end StatFormal.Wave23d
