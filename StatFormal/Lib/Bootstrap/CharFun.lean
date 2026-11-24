import StatFormal.Lib.Bootstrap.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Characteristic functions of resampling laws (library)

* `cAvg`: complex finite averages; `cAvg_prod_mul` (independent coordinates factorise),
  `cAvg_resample_exp` (`E* exp(iu Σ_i c_{I_i}) = (avg_j exp(iu c_j))^n`);
* `norm_pow_sub_pow_le_mul`: `‖a^N − b^N‖ ≤ N ‖a − b‖` on the closed unit disc;
* `tendsto_cAvg_pow`: the **triangular-array characteristic-function limit** — for centred `c^{(k)} ∈ ℝ^{N_k}`,
  `|c| ≤ C`, `N_k → ∞`, `N_k u_k² → ρ`, `avg (c^{(k)})² → V`:
  `(avg_j exp(i u_k c^{(k)}_j))^{N_k} → exp(−ρV/2)` (Taylor bounds from `Complex.exp_bound`);
* `bootLaw R = |ι|⁻¹ Σ_i δ_{R i}`, the law of `R` under the uniform law on `ι`: a probability measure, its
  characteristic function `cAvg exp(itR)` and its cdf `bAvg 1{R ≤ t}`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace StatFormal.Foundations.Bootstrap

section CAvg
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Complex finite average. -/
def cAvg (F : ι → ℂ) : ℂ := ((Fintype.card ι : ℂ))⁻¹ * ∑ i, F i

lemma norm_cAvg_le [Nonempty ι] {F : ι → ℂ} {C : ℝ} (h : ∀ i, ‖F i‖ ≤ C) : ‖cAvg F‖ ≤ C := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold cAvg
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, F i‖ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, C :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => h i)) (by positivity)
    _ = C := by rw [sum_const, card_univ, nsmul_eq_mul]; field_simp

lemma cAvg_sub (F G : ι → ℂ) : cAvg (fun i => F i - G i) = cAvg F - cAvg G := by
  unfold cAvg; rw [sum_sub_distrib, mul_sub]

lemma cAvg_prod_mul [Nonempty ι] [Nonempty κ] (F : ι → ℂ) (G : κ → ℂ) :
    cAvg (fun p : ι × κ => F p.1 * G p.2) = cAvg F * cAvg G := by
  unfold cAvg
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only
  rw [← Finset.sum_mul_sum]
  push_cast
  rw [mul_inv]
  ring

lemma norm_cAvg_sub_cAvg_le [Nonempty ι] (F G : ι → ℂ) :
    ‖cAvg F - cAvg G‖ ≤ bAvg fun i => ‖F i - G i‖ := by
  rw [← cAvg_sub]
  unfold cAvg bAvg
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

lemma cAvg_resample_exp {n : ℕ} (c : Fin n → ℝ) (u : ℝ) :
    cAvg (fun K : Fin n → Fin n => exp (↑(u * ∑ i, c (K i)) * I)) = (cAvg fun j => exp (↑(u * c j) * I)) ^ n := by
  unfold cAvg
  have hcard : ((Fintype.card (Fin n → Fin n) : ℕ) : ℂ) = (n : ℂ) ^ n := by simp
  rw [hcard]
  have e : ∀ K : Fin n → Fin n, exp (↑(u * ∑ i, c (K i)) * I) = ∏ i, (fun _ j => exp (↑(u * c j) * I)) i (K i) :=
    fun K => by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [mul_sum, sum_mul]
  rw [Finset.sum_congr rfl fun K _ => e K, ← Fintype.prod_sum (fun _ j => exp (↑(u * c j) * I)), prod_const,
    card_univ, Fintype.card_fin, mul_pow, inv_pow]

end CAvg

/-- `‖a^N − b^N‖ ≤ N ‖a − b‖` for `‖a‖, ‖b‖ ≤ 1`. -/
lemma norm_pow_sub_pow_le_mul {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (N : ℕ) :
    ‖a ^ N - b ^ N‖ ≤ N * ‖a - b‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : a ^ (N + 1) - b ^ (N + 1) = a * (a ^ N - b ^ N) + (a - b) * b ^ N := by ring
    rw [e]
    have hbN : ‖b‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
    calc ‖a * (a ^ N - b ^ N) + (a - b) * b ^ N‖ ≤ ‖a‖ * ‖a ^ N - b ^ N‖ + ‖a - b‖ * ‖b‖ ^ N := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 1 * (N * ‖a - b‖) + ‖a - b‖ * 1 := by
          gcongr
      _ = ((N + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

/-- Third-order Taylor bound for `exp(ix)`. -/
lemma norm_exp_mul_I_sub_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖exp (↑x * I) - (((1 - x ^ 2 / 2 : ℝ) : ℂ) + ↑x * I)‖ ≤ |x| ^ 3 := by
  have hn : ‖(↑x * I : ℂ)‖ = |x| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := ↑x * I) (by rw [hn]; exact hx) (n := 3) (by norm_num)
  have e : ∑ m ∈ range 3, (↑x * I : ℂ) ^ m / (m.factorial : ℂ) = ((1 - x ^ 2 / 2 : ℝ) : ℂ) + ↑x * I := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.factorial]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [e, hn] at hb
  refine hb.trans ?_
  have : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  calc |x| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹) ≤ |x| ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = |x| ^ 3 := mul_one _

/-- Second-order Taylor bound for the real exponential, in `ℂ`. -/
lemma norm_exp_ofReal_sub_le {z : ℝ} (hz : |z| ≤ 1) : ‖exp (↑z : ℂ) - (1 + ↑z)‖ ≤ z ^ 2 := by
  have hb := Real.exp_bound hz (n := 2) (by norm_num)
  have e : ∑ m ∈ range 2, z ^ m / (m.factorial : ℝ) = 1 + z := by
    simp [sum_range_succ]
  rw [e] at hb
  have e2 : exp (↑z : ℂ) - (1 + ↑z) = ↑(Real.exp z - (1 + z)) := by push_cast; ring
  rw [e2, Complex.norm_real, Real.norm_eq_abs]
  refine hb.trans ?_
  have : ((Nat.succ 2 : ℕ) : ℝ) * ((Nat.factorial 2 : ℕ) * (2 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  rw [← sq_abs z]
  calc |z| ^ 2 * (((Nat.succ 2 : ℕ) : ℝ) * ((Nat.factorial 2 : ℕ) * (2 : ℕ) : ℝ)⁻¹) ≤ |z| ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = |z| ^ 2 := mul_one _

/-- **Triangular-array characteristic-function limit** for averages of centred bounded arrays. -/
theorem tendsto_cAvg_pow {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {c : (k : ℕ) → Fin (N k) → ℝ} {C : ℝ}
    (hcb : ∀ k j, |c k j| ≤ C) (hc0 : ∀ k, ∑ j, c k j = 0) {u : ℕ → ℝ} {ρ V : ℝ}
    (hu : Tendsto (fun k => (N k : ℝ) * u k ^ 2) atTop (𝓝 ρ))
    (hV : Tendsto (fun k => (∑ j, c k j ^ 2) / N k) atTop (𝓝 V)) :
    Tendsto (fun k => (cAvg fun j : Fin (N k) => exp (↑(u k * c k j) * I)) ^ N k) atTop
      (𝓝 (exp (↑(-(ρ * V / 2))))) := by
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hN.eventually_gt_atTop 0
  have hu2 : Tendsto (fun k => u k ^ 2) atTop (𝓝 0) := by
    have h1 := hu.mul (tendsto_inv_atTop_zero.comp hNr)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hNpos] with k hk
    have : (N k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Function.comp]
    field_simp
  have hua : Tendsto (fun k => |u k|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hu2
    rw [Real.sqrt_zero] at this
    exact this.congr fun k => by simp only [Function.comp, Real.sqrt_sq_eq_abs]
  set s : ℕ → ℝ := fun k => (∑ j, c k j ^ 2) / N k
  set z : ℕ → ℝ := fun k => -(u k ^ 2 * s k / 2)
  set w : ℕ → ℂ := fun k => cAvg fun j : Fin (N k) => exp (↑(u k * c k j) * I)
  -- the error terms
  have herr : Tendsto (fun k => (N k : ℝ) * (|u k| ^ 3 * |C| ^ 3 + z k ^ 2)) atTop (𝓝 0) := by
    have e : (fun k => (N k : ℝ) * (|u k| ^ 3 * |C| ^ 3 + z k ^ 2)) =
        fun k => ((N k : ℝ) * u k ^ 2) * (|u k| * |C| ^ 3) + ((N k : ℝ) * u k ^ 2) * (u k ^ 2 * s k ^ 2 / 4) := by
      funext k
      simp only [z]
      have : |u k| ^ 3 = u k ^ 2 * |u k| := by rw [pow_succ, sq_abs]
      rw [this]; ring
    rw [e]
    have := (hu.mul (hua.mul_const (|C| ^ 3))).add (hu.mul ((hu2.mul (hV.pow 2)).div_const 4))
    simpa using this
  have hzN : Tendsto (fun k => (N k : ℝ) * z k) atTop (𝓝 (-(ρ * V / 2))) := by
    have := ((hu.mul hV).div_const 2).neg
    refine this.congr fun k => ?_
    simp only [z, s]; ring
  have hlim : Tendsto (fun k => exp (↑((N k : ℝ) * z k) : ℂ)) atTop (𝓝 (exp (↑(-(ρ * V / 2))))) :=
    (Complex.continuous_exp.tendsto _).comp ((Complex.continuous_ofReal.tendsto _).comp hzN)
  -- main estimate
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hcb' : ∀ k j, |c k j| ≤ |C| := fun k j => (hcb k j).trans (le_abs_self C)
  have hs_le : ∀ k, 0 < N k → s k ≤ |C| ^ 2 := fun k hk => by
    have hk' : (0 : ℝ) < N k := by exact_mod_cast hk
    simp only [s]
    rw [div_le_iff₀ hk']
    calc ∑ j, c k j ^ 2 ≤ ∑ _j : Fin (N k), |C| ^ 2 := sum_le_sum fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb' k j) 2
      _ = |C| ^ 2 * N k := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hs0 : ∀ k, 0 ≤ s k := fun k => div_nonneg (sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg _)
  have hsmall : ∀ᶠ k in atTop, |u k| * |C| ≤ 1 ∧ |z k| ≤ 1 := by
    have h1 : Tendsto (fun k => |u k| * |C|) atTop (𝓝 0) := by simpa using hua.mul_const |C|
    have h2 : Tendsto (fun k => |z k|) atTop (𝓝 0) := by
      have : Tendsto z atTop (𝓝 0) := by
        have := ((hu2.mul hV).div_const 2).neg
        simpa [z, s] using this
      simpa using this.abs
    filter_upwards [h1.eventually (ge_mem_nhds one_pos), h2.eventually (ge_mem_nhds one_pos)] with k a b
    exact ⟨a, b⟩
  have hkey : ∀ᶠ k in atTop, ‖w k ^ N k - exp (↑((N k : ℝ) * z k) : ℂ)‖ ≤
      (N k : ℝ) * (|u k| ^ 3 * |C| ^ 3 + z k ^ 2) := by
    filter_upwards [hNpos, hsmall] with k hk ⟨hsm1, hsm2⟩
    have : Nonempty (Fin (N k)) := ⟨⟨0, hk⟩⟩
    have hk' : (0 : ℝ) < N k := by exact_mod_cast hk
    have hw1 : ‖w k‖ ≤ 1 := norm_cAvg_le fun j => by rw [Complex.norm_exp_ofReal_mul_I]
    have hz0 : z k ≤ 0 := by
      simp only [z]; have := hs0 k; have := sq_nonneg (u k); nlinarith
    have he1 : ‖exp (↑(z k) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_exp_ofReal]; exact Real.exp_le_one_iff.2 hz0
    have hpow : exp (↑((N k : ℝ) * z k) : ℂ) = exp (↑(z k) : ℂ) ^ N k := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hpow]
    refine (norm_pow_sub_pow_le_mul hw1 he1 (N k)).trans (mul_le_mul_of_nonneg_left ?_ hk'.le)
    -- `‖w − e^z‖ ≤ |u|³|C|³ + z²`
    have hw : w k - (1 + ↑(z k)) = cAvg fun j : Fin (N k) =>
        exp (↑(u k * c k j) * I) - (((1 - (u k * c k j) ^ 2 / 2 : ℝ) : ℂ) + ↑(u k * c k j) * I) := by
      rw [cAvg_sub]
      congr 1
      unfold cAvg
      rw [sum_add_distrib, ← sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← mul_sum, hc0 k, mul_zero]
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Fintype.card_fin]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_one,
        ← Complex.ofReal_add]
      congr 1
      simp only [z, s]
      have e3 : ∑ j : Fin (N k), (1 - (u k * c k j) ^ 2 / 2) = N k - u k ^ 2 * (∑ j, c k j ^ 2) / 2 := by
        rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← sum_div]
        congr 2
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
      rw [e3]
      field_simp
      ring
    have hb1 : ‖w k - (1 + ↑(z k))‖ ≤ |u k| ^ 3 * |C| ^ 3 := by
      rw [hw]
      refine norm_cAvg_le fun j => ?_
      have hx : |u k * c k j| ≤ 1 := by
        rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hcb' k j) (abs_nonneg _)).trans hsm1
      refine (norm_exp_mul_I_sub_le hx).trans ?_
      rw [abs_mul, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hcb' k j) 3) (by positivity)
    have hb2 : ‖(1 + ↑(z k)) - exp (↑(z k) : ℂ)‖ ≤ z k ^ 2 := by
      rw [norm_sub_rev]; exact norm_exp_ofReal_sub_le hsm2
    calc ‖w k - exp (↑(z k) : ℂ)‖ = ‖(w k - (1 + ↑(z k))) + ((1 + ↑(z k)) - exp (↑(z k) : ℂ))‖ := by ring_nf
      _ ≤ ‖w k - (1 + ↑(z k))‖ + ‖(1 + ↑(z k)) - exp (↑(z k) : ℂ)‖ := norm_add_le _ _
      _ ≤ |u k| ^ 3 * |C| ^ 3 + z k ^ 2 := add_le_add hb1 hb2
  -- conclude
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim' := (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by rw [← add_zero (0 : ℝ)]; exact herr.add hlim')
  filter_upwards [hkey] with k hk
  calc ‖w k ^ N k - exp (↑(-(ρ * V / 2)))‖ ≤ ‖w k ^ N k - exp (↑((N k : ℝ) * z k) : ℂ)‖ +
        ‖exp (↑((N k : ℝ) * z k) : ℂ) - exp (↑(-(ρ * V / 2)))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hk le_rfl

/-! ### The law of a resampled statistic -/

section Law
variable {ι : Type*} [Fintype ι]

/-- The law `|ι|⁻¹ Σ_i δ_{R i}` of `R` under the uniform law on `ι`. -/
def bootLaw (R : ι → ℝ) : Measure ℝ := ((Fintype.card ι : ℝ≥0∞))⁻¹ • ∑ i, Measure.dirac (R i)

lemma bootLaw_isProb [Nonempty ι] (R : ι → ℝ) : IsProbabilityMeasure (bootLaw R) := by
  constructor
  unfold bootLaw
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, sum_const, card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

lemma charFun_bootLaw (R : ι → ℝ) (t : ℝ) :
    charFun (bootLaw R) t = cAvg fun i => exp (↑(t * R i) * I) := by
  rw [charFun_apply_real]
  unfold bootLaw cAvg
  rw [integral_smul_measure, integral_finsetSum_measure fun i _ => integrable_dirac (by simp)]
  simp only [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  rfl

lemma bootLaw_real_Iic (R : ι → ℝ) (t : ℝ) :
    (bootLaw R).real (Set.Iic t) = bAvg fun i => if R i ≤ t then (1 : ℝ) else 0 := by
  unfold bootLaw bAvg
  rw [measureReal_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
  · congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    by_cases h : R i ≤ t
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  · intro i _
    exact measure_ne_top _ _

end Law

end StatFormal.Foundations.Bootstrap
