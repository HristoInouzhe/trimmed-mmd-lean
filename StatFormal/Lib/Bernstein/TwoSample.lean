import StatFormal.Lib.Bernstein.SampleVariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-sample Bernstein inequality; Popoviciu; the unbiased sample variance

Library component F.B (part 6). Untrusted library code: no `Statements.lean` is involved.

## Main results

* `subgamma_tail`: **sub-gamma tail bound** (Boucheron–Lugosi–Massart 2013, Thm 2.10 / §2.4): if
  `E e^{λS} ≤ exp(λ² v / (2(1 − bλ/3)))` for every `λ ∈ [0, 3/b)`, then `P(S ≥ √(2vL) + bL/3) ≤ e^{−L}` for
  every `L ≥ 0` (also for `v = 0`, by letting `λ ↑ 3/b`);
* `two_sample_bernstein`: for a measurable `g` with values in `[0,1]`, `X_1..X_n` i.i.d. `P` and `Y_1..Y_m` i.i.d.
  `Q` independent, with `v = σ_P²/n + σ_Q²/m` and `b = max(1/n, 1/m)`:
  `P((Ḡ − H̄) − (E_P g − E_Q g) ≥ √(2vL) + bL/3) ≤ e^{−L}`;
* `popVar_le_quarter` (Popoviciu): `σ² ≤ 1/4` for a `[0,1]`-valued variable;
* `sampleVar_eq_sum_sq`: the library's pairwise `V_n` is the unbiased sample variance
  `(n − 1)⁻¹ Σ (Z_i − Z̄)²`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace StatFormal.Bernstein

/-- **Sub-gamma tail bound**: `P(S ≥ √(2vL) + bL/3) ≤ e^{−L}` from the sub-gamma MGF bound on `[0, 3/b)`. -/
theorem subgamma_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → ℝ} {v b L : ℝ} (hv : 0 ≤ v) (hb : 0 < b) (hL : 0 ≤ L)
    (hint : ∀ l, 0 ≤ l → l * b < 3 → Integrable (fun ω => exp (l * S ω)) μ)
    (hmgf : ∀ l, 0 ≤ l → l * b < 3 →
      ∫ ω, exp (l * S ω) ∂μ ≤ exp (l ^ 2 * v / (2 * (1 - l * b / 3)))) :
    μ.real {ω | √(2 * v * L) + b * L / 3 ≤ S ω} ≤ exp (-L) := by
  set x := √(2 * v * L) + b * L / 3 with hx
  have hchern : ∀ l, 0 ≤ l → l * b < 3 →
      μ.real {ω | x ≤ S ω} ≤ exp (-l * x + l ^ 2 * v / (2 * (1 - l * b / 3))) := fun l hl0 hl3 => by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) x hl0 (hint l hl0 hl3)
    refine h.trans ?_
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (hmgf l hl0 hl3) (exp_pos _).le
  rcases hv.eq_or_lt with hv0 | hvpos
  · -- `v = 0`: `P ≤ e^{−λ b L / 3}` for every `λ < 3/b`; let `λ ↑ 3/b`
    subst hv0
    have hxv : x = b * L / 3 := by simp [hx]
    have hbound : ∀ l, 0 ≤ l → l * b < 3 → μ.real {ω | x ≤ S ω} ≤ exp (-l * (b * L / 3)) :=
      fun l hl0 hl3 => by
        refine (hchern l hl0 hl3).trans (le_of_eq ?_)
        rw [hxv]; simp
    have hlim : Tendsto (fun l : ℝ => exp (-l * (b * L / 3))) (𝓝[<] (3 / b)) (𝓝 (exp (-L))) := by
      have hc : Continuous fun l : ℝ => exp (-l * (b * L / 3)) := by fun_prop
      have h3 : exp (-(3 / b) * (b * L / 3)) = exp (-L) := by
        congr 1; field_simp
      rw [← h3]
      exact (hc.tendsto _).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    have hpos : ∀ᶠ l in 𝓝[<] (3 / b), 0 < l := by
      have : (0 : ℝ) < 3 / b := by positivity
      exact (eventually_gt_nhds this).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with l hl0 hl3
    have hl3' : l * b < 3 := by
      have := (lt_div_iff₀ hb).1 hl3; linarith
    exact hbound l hl0.le hl3'
  · -- `v > 0`: the optimal `λ`
    set s := √(2 * L / v) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 2 * L / v := Real.sq_sqrt (by positivity)
    have hsv : √(2 * v * L) = s * v := by
      rw [← Real.sqrt_sq (mul_nonneg hs0 hvpos.le), mul_pow, hs2]
      congr 1; field_simp
    set w := 1 + b * s / 3 with hw
    have hw0 : 0 < w := by rw [hw]; positivity
    set l := s / w with hl
    have hl0 : 0 ≤ l := div_nonneg hs0 hw0.le
    have hl3 : l * b < 3 := by
      rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hw0, hw]; nlinarith [mul_nonneg hb.le hs0]
    refine (hchern l hl0 hl3).trans (le_of_eq ?_)
    congr 1
    have hden : 1 - l * b / 3 = 1 / w := by
      rw [hl]; field_simp; rw [hw]; ring
    rw [hden, hx, hsv, hl]
    have hL' : L = s ^ 2 * v / 2 := by rw [hs2]; field_simp
    rw [hL']
    field_simp
    rw [hw]
    ring

/-- **Popoviciu**: a `[0,1]`-valued variable has variance at most `1/4`. -/
theorem popVar_le_quarter {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {g : β → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) : popVar ν g ≤ 1 / 4 := by
  have h := variance_le_sq_of_bounded (μ := ν) (X := g) (ae_of_all _ hg01) hg.aemeasurable
  rw [variance_eq_integral hg.aemeasurable] at h
  unfold popVar popMean
  norm_num at h ⊢
  exact h

/-- The library's pairwise sample variance is the unbiased sample variance. -/
theorem sampleVar_eq_sum_sq {Z : Type*} {k : ℕ} (hk : 2 ≤ k) (g : Z → ℝ) (x : Fin k → Z) :
    sampleVar g x = (∑ i, (g (x i) - (∑ j, g (x j)) / k) ^ 2) / ((k : ℝ) - 1) := by
  set s : Fin k → ℝ := fun i => g (x i) with hs
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsym : ∑ i, ∑ j, (if i < j then (s i - s j) ^ 2 else 0) =
      ∑ i, ∑ j, (if j < i then (s i - s j) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hsplit : ∀ i j, (s i - s j) ^ 2 =
      (if i < j then (s i - s j) ^ 2 else 0) + (if j < i then (s i - s j) ^ 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp
    · simp [h, h.not_gt]
  have hkey : 2 * ∑ i, ∑ j, (if i < j then (s i - s j) ^ 2 else 0) =
      ∑ i, ∑ j, (s i - s j) ^ 2 := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (hsplit i j).symm
  have hexp : ∑ i, ∑ j, (s i - s j) ^ 2 = 2 * k * ∑ i, s i ^ 2 - 2 * (∑ i, s i) ^ 2 := by
    have : ∀ i, ∑ j, (s i - s j) ^ 2 = k * s i ^ 2 - 2 * s i * ∑ j, s j + ∑ j, s j ^ 2 := by
      intro i
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hvar : ∑ i, (s i - (∑ l, s l) / k) ^ 2 =
      ∑ i, s i ^ 2 - 2 * ((∑ l, s l) / k) * ∑ i, s i + k * ((∑ l, s l) / k) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  unfold sampleVar
  change (∑ i, ∑ j, (if i < j then (s i - s j) ^ 2 else 0)) / (k * (k - 1)) =
    (∑ i, (s i - (∑ l, s l) / k) ^ 2) / ((k : ℝ) - 1)
  have hA : ∑ i, ∑ j, (if i < j then (s i - s j) ^ 2 else 0) =
      k * ∑ i, s i ^ 2 - (∑ i, s i) ^ 2 := by
    linarith [hkey, hexp]
  rw [hA, hvar]
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (k : ℝ) ≠ 0 := by linarith
  field_simp
  ring

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- MGF of one centred, rescaled summand: `E e^{λ a} ≤ exp(λ² E a² / (2(1 − λb/3)))` when `|a| ≤ b`. -/
lemma integral_exp_le_of_abs_le (ν : Measure 𝒳) [IsProbabilityMeasure ν] {a : 𝒳 → ℝ} (ha : Measurable a)
    {b : ℝ} (hb : 0 < b) (hab : ∀ x, |a x| ≤ b) (ha0 : ∫ x, a x ∂ν = 0) {l : ℝ} (hl0 : 0 ≤ l)
    (hl3 : l * b < 3) :
    ∫ x, exp (l * a x) ∂ν ≤ exp (l ^ 2 / (2 * (1 - l * b / 3)) * ∫ x, a x ^ 2 ∂ν) := by
  have hX : Measurable fun x => a x / b := ha.div_const b
  have hX1 : ∀ x, |a x / b| ≤ 1 := fun x => by
    rw [abs_div, abs_of_pos hb, div_le_one hb]; exact hab x
  have hX0 : ∫ x, a x / b ∂ν = 0 := by rw [integral_div, ha0, zero_div]
  have h := integral_exp_mul_le_of_abs_le_one ν hX hX1 hX0 (l := l * b) (mul_nonneg hl0 hb.le) hl3
  have e1 : (fun x => exp (l * b * (a x / b))) = fun x => exp (l * a x) := by
    funext x; congr 1; field_simp
  have e2 : ∫ x, (a x / b) ^ 2 ∂ν = (∫ x, a x ^ 2 ∂ν) / b ^ 2 := by
    rw [← integral_div]; congr 1; funext x; ring
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

/-- **Two-sample Bernstein inequality** (Boucheron–Lugosi–Massart 2013, Thm 2.10 with `c = b/3`), upper tail of
`(Ḡ − H̄) − (E_P g − E_Q g)`. -/
theorem two_sample_bernstein (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : 𝒳 → ℝ} (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) {L : ℝ} (hL : 0 ≤ L) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real
      {ω | √(2 * (popVar P g / n + popVar Q g / m) * L) + max (1 / (n : ℝ)) (1 / (m : ℝ)) * L / 3 ≤
        (sampleMean g ω.1 - sampleMean g ω.2) - (popMean P g - popMean Q g)} ≤ exp (-L) := by
  set ν := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hν
  set b : ℝ := max (1 / (n : ℝ)) (1 / (m : ℝ)) with hbdef
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hb : 0 < b := lt_max_of_lt_left (by positivity)
  set μP := popMean P g with hμP
  set μQ := popMean Q g with hμQ
  have hμP01 := popMean_mem_Icc P hg hg01
  have hμQ01 := popMean_mem_Icc Q hg hg01
  set a : 𝒳 → ℝ := fun x => (g x - μP) / n with ha
  set c : 𝒳 → ℝ := fun y => (μQ - g y) / m with hc
  have ham : Measurable a := (hg.sub measurable_const).div_const _
  have hcm : Measurable c := (measurable_const.sub hg).div_const _
  have hgi : ∀ ρ : Measure 𝒳, IsFiniteMeasure ρ → Integrable g ρ := fun ρ _ =>
    Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ hg01)
  have hab : ∀ x, |a x| ≤ b := fun x => by
    have h1 := hg01 x
    have : |g x - μP| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hμP01.1, hμP01.2, h1.1, h1.2]
    simp only [ha]
    rw [abs_div, abs_of_pos hnR]
    calc |g x - μP| / n ≤ 1 / n := div_le_div_of_nonneg_right this hnR.le
      _ ≤ b := le_max_left _ _
  have hcb : ∀ y, |c y| ≤ b := fun y => by
    have h1 := hg01 y
    have : |μQ - g y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hμQ01.1, hμQ01.2, h1.1, h1.2]
    simp only [hc]
    rw [abs_div, abs_of_pos hmR]
    calc |μQ - g y| / m ≤ 1 / m := div_le_div_of_nonneg_right this hmR.le
      _ ≤ b := le_max_right _ _
  have ha0 : ∫ x, a x ∂P = 0 := by
    simp only [ha]
    rw [integral_div, integral_sub (hgi P inferInstance) (integrable_const _), integral_const,
      probReal_univ, one_smul, hμP, popMean, sub_self, zero_div]
  have hc0 : ∫ y, c y ∂Q = 0 := by
    simp only [hc]
    rw [integral_div, integral_sub (integrable_const _) (hgi Q inferInstance), integral_const,
      probReal_univ, one_smul, hμQ, popMean, sub_self, zero_div]
  have ha2 : ∫ x, a x ^ 2 ∂P = popVar P g / n ^ 2 := by
    simp only [ha, popVar, ← hμP]
    rw [← integral_div]; congr 1; funext x; ring
  have hc2 : ∫ y, c y ^ 2 ∂Q = popVar Q g / m ^ 2 := by
    simp only [hc, popVar, ← hμQ]
    rw [← integral_div]; congr 1; funext y; ring
  -- the sum
  set S : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => (∑ i, a (ω.1 i)) + ∑ j, c (ω.2 j) with hS
  have hSeq : ∀ ω, S ω = (sampleMean g ω.1 - sampleMean g ω.2) - (μP - μQ) := fun ω => by
    simp only [hS, ha, hc, sampleMean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hSm : Measurable S :=
    (Finset.measurable_sum _ fun i _ => ham.comp ((measurable_pi_apply i).comp measurable_fst)).add
      (Finset.measurable_sum _ fun j _ => hcm.comp ((measurable_pi_apply j).comp measurable_snd))
  have hSb : ∀ ω, |S ω| ≤ n * b + m * b := fun ω => by
    simp only [hS]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |a (ω.1 i)| ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => hab _
        _ = n * b := by simp
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |c (ω.2 j)| ≤ ∑ _j : Fin m, b := Finset.sum_le_sum fun j _ => hcb _
        _ = m * b := by simp
  have hint : ∀ l, 0 ≤ l → l * b < 3 → Integrable (fun ω => exp (l * S ω)) ν := fun l hl0 _ =>
    Integrable.of_mem_Icc 0 (exp (l * (n * b + m * b))) (measurable_exp.comp (hSm.const_mul l)).aemeasurable
      (ae_of_all _ fun ω => ⟨(exp_pos _).le, exp_le_exp.2 (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hSb ω)) hl0)⟩)
  have hmgf : ∀ l, 0 ≤ l → l * b < 3 → ∫ ω, exp (l * S ω) ∂ν ≤
      exp (l ^ 2 * (popVar P g / n + popVar Q g / m) / (2 * (1 - l * b / 3))) := fun l hl0 hl3 => by
    have hsplit : ∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳), exp (l * S ω) =
        exp (l * ∑ i, a (ω.1 i)) * exp (l * ∑ j, c (ω.2 j)) := fun ω => by
      rw [← Real.exp_add]; congr 1; simp only [hS]; ring
    simp_rw [hsplit]
    rw [hν, integral_prod_mul (fun x : Fin n → 𝒳 => exp (l * ∑ i, a (x i)))
      (fun y : Fin m → 𝒳 => exp (l * ∑ j, c (y j))), integral_exp_mul_sum_eq P a n l,
      integral_exp_mul_sum_eq Q c m l]
    have hA := integral_exp_le_of_abs_le P ham hb hab ha0 hl0 hl3
    have hC := integral_exp_le_of_abs_le Q hcm hb hcb hc0 hl0 hl3
    rw [ha2] at hA
    rw [hc2] at hC
    have hpos : 0 < 1 - l * b / 3 := by linarith
    calc (∫ x, exp (l * a x) ∂P) ^ n * (∫ y, exp (l * c y) ∂Q) ^ m
        ≤ (exp (l ^ 2 / (2 * (1 - l * b / 3)) * (popVar P g / n ^ 2))) ^ n *
            (exp (l ^ 2 / (2 * (1 - l * b / 3)) * (popVar Q g / m ^ 2))) ^ m := by
          gcongr
      _ = exp (l ^ 2 * (popVar P g / n + popVar Q g / m) / (2 * (1 - l * b / 3))) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          field_simp
  have hv : 0 ≤ popVar P g / n + popVar Q g / m :=
    add_nonneg (div_nonneg (popVar_nonneg P g) hnR.le) (div_nonneg (popVar_nonneg Q g) hmR.le)
  have h := subgamma_tail (μ := ν) (S := S) hv hb hL hint hmgf
  refine (measureReal_mono fun ω hω => ?_).trans h
  simp only [mem_ofPred_eq] at hω ⊢
  rw [hSeq]
  linarith [hω]

end StatFormal.Bernstein
