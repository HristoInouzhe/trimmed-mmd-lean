import StatFormal.Lib.NormalScores.Gauss
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The deterministic normal-scores bound (library, `lem:scores`)

With `a_n = log n / n`, `κ_n = 64 a_n`, `m(u) = min(u, 1 − u)` and `c = 1/√(2π)`:
* `sq_le_BF` (pointwise): if `U ∈ (0,1)`, `|W − U| ≤ 2√(m(U) a_n) + 6 a_n`, `V ∈ [1/(2n), 1 − 1/(2n)]` and `V` is
  no farther from `U` than `W` whenever `U` lies in that interval, then `(Φ⁻¹(V) − Φ⁻¹(U))² ≤ B_n(U)`, where
  `B_n(u) = (32 a_n m + 288 a_n²)/(c² m²)` if `m = m(u) ≥ κ_n` (bulk) and `4 log(2n) − 4 log m` otherwise (tails);
* `lintegral_BF_le` (integral): `∫_0^1 B_n ≤ 2700 (log n)²/n` for `n ≥ 3`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace StatFormal.NormalScores

open StatFormal.Foundations.MatchedGrid (Φq)

/-- `a_n = log n / n`. -/
def aN (n : ℕ) : ℝ := Real.log n / n

/-- The bulk bound `(32 a m + 288 a²)/(c² m²)`. -/
def bulkF (n : ℕ) (s : ℝ) : ℝ := (32 * aN n * s + 288 * aN n ^ 2) / (cG ^ 2 * s ^ 2)

/-- The tail bound `4 log(2n) − 4 log m`. -/
def tailF (n : ℕ) (s : ℝ) : ℝ := 4 * Real.log (2 * n) - 4 * Real.log s

/-- The bound as a function of `m`. -/
def bF (n : ℕ) (s : ℝ) : ℝ := if 64 * aN n ≤ s then bulkF n s else tailF n s

lemma one_le_log' {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.exp_one_lt_three
  linarith

lemma aN_pos {n : ℕ} (hn : 3 ≤ n) : 0 < aN n := by
  have := one_le_log' hn
  unfold aN; positivity

lemma inv_le_aN {n : ℕ} (hn : 3 ≤ n) : 1 / (n : ℝ) ≤ aN n := by
  unfold aN; gcongr; exact one_le_log' hn

lemma measurable_bF (n : ℕ) : Measurable (bF n) := by
  unfold bF bulkF tailF
  refine Measurable.ite measurableSet_Ici (by fun_prop) (by fun_prop)

lemma measurable_mm : Measurable mm := by
  unfold mm; fun_prop

/-! ### Pointwise bound -/

/-- The pointwise normal-scores bound. -/
lemma sq_le_bF {n : ℕ} (hn : 3 ≤ n) {U W V : ℝ} (hU : U ∈ Ioo (0 : ℝ) 1)
    (hW : |W - U| ≤ 2 * √(mm U * aN n) + 6 * aN n) (hV : V ∈ Icc (1 / (2 * n : ℝ)) (1 - 1 / (2 * n)))
    (hVU : U ∈ Icc (1 / (2 * n : ℝ)) (1 - 1 / (2 * n)) → |V - U| ≤ |W - U|) :
    (Φq V - Φq U) ^ 2 ≤ bF n (mm U) := by
  have hnR : (0 : ℝ) < n := by positivity
  have ha := aN_pos hn
  have hm := mm_pos hU
  set m := mm U with hmdef
  set a := aN n with hadef
  have h2n : (0 : ℝ) < 1 / (2 * n) := by positivity
  have hV01 : V ∈ Ioo (0 : ℝ) 1 := ⟨h2n.trans_le hV.1, by linarith [hV.2]⟩
  unfold bF
  split_ifs with hκ
  · -- bulk
    unfold bulkF
    have hsq : √(m * a) ≤ m / 8 := by
      calc √(m * a) ≤ √((m / 8) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = m / 8 := Real.sqrt_sq (by linarith)
    have hΔ : 2 * √(m * a) + 6 * a ≤ m / 2 := by nlinarith
    have hUin : U ∈ Icc (1 / (2 * n : ℝ)) (1 - 1 / (2 * n)) := by
      have h1 : 1 / (2 * n : ℝ) ≤ m := by
        have := inv_le_aN hn
        have e : 1 / (2 * n : ℝ) = (1 / n) / 2 := by field_simp
        rw [e]; linarith
      exact ⟨h1.trans (mm_le_left U), by linarith [mm_le_right U]⟩
    have hVU' : |V - U| ≤ 2 * √(m * a) + 6 * a := (hVU hUin).trans hW
    have hmV : m / 2 ≤ mm V := by
      have := abs_mm_sub_le V U
      have := (abs_le.1 this).1
      linarith
    have hmin : m / 2 ≤ min m (mm V) := le_min (by linarith) hmV
    have hq := quantile_sub_le hU hV01
    have hcG := cG_pos
    have h1 : cG * (m / 2) * |Φq V - Φq U| ≤ 2 * √(m * a) + 6 * a := by
      refine le_trans ?_ (hq.trans hVU')
      gcongr
    rw [le_div_iff₀ (by positivity)]
    have hsa : (√(m * a)) ^ 2 = m * a := Real.sq_sqrt (by positivity)
    have h2 : (cG * m * |Φq V - Φq U|) ^ 2 ≤ (2 * (2 * √(m * a) + 6 * a)) ^ 2 := by
      have h0 : 0 ≤ cG * m * |Φq V - Φq U| := by positivity
      have : cG * m * |Φq V - Φq U| ≤ 2 * (2 * √(m * a) + 6 * a) := by nlinarith
      exact pow_le_pow_left₀ h0 this 2
    have h3 : (2 * (2 * √(m * a) + 6 * a)) ^ 2 ≤ 32 * a * m + 288 * a ^ 2 := by
      nlinarith [sq_nonneg (2 * √(m * a) - 6 * a)]
    have h4 : (Φq V - Φq U) ^ 2 * (cG ^ 2 * m ^ 2) = (cG * m * |Φq V - Φq U|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    rw [h4]; linarith
  · -- tails
    unfold tailF
    have hV1 := quantile_sq_le hV01
    have hU1 := quantile_sq_le hU
    have hmV : 1 / (2 * n : ℝ) ≤ mm V := le_min hV.1 (by linarith [hV.2])
    have hlogV : -Real.log (2 * n) ≤ Real.log (mm V) := by
      rw [← Real.log_inv, ← one_div]
      exact Real.log_le_log h2n hmV
    have : (Φq V - Φq U) ^ 2 ≤ 2 * Φq V ^ 2 + 2 * Φq U ^ 2 := by
      nlinarith [sq_nonneg (Φq V + Φq U)]
    rw [← hmdef] at hU1
    linarith

/-! ### Integral bound -/

lemma lintegral_Ioc_ofReal {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (h0 : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal hf.1 (ae_restrict_of_forall_mem measurableSet_Ioc h0)]

lemma lintegral_reflect (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Icc (0 : ℝ) 1, g (1 - u) = ∫⁻ u in Icc (0 : ℝ) 1, g u := by
  have hmp : MeasurePreserving (fun u : ℝ => 1 - u) volume volume := Measure.measurePreserving_sub_left volume 1
  have hemb : MeasurableEmbedding (fun u : ℝ => 1 - u) := (MeasurableEquiv.subLeft (1 : ℝ)).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hemb g (Icc 0 1)
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext u; simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rwa [hpre] at this

/-- Symmetry: `∫_0^1 b(m(u)) du ≤ 2 ∫_{[0,½]} b`. -/
lemma lintegral_mm_le {b : ℝ → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ u in Icc (0 : ℝ) 1, b (mm u) ≤ 2 * ∫⁻ s in Icc (0 : ℝ) (1 / 2), b s := by
  set g := (Icc (0 : ℝ) (1 / 2)).indicator b with hg
  have hgm : Measurable g := hb.indicator measurableSet_Icc
  have hpt : ∀ u ∈ Icc (0 : ℝ) 1, b (mm u) ≤ g u + g (1 - u) := by
    intro u hu
    rcases le_total u (1 / 2) with h | h
    · have : mm u = u := min_eq_left (by linarith)
      rw [this, hg, indicator_of_mem (show u ∈ Icc (0 : ℝ) (1 / 2) from ⟨hu.1, h⟩)]
      exact le_self_add
    · have : mm u = 1 - u := min_eq_right (by linarith)
      rw [this, hg, indicator_of_mem (show 1 - u ∈ Icc (0 : ℝ) (1 / 2) from ⟨by linarith [hu.2], by linarith⟩)]
      exact le_add_self
  have hgi : ∫⁻ u in Icc (0 : ℝ) 1, g u = ∫⁻ s in Icc (0 : ℝ) (1 / 2), b s := by
    rw [hg, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 (Icc_subset_Icc le_rfl (by norm_num))]
  calc ∫⁻ u in Icc (0 : ℝ) 1, b (mm u) ≤ ∫⁻ u in Icc (0 : ℝ) 1, (g u + g (1 - u)) :=
        setLIntegral_mono (hgm.add (hgm.comp (measurable_const.sub measurable_id))) hpt
    _ = (∫⁻ u in Icc (0 : ℝ) 1, g u) + ∫⁻ u in Icc (0 : ℝ) 1, g (1 - u) := lintegral_add_left hgm _
    _ = 2 * ∫⁻ s in Icc (0 : ℝ) (1 / 2), b s := by rw [lintegral_reflect, hgi, two_mul]

lemma cG_sq : cG ^ 2 = 1 / (2 * π) := by
  rw [cG, inv_pow, Real.sq_sqrt (by positivity), one_div]

/-- The bulk integral. -/
lemma bulk_le {n : ℕ} (hn : 3 ≤ n) :
    ∫⁻ s in Icc (64 * aN n) (1 / 2), ENNReal.ofReal (bulkF n s) ≤
      ENNReal.ofReal (296 * (Real.log n ^ 2 / n)) := by
  have hnR : (0 : ℝ) < n := by positivity
  have ha := aN_pos hn
  have hL := one_le_log' hn
  set a := aN n with hadef
  set κ := 64 * a with hκ
  have hκ0 : 0 < κ := by positivity
  rcases le_or_gt κ (1 / 2) with hκ2 | hκ2
  · rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    set K := 1 / cG ^ 2 with hK
    have hK0 : 0 < K := by have := cG_pos; positivity
    have hKv : K = 2 * π := by rw [hK, cG_sq]; field_simp
    have hbulk : ∀ s, s ≠ 0 → bulkF n s = K * (32 * a / s + 288 * a ^ 2 / s ^ 2) := by
      intro s hs
      rw [bulkF, hK, ← hadef]
      have : cG ≠ 0 := cG_pos.ne'
      field_simp
    -- antiderivative
    set G : ℝ → ℝ := fun s => K * (32 * a * Real.log s - 288 * a ^ 2 * s⁻¹) with hG
    have hderiv : ∀ x ∈ uIcc κ (1 / 2), HasDerivAt G (bulkF n x) x := by
      intro x hx
      rw [uIcc_of_le hκ2] at hx
      have hx0 : x ≠ 0 := (hκ0.trans_le hx.1).ne'
      rw [hbulk x hx0]
      have h1 := ((Real.hasDerivAt_log hx0).const_mul (32 * a)).sub ((hasDerivAt_inv hx0).const_mul (288 * a ^ 2))
      have h2 := h1.const_mul K
      convert h2 using 1
      field_simp
      ring
    have hcont : ContinuousOn (bulkF n) (uIcc κ (1 / 2)) := by
      unfold bulkF
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
      rw [uIcc_of_le hκ2] at hx
      have := hκ0.trans_le hx.1
      have := cG_pos
      positivity
    have hint : IntervalIntegrable (bulkF n) volume κ (1 / 2) := hcont.intervalIntegrable
    have hnn : ∀ x ∈ Ioc κ (1 / 2), 0 ≤ bulkF n x := fun x hx => by
      unfold bulkF
      have := hκ0.trans hx.1
      have := cG_pos
      positivity
    rw [lintegral_Ioc_ofReal hκ2 hint hnn, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hG]
    have hlogκ : -Real.log κ ≤ Real.log n := by
      have h1 : 1 / (n : ℝ) ≤ κ := by have := inv_le_aN hn; linarith
      have := Real.log_le_log (by positivity) h1
      rw [one_div, Real.log_inv] at this
      linarith
    have hlog2 : Real.log (1 / 2) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have hκinv : 288 * a ^ 2 * κ⁻¹ = 4.5 * a := by rw [hκ]; field_simp; norm_num
    have hπ := Real.pi_le_four
    have haL : a * Real.log n = Real.log n ^ 2 / n := by rw [hadef, aN]; ring
    have ha2 : a ≤ Real.log n ^ 2 / n := by
      rw [hadef, aN]; gcongr; nlinarith
    have e : K * (32 * a * Real.log (1 / 2) - 288 * a ^ 2 * (1 / 2)⁻¹) -
        K * (32 * a * Real.log κ - 288 * a ^ 2 * κ⁻¹) =
        K * (32 * a * Real.log (1 / 2) - 576 * a ^ 2 + 32 * a * (-Real.log κ) + 288 * a ^ 2 * κ⁻¹) := by ring
    rw [e, hκinv]
    have hin : 32 * a * Real.log (1 / 2) - 576 * a ^ 2 + 32 * a * (-Real.log κ) + 4.5 * a ≤
        37 * (Real.log n ^ 2 / n) := by
      have : 32 * a * Real.log (1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog2
      have : 32 * a * (-Real.log κ) ≤ 32 * a * Real.log n := mul_le_mul_of_nonneg_left hlogκ (by positivity)
      nlinarith
    have hpos : 0 ≤ Real.log n ^ 2 / n := by positivity
    calc K * (32 * a * Real.log (1 / 2) - 576 * a ^ 2 + 32 * a * (-Real.log κ) + 4.5 * a)
        ≤ K * (37 * (Real.log n ^ 2 / n)) := mul_le_mul_of_nonneg_left hin hK0.le
      _ ≤ 296 * (Real.log n ^ 2 / n) := by rw [hKv]; nlinarith
  · rw [Icc_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le

/-- The tail integral. -/
lemma tail_le' {n : ℕ} (hn : 3 ≤ n) :
    ∫⁻ s in Ioc 0 (min (64 * aN n) (1 / 2)), ENNReal.ofReal (tailF n s) ≤
      ENNReal.ofReal (1024 * (Real.log n ^ 2 / n)) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ha := aN_pos hn
  have hL := one_le_log' hn
  set a := aN n with hadef
  set κ := min (64 * a) (1 / 2) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκ2 : κ ≤ 1 / 2 := min_le_right _ _
  have hκa : κ ≤ 64 * a := min_le_left _ _
  have hint : IntervalIntegrable (tailF n) volume 0 κ := by
    unfold tailF
    exact intervalIntegrable_const.sub ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := κ)).const_mul 4)
  have hlog2n : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hnn : ∀ x ∈ Ioc 0 κ, 0 ≤ tailF n x := fun x hx => by
    unfold tailF
    have : Real.log x ≤ 0 := Real.log_nonpos hx.1.le (by linarith [hx.2])
    linarith
  rw [lintegral_Ioc_ofReal hκ0.le hint hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcalc : ∫ x in (0 : ℝ)..κ, tailF n x = 4 * κ * (Real.log (2 * n) + 1 - Real.log κ) := by
    unfold tailF
    rw [intervalIntegral.integral_sub intervalIntegrable_const ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := κ)).const_mul 4),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_log]
    simp only [Real.log_zero, mul_zero, sub_zero, add_zero, smul_eq_mul]
    ring
  rw [hcalc]
  have hlogκ : -Real.log κ ≤ Real.log n := by
    have h1 : 1 / (n : ℝ) ≤ κ := by
      refine le_min ?_ ?_
      · have := inv_le_aN hn; linarith
      · rw [div_le_div_iff₀ hnR (by norm_num)]; have : (3 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
    have := Real.log_le_log (by positivity) h1
    rw [one_div, Real.log_inv] at this
    linarith
  have hlog2 : Real.log (2 * n) ≤ 1 + Real.log n := by
    rw [Real.log_mul (by norm_num) hnR.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hκnn : 0 ≤ -Real.log κ := by have := Real.log_nonpos hκ0.le (by linarith); linarith
  have hbr : Real.log (2 * n) + 1 - Real.log κ ≤ 4 * Real.log n := by linarith
  have hbr0 : 0 ≤ Real.log (2 * n) + 1 - Real.log κ := by linarith
  have haL : a * Real.log n = Real.log n ^ 2 / n := by rw [hadef, aN]; ring
  calc 4 * κ * (Real.log (2 * n) + 1 - Real.log κ) ≤ 4 * (64 * a) * (4 * Real.log n) := by
        gcongr
    _ = 1024 * (a * Real.log n) := by ring
    _ = 1024 * (Real.log n ^ 2 / n) := by rw [haL]

/-- **The integral bound** `∫_0^1 B_n ≤ 2700 (log n)²/n`. -/
lemma lintegral_bF_le {n : ℕ} (hn : 3 ≤ n) :
    ∫⁻ u in Icc (0 : ℝ) 1, ENNReal.ofReal (bF n (mm u)) ≤ ENNReal.ofReal (2700 * (Real.log n ^ 2 / n)) := by
  have hb : Measurable fun s => ENNReal.ofReal (bF n s) := ENNReal.measurable_ofReal.comp (measurable_bF n)
  refine (lintegral_mm_le hb).trans ?_
  set κ := 64 * aN n with hκ
  set I1 := (Icc κ (1 / 2)).indicator fun s => ENNReal.ofReal (bulkF n s) with hI1
  set I2 := (Ioc 0 (min κ (1 / 2))).indicator fun s => ENNReal.ofReal (tailF n s) with hI2
  have hI1m : Measurable I1 :=
    (ENNReal.measurable_ofReal.comp (by unfold bulkF; fun_prop)).indicator measurableSet_Icc
  have hpt : ∀ s ∈ Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (bF n s) ≤ I1 s + I2 s := by
    intro s hs
    unfold bF
    split_ifs with h
    · rw [hI1, indicator_of_mem (show s ∈ Icc κ (1 / 2) from ⟨h, hs.2⟩)]; exact le_self_add
    · rw [hI2, indicator_of_mem (show s ∈ Ioc 0 (min κ (1 / 2)) from ⟨hs.1, le_min (not_le.1 h).le hs.2⟩)]
      exact le_add_self
  have hstep : ∫⁻ s in Icc (0 : ℝ) (1 / 2), ENNReal.ofReal (bF n s) ≤
      ENNReal.ofReal (296 * (Real.log n ^ 2 / n)) + ENNReal.ofReal (1024 * (Real.log n ^ 2 / n)) := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    calc ∫⁻ s in Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (bF n s) ≤ ∫⁻ s in Ioc (0 : ℝ) (1 / 2), (I1 s + I2 s) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ ≤ ∫⁻ s, (I1 s + I2 s) := setLIntegral_le_lintegral _ _
      _ = (∫⁻ s, I1 s) + ∫⁻ s, I2 s := lintegral_add_left hI1m _
      _ = (∫⁻ s in Icc κ (1 / 2), ENNReal.ofReal (bulkF n s)) +
            ∫⁻ s in Ioc 0 (min κ (1 / 2)), ENNReal.ofReal (tailF n s) := by
          rw [hI1, hI2, lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ioc]
      _ ≤ _ := add_le_add (bulk_le hn) (tail_le' hn)
  have hpos : 0 ≤ Real.log n ^ 2 / n := by positivity
  calc 2 * ∫⁻ s in Icc (0 : ℝ) (1 / 2), ENNReal.ofReal (bF n s)
      ≤ 2 * (ENNReal.ofReal (296 * (Real.log n ^ 2 / n)) + ENNReal.ofReal (1024 * (Real.log n ^ 2 / n))) := by
        gcongr
    _ = ENNReal.ofReal (2640 * (Real.log n ^ 2 / n)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (2700 * (Real.log n ^ 2 / n)) := ENNReal.ofReal_le_ofReal (by nlinarith)

end StatFormal.NormalScores
