import StatFormal.Archive.Wave30h.Statements
import StatFormal.Lib.Bernstein.Bernstein
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Route — `lem:reldev` (untrusted)

Bernstein's inequality (`StatFormal.Bernstein.bernstein`, one-sided, applied to `1{u ≤ t}` and `1 − 1{u ≤ t}`)
at the grid points `t_j = j/n`, `j = 0, …, n`, with `δ = n⁻²`; union bound `2(n+1)/n² ≤ 4/n`; monotone interpolation
between grid points, `u ↦ u(1 − u)` being `1`-Lipschitz on `[0,1]`, `√(a + b) ≤ √a + √b` and `log n ≥ 1` (`n ≥ 3`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Bernstein (popMean popVar sampleMean bernstein)

namespace RelDev

instance isProbabilityMeasure_unif : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- The indicator `u ↦ 1{u ≤ t}`. -/
def gI (t u : ℝ) : ℝ := if u ≤ t then 1 else 0

lemma measurable_gI (t : ℝ) : Measurable (gI t) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma gI_mem (t u : ℝ) : gI t u ∈ Icc (0 : ℝ) 1 := by
  unfold gI; split_ifs <;> simp

lemma gI_eq_indicator (t : ℝ) : gI t = (Iic t).indicator 1 := by
  funext u; simp [gI, Set.indicator]

lemma sampleMean_gI {n : ℕ} (t : ℝ) (ω : Fin n → ℝ) : sampleMean (gI t) ω = empCdf ω t := by
  simp [sampleMean, empCdf, gI, Finset.sum_boole]

lemma measurable_empCdf {n : ℕ} (t : ℝ) : Measurable fun ω : Fin n → ℝ => empCdf ω t := by
  have : (fun ω : Fin n → ℝ => empCdf ω t) = fun ω => sampleMean (gI t) ω := by
    funext ω; rw [sampleMean_gI]
  rw [this]
  exact (Finset.measurable_sum _ fun i _ => (measurable_gI t).comp (measurable_pi_apply i)).div_const _

local notation "νU" => (volume.restrict (Icc (0 : ℝ) 1))

lemma popMean_gI {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : popMean νU (gI t) = t := by
  rw [popMean, gI_eq_indicator, integral_indicator_one measurableSet_Iic, measureReal_def,
    Measure.restrict_apply measurableSet_Iic]
  have : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht.2⟩
  rw [this, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht.1]

lemma integrable_gI (t : ℝ) : Integrable (gI t) νU :=
  Integrable.of_mem_Icc 0 1 (measurable_gI t).aemeasurable (ae_of_all _ (gI_mem t))

lemma popVar_gI {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : popVar νU (gI t) = t * (1 - t) := by
  rw [popVar, popMean_gI ht]
  have e : (fun u => (gI t u - t) ^ 2) = fun u => gI t u * (1 - 2 * t) + t ^ 2 := by
    funext u; unfold gI; split_ifs <;> ring
  rw [e, integral_add ((integrable_gI t).mul_const _) (integrable_const _), integral_mul_const]
  have := popMean_gI ht
  rw [popMean] at this
  rw [this]
  simp
  ring

/-- The complementary indicator `u ↦ 1 − 1{u ≤ t}`. -/
def hI (t u : ℝ) : ℝ := 1 - gI t u

lemma measurable_hI (t : ℝ) : Measurable (hI t) := measurable_const.sub (measurable_gI t)

lemma hI_mem (t u : ℝ) : hI t u ∈ Icc (0 : ℝ) 1 := by
  have := gI_mem t u
  unfold hI; constructor <;> linarith [this.1, this.2]

lemma popMean_hI {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : popMean νU (hI t) = 1 - t := by
  have := popMean_gI ht
  rw [popMean] at this ⊢
  unfold hI
  rw [integral_sub (integrable_const _) (integrable_gI t), this]
  simp

lemma popVar_hI {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : popVar νU (hI t) = t * (1 - t) := by
  rw [← popVar_gI ht, popVar, popVar, popMean_hI ht, popMean_gI ht]
  congr 1; funext u; unfold hI; ring

lemma sampleMean_hI {n : ℕ} (hn : 0 < n) (t : ℝ) (ω : Fin n → ℝ) :
    sampleMean (hI t) ω = 1 - empCdf ω t := by
  rw [← sampleMean_gI]
  simp only [sampleMean, hI, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

/-- The Bernstein deviation `s(t) = √(2 t(1−t) λ / n) + λ/(3n)`, `λ = log(1/δ)`. -/
def sDev (n : ℕ) (δ t : ℝ) : ℝ := √(2 * (t * (1 - t)) * Real.log (1 / δ) / n) + Real.log (1 / δ) / (3 * n)

lemma bad_lower {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Measure.pi fun _ : Fin n => νU).real {ω | sDev n δ t ≤ t - empCdf ω t} ≤ δ := by
  have := bernstein νU (measurable_gI t) (gI_mem t) hn hδ0 hδ1
  rw [popVar_gI ht, popMean_gI ht] at this
  simp_rw [sampleMean_gI] at this
  exact this

lemma bad_upper {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Measure.pi fun _ : Fin n => νU).real {ω | sDev n δ t ≤ empCdf ω t - t} ≤ δ := by
  have := bernstein νU (measurable_hI t) (hI_mem t) hn hδ0 hδ1
  rw [popVar_hI ht, popMean_hI ht] at this
  simp_rw [sampleMean_hI hn] at this
  have e : {ω : Fin n → ℝ | sDev n δ t ≤ empCdf ω t - t} =
      {ω | √(2 * (t * (1 - t)) * Real.log (1 / δ) / n) + Real.log (1 / δ) / (3 * n) ≤
        1 - t - (1 - empCdf ω t)} := by
    ext ω; simp only [mem_ofPred_eq, sDev]
    constructor <;> intro h <;> linarith
  rw [e]; exact this

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  calc √(a + b) ≤ √((√a + √b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b])
    _ = √a + √b := Real.sqrt_sq (by positivity)

lemma one_le_log {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.exp_one_lt_three
  linarith

/-- The deterministic interpolation step: at a grid point `s` with `|s − t| ≤ 1/n`, the Bernstein deviation at
`δ = n⁻²` plus `1/n` is at most `2√(t(1−t) log n / n) + 5 log n / n`. -/
lemma sDev_add_le {n : ℕ} (hn : 3 ≤ n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : |s - t| ≤ 1 / n) :
    sDev n (1 / (n : ℝ) ^ 2) s + 1 / n ≤
      2 * √(t * (1 - t) * Real.log n / n) + 5 * Real.log n / n := by
  have hnR : (0 : ℝ) < n := by positivity
  set L := Real.log n with hL
  have hL1 : 1 ≤ L := one_le_log hn
  have hlog : Real.log (1 / (1 / (n : ℝ) ^ 2)) = 2 * L := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  unfold sDev
  rw [hlog]
  -- `u ↦ u(1 − u)` is `1`-Lipschitz on `[0, 1]`
  have hψ : s * (1 - s) ≤ t * (1 - t) + 1 / n := by
    have h1 : s * (1 - s) - t * (1 - t) = (s - t) * (1 - s - t) := by ring
    have h2 : |1 - s - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    have h3 : |s * (1 - s) - t * (1 - t)| ≤ 1 / n := by
      rw [h1, abs_mul]
      calc |s - t| * |1 - s - t| ≤ (1 / n) * 1 := mul_le_mul hst h2 (abs_nonneg _) (by positivity)
        _ = 1 / n := mul_one _
    linarith [(abs_le.1 h3).2]
  have hσ0 : 0 ≤ t * (1 - t) * L / n := by
    have : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    positivity
  have hA : 2 * (s * (1 - s)) * (2 * L) / n ≤ 4 * (t * (1 - t) * L / n) + 4 * (L / n ^ 2) := by
    have : 2 * (s * (1 - s)) * (2 * L) / n ≤ 2 * (t * (1 - t) + 1 / n) * (2 * L) / n := by
      gcongr
    calc _ ≤ _ := this
      _ = 4 * (t * (1 - t) * L / n) + 4 * (L / n ^ 2) := by field_simp; ring
  have hsq : √(2 * (s * (1 - s)) * (2 * L) / n) ≤ 2 * √(t * (1 - t) * L / n) + 2 * L / n := by
    have h4 : ∀ x : ℝ, 0 ≤ x → √(4 * x) = 2 * √x := fun x hx => by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hLn : √(L / n ^ 2) ≤ L / n := by
      rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ n ^ 2), Real.sqrt_sq hnR.le]
      gcongr
      calc √L ≤ √(L ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = L := Real.sqrt_sq (by linarith)
    calc √(2 * (s * (1 - s)) * (2 * L) / n) ≤ √(4 * (t * (1 - t) * L / n) + 4 * (L / n ^ 2)) :=
          Real.sqrt_le_sqrt hA
      _ ≤ √(4 * (t * (1 - t) * L / n)) + √(4 * (L / n ^ 2)) :=
          sqrt_add_le' (by positivity) (by positivity)
      _ = 2 * √(t * (1 - t) * L / n) + 2 * √(L / n ^ 2) := by
          rw [h4 _ hσ0, h4 _ (by positivity)]
      _ ≤ 2 * √(t * (1 - t) * L / n) + 2 * (L / n) := by gcongr
      _ = _ := by ring
  have h1n : 1 / (n : ℝ) ≤ L / n := by gcongr
  have h2 : 2 * L / (3 * n) ≤ L / n := by
    rw [div_le_div_iff₀ (by positivity) hnR]; nlinarith
  calc √(2 * (s * (1 - s)) * (2 * L) / n) + 2 * L / (3 * n) + 1 / n
      ≤ 2 * √(t * (1 - t) * L / n) + 2 * L / n + L / n + L / n := by linarith
    _ ≤ 2 * √(t * (1 - t) * L / n) + 5 * L / n := by
      have : 0 ≤ L / n := by positivity
      have e : 2 * L / n + L / n + L / n = 4 * (L / n) := by ring
      have e' : 5 * L / n = 5 * (L / n) := by ring
      linarith

/-- The good event: at every grid point, both Bernstein deviations fail. -/
def goodE (n : ℕ) : Set (Fin n → ℝ) :=
  ⋂ j : Fin (n + 1), ({ω | sDev n (1 / (n : ℝ) ^ 2) ((j : ℕ) / n) ≤ (j : ℕ) / n - empCdf ω ((j : ℕ) / n)}ᶜ ∩
    {ω | sDev n (1 / (n : ℝ) ^ 2) ((j : ℕ) / n) ≤ empCdf ω ((j : ℕ) / n) - (j : ℕ) / n}ᶜ)

lemma measurableSet_goodE (n : ℕ) : MeasurableSet (goodE n) := by
  refine MeasurableSet.iInter fun j => ?_
  refine MeasurableSet.inter (MeasurableSet.compl ?_) (MeasurableSet.compl ?_)
  · exact measurableSet_le measurable_const (measurable_const.sub (measurable_empCdf _))
  · exact measurableSet_le measurable_const ((measurable_empCdf _).sub measurable_const)

lemma grid_mem {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) : ((j : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hnR]
  exact_mod_cast Nat.lt_succ_iff.1 j.2

lemma prob_goodE {n : ℕ} (hn : 3 ≤ n) :
    ENNReal.ofReal (1 - 4 / n) ≤ (Measure.pi fun _ : Fin n => νU) (goodE n) := by
  set P := Measure.pi fun _ : Fin n => νU with hP
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hδ0 : (0 : ℝ) < 1 / (n : ℝ) ^ 2 := by positivity
  have hδ1 : 1 / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  have hcompl : P.real (goodE n)ᶜ ≤ ∑ _j : Fin (n + 1), 2 * (1 / (n : ℝ) ^ 2) := by
    rw [goodE, compl_iInter]
    refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [compl_inter, compl_compl, compl_compl]
    refine (measureReal_union_le _ _).trans ?_
    have h1 := bad_lower hn0 hδ0 hδ1 (grid_mem hn0 j)
    have h2 := bad_upper hn0 hδ0 hδ1 (grid_mem hn0 j)
    linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcompl
  have hreal : 1 - 4 / n ≤ P.real (goodE n) := by
    rw [measureReal_compl (measurableSet_goodE n), probReal_univ] at hcompl
    have : ((n + 1 : ℕ) : ℝ) * (2 * (1 / (n : ℝ) ^ 2)) ≤ 4 / n := by
      push_cast
      rw [show ((n : ℝ) + 1) * (2 * (1 / (n : ℝ) ^ 2)) = (2 * n + 2) / n / n by field_simp,
        div_le_div_iff_of_pos_right hnR, div_le_iff₀ hnR]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      linarith
    linarith
  calc ENNReal.ofReal (1 - 4 / n) ≤ ENNReal.ofReal (P.real (goodE n)) := ENNReal.ofReal_le_ofReal hreal
    _ = P (goodE n) := ofReal_measureReal

lemma empCdf_mono {n : ℕ} (u : Fin n → ℝ) {s t : ℝ} (hst : s ≤ t) : empCdf u s ≤ empCdf u t := by
  unfold empCdf
  gcongr

lemma goodE_bound {n : ℕ} (hn : 3 ≤ n) {u : Fin n → ℝ} (hu : u ∈ goodE n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |empCdf u t - t| ≤ 2 * √(t * (1 - t) * Real.log n / n) + 5 * Real.log n / n := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgrid : ∀ j : Fin (n + 1),
      ((j : ℕ) / n - empCdf u ((j : ℕ) / n) < sDev n (1 / (n : ℝ) ^ 2) ((j : ℕ) / n)) ∧
      (empCdf u ((j : ℕ) / n) - (j : ℕ) / n < sDev n (1 / (n : ℝ) ^ 2) ((j : ℕ) / n)) := by
    intro j
    have := mem_iInter.1 hu j
    simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_le] at this
    exact this
  -- the cell containing `t`
  set k := min ⌊(n : ℝ) * t⌋₊ (n - 1) with hk
  have hk1 : k + 1 ≤ n := by omega
  have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg hnR.le ht.1
  have hkt : (k : ℝ) / n ≤ t := by
    rw [div_le_iff₀ hnR, mul_comm]
    calc (k : ℝ) ≤ ⌊(n : ℝ) * t⌋₊ := by exact_mod_cast min_le_left _ _
      _ ≤ (n : ℝ) * t := Nat.floor_le hnt
  have htk : t ≤ ((k + 1 : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hnR, mul_comm]
    rcases le_total ⌊(n : ℝ) * t⌋₊ (n - 1) with h | h
    · have : k = ⌊(n : ℝ) * t⌋₊ := min_eq_left h
      rw [this]; push_cast
      exact (Nat.lt_floor_add_one _).le
    · have : k + 1 = n := by omega
      rw [this]
      nlinarith [ht.2]
  set j0 : Fin (n + 1) := ⟨k, by omega⟩
  set j1 : Fin (n + 1) := ⟨k + 1, by omega⟩
  have e0 : ((j0 : ℕ) : ℝ) = k := rfl
  have e1 : ((j1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := rfl
  have hstep : ((k + 1 : ℕ) : ℝ) / n - (k : ℝ) / n = 1 / n := by push_cast; ring
  have hd0 : |(k : ℝ) / n - t| ≤ 1 / n := by
    rw [abs_le]; constructor <;> linarith
  have hd1 : |((k + 1 : ℕ) : ℝ) / n - t| ≤ 1 / n := by
    rw [abs_le]; constructor <;> linarith
  have b0 := sDev_add_le hn (grid_mem hn0 j0) ht (by rw [e0]; exact hd0)
  have b1 := sDev_add_le hn (grid_mem hn0 j1) ht (by rw [e1]; exact hd1)
  rw [e0] at b0
  rw [e1] at b1
  have g0 := (hgrid j0).1
  have g1 := (hgrid j1).2
  rw [e0] at g0
  rw [e1] at g1
  have m0 := empCdf_mono u hkt
  have m1 := empCdf_mono u htk
  rw [abs_le]
  constructor <;> linarith

end RelDev

open RelDev in
/-- **`lem:reldev`.** -/
theorem reldev_bound : Claims.reldev_bound := by
  intro n hn
  exact ⟨goodE n, measurableSet_goodE n, prob_goodE hn, fun u hu t ht => goodE_bound hn hu ht⟩

end StatFormal.Wave30h
