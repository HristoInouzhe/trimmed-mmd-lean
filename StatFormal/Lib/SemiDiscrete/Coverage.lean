import StatFormal.Lib.SemiDiscrete.Convex
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic

/-!
# Semi-discrete entropic OT: per-fold coverage (Hoeffding + subgradient)

The deviation step in the proof of `thm:coverage-general` (robust-equality JASA supplement,
`supp_proofs.tex:530-545`), for one fold: fix the discrete law `μ = Σ_i a_i δ_i` (labels `Fin k`)
and costs `c_i` with values in `[lo_i, lo_i + B]`; let `Y_1, …, Y_m` be i.i.d. `P` on `K` with
empirical measure `P̂_m` (`empMeasure`). Then with probability at least `1 − α`,
`Θ(P) ≤ Θ(P̂_m) + B √(log(1/α)/(2m))` (`coverage_fold`).

Route (the paper's): the subgradient inequality (`Theta_subgradient'`) with `Q = P`, `Q' = P̂_m`
gives `Θ(P) ≤ Θ(P̂_m) + (E_P g̃ − m⁻¹ Σ_j g̃(Y_j))` for the canonical potential `g̃`; the values
`g̃(Y_j)` lie in an interval of length `B` (`gsoft_osc_le`), and one-sided Hoeffding
(`hoeffding_lower`) bounds the deviation.
-/

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-- Empirical measure `P̂_m = m⁻¹ Σ_j δ_{y_j}`. -/
def empMeasure {K : Type*} [MeasurableSpace K] {m : ℕ} (y : Fin m → K) : Measure K :=
  ∑ j, ((m : ℝ≥0∞)⁻¹) • Measure.dirac (y j)

section Emp

variable {K : Type*} [MeasurableSpace K] {m : ℕ}

lemma isProb_empMeasure (hm : 0 < m) (y : Fin m → K) : IsProbabilityMeasure (empMeasure y) := by
  constructor
  simp only [empMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hm.ne') (ENNReal.natCast_ne_top m)

lemma integral_empMeasure (hm : 0 < m) (y : Fin m → K) {g : K → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) : ∫ x, g x ∂(empMeasure y) = (1 / (m : ℝ)) * ∑ j, g (y j) := by
  unfold empMeasure
  rw [integral_finsetSum_measure fun j _ =>
    (integrable_of_abs_le hg M hM (μ := Measure.dirac (y j))).smul_measure
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hm.ne'))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hg.stronglyMeasurable, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, one_div]

end Emp

/-- A function with oscillation at most `b` takes values in an interval `[lo, lo + b]`. -/
lemma exists_Icc_of_osc {X : Type*} [Nonempty X] {g : X → ℝ} {b : ℝ}
    (hosc : ∀ y y', g y - g y' ≤ b) : ∃ lo, ∀ y, g y ∈ Set.Icc lo (lo + b) := by
  obtain ⟨y0⟩ := ‹Nonempty X›
  have hbdd : BddBelow (Set.range g) :=
    ⟨g y0 - b, by rintro _ ⟨y, rfl⟩; linarith [hosc y0 y]⟩
  refine ⟨⨅ y, g y, fun y => ⟨ciInf_le hbdd y, ?_⟩⟩
  have : g y - b ≤ ⨅ y, g y := le_ciInf fun y' => by linarith [hosc y y']
  linarith

/-- One-sided Hoeffding: for i.i.d. `Y_j ~ P` and `g` with values in `[lo, lo + b]`,
`Pr[m t ≤ Σ_j (E_P g − g(Y_j))] ≤ exp(−2 m t² / b²)`. -/
theorem hoeffding_lower {K Ω : Type*} [MeasurableSpace K] [MeasurableSpace Ω] {P : Measure K}
    [IsProbabilityMeasure P] {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ} (hm0 : 0 < m)
    {g : K → ℝ} (hg : Measurable g) {lo b : ℝ} (hb : 0 < b)
    (hgI : ∀ y, g y ∈ Set.Icc lo (lo + b)) {Y : Fin m → Ω → K} (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) (hlaw : ∀ j, μ.map (Y j) = P) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (m : ℝ) * t ≤ ∑ j, ((∫ x, g x ∂P) - g (Y j ω))} ≤
      Real.exp (-(2 * m * t ^ 2 / b ^ 2)) := by
  set Eg := ∫ x, g x ∂P
  have hsub : ∀ j ∈ (univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => Eg - g (Y j ω)) ((‖(-lo) - (-(lo + b))‖₊ / 2) ^ 2) μ := by
    intro j _
    have hZm : AEMeasurable (fun ω => -g (Y j ω)) μ := (hg.comp (hY j)).neg.aemeasurable
    have hZb : ∀ᵐ ω ∂μ, -g (Y j ω) ∈ Set.Icc (-(lo + b)) (-lo) :=
      Filter.Eventually.of_forall fun ω =>
        ⟨by linarith [(hgI (Y j ω)).2], by linarith [(hgI (Y j ω)).1]⟩
    have h := hasSubgaussianMGF_of_mem_Icc hZm hZb
    have hmean : μ[fun ω => -g (Y j ω)] = -Eg := by
      rw [integral_neg]
      congr 1
      rw [← integral_map (hY j).aemeasurable hg.aestronglyMeasurable, hlaw j]
    convert h using 2 with ω
    rw [hmean]; ring
  have hind' : iIndepFun (fun j ω => Eg - g (Y j ω)) μ :=
    hind.comp (fun _ y => Eg - g y) (fun _ => measurable_const.sub hg)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub
    (show (0 : ℝ) ≤ m * t from mul_nonneg (Nat.cast_nonneg m) ht)
  refine le_trans (le_of_eq ?_) (le_trans hH (le_of_eq ?_))
  · rfl
  · have hc : ((∑ _i : Fin m, (‖(-lo) - (-(lo + b))‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = m * (b / 2) ^ 2 := by
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
        show -lo - -(lo + b) = b by ring, abs_of_pos hb, NNReal.coe_ofNat, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hc]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    congr 1
    field_simp

/-- **Per-fold coverage**: with probability at least `1 − α`,
`Θ(P) ≤ Θ(P̂_m) + B √(log(1/α)/(2m))`, where `P̂_m` is the empirical measure of `m` i.i.d. draws
from `P` and every cost `c_i` takes values in an interval `[lo_i, lo_i + B]`. -/
theorem coverage_fold {K Ω : Type} [MeasurableSpace K] [MeasurableSpace Ω] {k m : ℕ}
    {ε B α : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} {lo : Fin k → ℝ}
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) (hc : ∀ i, Measurable (c i))
    (hB : 0 < B) (hcI : ∀ i y, c i y ∈ Set.Icc (lo i) (lo i + B))
    (P : Measure K) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm0 : 0 < m) (Y : Fin m → Ω → K) (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y μ)
    (hlaw : ∀ j, μ.map (Y j) = P) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | Theta ε a c P ≤ Theta ε a c (empMeasure fun j => Y j ω) +
        ((B * √(Real.log (1 / α) / (2 * m)) : ℝ) : EReal)} := by
  -- standing hypotheses
  have hcb : ∀ i y, |c i y| ≤ ∑ i, |lo i| + B := fun i y => by
    have h1 := hcI i y
    have h2 : |lo i| ≤ ∑ i, |lo i| :=
      Finset.single_le_sum (f := fun i => |lo i|) (fun i _ => abs_nonneg _) (mem_univ i)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (lo i), le_abs_self (lo i), h1.1, h1.2]
  have h : SDHyp ε a c (∑ i, |lo i| + B) := ⟨hε, ha, hsum, hc, hcb⟩
  have hosc_c : ∀ i y y', c i y - c i y' ≤ B := fun i y y' => by
    linarith [(hcI i y).2, (hcI i y').1]
  -- canonical potential
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h P
  set g := gsoft ε a fs c
  have hg : Measurable g := h.measurable_gsoft fs
  have hgb : ∀ y, |g y| ≤ ‖fs‖ + (∑ i, |lo i| + B) := h.abs_gsoft_le fs
  have hne : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hK, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨glo, hgI⟩ := exists_Icc_of_osc (gsoft_osc_le c fs h.hk hε ha hosc_c)
  -- the deviation
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hlog : 0 ≤ Real.log (1 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)
  set s : ℝ := √(Real.log (1 / α) / (2 * m))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set t : ℝ := B * s
  have ht0 : 0 ≤ t := mul_nonneg hB.le hs0
  set bad : Set Ω := {ω | (m : ℝ) * t ≤ ∑ j, ((∫ x, g x ∂P) - g (Y j ω))}
  have hbad_meas : MeasurableSet bad :=
    measurableSet_le measurable_const
      (Finset.measurable_sum _ fun j _ => measurable_const.sub (hg.comp (hY j)))
  have hbad : μ bad ≤ ENNReal.ofReal α := by
    have hH := hoeffding_lower hm0 hg hB hgI hY hind hlaw ht0
    have hexp : Real.exp (-(2 * m * t ^ 2 / B ^ 2)) = α := by
      have : 2 * m * t ^ 2 / B ^ 2 = Real.log (1 / α) := by
        simp only [t, s]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    rw [hexp] at hH
    rw [← ofReal_measureReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hH
  have hgood : badᶜ ⊆ {ω | Theta ε a c P ≤ Theta ε a c (empMeasure fun j => Y j ω) +
      ((B * √(Real.log (1 / α) / (2 * m)) : ℝ) : EReal)} := by
    intro ω hω
    have : IsProbabilityMeasure (empMeasure fun j => Y j ω) := isProb_empMeasure hm0 _
    obtain ⟨hΘ, hsg⟩ := Theta_subgradient' h P (empMeasure fun j => Y j ω) hmax
    have hemp : ∫ y, g y ∂(empMeasure fun j => Y j ω) = (1 / (m : ℝ)) * ∑ j, g (Y j ω) :=
      integral_empMeasure hm0 _ hg hgb
    simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    rw [Finset.sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hω
    have hdev : (∫ x, g x ∂P) - (1 / (m : ℝ)) * ∑ j, g (Y j ω) < t := by
      rw [show (∫ x, g x ∂P) - (1 / (m : ℝ)) * ∑ j, g (Y j ω) =
        ((m : ℝ) * (∫ x, g x ∂P) - ∑ j, g (Y j ω)) / m by field_simp]
      rw [div_lt_iff₀ hm']
      linarith
    show Theta ε a c P ≤ Theta ε a c (empMeasure fun j => Y j ω) + (t : EReal)
    rw [hΘ]
    calc (Jdual ε a c P fs : EReal)
        ≤ ((Jdual ε a c P fs + ∫ y, g y ∂(empMeasure fun j => Y j ω) - ∫ y, g y ∂P : ℝ) : EReal)
          + (t : EReal) := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff, hemp]
          linarith
      _ ≤ _ := add_le_add_left hsg _
  calc ENNReal.ofReal (1 - α) = 1 - ENNReal.ofReal α := by
        rw [ENNReal.ofReal_sub _ hα0.le, ENNReal.ofReal_one]
    _ ≤ 1 - μ bad := tsub_le_tsub_left hbad _
    _ = μ badᶜ := (prob_compl_eq_one_sub hbad_meas).symm
    _ ≤ _ := measure_mono hgood

end StatFormal.Foundations.SemiDiscrete
