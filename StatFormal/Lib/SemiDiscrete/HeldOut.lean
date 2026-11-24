import StatFormal.Lib.SemiDiscrete.Coverage

/-!
# Semi-discrete entropic OT: per-fold coverage with a `Fintype`-indexed held-out sample

Same content as `StatFormal.Foundations.SemiDiscrete.Coverage`, with the held-out sample indexed by
an arbitrary nonempty finite type `ι` (e.g. the complement `{i // fold i ≠ v}` of a fold), which is
the form needed for random folds (`RandomFolds.lean`).

* `empOn y = Σ_{j : ι} (1/|ι|) δ_{y_j}` (`isProb_empOn`, `integral_empOn`);
* `hoeffding_lower_fintype`: one-sided Hoeffding for `|ι|` i.i.d. draws;
* `coverage_fold_fintype`: with probability at least `1 − α`,
  `Θ(P) ≤ Θ(P̂_ι) + B √(log(1/α)/(2|ι|))` when every `c_i` takes values in `[lo_i, lo_i + B]`.
-/

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-- Empirical measure of a finite family `y : ι → K`. -/
def empOn {K ι : Type*} [MeasurableSpace K] [Fintype ι] (y : ι → K) : Measure K :=
  ∑ j, ENNReal.ofReal (1 / Fintype.card ι) • Measure.dirac (y j)

section Emp

variable {K ι : Type*} [MeasurableSpace K] [Fintype ι] [Nonempty ι]

lemma card_pos_real : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos

lemma isProb_empOn (y : ι → K) : IsProbabilityMeasure (empOn y) := by
  constructor
  simp only [empOn, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    mul_one_div_cancel (card_pos_real (ι := ι)).ne', ENNReal.ofReal_one]

lemma integral_empOn (y : ι → K) {g : K → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) :
    ∫ x, g x ∂(empOn y) = (1 / (Fintype.card ι : ℝ)) * ∑ j, g (y j) := by
  unfold empOn
  rw [integral_finsetSum_measure fun j _ =>
    (integrable_of_abs_le hg M hM (μ := Measure.dirac (y j))).smul_measure ENNReal.ofReal_ne_top]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hg.stronglyMeasurable,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

end Emp

/-- One-sided Hoeffding for a finite i.i.d. family indexed by `ι` (`m = |ι|`). -/
theorem hoeffding_lower_fintype {K Ω ι : Type*} [MeasurableSpace K] [MeasurableSpace Ω]
    [Fintype ι] {P : Measure K} [IsProbabilityMeasure P] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : K → ℝ} (hg : Measurable g) {lo b : ℝ} (hb : 0 < b)
    (hgI : ∀ y, g y ∈ Set.Icc lo (lo + b)) {Y : ι → Ω → K} (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) (hlaw : ∀ j, μ.map (Y j) = P) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (Fintype.card ι : ℝ) * t ≤ ∑ j, ((∫ x, g x ∂P) - g (Y j ω))} ≤
      Real.exp (-(2 * Fintype.card ι * t ^ 2 / b ^ 2)) := by
  set Eg := ∫ x, g x ∂P
  have hsub : ∀ j ∈ (univ : Finset ι),
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
    (show (0 : ℝ) ≤ Fintype.card ι * t from mul_nonneg (Nat.cast_nonneg _) ht)
  refine le_trans (le_of_eq ?_) (le_trans hH (le_of_eq ?_))
  · rfl
  · have hc : ((∑ _i : ι, (‖(-lo) - (-(lo + b))‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) =
        Fintype.card ι * (b / 2) ^ 2 := by
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
        show -lo - -(lo + b) = b by ring, abs_of_pos hb, NNReal.coe_ofNat, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hc]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · simp [h0]
    · have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
      congr 1
      field_simp

/-- **Per-fold coverage, `Fintype` held-out index**: with probability at least `1 − α`,
`Θ(P) ≤ Θ(P̂_ι) + B √(log(1/α)/(2|ι|))`. -/
theorem coverage_fold_fintype {K Ω ι : Type} [MeasurableSpace K] [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] {k : ℕ} {ε B α : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ} {lo : Fin k → ℝ}
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) (hc : ∀ i, Measurable (c i))
    (hB : 0 < B) (hcI : ∀ i y, c i y ∈ Set.Icc (lo i) (lo i + B))
    (P : Measure K) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → K) (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y μ)
    (hlaw : ∀ j, μ.map (Y j) = P) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | Theta ε a c P ≤ Theta ε a c (empOn fun j => Y j ω) +
        ((B * √(Real.log (1 / α) / (2 * Fintype.card ι)) : ℝ) : EReal)} := by
  have hcb : ∀ i y, |c i y| ≤ ∑ i, |lo i| + B := fun i y => by
    have h1 := hcI i y
    have h2 : |lo i| ≤ ∑ i, |lo i| :=
      Finset.single_le_sum (f := fun i => |lo i|) (fun i _ => abs_nonneg _) (mem_univ i)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (lo i), le_abs_self (lo i), h1.1, h1.2]
  have h : SDHyp ε a c (∑ i, |lo i| + B) := ⟨hε, ha, hsum, hc, hcb⟩
  have hosc_c : ∀ i y y', c i y - c i y' ≤ B := fun i y y' => by
    linarith [(hcI i y).2, (hcI i y').1]
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
  have hm' : (0 : ℝ) < Fintype.card ι := card_pos_real
  have hlog : 0 ≤ Real.log (1 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)
  set s : ℝ := √(Real.log (1 / α) / (2 * Fintype.card ι))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set t : ℝ := B * s
  have ht0 : 0 ≤ t := mul_nonneg hB.le hs0
  set bad : Set Ω := {ω | (Fintype.card ι : ℝ) * t ≤ ∑ j, ((∫ x, g x ∂P) - g (Y j ω))}
  have hbad_meas : MeasurableSet bad :=
    measurableSet_le measurable_const
      (Finset.measurable_sum _ fun j _ => measurable_const.sub (hg.comp (hY j)))
  have hbad : μ bad ≤ ENNReal.ofReal α := by
    have hH := hoeffding_lower_fintype hg hB hgI hY hind hlaw ht0
    have hexp : Real.exp (-(2 * Fintype.card ι * t ^ 2 / B ^ 2)) = α := by
      have : 2 * (Fintype.card ι : ℝ) * t ^ 2 / B ^ 2 = Real.log (1 / α) := by
        simp only [t, s]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    rw [hexp] at hH
    rw [← ofReal_measureReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hH
  have hgood : badᶜ ⊆ {ω | Theta ε a c P ≤ Theta ε a c (empOn fun j => Y j ω) +
      ((B * √(Real.log (1 / α) / (2 * Fintype.card ι)) : ℝ) : EReal)} := by
    intro ω hω
    have : IsProbabilityMeasure (empOn fun j => Y j ω) := isProb_empOn _
    obtain ⟨hΘ, hsg⟩ := Theta_subgradient' h P (empOn fun j => Y j ω) hmax
    have hemp : ∫ y, g y ∂(empOn fun j => Y j ω) =
        (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) :=
      integral_empOn _ hg hgb
    simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    rw [Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hω
    have hdev : (∫ x, g x ∂P) - (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) < t := by
      rw [show (∫ x, g x ∂P) - (1 / (Fintype.card ι : ℝ)) * ∑ j, g (Y j ω) =
        ((Fintype.card ι : ℝ) * (∫ x, g x ∂P) - ∑ j, g (Y j ω)) / Fintype.card ι by
          field_simp]
      rw [div_lt_iff₀ hm']
      linarith
    show Theta ε a c P ≤ Theta ε a c (empOn fun j => Y j ω) + (t : EReal)
    rw [hΘ]
    calc (Jdual ε a c P fs : EReal)
        ≤ ((Jdual ε a c P fs + ∫ y, g y ∂(empOn fun j => Y j ω) - ∫ y, g y ∂P : ℝ) : EReal)
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
