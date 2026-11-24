import StatFormal.Lib.Exchangeable.Permutation

/-!
# Randomisation tests for a general finite group (component F.E, part 4)

A finite group `G` acting on a measurable space `Ω` through `act : G → Ω → Ω`
(`IsAct`: `act (g * h) = act g ∘ act h`, each `act g` measurable), a `G`-invariant law `μ`
(`μ.map (act g) = μ` for all `g`), and a measurable statistic `T : Ω → ℝ`.
The full-group p-value is `p(x) = #{g ∈ G | T(g·x) ≥ T(x)} / |G|` (`grpPval`).

Main results:
* `grp_test_valid`: `μ(p ≤ α) ≤ α` for every real `α`;
* `subgroup_test_valid`: the special case of a finite subgroup `G ≤ Perm ι` relabelling data
  `x : ι → X` by `x ↦ x ∘ σ⁻¹` (`(C_{σ⁻¹(1)}, …, C_{σ⁻¹(J)})`), e.g. strata-preserving or
  size-preserving permutations of clusters (otfd G `prop:test`(b));
* `sum_measure_eq_lintegral_card`: `Σ_i μ(A_i) = ∫ #{i | x ∈ A_i} dμ` (used for Monte Carlo).
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Foundations.Exchangeable

section Act

variable {G Ω : Type*} [Group G] [Fintype G] [MeasurableSpace Ω]

/-- `act` is a measurable left action of `G` on `Ω`. -/
structure IsAct (act : G → Ω → Ω) : Prop where
  mul : ∀ g h x, act (g * h) x = act g (act h x)
  meas : ∀ g, Measurable (act g)

/-- `#{g | T(g·x) ≥ T(x)}`. -/
def grpCount (act : G → Ω → Ω) (T : Ω → ℝ) (x : Ω) : ℕ :=
  #(univ.filter fun g : G => T x ≤ T (act g x))

/-- The full-group p-value `#{g | T(g·x) ≥ T(x)} / |G|`. -/
def grpPval (act : G → Ω → Ω) (T : Ω → ℝ) (x : Ω) : ℝ :=
  (grpCount act T x : ℝ) / Fintype.card G

variable {act : G → Ω → Ω} {T : Ω → ℝ}

lemma measurable_grpCount (hact : IsAct act) (hT : Measurable T) :
    Measurable (grpCount act T) := by
  unfold grpCount
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ fun g _ => ?_
  exact Measurable.ite (measurableSet_le hT (hT.comp (hact.meas g)))
    measurable_const measurable_const

lemma grpCount_act (hact : IsAct act) (x : Ω) (h : G) :
    grpCount act T (act h x) = #(univ.filter fun g : G => T (act h x) ≤ T (act g x)) := by
  unfold grpCount
  rw [Finset.card_filter, Finset.card_filter]
  simp_rw [← hact.mul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => if T (act h x) ≤ T (act g x) then 1 else 0)

theorem grp_count_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hact : IsAct act)
    (hinv : ∀ g, μ.map (act g) = μ) (hT : Measurable T) (K : ℕ) :
    (Fintype.card G : ℝ≥0∞) * μ {x | grpCount act T x ≤ K} ≤ K := by
  have hE : MeasurableSet {x : Ω | grpCount act T x ≤ K} :=
    measurable_grpCount hact hT (MeasurableSet.of_discrete (s := {c : ℕ | c ≤ K}))
  exact card_mul_measure_le μ act hact.meas hinv hE (K := K)
    (Filter.Eventually.of_forall fun x => by
      have hc := card_cntLe_le (fun g : G => -T (act g x)) K
      simp only [neg_le_neg_iff] at hc
      refine le_trans (le_of_eq ?_) hc
      congr 1
      ext h
      simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, grpCount_act hact])

/-- **Validity of the full-group randomisation test**: `μ(p ≤ α) ≤ α`. -/
theorem grp_test_valid (μ : Measure Ω) [IsProbabilityMeasure μ] (hact : IsAct act)
    (hinv : ∀ g, μ.map (act g) = μ) (hT : Measurable T) (α : ℝ) :
    μ {x | grpPval act T x ≤ α} ≤ ENNReal.ofReal α := by
  have hf : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rcases lt_or_ge α 0 with hα | hα
  · have : {x : Ω | grpPval act T x ≤ α} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hα (div_nonneg (Nat.cast_nonneg _) hf.le)
    rw [this, measure_empty]
    exact bot_le
  set K := ⌊α * Fintype.card G⌋₊
  have hsub : {x : Ω | grpPval act T x ≤ α} ⊆ {x | grpCount act T x ≤ K} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, grpPval, div_le_iff₀ hf] at hx ⊢
    exact Nat.le_floor hx
  have hK := grp_count_le μ hact hinv hT K
  have hKb : (K : ℝ≥0∞) ≤ (Fintype.card G : ℝ≥0∞) * ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_comm]
    exact Nat.floor_le (mul_nonneg hα hf.le)
  have hc0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hct : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (measure_mono hsub).trans
    ((ENNReal.mul_le_mul_iff_right hc0 hct).mp (hK.trans hKb))

end Act

/-! ### Subgroups of permutations: relabelling clusters -/

section Subgroup

variable {ι X : Type*} [MeasurableSpace X]

/-- Relabelling by `σ`: `x ↦ x ∘ σ⁻¹`, i.e. `(x_{σ⁻¹(1)}, …)`. -/
def relabel (G : Subgroup (Equiv.Perm ι)) (σ : G) (x : ι → X) : ι → X :=
  x ∘ ⇑((σ : Equiv.Perm ι)⁻¹)

lemma isAct_relabel (G : Subgroup (Equiv.Perm ι)) : IsAct (relabel (X := X) G) where
  mul g h x := by
    ext i
    simp [relabel, mul_inv_rev, Equiv.Perm.coe_mul]
  meas σ := Measurable.of_eval fun i => measurable_pi_apply _

/-- **Cluster relabelling test** (otfd G `prop:test`(b)): for a finite group `G` of permutations
of the clusters under which the law of `(C_1, …, C_J)` is invariant, the test relabelling whole
clusters by `G` has level at most `α`. -/
theorem subgroup_test_valid (G : Subgroup (Equiv.Perm ι)) [Fintype G]
    (μ : Measure (ι → X)) [IsProbabilityMeasure μ]
    (hinv : ∀ σ ∈ G, μ.map (fun x => x ∘ ⇑σ⁻¹) = μ) {T : (ι → X) → ℝ} (hT : Measurable T)
    (α : ℝ) :
    μ {x | grpPval (relabel G) T x ≤ α} ≤ ENNReal.ofReal α :=
  grp_test_valid μ (isAct_relabel G) (fun σ => hinv σ σ.2) hT α

end Subgroup

/-- `Σ_i μ(A_i) = ∫ #{i | x ∈ A_i} dμ`. -/
theorem sum_measure_eq_lintegral_card {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] (A : ι → Set Ω) [∀ x, DecidablePred fun i => x ∈ A i]
    (hA : ∀ i, MeasurableSet (A i)) :
    ∑ i, μ (A i) = ∫⁻ x, (#(univ.filter fun i => x ∈ A i) : ℝ≥0∞) ∂μ := by
  have h2 : ∀ x, (#(univ.filter fun i => x ∈ A i) : ℝ≥0∞) = ∑ i, (A i).indicator 1 x := by
    intro x
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x ∈ A i
    · rw [ite_eq_left h, Set.indicator_of_mem h, Pi.one_apply]
    · rw [ite_eq_right h, Set.indicator_of_notMem h]
  simp_rw [h2]
  rw [lintegral_finsetSum _ fun i _ => (measurable_one.indicator (hA i))]
  exact Finset.sum_congr rfl fun i _ => (lintegral_indicator_one (hA i)).symm

end StatFormal.Foundations.Exchangeable
