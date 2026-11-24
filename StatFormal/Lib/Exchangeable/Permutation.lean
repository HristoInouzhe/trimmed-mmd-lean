import StatFormal.Lib.Exchangeable.Ranks
import Mathlib.Data.Fintype.Perm

/-!
# Permutation (randomisation) tests, full group (component F.E, part 3)

Data `x : Fin n → X`, the group `G = S_n` acting by `x ↦ x ∘ g`, a measurable statistic
`T : (Fin n → X) → ℝ`, and a null law `μ` invariant under every `g` (`μ.map (· ∘ g) = μ`).
The full-group p-value is `p(x) = #{g ∈ G | T(x ∘ g) ≥ T(x)} / |G|` (`permPval`; the identity is
counted, so `p ≥ 1/|G|`).

Main results:
* `perm_test_valid`: `μ(p ≤ α) ≤ α` for every real `α`;
* `perm_test_valid'`: the same for `p' = (1 + #{g | T(x∘g) ≥ T(x)})/(1 + |G|)` (`p' ≥ p`);
* `perm_test_valid_rv`: the same for a random data vector with permutation-invariant law.
Route: averaging over the group (`card_mul_measure_le`) and the combinatorial bound
`#{h | #{g | v_h ≤ v_g} ≤ K} ≤ K` (`card_cntLe_le` applied to `−v`).
Not covered: Monte-Carlo p-values with randomly sampled group elements.
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal

namespace StatFormal.Foundations.Exchangeable

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- `#{g | T(x ∘ g) ≥ T(x)}`. -/
def permCount (T : (Fin n → X) → ℝ) (x : Fin n → X) : ℕ :=
  #(univ.filter fun g : Equiv.Perm (Fin n) => T x ≤ T (x ∘ g))

/-- The full-group permutation p-value `#{g | T(x ∘ g) ≥ T(x)} / n!`. -/
def permPval (T : (Fin n → X) → ℝ) (x : Fin n → X) : ℝ :=
  (permCount T x : ℝ) / (Nat.factorial n)

lemma measurable_comp_perm' (τ : Equiv.Perm (Fin n)) :
    Measurable fun z : Fin n → X => z ∘ τ :=
  Measurable.of_eval fun i => measurable_pi_apply (τ i)

lemma measurable_permCount {T : (Fin n → X) → ℝ} (hT : Measurable T) :
    Measurable (permCount T) := by
  unfold permCount
  simp_rw [Finset.card_filter]
  refine Finset.measurable_sum _ fun g _ => ?_
  exact Measurable.ite (measurableSet_le hT (hT.comp (measurable_comp_perm' g)))
    measurable_const measurable_const

omit [MeasurableSpace X] in
lemma permCount_comp (T : (Fin n → X) → ℝ) (x : Fin n → X) (h : Equiv.Perm (Fin n)) :
    permCount T (x ∘ h) = #(univ.filter fun g : Equiv.Perm (Fin n) => T (x ∘ h) ≤ T (x ∘ g)) := by
  unfold permCount
  rw [Finset.card_filter, Finset.card_filter]
  have : ∀ g : Equiv.Perm (Fin n), (x ∘ h) ∘ g = x ∘ (h * g) := fun g => by
    ext i; simp [Equiv.Perm.coe_mul]
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => if T (x ∘ h) ≤ T (x ∘ g) then 1 else 0)

/-- `μ(#{g | T(x∘g) ≥ T(x)} ≤ K) ≤ K / n!`. -/
theorem perm_count_le (μ : Measure (Fin n → X)) [IsProbabilityMeasure μ]
    (hinv : ∀ τ : Equiv.Perm (Fin n), μ.map (fun z => z ∘ τ) = μ) {T : (Fin n → X) → ℝ}
    (hT : Measurable T) (K : ℕ) :
    (Nat.factorial n : ℝ≥0∞) * μ {x | permCount T x ≤ K} ≤ K := by
  have hE : MeasurableSet {x : Fin n → X | permCount T x ≤ K} :=
    measurable_permCount hT (MeasurableSet.of_discrete (s := {c : ℕ | c ≤ K}))
  have := card_mul_measure_le μ (fun (h : Equiv.Perm (Fin n)) (z : Fin n → X) => z ∘ h)
    (fun h => measurable_comp_perm' h)
    hinv hE (K := K) (Filter.Eventually.of_forall fun x => by
      have hc := card_cntLe_le (fun g : Equiv.Perm (Fin n) => -T (x ∘ g)) K
      simp only [neg_le_neg_iff] at hc
      refine le_trans (le_of_eq ?_) hc
      congr 1
      ext h
      simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, permCount_comp])
  rwa [Fintype.card_perm, Fintype.card_fin] at this

/-- **Validity of the full-group permutation test**: `μ(p ≤ α) ≤ α`. -/
theorem perm_test_valid (μ : Measure (Fin n → X)) [IsProbabilityMeasure μ]
    (hinv : ∀ τ : Equiv.Perm (Fin n), μ.map (fun z => z ∘ τ) = μ) {T : (Fin n → X) → ℝ}
    (hT : Measurable T) (α : ℝ) :
    μ {x | permPval T x ≤ α} ≤ ENNReal.ofReal α := by
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rcases lt_or_ge α 0 with hα | hα
  · have : {x : Fin n → X | permPval T x ≤ α} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hα (div_nonneg (Nat.cast_nonneg _) hf.le)
    rw [this, measure_empty]
    exact bot_le
  set K := ⌊α * Nat.factorial n⌋₊
  have hsub : {x : Fin n → X | permPval T x ≤ α} ⊆ {x | permCount T x ≤ K} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, permPval, div_le_iff₀ hf] at hx ⊢
    exact Nat.le_floor hx
  have hK := perm_count_le μ hinv hT K
  have hKb : (K : ℝ≥0∞) ≤ (Nat.factorial n : ℝ≥0∞) * ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_comm]
    exact Nat.floor_le (mul_nonneg hα hf.le)
  have hc0 : (Nat.factorial n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hct : (Nat.factorial n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (measure_mono hsub).trans
    ((ENNReal.mul_le_mul_iff_right hc0 hct).mp (hK.trans hKb))

/-- The `(1 + count)/(1 + |G|)` p-value dominates `count/|G|`, hence is also valid. -/
theorem perm_test_valid' (μ : Measure (Fin n → X)) [IsProbabilityMeasure μ]
    (hinv : ∀ τ : Equiv.Perm (Fin n), μ.map (fun z => z ∘ τ) = μ) {T : (Fin n → X) → ℝ}
    (hT : Measurable T) (α : ℝ) :
    μ {x | (1 + permCount T x : ℝ) / (1 + Nat.factorial n) ≤ α} ≤ ENNReal.ofReal α := by
  refine le_trans (measure_mono fun x hx => ?_) (perm_test_valid μ hinv hT α)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have hc : (permCount T x : ℝ) ≤ Nat.factorial n := by
    have : permCount T x ≤ Nat.factorial n := by
      unfold permCount
      exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_perm, Fintype.card_fin])
    exact_mod_cast this
  refine le_trans ?_ hx
  unfold permPval
  rw [div_le_div_iff₀ hf (by positivity)]
  nlinarith

/-- Permutation test for a random data vector with permutation-invariant law. -/
theorem perm_test_valid_rv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Fin n → X} (hD : Measurable D)
    (hexch : ∀ τ : Equiv.Perm (Fin n), P.map (fun ω => D ω ∘ τ) = P.map D)
    {T : (Fin n → X) → ℝ} (hT : Measurable T) (α : ℝ) :
    P {ω | permPval T (D ω) ≤ α} ≤ ENNReal.ofReal α := by
  have hinv : ∀ τ : Equiv.Perm (Fin n), (P.map D).map (fun z => z ∘ τ) = P.map D := fun τ => by
    rw [Measure.map_map (measurable_comp_perm' τ) hD]
    exact hexch τ
  have hmeas : MeasurableSet {x : Fin n → X | permPval T x ≤ α} :=
    measurableSet_le ((measurable_from_nat.comp (measurable_permCount hT)).div_const _)
      measurable_const
  have h := perm_test_valid (P.map D) hinv hT α
  rwa [Measure.map_apply hD hmeas] at h

end StatFormal.Foundations.Exchangeable
