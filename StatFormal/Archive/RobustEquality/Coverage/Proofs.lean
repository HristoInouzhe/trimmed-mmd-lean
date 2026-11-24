import StatFormal.Archive.RobustEquality.Coverage.Statements
import StatFormal.Lib.SemiDiscrete.Coverage

/-!
# Proofs: `thm:coverage-general` and the Hoeffding deviation term of `thm:coverage`
(untrusted proof file)

Routes (the paper's):
* `coverage_general`: pointwise in `ω`, `OT_ε(P̂, P) ≤ Σ_v w_v OT_ε(P̂_v, P)`
  (`SemiDiscrete.Theta_le_sum_fold_real`, after identifying `foldWeight = n v / N` and
  `foldA = 1 / n v`), then a union bound over the complements of the (measurable) per-fold events;
* `coverage_fold_hoeffding`: `SemiDiscrete.coverage_fold` (subgradient inequality at `Q = P`,
  `Q' = P̂_m`, plus one-sided Hoeffding), with `lo_i := inf_K c_i`
  so that `c_i ∈ [lo_i, lo_i + B_c]`.
`OTdisc` is definitionally `SemiDiscrete.Theta`; `empMeasure` here equals `SemiDiscrete.empMeasure`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatFormal.RobustEquality.Coverage

open StatFormal.RobustEquality.SemidualStrong StatFormal.RobustEquality.Semidual

/-! ### `thm:coverage-general` -/

lemma card_fiber {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (v : Fin V) :
    Fintype.card {i // fold i = v} = n v := by
  rw [← Fintype.card_congr (e v), Fintype.card_fin]

lemma n_pos {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (hsurj : Function.Surjective fold) (v : Fin V) :
    0 < n v := by
  obtain ⟨i, hi⟩ := hsurj v
  rw [← card_fiber e v]
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

lemma foldWeight_uniform {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (v : Fin V) :
    StatFormal.Foundations.SemiDiscrete.foldWeight (fun _ : Fin N => (1 : ℝ) / N) fold v =
      (n v : ℝ) / N := by
  unfold StatFormal.Foundations.SemiDiscrete.foldWeight
  rw [Finset.sum_const, Finset.card_univ, card_fiber e v, nsmul_eq_mul]
  ring

lemma foldA_uniform {N V : ℕ} (hN : 0 < N) {fold : Fin N → Fin V} {n : Fin V → ℕ}
    (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (hsurj : Function.Surjective fold) (v : Fin V) :
    StatFormal.Foundations.SemiDiscrete.foldA (fun _ : Fin N => (1 : ℝ) / N) fold e v =
      fun _ => (1 : ℝ) / n v := by
  funext j
  unfold StatFormal.Foundations.SemiDiscrete.foldA
  rw [foldWeight_uniform e v]
  have h1 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (0 : ℝ) < n v := by exact_mod_cast n_pos e hsurj v
  field_simp

theorem coverage_general : Claims.coverage_general := by
  intro K Ω _ _ μΩ _ P _ N V fold n e c x ρ ε a hε ha0 ha1 hN hsurj hc ⟨B, hB⟩ hmeas hprob
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · subst h0; exact (fold ⟨0, hN⟩).elim0
    · exact h0
  set E : Fin V → Set Ω := fun v => {ω | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
    (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)}
  -- deterministic step: on `⋂_v E_v` the conclusion holds
  have hdet : ∀ ω, (∀ v, ω ∈ E v) → OTdisc ε (fun _ : Fin N => (1 : ℝ) / N)
      (fun i => c (x ω i)) P ≤ ((∑ v, ((n v : ℝ) / N) * ρ v ω : ℝ) : EReal) := by
    intro ω hω
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h : StatFormal.Foundations.SemiDiscrete.SDHyp ε (fun _ : Fin N => (1 : ℝ) / N)
        (fun i => c (x ω i)) B :=
      ⟨hε, fun _ => by positivity, by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp,
        fun i => hc _, fun i y => hB _ y⟩
    obtain ⟨t, tv, ht, htv, hle⟩ :=
      StatFormal.Foundations.SemiDiscrete.Theta_le_sum_fold_real fold e h hsurj P
    change StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin N => (1 : ℝ) / N)
      (fun i => c (x ω i)) P ≤ _
    rw [ht, EReal.coe_le_coe_iff]
    refine hle.trans (Finset.sum_le_sum fun v _ => ?_)
    rw [foldWeight_uniform e v]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hv := hω v
    simp only [E, Set.mem_ofPred_eq] at hv
    have := htv v
    rw [foldA_uniform hN e hsurj v] at this
    change StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
      (fun j => c (x ω (e v j))) P ≤ _ at hv
    rw [show (StatFormal.Foundations.SemiDiscrete.foldC (fun i => c (x ω i)) fold e v) =
      fun j => c (x ω (e v j)) from rfl] at this
    rw [this] at hv
    exact EReal.coe_le_coe_iff.mp hv
  -- union bound
  set U : Set Ω := ⋃ v, (E v)ᶜ
  have hU : MeasurableSet U := MeasurableSet.iUnion fun v => (hmeas v).compl
  have hcompl : ∀ v, μΩ (E v)ᶜ ≤ ENNReal.ofReal (a / V) := by
    intro v
    rw [prob_compl_eq_one_sub (hmeas v), tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (a / V + (1 - a / V)) := by
          rw [add_sub_cancel, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (a / V) + ENNReal.ofReal (1 - a / V) := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add_right (hprob v) _
  have hUle : μΩ U ≤ ENNReal.ofReal a := by
    calc μΩ U ≤ ∑ v, μΩ (E v)ᶜ := measure_iUnion_fintype_le μΩ _
      _ ≤ ∑ _v : Fin V, ENNReal.ofReal (a / V) := Finset.sum_le_sum fun v _ => hcompl v
      _ = ENNReal.ofReal a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg V)]
        congr 1
        have : (0 : ℝ) < V := by exact_mod_cast hV
        field_simp
  have hgood : Uᶜ ⊆ {ω | OTdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (x ω i)) P ≤
      ((∑ v, ((n v : ℝ) / N) * ρ v ω : ℝ) : EReal)} := by
    intro ω hω
    simp only [U, Set.mem_compl_iff, Set.mem_iUnion, not_exists, not_not] at hω
    exact hdet ω hω
  calc ENNReal.ofReal (1 - a) = 1 - ENNReal.ofReal a := by
        rw [ENNReal.ofReal_sub _ ha0.le, ENNReal.ofReal_one]
    _ ≤ 1 - μΩ U := tsub_le_tsub_left hUle _
    _ = μΩ Uᶜ := (prob_compl_eq_one_sub hU).symm
    _ ≤ _ := measure_mono hgood

/-! ### Hoeffding deviation term -/

lemma empMeasure_eq {K : Type*} [MeasurableSpace K] {m : ℕ} (y : Fin m → K) :
    empMeasure y = StatFormal.Foundations.SemiDiscrete.empMeasure y := by
  unfold empMeasure StatFormal.Foundations.SemiDiscrete.empMeasure
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]

theorem coverage_fold_hoeffding : Claims.coverage_fold_hoeffding := by
  intro K Ω _ _ k m ε Bc α a c P _ μΩ _ Y hs hBc hosc hm0 hY hind hlaw hα0 hα1
  obtain ⟨hε, ha, hsum, hc, -⟩ := hs
  have hne : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have h1 : P Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hK, measure_empty] at h1
    exact zero_ne_one h1
  have hlo : ∀ i, ∃ lo, ∀ y, c i y ∈ Set.Icc lo (lo + Bc) := fun i =>
    StatFormal.Foundations.SemiDiscrete.exists_Icc_of_osc (hosc i)
  choose lo hlo using hlo
  have h := StatFormal.Foundations.SemiDiscrete.coverage_fold hε ha hsum hc hBc hlo P μΩ hm0 Y hY
    hind hlaw hα0 hα1
  simp_rw [empMeasure_eq]
  exact h

example : Claims.coverage_general := coverage_general
example : Claims.coverage_fold_hoeffding := coverage_fold_hoeffding

end StatFormal.RobustEquality.Coverage
