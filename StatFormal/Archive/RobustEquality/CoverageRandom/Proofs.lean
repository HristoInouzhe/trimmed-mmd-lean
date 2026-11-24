import StatFormal.Archive.RobustEquality.CoverageRandom.Statements
import StatFormal.Lib.SemiDiscrete.RandomFolds

/-!
# Proofs: `thm:coverage` with random folds, and inner-measure forms of the coverage claims
(untrusted proof file)

* `coverage_general_inner`: the measurable-event strengthening of `Coverage.Claims.coverage_general`
  (the event is `⋂_v E_v`, the per-fold events; union bound on the complements; pointwise fold
  convexity `OT_ε(P̂,P) ≤ Σ_v w_v OT_ε(P̂_v,P)`);
* `coverage_fold_hoeffding_inner`: the measurable-event strengthening of
  `Coverage.Claims.coverage_fold_hoeffding` (the coverage event itself is measurable, because
  `Θ(P̂_m) = sup_n J_{P̂_m}(d_n)` over a countable dense sequence);
* `coverage_random_folds : Claims.coverage_random_folds`: `coverage_general_inner` with `Ω = K^N`,
  `x = id`, `ρ = ρ̂`; the per-fold events are measurable with probability `≥ 1 − a/V` by
  `SemiDiscrete.fold_coverage_random` (Fubini over fold ⊗ held-out coordinates).
`OTdisc`, `empOn`, `rhoHat` here are definitionally `SemiDiscrete.Theta`, `.empOn`, `.rhoHat`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatFormal.RobustEquality.CoverageRandom

open StatFormal.RobustEquality.SemidualStrong StatFormal.RobustEquality.Semidual

/-- Union bound, inner form: if each measurable `E v` has probability `≥ 1 − a/V`, then
`⋂_v E v` has probability `≥ 1 − a`. -/
lemma inner_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ} (hV : 0 < V) {a : ℝ} (ha0 : 0 < a) (E : Fin V → Set Ω)
    (hE : ∀ v, MeasurableSet (E v)) (hp : ∀ v, ENNReal.ofReal (1 - a / V) ≤ μ (E v)) :
    ENNReal.ofReal (1 - a) ≤ μ (⋂ v, E v) := by
  set U : Set Ω := ⋃ v, (E v)ᶜ
  have hU : MeasurableSet U := MeasurableSet.iUnion fun v => (hE v).compl
  have hcompl : ∀ v, μ (E v)ᶜ ≤ ENNReal.ofReal (a / V) := by
    intro v
    rw [prob_compl_eq_one_sub (hE v), tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (a / V + (1 - a / V)) := by
          rw [add_sub_cancel, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (a / V) + ENNReal.ofReal (1 - a / V) := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add_right (hp v) _
  have hUle : μ U ≤ ENNReal.ofReal a := by
    calc μ U ≤ ∑ v, μ (E v)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _v : Fin V, ENNReal.ofReal (a / V) := Finset.sum_le_sum fun v _ => hcompl v
      _ = ENNReal.ofReal a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg V)]
        congr 1
        have : (0 : ℝ) < V := by exact_mod_cast hV
        field_simp
  have hgood : Uᶜ ⊆ ⋂ v, E v := by
    intro ω hω
    simp only [U, Set.mem_compl_iff, Set.mem_iUnion, not_exists, not_not] at hω
    exact Set.mem_iInter.mpr hω
  calc ENNReal.ofReal (1 - a) = 1 - ENNReal.ofReal a := by
        rw [ENNReal.ofReal_sub _ ha0.le, ENNReal.ofReal_one]
    _ ≤ 1 - μ U := tsub_le_tsub_left hUle _
    _ = μ Uᶜ := (prob_compl_eq_one_sub hU).symm
    _ ≤ _ := measure_mono hgood

/-- **`thm:coverage-general`, inner-measure form**: under the hypotheses of
`Coverage.Claims.coverage_general`, there is a measurable event of probability `≥ 1 − a` inside the
coverage event. -/
theorem coverage_general_inner (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω]
    (μΩ : Measure Ω) [IsProbabilityMeasure μΩ] (P : Measure K) [IsProbabilityMeasure P]
    (N V : ℕ) (fold : Fin N → Fin V) (n : Fin V → ℕ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (c : K → K → ℝ) (x : Ω → Fin N → K) (ρ : Fin V → Ω → ℝ) (ε a : ℝ)
    (hε : 0 < ε) (ha0 : 0 < a) (hN : 0 < N) (hsurj : Function.Surjective fold)
    (hc : ∀ x0, Measurable (c x0)) (hcb : ∃ B, ∀ x0 y, |c x0 y| ≤ B)
    (hmeas : ∀ v, MeasurableSet {ω | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)})
    (hprob : ∀ v, ENNReal.ofReal (1 - a / V) ≤ μΩ {ω | OTdisc ε
        (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)}) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - a) ≤ μΩ E ∧
      E ⊆ {ω | OTdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (x ω i)) P ≤
          ((∑ v, ((n v : ℝ) / N) * ρ v ω : ℝ) : EReal)} := by
  obtain ⟨B, hB⟩ := hcb
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · subst h0; exact (fold ⟨0, hN⟩).elim0
    · exact h0
  set E : Fin V → Set Ω := fun v => {ω | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
    (fun j => c (x ω (e v j))) P ≤ (ρ v ω : EReal)}
  refine ⟨⋂ v, E v, MeasurableSet.iInter hmeas, inner_union_bound μΩ hV ha0 E hmeas hprob, ?_⟩
  intro ω hω
  have hω : ∀ v, ω ∈ E v := Set.mem_iInter.mp hω
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
  rw [StatFormal.RobustEquality.Coverage.foldWeight_uniform e v]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hv := hω v
  simp only [E, Set.mem_ofPred_eq] at hv
  have := htv v
  rw [StatFormal.RobustEquality.Coverage.foldA_uniform hN e hsurj v] at this
  change StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
    (fun j => c (x ω (e v j))) P ≤ _ at hv
  rw [show (StatFormal.Foundations.SemiDiscrete.foldC (fun i => c (x ω i)) fold e v) =
    fun j => c (x ω (e v j)) from rfl] at this
  rw [this] at hv
  exact EReal.coe_le_coe_iff.mp hv

/-- **Hoeffding deviation term, inner-measure form**: under the hypotheses of
`Coverage.Claims.coverage_fold_hoeffding`, the coverage event is itself measurable (so it is a
measurable event of probability `≥ 1 − α` inside itself). -/
theorem coverage_fold_hoeffding_inner (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω]
    (k m : ℕ) (ε Bc α : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (P : Measure K)
    [IsProbabilityMeasure P] (μΩ : Measure Ω) [IsProbabilityMeasure μΩ] (Y : Fin m → Ω → K)
    (hs : Setting ε a c) (hBc : 0 < Bc) (hosc : ∀ i y y', c i y - c i y' ≤ Bc) (hm0 : 0 < m)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y μΩ) (hlaw : ∀ j, μΩ.map (Y j) = P)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ μΩ E ∧
      E ⊆ {ω | OTdisc ε a c P ≤
        OTdisc ε a c (StatFormal.RobustEquality.Coverage.empMeasure fun j => Y j ω) +
          ((Bc * √(Real.log (1 / α) / (2 * m)) : ℝ) : EReal)} := by
  obtain ⟨hε, ha, hsum, hc, B, hB⟩ := hs
  have hz : ∀ _z : Unit, StatFormal.Foundations.SemiDiscrete.SDHyp ε a c B :=
    fun _ => ⟨hε, ha, hsum, hc, hB⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
  have hC : ∀ i, Measurable fun p : Unit × K => (fun _ : Unit => c) p.1 i p.2 := fun i =>
    (hc i).comp measurable_snd
  have hmT := StatFormal.Foundations.SemiDiscrete.measurable_Theta_empOn (ι := Fin m) hC hz
  have hemp : ∀ ω, StatFormal.RobustEquality.Coverage.empMeasure (fun j => Y j ω) =
      StatFormal.Foundations.SemiDiscrete.empOn (fun j => Y j ω) := fun ω => by
    unfold StatFormal.RobustEquality.Coverage.empMeasure StatFormal.Foundations.SemiDiscrete.empOn
    rw [Fintype.card_fin]
  have hmeasT : Measurable fun ω => OTdisc ε a c
      (StatFormal.RobustEquality.Coverage.empMeasure fun j => Y j ω) := by
    have hpair : Measurable fun ω : Ω => (((), fun j => Y j ω) : Unit × (Fin m → K)) :=
      measurable_const.prodMk (measurable_pi_iff.mpr hY)
    have := hmT.comp (f := fun ω : Ω => (((), fun j => Y j ω) : Unit × (Fin m → K))) hpair
    simp_rw [hemp]
    exact this
  refine ⟨_, measurableSet_le measurable_const (hmeasT.add_const _),
    StatFormal.RobustEquality.Coverage.coverage_fold_hoeffding K Ω k m ε Bc α a c P μΩ Y
      ⟨hε, ha, hsum, hc, B, hB⟩ hBc hosc hm0 hY hind hlaw hα0 hα1, subset_rfl⟩

/-- **`thm:coverage` with random folds.** -/
theorem coverage_random_folds : Claims.coverage_random_folds := by
  intro K _ P _ N V fold n e c B Bc ε a hsurj hheld hcm hB hε hBc hosc ha0 ha1 hN
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · subst h0; exact (fold ⟨0, hN⟩).elim0
    · exact h0
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have hαV0 : 0 < a / V := div_pos ha0 hV'
  have hαV1 : a / V ≤ 1 := by
    rw [div_le_one hV']
    have : (1 : ℝ) ≤ V := by exact_mod_cast hV
    linarith
  have hset : ∀ v, {X : Fin N → K | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (X (e v j))) P ≤ (rhoHat ε c e Bc a v X : EReal)} =
      {X : Fin N → K |
        StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
            (fun j => c (X (e v j))) P ≤
          StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
            (fun j => c (X (e v j)))
            (StatFormal.Foundations.SemiDiscrete.empOn fun i : {i // ¬ fold i = v} => X i) +
          ((Bc * √(Real.log (1 / (a / V)) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) :
            EReal)} := by
    intro v
    obtain ⟨i0, hi0⟩ := hheld v
    have : Nonempty {i // ¬ fold i = v} := ⟨⟨i0, hi0⟩⟩
    ext X
    have hP := StatFormal.Foundations.SemiDiscrete.isProb_empOn (K := K)
      fun i : {i // ¬ fold i = v} => X i
    obtain ⟨r, hr⟩ := StatFormal.Foundations.SemiDiscrete.Theta_finite
      (StatFormal.Foundations.SemiDiscrete.sdhyp_fold_uniform hε hcm hB e hsurj v
        (fun i => X i)) (StatFormal.Foundations.SemiDiscrete.empOn
          fun i : {i // ¬ fold i = v} => X i)
    simp only [Set.mem_ofPred_eq]
    show StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (X (e v j))) P ≤
        (((StatFormal.Foundations.SemiDiscrete.Theta ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
          (fun j => c (X (e v j)))
          (StatFormal.Foundations.SemiDiscrete.empOn fun i : {i // ¬ fold i = v} => X i)).toReal +
          Bc * √(Real.log (V / a) / (2 * Fintype.card {i // ¬ fold i = v})) : ℝ) : EReal) ↔ _
    rw [hr, EReal.toReal_coe, EReal.coe_add, one_div_div]
  have hfold : ∀ v, MeasurableSet {X : Fin N → K | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
        (fun j => c (X (e v j))) P ≤ (rhoHat ε c e Bc a v X : EReal)} ∧
      ENNReal.ofReal (1 - a / V) ≤ Measure.pi (fun _ : Fin N => P)
        {X : Fin N → K | OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v)
          (fun j => c (X (e v j))) P ≤ (rhoHat ε c e Bc a v X : EReal)} := by
    intro v
    obtain ⟨i0, hi0⟩ := hheld v
    have : Nonempty {i // ¬ fold i = v} := ⟨⟨i0, hi0⟩⟩
    rw [hset v]
    exact StatFormal.Foundations.SemiDiscrete.fold_coverage_random P e hsurj v hcm hB hε hBc
      hosc hαV0 hαV1
  exact coverage_general_inner K (Fin N → K) (Measure.pi fun _ : Fin N => P) P N V fold n e c
    (fun X => X) (rhoHat ε c e Bc a) ε a hε ha0 hN hsurj
    (fun x0 => hcm.comp (measurable_const.prodMk measurable_id)) ⟨B, hB⟩
    (fun v => (hfold v).1) (fun v => (hfold v).2)

example : Claims.coverage_random_folds := coverage_random_folds

end StatFormal.RobustEquality.CoverageRandom
