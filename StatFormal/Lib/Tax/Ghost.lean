import StatFormal.Lib.Tax.Tax
import StatFormal.Archive.RobustEquality.Coverage.Statements

/-!
# Ghost samples (`thm:ghost`)

Library component (robust equality, JASA). Untrusted library code; it imports the frozen
`Coverage/Statements.lean` only for `empMeasure`, and does not modify it.

## Main results

* `pi_empMeasure`: `(P̂_y)^{⊗n} = Σ_{J : [n] → [N]} N^{−n} δ_{y ∘ J}` (sampling with replacement);
* `map_comp_injective`: for injective `J : [n] → [N]`, `(P^{⊗N}).map (· ∘ J) = P^{⊗n}`;
* `card_not_injective_le`: at most `n² N^n / N` maps `[n] → [N]` are not injective (birthday bound);
* `prob_ge_of_empMeasure` (**the core of `thm:ghost`**): an event `A ⊆ K^n` of probability at
  least `1 − α` under every finitely supported (empirical) law `Q^{⊗n}` has probability at least
  `1 − α` under every `P^{⊗n}`. Proof: average the hypothesis over the ghost empirical law of
  `N` i.i.d. draws from `P`; the resampled `n`-tuple has law `P^{⊗n}` except when the indices
  collide, of probability `≤ n²/N`; let `N → ∞`;
* `ghost_atomless` (**`thm:ghost`, atomless classes**): if no reference in `𝒩` has an atom, a radius
  `r̂` valid at every finitely supported population is `⊤` with probability at least `1 − α` at
  every population `P` (`a_𝒩 = ∞`).

Not covered here: the finite-`a_𝒩` clause `Pr_P[r̂ ≥ OT_ε(P̂, P) + ε a_𝒩] ≥ 1 − α`, whose event
moves with the population (the paper couples `(X', Π_N)` with `(X, Π'_N)` by exchangeability and
uses continuity of `OT_ε(P̂, ·)`).
-/

noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal

namespace StatFormal.Foundations.Tax

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual
  StatFormal.RobustEquality.SemidualStrong StatFormal.RobustEquality.Coverage

variable {K : Type} [MeasurableSpace K]

theorem isProb_empMeasure' {N : ℕ} (hN : 0 < N) (y : Fin N → K) :
    IsProbabilityMeasure (empMeasure y) := by
  constructor
  simp only [empMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  have : (N : ℝ) * (1 / N) = 1 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp
  rw [this, ENNReal.ofReal_one]

/-- **Sampling with replacement**: `(P̂_y)^{⊗n} = Σ_J N^{−n} δ_{y ∘ J}`. -/
theorem pi_empMeasure {N n : ℕ} (hN : 0 < N) (y : Fin N → K) :
    Measure.pi (fun _ : Fin n => empMeasure y) =
      ∑ J : Fin n → Fin N,
        ENNReal.ofReal ((1 / (N : ℝ)) ^ n) • Measure.dirac (fun k => y (J k)) := by
  have := isProb_empMeasure' hN y
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    empMeasure]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [Measure.dirac_apply' _ hbox]
  simp only [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ k, y (J k) ∈ s k
  · rw [Set.indicator_of_mem (by simpa [Set.mem_univ_pi] using h)]
    rw [Finset.prod_eq_one fun k _ => Set.indicator_of_mem (h k) _]
    rfl
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_univ_pi] using h)]
    push Not at h
    obtain ⟨k, hk⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm

theorem measureReal_pi_empMeasure {N n : ℕ} (hN : 0 < N) (y : Fin N → K) {A : Set (Fin n → K)}
    (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin n => empMeasure y).real A =
      ∑ J : Fin n → Fin N, (1 / (N : ℝ)) ^ n * A.indicator 1 (fun k => y (J k)) := by
  rw [measureReal_def, pi_empMeasure hN y]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun J _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Measure.dirac_apply' _ hA]
  congr 1
  by_cases h : (fun k => y (J k)) ∈ A
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- For an injective `J`, the coordinates `Y ∘ J` of `Y ~ P^{⊗N}` are i.i.d. `P`. -/
theorem map_comp_injective (P : Measure K) [IsProbabilityMeasure P] {n N : ℕ}
    {J : Fin n → Fin N} (hJ : Function.Injective J) :
    (Measure.pi fun _ : Fin N => P).map (fun Y k => Y (J k)) = Measure.pi fun _ : Fin n => P := by
  have hm : Measurable fun (Y : Fin N → K) (k : Fin n) => Y (J k) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply (J k)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : Fin N → Set K := fun j => ⋂ (k : Fin n) (_ : J k = j), s k with ht
  have hset : (fun (Y : Fin N → K) (k : Fin n) => Y (J k)) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_univ_pi, ht, Set.mem_iInter]
    constructor
    · intro h j k hk; rw [← hk]; exact h k
    · intro h k; exact h (J k) k rfl
  rw [hset, Measure.pi_pi]
  have htJ : ∀ k, t (J k) = s k := fun k => by
    simp only [ht]
    have : ∀ k', (J k' = J k) = (k' = k) := fun k' => propext hJ.eq_iff
    simp_rw [this]
    exact Set.iInter_iInter_eq_left
  have hrest : ∀ j ∉ Finset.univ.image J, P (t j) = 1 := fun j hj => by
    have : t j = Set.univ := Set.eq_univ_of_forall fun x => Set.mem_iInter₂.2 fun k hk =>
      absurd (Finset.mem_image.2 ⟨k, Finset.mem_univ k, hk⟩) hj
    rw [this, measure_univ]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image J)) fun j _ hj => hrest j hj,
    Finset.prod_image fun k _ k' _ h => hJ h]
  exact Finset.prod_congr rfl fun k _ => by rw [htJ]

/-- For `k ≠ l`, exactly `N^n / N` maps `[n] → [N]` identify `k` and `l`. -/
theorem card_eq_mul {n N : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    (Finset.univ.filter fun J : Fin n → Fin N => J l = J k).card * N = N ^ n := by
  have e : {J : Fin n → Fin N // J l = J k} × Fin N ≃ (Fin n → Fin N) :=
    { toFun := fun p => Function.update p.1.1 l p.2
      invFun := fun J => (⟨Function.update J l (J k), by simp [Function.update_of_ne hkl]⟩, J l)
      left_inv := fun ⟨⟨J, hJ⟩, v⟩ => by
        simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, Subtype.mk.injEq,
          and_true]
        rw [Function.update_of_ne hkl, ← hJ, Function.update_eq_self]
      right_inv := fun J => by
        simp only [Function.update_idem, Function.update_eq_self] }
  have := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_subtype] at this
  exact this

/-- **Birthday bound**: at most `n² N^n / N` maps `[n] → [N]` are not injective. -/
theorem card_not_injective_le {n N : ℕ} (hN : 0 < N) :
    ((Finset.univ.filter fun J : Fin n → Fin N => ¬ Function.Injective J).card : ℝ) ≤
      (n : ℝ) ^ 2 * N ^ n / N := by
  classical
  have hsub : (Finset.univ.filter fun J : Fin n → Fin N => ¬ Function.Injective J) ⊆
      ((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≠ p.2).biUnion
        fun p => Finset.univ.filter fun J : Fin n → Fin N => J p.2 = J p.1 := by
    intro J hJ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Injective, not_forall] at hJ
    obtain ⟨k, l, hkl, hne⟩ := hJ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(k, l), hne, hkl.symm⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2),
      ((Finset.univ.filter fun J : Fin n → Fin N => J p.2 = J p.1).card : ℝ) = N ^ n / N := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h := card_eq_mul (N := N) hp
    rw [eq_div_iff hNR.ne']
    exact_mod_cast h
  calc ((Finset.univ.filter fun J : Fin n → Fin N => ¬ Function.Injective J).card : ℝ)
      ≤ (((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≠ p.2).biUnion
        fun p => Finset.univ.filter fun J : Fin n → Fin N => J p.2 = J p.1).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2),
        ((Finset.univ.filter fun J : Fin n → Fin N => J p.2 = J p.1).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card *
        ((N : ℝ) ^ n / N) := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 * (N ^ n / N) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card ≤
            n ^ 2 := by
          calc _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
            _ = n ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
        exact_mod_cast this
    _ = _ := by ring

/-- **Core of `thm:ghost`**: an event of probability at least `1 − α` under `Q^{⊗n}` for every
empirical (hence finitely supported) law `Q` has probability at least `1 − α` under `P^{⊗n}` for
every probability `P`. -/
theorem prob_ge_of_empMeasure {n : ℕ} {A : Set (Fin n → K)} (hA : MeasurableSet A) {α : ℝ}
    (h : ∀ (N : ℕ) (y : Fin N → K), 0 < N →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => empMeasure y) A)
    (P : Measure K) [IsProbabilityMeasure P] :
    ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) A := by
  set Pn := Measure.pi fun _ : Fin n => P with hPn
  -- the real inequality for each ghost size `N`
  have key : ∀ N : ℕ, 0 < N → 1 - α ≤ Pn.real A + (n : ℝ) ^ 2 / N := by
    intro N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set PN := Measure.pi fun _ : Fin N => P with hPN
    set c : ℝ := (1 / (N : ℝ)) ^ n with hc
    have hc0 : 0 < c := by positivity
    have hcN : c * (N : ℝ) ^ n = 1 := by rw [hc, ← mul_pow]; field_simp; simp
    have hmJ : ∀ J : Fin n → Fin N, Measurable fun (Y : Fin N → K) (k : Fin n) => Y (J k) :=
      fun J => measurable_pi_iff.mpr fun k => measurable_pi_apply (J k)
    have hpre : ∀ J : Fin n → Fin N, MeasurableSet ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A) :=
      fun J => hmJ J hA
    -- pointwise: `1 − α ≤ (P̂_Y)^n (A) = c Σ_J 1_A(Y ∘ J)`
    have hpt : ∀ Y : Fin N → K, 1 - α ≤
        ∑ J : Fin n → Fin N, c * ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A).indicator 1 Y := by
      intro Y
      have := isProb_empMeasure' hN Y
      have h1 := h N Y hN
      rw [← ofReal_measureReal (measure_ne_top _ _)] at h1
      rcases le_or_gt (1 - α) 0 with hneg | hpos
      · exact hneg.trans (Finset.sum_nonneg fun J _ => mul_nonneg hc0.le
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      have h2 := (ENNReal.ofReal_le_ofReal_iff measureReal_nonneg).1 h1
      rw [measureReal_pi_empMeasure hN Y hA] at h2
      refine h2.trans_eq (Finset.sum_congr rfl fun J _ => ?_)
      rfl
    -- integrate over the ghost sample
    have hint : 1 - α ≤
        ∑ J : Fin n → Fin N, c * PN.real ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A) := by
      have hi : ∀ J : Fin n → Fin N, Integrable
          (fun Y => c * ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A).indicator 1 Y) PN :=
        fun J => ((integrable_const (1 : ℝ)).indicator (hpre J)).const_mul c
      calc 1 - α = ∫ _Y, (1 - α) ∂PN := by simp
        _ ≤ ∫ Y, ∑ J : Fin n → Fin N,
            c * ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A).indicator 1 Y ∂PN :=
          integral_mono (integrable_const _) (integrable_finsetSum _ fun J _ => hi J) hpt
        _ = _ := by
          rw [integral_finsetSum _ fun J _ => hi J]
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [integral_const_mul, integral_indicator_one (hpre J)]
    -- injective indices give `P^n(A)`, the others at most `1`
    have hterm : ∀ J : Fin n → Fin N,
        PN.real ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A) ≤
          Pn.real A + if Function.Injective J then 0 else 1 := by
      intro J
      split_ifs with hJ
      · rw [add_zero, measureReal_def, ← Measure.map_apply (hmJ J) hA,
          map_comp_injective P hJ]
        rfl
      · have h1 : PN.real ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A) ≤ 1 :=
          (measureReal_mono (subset_univ _)).trans_eq probReal_univ
        linarith [measureReal_nonneg (μ := Pn) (s := A)]
    have hsum : ∑ J : Fin n → Fin N, c * PN.real ((fun (Y : Fin N → K) k => Y (J k)) ⁻¹' A) ≤
        c * ((N : ℝ) ^ n * Pn.real A +
          ((Finset.univ.filter fun J : Fin n → Fin N => ¬ Function.Injective J).card : ℝ)) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      calc _ ≤ ∑ J : Fin n → Fin N, (Pn.real A + if Function.Injective J then 0 else 1) :=
            Finset.sum_le_sum fun J _ => hterm J
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          · push_cast; ring
          · rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
              mul_one]
    have hbd := card_not_injective_le (n := n) hN
    have : c * ((Finset.univ.filter fun J : Fin n → Fin N => ¬ Function.Injective J).card : ℝ) ≤
        (n : ℝ) ^ 2 / N := by
      calc _ ≤ c * ((n : ℝ) ^ 2 * N ^ n / N) := mul_le_mul_of_nonneg_left hbd hc0.le
        _ = (n : ℝ) ^ 2 / N * (c * N ^ n) := by ring
        _ = _ := by rw [hcN, mul_one]
    have e : c * ((N : ℝ) ^ n * Pn.real A) = Pn.real A := by
      rw [← mul_assoc, hcN, one_mul]
    nlinarith [hint, hsum, this, e]
  -- let `N → ∞`
  have hreal : 1 - α ≤ Pn.real A := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) ^ 2 / δ)
    have hN0 : 0 < N := by
      have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
      exact_mod_cast this
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
    have h1 := key N hN0
    have h2 : (n : ℝ) ^ 2 / N < δ := by
      rw [div_lt_iff₀ hNR]
      rw [div_lt_iff₀ hδ] at hN
      linarith
    linarith
  rw [← ofReal_measureReal (measure_ne_top Pn A)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The labelled centre `P̂_x = n⁻¹ Σ_i δ_{x_i}` satisfies the standing hypotheses. -/
theorem setting_centre {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) {cost : K → K → ℝ}
    (hcm : ∀ x0, Measurable (cost x0)) {B : ℝ} (hcb : ∀ x0 y, |cost x0 y| ≤ B)
    (x : Fin n → K) : Setting ε (fun _ : Fin n => (1 : ℝ) / n) (fun i => cost (x i)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨hε, fun _ => by positivity, ?_, fun i => hcm _, B, fun i y => hcb _ _⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **`thm:ghost`, atomless classes**: if no reference in `𝒩` has an atom, a radius valid at
every finitely supported population is `⊤` with probability at least `1 − α` at every
population. -/
theorem ghost_atomless [MeasurableSingletonClass K] {n : ℕ} (hn : 0 < n) {ε α : ℝ}
    (hε : 0 < ε) {cost : K → K → ℝ} (hcm : ∀ x0, Measurable (cost x0))
    (hcb : ∃ B, ∀ x0 y, |cost x0 y| ≤ B) (𝒩 : Set (Measure K))
    (hN : ∀ ν ∈ 𝒩, IsFiniteMeasure ν) (hatom : ∀ ν ∈ 𝒩, ∀ y, ν {y} = 0)
    (r : (Fin n → K) → EReal) (hr : Measurable r)
    (hvalid : ∀ Q : Measure K, IsProbabilityMeasure Q → (∃ s : Finset K, Q (↑s)ᶜ = 0) →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN 𝒩 ε (fun _ : Fin n => (1 : ℝ) / n) (fun i => cost (x i)) (r x)})
    (P : Measure K) [IsProbabilityMeasure P] :
    ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) {x | r x = ⊤} := by
  obtain ⟨B, hB⟩ := hcb
  have hA : MeasurableSet {x : Fin n → K | r x = ⊤} := hr (measurableSet_singleton ⊤)
  refine prob_ge_of_empMeasure hA (fun N y hN0 => ?_) P
  have hQ := isProb_empMeasure' hN0 y
  -- `empMeasure y` is finitely supported
  have hfin : ∃ s : Finset K, (empMeasure y) (↑s)ᶜ = 0 := by
    classical
    refine ⟨Finset.univ.image y, ?_⟩
    simp only [empMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Measure.dirac_apply' _ (Finset.measurableSet _).compl,
      Set.indicator_of_notMem (by simp), mul_zero]
  refine (hvalid _ hQ hfin).trans (measure_mono fun x hx => ?_)
  -- on the validity event, the tax is infinite, hence so is the radius
  have hsub := ballN_subset (setting_centre hn hε hcm hB x) hN hx
  have htax : tax 𝒩 (empMeasure y) = ⊤ := by
    refine le_antisymm le_top (le_iInf₂ fun ν hν => ?_)
    refine (klRef_eq_top_of_atom (x := y ⟨0, hN0⟩) ?_ (hatom ν hν _)).ge
    simp only [empMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    intro h0
    have h1 := (Finset.sum_eq_zero_iff.1 h0) ⟨0, hN0⟩ (Finset.mem_univ _)
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one, ENNReal.ofReal_eq_zero] at h1
    have : (0 : ℝ) < 1 / N := by
      have : (0 : ℝ) < N := by exact_mod_cast hN0
      positivity
    linarith
  rw [htax, EReal.coe_mul_top_of_pos hε,
    EReal.add_top_of_ne_bot (OTdisc_ne_bot (setting_centre hn hε hcm hB x) _)] at hsub
  exact top_le_iff.1 hsub

end StatFormal.Foundations.Tax
