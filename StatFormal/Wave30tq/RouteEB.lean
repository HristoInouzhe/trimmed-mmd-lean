import StatFormal.Wave30tq.RouteBetting
import StatFormal.Lib.Bernstein.TwoSample

/-!
# Wave 30tq route: Corollary 1 (the closed-form empirical-Bernstein certificate) — untrusted

`eb_level` (fold one fixed): `{L̂B > Δ} ⊆ E₁ᶜ ∪ E₂ᶜ ∪ E₃ᶜ`, where
* `E₁ᶜ = {(Ḡ − H̄) − Δ ≥ √(2vL₁) + bL₁/3}` has probability `≤ e^{−L₁} = δ₁` (library `two_sample_bernstein`,
  the upper tail of `(Ḡ − H̄) − Δ`, i.e. of the summands `(G_i − EG)/n ≤ 1/n` and `(EH − H_j)/m ≤ 1/m`);
* `E₂ᶜ = {σ_G ≥ √V_G + √(2 log(1/δ₂)/(n−1))}`, `E₃ᶜ` likewise, each of probability `≤ δ₂` (library `sqrt_popVar_le`,
  Maurer–Pontil 2009 Thm 10; `V_n` is the unbiased sample variance by `sampleVar_eq_sum_sq`);
* off the three events `σ_G ≤ σ̄_G` (with Popoviciu `σ_G ≤ 1/2`), so `v ≤ v̄` and `L̂B ≤ Δ`.
Random fold one: Fubini (`prod_le_of_slices`) and `Δ ≤ TV`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tq

open StatFormal.Bernstein

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

omit [MeasurableSpace 𝒳] in
lemma uVar_eq_sampleVar {n : ℕ} (hn : 2 ≤ n) (g : 𝒳 → ℝ) (x : Fin n → 𝒳) :
    uVar (fun i => g (x i)) = sampleVar g x := by
  rw [sampleVar_eq_sum_sq hn]; rfl

omit [MeasurableSpace 𝒳] in
lemma sMean_eq_sampleMean {n : ℕ} (g : 𝒳 → ℝ) (x : Fin n → 𝒳) :
    sMean (fun i => g (x i)) = sampleMean g x := rfl

lemma measure_fst_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure ν] [SigmaFinite μ] (A : Set α) :
    (μ.prod ν) (Prod.fst ⁻¹' A) = μ A := by
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

lemma measure_snd_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [SigmaFinite ν] (A : Set β) :
    (μ.prod ν) (Prod.snd ⁻¹' A) = ν A := by
  rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]

/-- **Corollary 1, one fold**: `P(L̂B > Δ) ≤ δ₁ + 2δ₂`. -/
theorem eb_level (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {g : 𝒳 → ℝ}
    (hg : Measurable g) (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
      {ω | (∫ x, g x ∂P) - (∫ y, g y ∂Q) < ebLB δ₁ δ₂ (fun i => g (ω.1 i)) (fun j => g (ω.2 j))}
        ≤ ENNReal.ofReal (δ₁ + 2 * δ₂) := by
  set ν := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hν
  set S := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
    (∫ x, g x ∂P) - (∫ y, g y ∂Q) < ebLB δ₁ δ₂ (fun i => g (ω.1 i)) (fun j => g (ω.2 j))} with hSdef
  by_cases hle : δ₁ ≤ 1 ∧ δ₂ ≤ 1
  swap
  · -- trivial case: the right side is at least `1`
    refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases not_and_or.1 hle with h | h <;> push Not at h <;> linarith
  obtain ⟨h1, h2⟩ := hle
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set L₁ := Real.log (1 / δ₁) with hL₁
  have hL₁0 : 0 ≤ L₁ := Real.log_nonneg (by rw [le_div_iff₀ hδ₁]; linarith)
  have hexp : Real.exp (-L₁) = δ₁ := by
    rw [hL₁, Real.log_div one_ne_zero hδ₁.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hδ₁]
  set rG := √(2 * Real.log (1 / δ₂) / ((n : ℝ) - 1)) with hrG
  set rH := √(2 * Real.log (1 / δ₂) / ((m : ℝ) - 1)) with hrH
  set E₁ := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
    √(2 * (popVar P g / n + popVar Q g / m) * L₁) + max (1 / (n : ℝ)) (1 / (m : ℝ)) * L₁ / 3 ≤
      (sampleMean g ω.1 - sampleMean g ω.2) - (popMean P g - popMean Q g)} with hE₁
  set A₂ := {x : Fin n → 𝒳 | √(sampleVar g x) + √(2 * Real.log (1 / δ₂) / (n - 1)) ≤ √(popVar P g)}
    with hA₂
  set A₃ := {y : Fin m → 𝒳 | √(sampleVar g y) + √(2 * Real.log (1 / δ₂) / (m - 1)) ≤ √(popVar Q g)}
    with hA₃
  have hE₁m : ν E₁ ≤ ENNReal.ofReal δ₁ := by
    have h := two_sample_bernstein P Q hg hg01 (by omega : 0 < n) (by omega : 0 < m) hL₁0
    rw [hexp] at h
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  have hA₂m : ν (Prod.fst ⁻¹' A₂) ≤ ENNReal.ofReal δ₂ := by
    rw [hν, measure_fst_preimage]
    have h := sqrt_popVar_le P hg hg01 hn hδ₂ h2
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  have hA₃m : ν (Prod.snd ⁻¹' A₃) ≤ ENNReal.ofReal δ₂ := by
    rw [hν, measure_snd_preimage]
    have h := sqrt_popVar_le Q hg hg01 hm hδ₂ h2
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  -- the deterministic inclusion
  have hsub : S ⊆ E₁ ∪ Prod.fst ⁻¹' A₂ ∪ Prod.snd ⁻¹' A₃ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hcon
    simp only [hA₂, hA₃, Set.mem_preimage, mem_ofPred_eq, not_le] at hn2 hn3
    simp only [hE₁, mem_ofPred_eq, not_le] at hn1
    simp only [hSdef, mem_ofPred_eq] at hω
    -- `σ ≤ σ̄`
    have hσG0 : 0 ≤ √(popVar P g) := Real.sqrt_nonneg _
    have hσH0 : 0 ≤ √(popVar Q g) := Real.sqrt_nonneg _
    have hσGh : √(popVar P g) ≤ 1 / 2 := by
      rw [show (1 : ℝ) / 2 = √(1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (popVar_le_quarter P hg hg01)
    have hσHh : √(popVar Q g) ≤ 1 / 2 := by
      rw [show (1 : ℝ) / 2 = √(1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (popVar_le_quarter Q hg hg01)
    have hbarG : √(popVar P g) ≤ sigBar n δ₂ (uVar fun i => g (ω.1 i)) := by
      unfold sigBar
      rw [uVar_eq_sampleVar hn]
      exact le_min hσGh hn2.le
    have hbarH : √(popVar Q g) ≤ sigBar m δ₂ (uVar fun j => g (ω.2 j)) := by
      unfold sigBar
      rw [uVar_eq_sampleVar hm]
      exact le_min hσHh hn3.le
    have hvG : popVar P g ≤ sigBar n δ₂ (uVar fun i => g (ω.1 i)) ^ 2 := by
      rw [← Real.sq_sqrt (popVar_nonneg P g)]
      exact pow_le_pow_left₀ hσG0 hbarG 2
    have hvH : popVar Q g ≤ sigBar m δ₂ (uVar fun j => g (ω.2 j)) ^ 2 := by
      rw [← Real.sq_sqrt (popVar_nonneg Q g)]
      exact pow_le_pow_left₀ hσH0 hbarH 2
    have hnpos : (0 : ℝ) < n := by linarith
    have hmpos : (0 : ℝ) < m := by linarith
    have hv : popVar P g / n + popVar Q g / m ≤
        sigBar n δ₂ (uVar fun i => g (ω.1 i)) ^ 2 / n + sigBar m δ₂ (uVar fun j => g (ω.2 j)) ^ 2 / m :=
      add_le_add (div_le_div_of_nonneg_right hvG hnpos.le) (div_le_div_of_nonneg_right hvH hmpos.le)
    have hsq : √(2 * (popVar P g / n + popVar Q g / m) * L₁) ≤
        √(2 * L₁ * (sigBar n δ₂ (uVar fun i => g (ω.1 i)) ^ 2 / n +
          sigBar m δ₂ (uVar fun j => g (ω.2 j)) ^ 2 / m)) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [mul_le_mul_of_nonneg_left hv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL₁0)]
    unfold ebLB at hω
    rw [sMean_eq_sampleMean, sMean_eq_sampleMean] at hω
    unfold popMean at hn1
    linarith
  calc ν S ≤ ν (E₁ ∪ Prod.fst ⁻¹' A₂ ∪ Prod.snd ⁻¹' A₃) := measure_mono hsub
    _ ≤ ν E₁ + ν (Prod.fst ⁻¹' A₂) + ν (Prod.snd ⁻¹' A₃) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _) |>.trans_eq (by ring)
    _ ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₂ + ENNReal.ofReal δ₂ := by gcongr
    _ = ENNReal.ofReal (δ₁ + 2 * δ₂) := by
        rw [← ENNReal.ofReal_add hδ₁.le hδ₂.le, ← ENNReal.ofReal_add (by positivity) hδ₂.le]
        congr 1; ring

theorem cor1_route : Claims.cor1 := by
  intro 𝒳 _ P Q _ _ n m g δ₁ δ₂ hn hm hδ₁ hδ₂ hg hg01
  exact eb_level P Q hg hg01 hn hm hδ₁ hδ₂

/-- `L̂B` is a measurable function of the whole sample when the ramp is jointly measurable in `D_1`. -/
lemma measurable_ebLB {Ω₁ : Type*} [MeasurableSpace Ω₁] {g : Ω₁ → 𝒳 → ℝ}
    (hg : Measurable fun p : Ω₁ × 𝒳 => g p.1 p.2) {n m : ℕ} (δ₁ δ₂ : ℝ) :
    Measurable fun ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) =>
      ebLB δ₁ δ₂ (fun i => g ω.1 (ω.2.1 i)) (fun j => g ω.1 (ω.2.2 j)) := by
  have hG : ∀ i : Fin n, Measurable fun ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) => g ω.1 (ω.2.1 i) :=
    fun i => hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
  have hH : ∀ j : Fin m, Measurable fun ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) => g ω.1 (ω.2.2 j) :=
    fun j => hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
  have hmean : ∀ {k : ℕ} {u : Fin k → Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) → ℝ}, (∀ i, Measurable (u i)) →
      Measurable fun ω => sMean fun i => u i ω := fun hu => by
    unfold sMean; exact (Finset.measurable_sum _ fun i _ => hu i).div_const _
  have hvar : ∀ {k : ℕ} {u : Fin k → Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) → ℝ}, (∀ i, Measurable (u i)) →
      Measurable fun ω => uVar fun i => u i ω := fun hu => by
    unfold uVar
    exact (Finset.measurable_sum _ fun i _ => ((hu i).sub (hmean hu)).pow_const 2).div_const _
  have hbar : ∀ (k : ℕ) {u : Fin k → Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) → ℝ}, (∀ i, Measurable (u i)) →
      Measurable fun ω => sigBar k δ₂ (uVar fun i => u i ω) := fun k {u} hu => by
    unfold sigBar
    exact measurable_const.min ((hvar hu).sqrt.add measurable_const)
  unfold ebLB
  refine (((hmean hG).sub (hmean hH)).sub (Measurable.sqrt (measurable_const.mul
    ((((hbar n hG).pow_const 2).div_const _).add (((hbar m hH).pow_const 2).div_const _))))).sub
    measurable_const

theorem cor1_test_route : Claims.cor1_test := by
  intro 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m g α δ₁ δ₂ hn hm hδ₁ hδ₂ hg hg01 hTV
  have hS : MeasurableSet {ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      α < ebLB δ₁ δ₂ (fun i => g ω.1 (ω.2.1 i)) (fun j => g ω.1 (ω.2.2 j))} :=
    measurableSet_lt measurable_const (measurable_ebLB hg δ₁ δ₂)
  refine prod_le_of_slices μ₁ _ hS fun d => ?_
  have hgd := measurable_section hg d
  refine (measure_mono fun ω hω => ?_).trans (eb_level P Q hgd (hg01 d) hn hm hδ₁ hδ₂)
  simp only [Set.mem_preimage, mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt ((delta_le_tv P Q hgd (hg01 d)).trans hTV) hω

theorem cor1_lcb_route : Claims.cor1_lcb := by
  intro 𝒳 Ω₁ _ _ P Q _ _ μ₁ _ n m g δ₁ δ₂ hn hm hδ₁ hδ₂ hg hg01
  have hS : MeasurableSet {ω : Ω₁ × ((Fin n → 𝒳) × (Fin m → 𝒳)) |
      StatFormal.Distances.tvDist P Q < ebLB δ₁ δ₂ (fun i => g ω.1 (ω.2.1 i)) (fun j => g ω.1 (ω.2.2 j))} :=
    measurableSet_lt measurable_const (measurable_ebLB hg δ₁ δ₂)
  refine prod_le_of_slices μ₁ _ hS fun d => ?_
  have hgd := measurable_section hg d
  refine (measure_mono fun ω hω => ?_).trans (eb_level P Q hgd (hg01 d) hn hm hδ₁ hδ₂)
  simp only [Set.mem_preimage, mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (delta_le_tv P Q hgd (hg01 d)) hω

end StatFormal.Wave30tq
