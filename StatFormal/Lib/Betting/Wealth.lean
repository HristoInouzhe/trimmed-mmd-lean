import StatFormal.Lib.Betting.Ville
import Mathlib.Probability.Independence.Integration

/-!
# Testing by betting: the wealth of a predictable strategy is a nonnegative supermartingale

Library component (untrusted library code: no `Statements.lean` is involved).

## Setting

`N` rounds; at round `k` the bettor stakes the fraction `Λ_k` (measurable with respect to `𝒢_k`, the information
before round `k`) on the outcome `Y_k` (measurable with respect to `𝒢_{k+1}` and independent of `𝒢_k`, with
`E Y_k ≤ 0`). The wealth is `W_t = ∏_{k < t} (1 + Λ_k Y_k)` (`wealthP`, over `k : Fin N`, so `W_t = W_N` for
`t ≥ N`).

## Main results

* `betting_supermartingale`: if the factors are nonnegative and everything is bounded, `(W_t)` is a nonnegative
  supermartingale for `𝒢`;
* `betting_ville`: **Ville's inequality for the betting test**, `μ{∃ t ≤ N, W_t ≥ a} ≤ 1/a` (`W_0 = 1`);
* `iIndepFun_of_indep_past`: if each `Z_k` is independent of `σ(Z_i : i < k)`, the family `(Z_k)_{k < N}` is
  mutually independent.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatFormal.Betting

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The wealth `W_t = ∏_{k < t} (1 + Λ_k Y_k)` after `t` rounds (`k : Fin N`). -/
def wealthP {N : ℕ} (Λ Y : Fin N → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + Λ k ω * Y k ω)

lemma filter_lt_succ {N : ℕ} (t : ℕ) (ht : t < N) :
    Finset.univ.filter (fun k : Fin N => (k : ℕ) < t + 1) =
      insert ⟨t, ht⟩ (Finset.univ.filter (fun k : Fin N => (k : ℕ) < t)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

lemma filter_lt_of_le {N t : ℕ} (ht : N ≤ t) :
    Finset.univ.filter (fun k : Fin N => (k : ℕ) < t) = Finset.univ := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact lt_of_lt_of_le k.isLt ht

lemma wealthP_zero {N : ℕ} (Λ Y : Fin N → Ω → ℝ) (ω : Ω) : wealthP Λ Y 0 ω = 1 := by
  unfold wealthP
  rw [Finset.prod_eq_one]
  intro k hk
  simp at hk

lemma wealthP_succ {N : ℕ} (Λ Y : Fin N → Ω → ℝ) (t : ℕ) (ht : t < N) (ω : Ω) :
    wealthP Λ Y (t + 1) ω = wealthP Λ Y t ω * (1 + Λ ⟨t, ht⟩ ω * Y ⟨t, ht⟩ ω) := by
  unfold wealthP
  rw [filter_lt_succ t ht, Finset.prod_insert, mul_comm]
  simp

lemma wealthP_succ_of_le {N : ℕ} (Λ Y : Fin N → Ω → ℝ) {t : ℕ} (ht : N ≤ t) (ω : Ω) :
    wealthP Λ Y (t + 1) ω = wealthP Λ Y t ω := by
  unfold wealthP
  rw [filter_lt_of_le ht, filter_lt_of_le (le_trans ht (Nat.le_succ t))]

lemma wealthP_nonneg {N : ℕ} {Λ Y : Fin N → Ω → ℝ} (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω)
    (t : ℕ) (ω : Ω) : 0 ≤ wealthP Λ Y t ω :=
  Finset.prod_nonneg fun k _ => hfac k ω

lemma wealthP_le {N : ℕ} {Λ Y : Fin N → Ω → ℝ} {L B : ℝ}
    (hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ L) (hYb : ∀ k ω, |Y k ω| ≤ B)
    (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω) (t : ℕ) (ω : Ω) :
    wealthP Λ Y t ω ≤ ∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B) := by
  unfold wealthP
  refine Finset.prod_le_prod₀ (fun k _ => hfac k ω) fun k _ => ?_
  have h1 : Λ k ω * Y k ω ≤ |Λ k ω * Y k ω| := le_abs_self _
  rw [abs_mul, abs_of_nonneg (hΛb k ω).1] at h1
  have h2 : Λ k ω * |Y k ω| ≤ L * B :=
    mul_le_mul (hΛb k ω).2 (hYb k ω) (abs_nonneg _) ((hΛb k ω).1.trans (hΛb k ω).2)
  linarith

/-- The wealth after `t` rounds is `𝒢_t`-measurable. -/
lemma measurable_wealthP {N : ℕ} (𝒢 : Filtration ℕ m0) {Λ Y : Fin N → Ω → ℝ}
    (hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k)) (hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k))
    (t : ℕ) : Measurable[𝒢 t] (wealthP Λ Y t) := by
  unfold wealthP
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkt : (k : ℕ) < t := (Finset.mem_filter.1 hk).2
  have hΛt : Measurable[𝒢 t] (Λ k) := (hΛ k).mono (𝒢.mono hkt.le) le_rfl
  have hYt : Measurable[𝒢 t] (Y k) := (hY k).mono (𝒢.mono (Nat.succ_le_of_lt hkt)) le_rfl
  exact measurable_const.add (hΛt.mul hYt)

/-- **The wealth of a predictable betting strategy is a supermartingale.** -/
theorem betting_supermartingale [IsFiniteMeasure μ] {N : ℕ} (𝒢 : Filtration ℕ m0)
    (Λ Y : Fin N → Ω → ℝ)
    (hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k)) (hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k))
    (hind : ∀ k : Fin N, Indep (MeasurableSpace.comap (Y k) inferInstance) (𝒢 k) μ)
    {L B : ℝ} (hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ L) (hYb : ∀ k ω, |Y k ω| ≤ B)
    (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω) (hmean : ∀ k, ∫ ω, Y k ω ∂μ ≤ 0) :
    Supermartingale (wealthP Λ Y) 𝒢 μ := by
  have hmeas : ∀ t, Measurable[𝒢 t] (wealthP Λ Y t) := measurable_wealthP 𝒢 hY hΛ
  have hmeas0 : ∀ t, Measurable (wealthP Λ Y t) := fun t => (hmeas t).mono (𝒢.le t) le_rfl
  have hint : ∀ t, Integrable (wealthP Λ Y t) μ := fun t =>
    Integrable.of_mem_Icc 0 _ (hmeas0 t).aemeasurable
      (ae_of_all _ fun ω => ⟨wealthP_nonneg hfac t ω, wealthP_le hΛb hYb hfac t ω⟩)
  have hYm : ∀ k, Measurable (Y k) := fun k => (hY k).mono (𝒢.le _) le_rfl
  have hΛm : ∀ k, Measurable (Λ k) := fun k => (hΛ k).mono (𝒢.le _) le_rfl
  have hYi : ∀ k, Integrable (Y k) μ := fun k =>
    Integrable.of_mem_Icc (-B) B (hYm k).aemeasurable (ae_of_all _ fun ω => abs_le.1 (hYb k ω))
  refine supermartingale_of_setIntegral_succ_le
    (fun t => (hmeas t).stronglyMeasurable) hint fun t s hs => ?_
  rcases lt_or_ge t N with ht | ht
  · set k : Fin N := ⟨t, ht⟩ with hk
    have hs0 : MeasurableSet s := 𝒢.le t s hs
    have hsplit : ∀ ω, wealthP Λ Y (t + 1) ω =
        wealthP Λ Y t ω + (wealthP Λ Y t ω * Λ k ω) * Y k ω := fun ω => by
      rw [wealthP_succ Λ Y t ht ω]; ring
    simp_rw [hsplit]
    have hWΛ : Integrable (fun ω => wealthP Λ Y t ω * Λ k ω) μ :=
      Integrable.of_mem_Icc 0 ((∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B)) * L)
        ((hmeas0 t).mul (hΛm k)).aemeasurable (ae_of_all _ fun ω =>
          ⟨mul_nonneg (wealthP_nonneg hfac t ω) (hΛb k ω).1,
            mul_le_mul (wealthP_le hΛb hYb hfac t ω) (hΛb k ω).2 (hΛb k ω).1
              ((wealthP_nonneg hfac t ω).trans (wealthP_le hΛb hYb hfac t ω))⟩)
    have hprodint : Integrable (fun ω => wealthP Λ Y t ω * Λ k ω * Y k ω) μ := by
      refine Integrable.of_mem_Icc
        (-(((∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B)) * L) * B))
        (((∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B)) * L) * B)
        (((hmeas0 t).mul (hΛm k)).mul (hYm k)).aemeasurable (ae_of_all _ fun ω => ?_)
      have h0 : 0 ≤ wealthP Λ Y t ω * Λ k ω := mul_nonneg (wealthP_nonneg hfac t ω) (hΛb k ω).1
      have h1 : wealthP Λ Y t ω * Λ k ω ≤
          (∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B)) * L :=
        mul_le_mul (wealthP_le hΛb hYb hfac t ω) (hΛb k ω).2 (hΛb k ω).1
          ((wealthP_nonneg hfac t ω).trans (wealthP_le hΛb hYb hfac t ω))
      have h2 : |wealthP Λ Y t ω * Λ k ω * Y k ω| ≤
          (∏ _k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < t), (1 + L * B)) * L * B := by
        rw [abs_mul, abs_of_nonneg h0]
        exact mul_le_mul h1 (hYb k ω) (abs_nonneg _) (h0.trans h1)
      exact ⟨by linarith [neg_abs_le (wealthP Λ Y t ω * Λ k ω * Y k ω)],
        (le_abs_self _).trans h2⟩
    rw [integral_add (hint t).integrableOn hprodint.integrableOn]
    -- the bet term has nonpositive integral over `s`
    set V : Ω → ℝ := s.indicator fun ω => wealthP Λ Y t ω * Λ k ω with hV
    have hVm : Measurable[𝒢 t] V :=
      Measurable.indicator ((hmeas t).mul ((hΛ k).mono le_rfl le_rfl)) hs
    have hVind : IndepFun V (Y k) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hind k).symm hVm.comap_le
    have hVY : ∫ ω in s, wealthP Λ Y t ω * Λ k ω * Y k ω ∂μ = ∫ ω, (V * Y k) ω ∂μ := by
      rw [← integral_indicator hs0]
      congr 1
      funext ω
      simp only [hV, Pi.mul_apply]
      by_cases h : ω ∈ s <;> simp [h]
    have hVmul := hVind.integral_mul_eq_mul_integral
      ((hVm.mono (𝒢.le t) le_rfl).aestronglyMeasurable) (hYm k).aestronglyMeasurable
    have hV0 : 0 ≤ ∫ ω, V ω ∂μ := integral_nonneg fun ω => by
      simp only [hV]
      by_cases h : ω ∈ s
      · simp only [h, Set.indicator_of_mem]
        exact mul_nonneg (wealthP_nonneg hfac t ω) (hΛb k ω).1
      · simp [h]
    have hneg : ∫ ω in s, wealthP Λ Y t ω * Λ k ω * Y k ω ∂μ ≤ 0 := by
      rw [hVY, hVmul]
      exact mul_nonpos_of_nonneg_of_nonpos hV0 (hmean k)
    linarith
  · simp_rw [wealthP_succ_of_le Λ Y ht]
    exact le_rfl

/-- **Ville's inequality for the betting test**: `μ{∃ t ≤ N, W_t ≥ a} ≤ 1/a`. -/
theorem betting_ville [IsProbabilityMeasure μ] {N : ℕ} (𝒢 : Filtration ℕ m0)
    (Λ Y : Fin N → Ω → ℝ)
    (hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k)) (hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k))
    (hind : ∀ k : Fin N, Indep (MeasurableSpace.comap (Y k) inferInstance) (𝒢 k) μ)
    {L B : ℝ} (hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ L) (hYb : ∀ k ω, |Y k ω| ≤ B)
    (hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω) (hmean : ∀ k, ∫ ω, Y k ω ∂μ ≤ 0)
    {a : ℝ} (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ wealthP Λ Y t ω} ≤ ENNReal.ofReal (1 / a) := by
  have hK := betting_supermartingale 𝒢 Λ Y hY hΛ hind hΛb hYb hfac hmean
  have h := ville_finite_le hK (fun t ω => wealthP_nonneg hfac t ω) N ha
  simp_rw [wealthP_zero, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h

/-- **Sequential independence implies mutual independence**: if each `Z_k` is independent of
`σ(Z_i : i < k)`, then `(Z_k)_{k < N}` is mutually independent. -/
theorem iIndepFun_of_indep_past [IsProbabilityMeasure μ] {N : ℕ} {β : Type*} [mβ : MeasurableSpace β]
    (Z : Fin N → Ω → β) (hZ : ∀ k, Measurable (Z k))
    (hind : ∀ k : Fin N, Indep (MeasurableSpace.comap (Z k) mβ)
      (⨆ i ∈ {i : Fin N | i < k}, MeasurableSpace.comap (Z i) mβ) μ) :
    iIndepFun Z μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro sets _; simp
  | insert a S hlt ih =>
    intro sets hsets
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    rw [Finset.set_biInter_insert, Finset.prod_insert haS]
    have hA : MeasurableSet[MeasurableSpace.comap (Z a) mβ] (Z a ⁻¹' sets a) :=
      ⟨sets a, hsets a (Finset.mem_insert_self a S), rfl⟩
    have hBm : MeasurableSet[⨆ i ∈ {i : Fin N | i < a}, MeasurableSpace.comap (Z i) mβ]
        (⋂ i ∈ S, Z i ⁻¹' sets i) := by
      refine Finset.measurableSet_biInter S fun i hi => ?_
      have hle : MeasurableSpace.comap (Z i) mβ ≤
          ⨆ i ∈ {i : Fin N | i < a}, MeasurableSpace.comap (Z i) mβ :=
        le_iSup₂ (f := fun j (_ : j ∈ {i : Fin N | i < a}) => MeasurableSpace.comap (Z j) mβ) i
          (hlt i hi)
      exact hle _ ⟨sets i, hsets i (Finset.mem_insert_of_mem hi), rfl⟩
    rw [(Indep_iff _ _ μ).1 (hind a) _ _ hA hBm,
      ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi))]

end StatFormal.Betting
