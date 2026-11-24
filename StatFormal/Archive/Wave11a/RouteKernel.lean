import StatFormal.Archive.Wave11a.Statements
import StatFormal.Lib.Tax.Tax
import StatFormal.Lib.Strong.Single
import StatFormal.Archive.RobustEquality.Gibbs
import StatFormal.Archive.RobustEquality.Tax.Proofs
import StatFormal.Archive.RobustEquality.SemidualStrong.Proofs
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Wave 11a route: robust equality JASA `lem:kernel`

Untrusted proof file.
* Floor: the Gibbs variational principle (frozen `lem_gibbs`) at each anchor with `g = −c(x_i,·)/ε` gives
  `E_Γ c_i + ε KL(Γ‖ν) ≥ −ε log ∫ e^{−c_i/ε} dν`, with equality only at the tilted law; averaging gives
  `G_ν(Γ) ≥ ρ_ν`, equality only at the Gibbs kernel; non-emptiness follows (`kernel_floor_ref`, `kernel_floor`),
  and for weakly compact classes `ν ↦ ρ_ν` is continuous, so the floor is attained (`kernel_floor_compact`).
* Coupling ↔ kernel: a coupling of `μ = n⁻¹Σδ_i` (labels) is `μ ⊗ₘ Γ` for the kernel
  `Γ_i = n · γ({i} × ·)`, and the conditional chain rule (Tau Ceti `klDiv_compProd_right`) gives
  `KL(μ ⊗ₘ Γ ‖ μ ⊗ ν) = n⁻¹ Σ KL(Γ_i‖ν)`; attainment comes from the frozen strong duality and `lem:tax`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace StatFormal.Wave11a

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Certificate StatFormal.RobustEquality.Strong

variable {K : Type} [MeasurableSpace K]

/-! ### One anchor -/

lemma klRef_ne_bot' (Γ ν : Measure K) : klRef Γ ν ≠ ⊥ := StatFormal.Foundations.Tax.klRef_ne_bot Γ ν

lemma anchor_term_ne_bot {ε : ℝ} (hε : 0 < ε) (I : ℝ) (Γ ν : Measure K) :
    ((I : ℝ) : EReal) + (ε : EReal) * klRef Γ ν ≠ ⊥ :=
  EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, StatFormal.Foundations.Tax.coe_mul_klRef_ne_bot hε Γ ν⟩

/-- Gibbs at one anchor: `E_Γ f + ε KL(Γ‖ν) ≥ −ε log ∫ e^{−f/ε} dν`, with equality only at the tilted law. -/
lemma anchor_ge (ν : Measure K) [IsFiniteMeasure ν] (hν : ν univ ≠ 0) {ε : ℝ} (hε : 0 < ε) {f : K → ℝ}
    (hf : Measurable f) {B : ℝ} (hfb : ∀ z, |f z| ≤ B) (Γ : Measure K) [IsProbabilityMeasure Γ] :
    ((-ε * Real.log (∫ z, Real.exp (-f z / ε) ∂ν) : ℝ) : EReal) ≤
        ((∫ z, f z ∂Γ : ℝ) : EReal) + (ε : EReal) * klRef Γ ν ∧
      (((∫ z, f z ∂Γ : ℝ) : EReal) + (ε : EReal) * klRef Γ ν =
          ((-ε * Real.log (∫ z, Real.exp (-f z / ε) ∂ν) : ℝ) : EReal) → Γ = ν.tilted (fun z => -f z / ε)) := by
  have hgm : Measurable fun z => -f z / ε := hf.neg.div_const ε
  have hgb : ∀ z, |-f z / ε| ≤ B / ε := fun z => by
    rw [abs_div, abs_neg, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (hfb z) hε.le
  obtain ⟨⟨-, hub⟩, huniq⟩ := StatFormal.RobustEquality.lem_gibbs K ν hν _ hgm ⟨B / ε, hgb⟩
  have hint : ∫ z, -f z / ε ∂Γ = -(∫ z, f z ∂Γ) / ε := by rw [integral_div, integral_neg]
  set L := Real.log (∫ z, Real.exp (-f z / ε) ∂ν)
  by_cases htop : klRef Γ ν = ⊤
  · refine ⟨by rw [htop, EReal.coe_mul_top_of_pos hε, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]; exact le_top, ?_⟩
    intro h
    rw [htop, EReal.coe_mul_top_of_pos hε, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at h
    exact absurd h.symm (EReal.coe_ne_top _)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, klRef Γ ν = k :=
    ⟨(klRef Γ ν).toReal, (EReal.coe_toReal htop (klRef_ne_bot' Γ ν)).symm⟩
  have hmem := hub ⟨Γ, inferInstance, rfl⟩
  rw [hk, hint, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hmem
  have hsum : ((∫ z, f z ∂Γ : ℝ) : EReal) + (ε : EReal) * klRef Γ ν = (((∫ z, f z ∂Γ) + ε * k : ℝ) : EReal) := by
    rw [hk]; norm_cast
  rw [hsum, EReal.coe_le_coe_iff]
  refine ⟨?_, fun h => ?_⟩
  · have := mul_le_mul_of_nonneg_left hmem hε.le
    rw [mul_sub, mul_div_cancel₀ _ hε.ne'] at this
    nlinarith
  · rw [EReal.coe_eq_coe_iff] at h
    refine huniq Γ inferInstance ?_
    rw [hk, hint, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    field_simp
    linarith

/-- The tilted law attains the anchor bound. -/
lemma anchor_tilted (ν : Measure K) [IsFiniteMeasure ν] (hν : ν univ ≠ 0) {ε : ℝ} (hε : 0 < ε) {f : K → ℝ}
    (hf : Measurable f) {B : ℝ} (hfb : ∀ z, |f z| ≤ B) :
    IsProbabilityMeasure (ν.tilted (fun z => -f z / ε)) ∧
      ((∫ z, f z ∂(ν.tilted (fun z => -f z / ε)) : ℝ) : EReal) +
          (ε : EReal) * klRef (ν.tilted (fun z => -f z / ε)) ν =
        ((-ε * Real.log (∫ z, Real.exp (-f z / ε) ∂ν) : ℝ) : EReal) := by
  haveI : NeZero ν := ⟨fun h => hν (by simp [h])⟩
  have hgm : Measurable fun z => -f z / ε := hf.neg.div_const ε
  have hgb : ∀ z, |-f z / ε| ≤ B / ε := fun z => by
    rw [abs_div, abs_neg, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (hfb z) hε.le
  obtain ⟨hprob, -, -, -⟩ := StatFormal.Foundations.Strong.tilted_facts ν hgm hgb
  refine ⟨hprob, ?_⟩
  rw [StatFormal.Foundations.Strong.klRef_tilted ν hgm hgb, integral_div, integral_neg]
  norm_cast
  field_simp
  ring

/-! ### Averaging -/

lemma ereal_sum_ne_bot {n : ℕ} (T : Fin n → EReal) (hT : ∀ i, T i ≠ ⊥) : ∑ i, T i ≠ ⊥ := by
  induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons]; exact EReal.add_ne_bot_iff.2 ⟨hT i, ih⟩

lemma ereal_sum_eq_top {n : ℕ} (T : Fin n → EReal) (hT : ∀ i, T i ≠ ⊥) (j : Fin n) (hj : T j = ⊤) :
    ∑ i, T i = ⊤ := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj]
  exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot' _ hT)
where
  ereal_sum_ne_bot' (s : Finset (Fin n)) (hT : ∀ i, T i ≠ ⊥) : ∑ i ∈ s, T i ≠ ⊥ := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => rw [Finset.sum_cons]; exact EReal.add_ne_bot_iff.2 ⟨hT i, ih⟩

/-- The floor equals the average of the anchor floors. -/
lemma floorRef_eq_avg {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν : Measure K) :
    floorRef x c ε ν = (n : ℝ)⁻¹ * ∑ i, (-ε * Real.log (∫ z, Real.exp (-c (x i) z / ε) ∂ν)) := by
  unfold floorRef
  rw [← Finset.mul_sum]
  ring

/-- `G_ν(Γ) ≥ ρ_ν`, with equality only at the Gibbs kernel. -/
lemma budget_ge {n : ℕ} (hn : 0 < n) (x : Fin n → K) (c : K → K → ℝ) {ε : ℝ} (hε : 0 < ε) (ν : Measure K)
    [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (hcm : ∀ y, Measurable (c y)) {B : ℝ} (hB : ∀ a b, |c a b| ≤ B)
    (Γ : Fin n → Measure K) (hΓ : ∀ i, IsProbabilityMeasure (Γ i)) :
    ((floorRef x c ε ν : ℝ) : EReal) ≤ budget x c ε ν Γ ∧
      (budget x c ε ν Γ = ((floorRef x c ε ν : ℝ) : EReal) → ∀ i, Γ i = ν.tilted (fun z => -c (x i) z / ε)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set T : Fin n → EReal := fun i => ((∫ z, c (x i) z ∂(Γ i) : ℝ) : EReal) + (ε : EReal) * klRef (Γ i) ν with hTdef
  set A : Fin n → ℝ := fun i => -ε * Real.log (∫ z, Real.exp (-c (x i) z / ε) ∂ν) with hAdef
  have hanc := fun i => @anchor_ge K _ ν _ hν ε hε (c (x i)) (hcm _) B (hB _) (Γ i) (hΓ i)
  have hTbot : ∀ i, T i ≠ ⊥ := fun i => anchor_term_ne_bot hε _ _ _
  have hbud : budget x c ε ν Γ = ((n : ℝ)⁻¹ : EReal) * ∑ i, T i := rfl
  have hfl : ((floorRef x c ε ν : ℝ) : EReal) = (((n : ℝ)⁻¹ * ∑ i, A i : ℝ) : EReal) := by
    rw [floorRef_eq_avg]
  have hninv : (0 : EReal) < ((n : ℝ) : EReal)⁻¹ := by
    rw [← EReal.coe_inv]; exact EReal.coe_pos.2 (inv_pos.2 hnR)
  by_cases htop : ∃ j, T j = ⊤
  · obtain ⟨j, hj⟩ := htop
    have hS : ∑ i, T i = ⊤ := ereal_sum_eq_top T hTbot j hj
    rw [hbud, hS, EReal.mul_top_of_pos hninv]
    exact ⟨le_top, fun h => absurd h (EReal.coe_ne_top _ ∘ Eq.symm)⟩
  push Not at htop
  have hreal : ∀ i, T i = ((T i).toReal : EReal) := fun i => (EReal.coe_toReal (htop i) (hTbot i)).symm
  have hS : ∑ i, T i = ((∑ i, (T i).toReal : ℝ) : EReal) := by
    rw [StatFormal.Foundations.SemiDiscrete.EReal.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => hreal i
  have hle : ∀ i, A i ≤ (T i).toReal := fun i => by
    have : ((A i : ℝ) : EReal) ≤ T i := (hanc i).1
    rw [hreal i] at this
    exact EReal.coe_le_coe_iff.1 this
  rw [hbud, hS, ← EReal.coe_inv, ← EReal.coe_mul, hfl]
  refine ⟨EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i)
    (inv_nonneg.2 hnR.le)), fun h => ?_⟩
  rw [EReal.coe_eq_coe_iff] at h
  have h' : ∑ i, A i = ∑ i, (T i).toReal := by
    have := congrArg (fun t => (n : ℝ) * t) h
    simp only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] at this
    exact this.symm
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 h'
  intro i
  refine (hanc i).2 ?_
  change T i = _
  rw [hreal i, ← heq i (Finset.mem_univ i)]

lemma isProb_avg {n : ℕ} (hn : 0 < n) (Γ : Fin n → Measure K) (hΓ : ∀ i, IsProbabilityMeasure (Γ i)) :
    IsProbabilityMeasure ((n : ℝ≥0∞)⁻¹ • ∑ i, Γ i) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- The Gibbs kernel and its budget. -/
lemma gibbs_kernel {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) {ε : ℝ} (hε : 0 < ε) (ν : Measure K)
    [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (hcm : ∀ y, Measurable (c y)) {B : ℝ} (hB : ∀ a b, |c a b| ≤ B) :
    (∀ i, IsProbabilityMeasure (ν.tilted (fun z => -c (x i) z / ε))) ∧
      budget x c ε ν (fun i => ν.tilted (fun z => -c (x i) z / ε)) = ((floorRef x c ε ν : ℝ) : EReal) := by
  have hanc := fun i => @anchor_tilted K _ ν _ hν ε hε (c (x i)) (hcm _) B (hB _)
  refine ⟨fun i => (hanc i).1, ?_⟩
  change ((n : ℝ)⁻¹ : EReal) * ∑ i, (((∫ z, c (x i) z ∂(ν.tilted (fun z => -c (x i) z / ε)) : ℝ) : EReal) +
    (ε : EReal) * klRef (ν.tilted (fun z => -c (x i) z / ε)) ν) = _
  simp only [fun i => (hanc i).2]
  rw [← StatFormal.Foundations.SemiDiscrete.EReal.coe_finsetSum, ← EReal.coe_inv, ← EReal.coe_mul,
    floorRef_eq_avg]

theorem kernel_floor_min : Claims.kernel_floor_min := by
  intro K _ n x c ε ν _ hn hε hcm ⟨B, hB⟩ hν
  obtain ⟨hprob, hval⟩ := gibbs_kernel x c hε ν hν hcm hB
  refine ⟨⟨⟨_, hprob, hval.symm⟩, ?_⟩, fun Γ hΓ h => (budget_ge hn x c hε ν hν hcm hB Γ hΓ).2 h⟩
  rintro v ⟨Γ, hΓ, rfl⟩
  exact (budget_ge hn x c hε ν hν hcm hB Γ hΓ).1

theorem kernel_floor_ref : Claims.kernel_floor_ref := by
  intro K _ n x c ε r ν _ hn hε hcm ⟨B, hB⟩ hν
  constructor
  · rintro ⟨Q, -, Γ, hΓ, -, hle⟩
    exact EReal.coe_le_coe_iff.1 ((budget_ge hn x c hε ν hν hcm hB Γ hΓ).1.trans hle)
  · intro hr
    obtain ⟨hprob, hval⟩ := gibbs_kernel x c hε ν hν hcm hB
    refine ⟨_, isProb_avg hn _ hprob, _, hprob, rfl, ?_⟩
    change budget x c ε ν _ ≤ _
    rw [hval]
    exact EReal.coe_le_coe_iff.2 hr

theorem kernel_floor : Claims.kernel_floor := by
  intro K _ n x c ε r 𝒩 hn hε hcm hB h𝒩
  have href : ∀ ν ∈ 𝒩, (∃ Q, StatFormal.Wave4b.InBall x c ε r {ν} Q) ↔ floorRef x c ε ν ≤ r := by
    intro ν hν
    obtain ⟨hfin, hν0, -⟩ := h𝒩 ν hν
    rw [← kernel_floor_ref K n x c ε r ν hn hε hcm hB hν0]
    constructor
    · rintro ⟨Q, hQ, ν', hν', hW⟩
      rw [Set.mem_singleton_iff] at hν'
      exact ⟨Q, hQ, hν' ▸ hW⟩
    · rintro ⟨Q, hQ, hW⟩
      exact ⟨Q, hQ, ν, rfl, hW⟩
  have hone : (∃ Q, StatFormal.Wave4b.InBall x c ε r 𝒩 Q) ↔ ∃ ν ∈ 𝒩, floorRef x c ε ν ≤ r := by
    constructor
    · rintro ⟨Q, hQ, ν, hν, hW⟩
      exact ⟨ν, hν, (href ν hν).1 ⟨Q, hQ, ν, rfl, hW⟩⟩
    · rintro ⟨ν, hν, hle⟩
      obtain ⟨Q, hQ, ν', hν', hW⟩ := (href ν hν).2 hle
      rw [Set.mem_singleton_iff] at hν'
      exact ⟨Q, hQ, ν, hν, hν' ▸ hW⟩
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨ν, hν, heq⟩ => ?_⟩
  · obtain ⟨ν, hν, hle⟩ := hone.1 h
    exact (iInf₂_le ν hν).trans (EReal.coe_le_coe_iff.2 hle)
  · refine hone.2 ?_
    by_contra hcon
    push Not at hcon
    exact absurd h (not_lt.2 (le_iInf₂ fun ν hν => (EReal.coe_le_coe_iff.2 (hcon ν hν).le)))
  · refine ⟨fun h => ?_, fun h => hone.2 ⟨ν, hν, ?_⟩⟩
    · obtain ⟨ν', hν', hle⟩ := hone.1 h
      exact (iInf₂_le ν' hν').trans (EReal.coe_le_coe_iff.2 hle)
    · rw [← heq] at h
      exact EReal.coe_le_coe_iff.1 h

theorem kernel_floor_compact : Claims.kernel_floor_compact := by
  intro K _ _ _ _ n x c ε r 𝒩 hn hε hc h𝒩c h𝒩
  have hcm : ∀ y, Measurable (c y) := fun y =>
    (hc.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  obtain ⟨B, hB'⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hB : ∀ a b, |c a b| ≤ B := fun a b => by
    have := hB' _ ⟨(a, b), rfl⟩
    rwa [Real.norm_eq_abs] at this
  set 𝒩' : Set (Measure K) := ((↑) : FiniteMeasure K → Measure K) '' 𝒩
  have href : StatFormal.Wave4b.RefClass 𝒩' := by
    rintro ν ⟨μ, hμ, rfl⟩
    exact ⟨inferInstance, (h𝒩 μ hμ).1, (h𝒩 μ hμ).2⟩
  have hfl := kernel_floor K n x c ε r 𝒩' hn hε hcm ⟨B, hB⟩ href
  rcases Set.eq_empty_or_nonempty 𝒩 with h0 | hne
  · have hE : 𝒩' = ∅ := by simp [𝒩', h0]
    have hbot : floorN x c ε 𝒩' = ⊤ := by simp [floorN, hE]
    rw [hbot]
    refine ⟨?_, fun h => absurd h (not_le.2 (EReal.coe_lt_top r))⟩
    rintro ⟨Q, -, ν, hν, -⟩
    rw [hE] at hν
    exact hν.elim
  -- `ν ↦ ρ_ν` is continuous on `𝒩`, so the floor is attained
  have hcont : ∀ i, Continuous fun μ : FiniteMeasure K => ∫ z, Real.exp (-c (x i) z / ε) ∂(μ : Measure K) := by
    intro i
    have hf : Continuous fun z => Real.exp (-c (x i) z / ε) :=
      ((hc.comp (Continuous.prodMk continuous_const continuous_id)).neg.div_const ε).rexp
    exact FiniteMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨_, hf⟩)
  have hpos : ∀ μ ∈ 𝒩, ∀ i, 0 < ∫ z, Real.exp (-c (x i) z / ε) ∂(μ : Measure K) := by
    intro μ hμ i
    haveI : NeZero (μ : Measure K) := ⟨fun h => (h𝒩 μ hμ).1 (by simp [h])⟩
    refine integral_exp_pos ?_
    refine Integrable.of_bound ((hcm _).neg.div_const ε).exp.aestronglyMeasurable (Real.exp (B / ε))
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ?_
    have := abs_le.1 (hB (x i) z)
    rw [div_le_div_iff_of_pos_right hε]
    linarith
  have hcontOn : ContinuousOn (fun μ : FiniteMeasure K => floorRef x c ε (μ : Measure K)) 𝒩 := by
    unfold floorRef
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
    refine continuousOn_finset_sum _ fun i _ => ?_
    exact ((hcont i).continuousOn).log fun μ hμ => (hpos μ hμ i).ne'
  obtain ⟨μs, hμs, hmin⟩ := h𝒩c.exists_isMinOn hne hcontOn
  have hatt : ∃ ν ∈ 𝒩', ((floorRef x c ε ν : ℝ) : EReal) = floorN x c ε 𝒩' := by
    refine ⟨μs, ⟨μs, hμs, rfl⟩, le_antisymm ?_ (iInf₂_le _ ⟨μs, hμs, rfl⟩)⟩
    refine le_iInf₂ fun ν hν => ?_
    obtain ⟨μ, hμ, rfl⟩ := hν
    exact EReal.coe_le_coe_iff.2 (hmin hμ)
  exact hfl.2.2 hatt

end StatFormal.Wave11a
