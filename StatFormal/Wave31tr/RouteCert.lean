import StatFormal.Wave31tr.Statements
import StatFormal.Lib.FnCert.Level
import StatFormal.Lib.FnCert.Grid
import StatFormal.Lib.PaperRun.Fitting
import StatFormal.Wave31to.Proofs

/-!
# Wave 31tr, chunk M4: T46 (a)–(c), a bound certified for a fitted function (untrusted route)

The ramp of every batch and level is `f̂ = F(batch 0)` (`fnRamp`), `Δ = E_P f̂ − E_Q f̂` (`fnDrift`) is a function of batch 0.

* (a) `fncert_drift_err`: the certified `Wave31to.newapprox_err` at `f̂` (measurable as a section of the jointly measurable `F`).
* `first_level_cond`: given batch 0, the event "some level `α_j ≥ Δ` is reached by a down-closed run of rejections" lies in the
  rejection event of the first level `α_{j₁} ≥ Δ`, a fixed level once batch 0 is fixed, whose rejection probability is at most `δ` by
  the positive-fraction supermartingale for the fixed function `f̂` (`FnCert.level_fixed_cond`, no TV assumption: `Δ ≤ α_{j₁}`).
* (b), (c) conditional: `{max(Δ,0) < α̂}` (by `Wave31tj.alphaLo_gt_iff`) and `{H_{0,α̂} rejected ∧ Δ ≤ α̂}`
  (by `FnCert.forall_le_of_alphaLo_eq`) are inside that event.
* (b), (c) unconditional: both events are inside the measurable `T = ⋃_j {Δ ≤ α_j} ∩ ⋂_{i ≤ j} {H_{0,α_i} rejected}`; its law is the
  integral over an independent copy of batch 0 of the conditional ones (the certified `Wave31tj.map_wbz_two`, slices by
  `Wave30tq.prod_le_of_slices`), and the slice at `z₀` is the conditional event at `z₀`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteCert

open StatFormal.Wave30tz StatFormal.Wave30tv StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave31to

section Fn

variable {𝒳 : Type} [MeasurableSpace 𝒳] {n m N J : ℕ} {lx : Fin n → ℕ} {ly : Fin m → ℕ}

/-- `f̂ = F(u, v)` is measurable for every value `(u, v)` of batch 0. -/
theorem measurable_section {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (u : Fin (fitCard lx 1) → 𝒳) (v : Fin (fitCard ly 1) → 𝒳) : Measurable (F u v) :=
  hFm.comp (measurable_prodMk_left (x := (u, v)))

/-- `(ω, z) ↦ f̂(ω)(z)` is jointly measurable. -/
theorem measurable_fn {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2)) :
    Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => F (fitSample lx 1 p.1.1) (fitSample ly 1 p.1.2) p.2 :=
  hFm.comp ((((PaperRun.measurable_fitSample lx 1).comp measurable_fst.fst).prodMk
    ((PaperRun.measurable_fitSample ly 1).comp measurable_fst.snd)).prodMk measurable_snd)

/-- `Δ` is a measurable function of the sample. -/
theorem measurable_fnDrift (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2)) :
    Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => fnDrift P Q lx ly F ω.1 ω.2 :=
  (((measurable_fn hFm).stronglyMeasurable.integral_prod_right' (ν := P)).measurable).sub
    (((measurable_fn hFm).stronglyMeasurable.integral_prod_right' (ν := Q)).measurable)

/-- Batch 0 of `withBatchZero x₀ x` is that of `x₀`. -/
theorem fitSample_wbz {p : ℕ} (l : Fin p → ℕ) (x₀ x : Fin p → 𝒳) :
    fitSample l 1 (withBatchZero l x₀ x) = fitSample l 1 x₀ :=
  PaperRun.fitSample_congr l 1 fun i hi => StatFormal.Wave31tj.wbz_zero x₀ x i (by omega)

theorem fnDrift_wbz (P Q : Measure 𝒳) (F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ)
    (x₀ x : Fin n → 𝒳) (y₀ y : Fin m → 𝒳) :
    fnDrift P Q lx ly F (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) = fnDrift P Q lx ly F x₀ y₀ := by
  unfold fnDrift
  rw [fitSample_wbz, fitSample_wbz]

/-- The single-function ramp is an admissible fitting rule (a function of batch 0, which precedes every pair). -/
theorem isFitRule_fnRamp {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)}
    (hpair : IsBatchPairing lx ly bat A B) {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (hF01 : ∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) : IsFitRule lx ly bat (fnRamp lx ly F) := by
  intro k
  refine ⟨(measurable_fn hFm).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd), fun _ _ _ z => hF01 _ _ z,
    fun _ x x' y y' hx hy => ?_⟩
  have hb := hpair.2.2.1 k
  change F (fitSample lx 1 x) (fitSample ly 1 y) = F (fitSample lx 1 x') (fitSample ly 1 y')
  rw [PaperRun.fitSample_congr lx 1 fun i hi => hx i (by omega), PaperRun.fitSample_congr ly 1 fun j hj => hy j (by omega)]

/-- **The first level above `Δ`, given batch 0**: the probability that some level `α_j ≥ Δ` is reached by a down-closed run of
rejections is at most `δ`, for every value of batch 0. -/
theorem first_level_cond (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {bat : Fin N → ℕ}
    {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)} {α : Fin J → ℝ} {δ c : ℝ}
    {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    {lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hpair : IsBatchPairing lx ly bat A B) (hδ0 : 0 < δ) (hc1 : c ≤ 1) (hα0 : ∀ j, 0 ≤ α j)
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (hF01 : ∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) (hlam : ∀ j, IsFracRule lx ly bat (α j) c (lam j))
    (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳) :
    sampleLaw P Q n m {ω | ∃ j, fnDrift P Q lx ly F x₀ y₀ ≤ α j ∧ ∀ i ≤ j,
      rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ≤
        ENNReal.ofReal δ := by
  classical
  by_cases hex : ∃ j, fnDrift P Q lx ly F x₀ y₀ ≤ α j
  · set s := Finset.univ.filter (fun j : Fin J => fnDrift P Q lx ly F x₀ y₀ ≤ α j) with hs
    have hsne : s.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    set j₁ := s.min' hsne with hj₁
    have hj₁mem : fnDrift P Q lx ly F x₀ y₀ ≤ α j₁ := (Finset.mem_filter.1 (s.min'_mem hsne)).2
    have hsub : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ∃ j, fnDrift P Q lx ly F x₀ y₀ ≤ α j ∧ ∀ i ≤ j,
        rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ⊆
        {ω | rejects (lam j₁) (fun _ _ _ => F (fitSample lx 1 x₀) (fitSample ly 1 y₀)) bat A B (α j₁) δ
          (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} := by
      rintro ω ⟨j, hj, hall⟩
      have hle : j₁ ≤ j := s.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
      refine (FnCert.rejects_congr_ramp fun k => ?_).1 (hall j₁ hle)
      change F (fitSample lx 1 (withBatchZero lx x₀ ω.1)) (fitSample ly 1 (withBatchZero ly y₀ ω.2)) =
        F (fitSample lx 1 x₀) (fitSample ly 1 y₀)
      rw [fitSample_wbz, fitSample_wbz]
    exact (measure_mono hsub).trans (FnCert.level_fixed_cond P Q hpair (hα0 j₁) hδ0 hc1
      (measurable_section hFm _ _) (fun z => hF01 _ _ z) hj₁mem (hlam j₁) x₀ y₀)
  · push Not at hex
    have hemp : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ∃ j, fnDrift P Q lx ly F x₀ y₀ ≤ α j ∧ ∀ i ≤ j,
        rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨j, hj, -⟩
      exact absurd hj (not_le.2 (hex j))
    rw [hemp, measure_empty]
    exact zero_le

/-- The same event, unconditionally (integration over an independent copy of batch 0). -/
theorem first_level (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {bat : Fin N → ℕ}
    {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)} {α : Fin J → ℝ} {δ c : ℝ}
    {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    {lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hpair : IsBatchPairing lx ly bat A B) (hδ0 : 0 < δ) (hc1 : c ≤ 1) (hα0 : ∀ j, 0 ≤ α j)
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (hF01 : ∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) (hlam : ∀ j, IsFracRule lx ly bat (α j) c (lam j)) :
    MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ∃ j, fnDrift P Q lx ly F ω.1 ω.2 ≤ α j ∧ ∀ i ≤ j,
      rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ ω.1 ω.2} ∧
    sampleLaw P Q n m {ω | ∃ j, fnDrift P Q lx ly F ω.1 ω.2 ≤ α j ∧ ∀ i ≤ j,
      rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ ω.1 ω.2} ≤ ENNReal.ofReal δ := by
  set T := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ∃ j, fnDrift P Q lx ly F ω.1 ω.2 ≤ α j ∧ ∀ i ≤ j,
      rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ ω.1 ω.2} with hTdef
  have hR : ∀ i, MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
      rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ ω.1 ω.2} := fun i =>
    Upper.measurableSet_rejects (isFitRule_fnRamp hpair hFm hF01) (hlam i)
  have hT : MeasurableSet T := by
    have e : T = ⋃ j : Fin J, ({ω : (Fin n → 𝒳) × (Fin m → 𝒳) | fnDrift P Q lx ly F ω.1 ω.2 ≤ α j} ∩
        ⋂ i : Fin J, ⋂ (_ : i ≤ j), {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
          rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ ω.1 ω.2}) := by
      ext ω
      simp only [hTdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact MeasurableSet.iUnion fun j => (measurableSet_le (measurable_fnDrift P Q hFm) measurable_const).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hR i)
  refine ⟨hT, ?_⟩
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  change μ T ≤ _
  have hmap := StatFormal.Wave31tj.map_wbz_two P Q lx ly
  rw [hμ, ← hmap, Measure.map_apply (StatFormal.Wave31tj.measurable_wbz_pair lx ly) hT]
  refine prod_le_of_slices μ μ (StatFormal.Wave31tj.measurable_wbz_pair lx ly hT) fun z₀ => ?_
  refine le_of_eq_of_le ?_ (first_level_cond (A := A) (B := B) P Q hpair hδ0 hc1 hα0 hFm hF01 hlam z₀.1 z₀.2)
  unfold sampleLaw
  congr 1
  ext ω
  simp only [Set.mem_preimage, hTdef, Set.mem_ofPred_eq, fnDrift_wbz]

end Fn

/-! ### The claims -/

theorem fncert_drift_err_route : Claims.fncert_drift_err := by
  intro 𝒳 _ P Q _ _ n m lx ly F hFm hF01 x y
  have hf := measurable_section hFm (fitSample lx 1 x) (fitSample ly 1 y)
  have h := (StatFormal.Wave31to.newapprox_err 𝒳 P Q _ hf fun z => ⟨(hF01 _ _ z).1, (hF01 _ _ z).2⟩).1
  unfold fnDrift
  linarith

theorem fncert_upper_route : Claims.fncert_upper := by
  intro 𝒳 _ P Q _ _ n m N J lx ly bat A B α δ c F lam hpair hδ0 hδ1 hc0 hc1 hmono hα0 hFm hF01 hlam
  have hsub : ∀ (Δ : ℝ) (rej : Fin J → Prop), max Δ 0 < StatFormal.TrimmedMMD.Lower.alphaLo α rej →
      ∃ j, Δ ≤ α j ∧ ∀ i ≤ j, rej i := by
    intro Δ rej h
    obtain ⟨j, hall, hlt⟩ := (StatFormal.Wave31tj.alphaLo_gt_iff α rej (le_max_right Δ 0)).1 h
    exact ⟨j, ((le_max_left Δ 0).trans hlt.le), hall⟩
  refine ⟨fun x₀ y₀ => ?_, ?_⟩
  · refine (measure_mono fun ω hω => ?_).trans
      (first_level_cond (A := A) (B := B) P Q hpair hδ0 hc1 hα0 hFm hF01 hlam x₀ y₀)
    exact hsub _ _ hω
  · refine (measure_mono fun ω hω => ?_).trans
      (first_level (A := A) (B := B) P Q hpair hδ0 hc1 hα0 hFm hF01 hlam).2
    exact hsub _ _ hω

theorem fncert_rejected_upper_route : Claims.fncert_rejected_upper := by
  intro 𝒳 _ P Q _ _ n m N J lx ly bat A B α δ c F lam hpair hδ0 hδ1 hc0 hc1 hmono hα0 hFm hF01 hlam
  have hsub : ∀ (Δ : ℝ) (rej : Fin J → Prop),
      ((∃ j, StatFormal.TrimmedMMD.Lower.alphaLo α rej = α j ∧ rej j) ∧ Δ ≤ StatFormal.TrimmedMMD.Lower.alphaLo α rej) →
      ∃ j, Δ ≤ α j ∧ ∀ i ≤ j, rej i := by
    rintro Δ rej ⟨⟨j, heq, hrej⟩, hΔ⟩
    exact ⟨j, heq ▸ hΔ, FnCert.forall_le_of_alphaLo_eq hmono hα0 heq hrej⟩
  refine ⟨fun x₀ y₀ => ?_, ?_⟩
  · refine (measure_mono fun ω hω => ?_).trans
      (first_level_cond (A := A) (B := B) P Q hpair hδ0 hc1 hα0 hFm hF01 hlam x₀ y₀)
    exact hsub _ _ hω
  · refine (measure_mono fun ω hω => ?_).trans
      (first_level (A := A) (B := B) P Q hpair hδ0 hc1 hα0 hFm hF01 hlam).2
    exact hsub _ _ hω

end StatFormal.Wave31tr.RouteCert
