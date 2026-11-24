import StatFormal.Wave31tr.RouteCert
import StatFormal.Lib.FnCert.Bet
import StatFormal.Lib.PaperRun.Batches
import StatFormal.Wave30tz.Proofs

/-!
# Wave 31tr, chunk M4: T46 (d), the betting error of the fitted-function certificate (untrusted route)

Fractions of `eq:fractions` (`λ_max = 1/2`, a prior rule, floor `σ²_min ∈ (0,4]`, every pair bet on), `L = log(1/δ)`,
`C = FnCert.betC δ η σ²_min J` (depends on `δ, η, J, σ²_min` only).

* `level_power_cond`: given batch 0, at a level `α_j ∈ [0,1)` with excess `Δ − α_j ≥ C/√N` and `N ≥ 8L`, the certified
  `Wave30tz.bet_power_frac` (ramp frozen at `f̂`, fractions frozen at batch 0; `λ_N ≤ λ_k ≤ λ̄_N` by the certified `fractions_bounds`
  through `PaperRun.lamLo_le_fracFormula`, `fracFormula_le_lamHi`) bounds the non-rejection probability by `ε_N(C/√N) ≤ η/(J+1)`
  (`FnCert.epsN_le_of_C`).
* `betting_error_cond`: if `Δ − h − C/√N ≤ 0` the bound is trivial (`α̂ ≥ 0`). Otherwise `C/√N < 1` (as `Δ ≤ α⋆ ≤ 1`), so
  `N > C² ≥ 8L`; `a = Δ − C/√N ∈ [0, Δ]` has the grid floor `α_{j₀} ≥ a − h > 0` (mesh), every `i ≤ j₀` has excess `≥ C/√N`, and on
  the intersection `E` of their rejection events (a union bound over at most `J` levels at `η/(J+1)`), `α̂ ≥ α_{j₀} ≥ Δ − h − C/√N`.
* Unconditional: `{Δ − h − C/√N ≤ α̂}` is measurable, and its complement has probability `≤ η` by integrating the conditional bound
  over an independent copy of batch 0 (`Wave31tj.map_wbz_two`). The bound on `α⋆ − α̂` follows from (a), `Δ = α⋆ − err(f̂)`.
* Last conjunct: `N = min(n_[1], m_[1])` (the printed pairing at `nb = 1`), `n_[1] = n − c₁ ≥ n/2 − 1` (`PaperRun.batchCount_cutLabel`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave31tr.RouteCert

open StatFormal.Wave30tz StatFormal.Wave30tv StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave31to

section Bet

variable {𝒳 : Type} [MeasurableSpace 𝒳] {n m N J : ℕ} {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ}
  {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)}

/-- The fractions of `eq:fractions` (every pair bet on) are admissible at every level of a nonnegative grid, cap `1/2`. -/
theorem isFracRule_of_formula {α : Fin J → ℝ} (hα0 : ∀ j, 0 ≤ α j) {δ s2 w0 : ℝ}
    {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ} (hv0 : IsPriorRule lx ly v0)
    {lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hlam : ∀ (j : Fin J) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      lam j k x y z = fracFormula (1 / 2) (α j) (Real.log (1 / δ)) N s2 w0 (v0 j (bat k) x y) (fun _ => 1) z) (j : Fin J) :
    IsFracRule lx ly bat (α j) (1 / 2) (lam j) :=
  FnCert.isFracRule_fracFormula (by norm_num) (hα0 j) (s0 := v0 j) (fun b => (hv0 j b).1)
    (fun b x x' y y' hx hy => (hv0 j b).2.2 x x' y y' hx hy) (hlam j)

/-- **Power at one level, given batch 0**: excess `Δ − α_j ≥ C/√N`, `α_j ∈ [0,1)`, `N ≥ 8L`: the rejection event is measurable and
its complement has probability at most `ε_N(C/√N)`. -/
theorem level_power_cond (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {α : Fin J → ℝ}
    {δ s2 w0 C : ℝ} {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ}
    {lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hpair : IsBatchPairing lx ly bat A B) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (hF01 : ∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) (hw0 : 0 < w0) (hv0 : IsPriorRule lx ly v0)
    (hlam : ∀ (j : Fin J) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      lam j k x y z = fracFormula (1 / 2) (α j) (Real.log (1 / δ)) N s2 w0 (v0 j (bat k) x y) (fun _ => 1) z)
    (hN : 1 ≤ N) (hN8 : 8 * Real.log (1 / δ) ≤ N) (j : Fin J) (hα0 : 0 ≤ α j) (hα1 : α j < 1)
    (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳) (hexc : α j + C / √(N : ℝ) ≤ fnDrift P Q lx ly F x₀ y₀) :
    MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
        rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} ∧
      sampleLaw P Q n m {ω | ¬ rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ (withBatchZero lx x₀ ω.1)
        (withBatchZero ly y₀ ω.2)} ≤ ENNReal.ofReal (epsN s2 (α j) (Real.log (1 / δ)) N (C / √(N : ℝ))) := by
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set f₀ := F (fitSample lx 1 x₀) (fitSample ly 1 y₀) with hf₀
  have hf₀m : Measurable f₀ := measurable_section hFm _ _
  set lam' : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ :=
    fun k x y => lam j k (withBatchZero lx x₀ x) (withBatchZero ly y₀ y) with hlam'
  have hlamj : IsFracRule lx ly bat (α j) (1 / 2) (lam j) :=
    FnCert.isFracRule_fracFormula (by norm_num) hα0 (s0 := v0 j) (fun b => (hv0 j b).1)
      (fun b x x' y y' hx hy => (hv0 j b).2.2 x x' y y' hx hy) (hlam j)
  have hlam'R : IsFracRule lx ly bat (α j) (1 / 2) lam' := FnCert.isFracRule_frozen hlamj x₀ y₀
  have hg' : IsFitRule lx ly bat (fun _ _ _ => f₀) := fun k =>
    ⟨hf₀m.comp measurable_snd, fun _ _ _ z => hF01 _ _ z, fun _ _ _ _ _ _ _ => rfl⟩
  have hset : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
      rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} =
      {ω | rejects lam' (fun _ _ _ => f₀) bat A B (α j) δ ω.1 ω.2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hlam']
    rw [FnCert.rejects_frozen_iff hpair f₀ x₀ ω.1 y₀ ω.2]
    refine FnCert.rejects_congr_ramp fun k => ?_
    change F (fitSample lx 1 (withBatchZero lx x₀ ω.1)) (fitSample ly 1 (withBatchZero ly y₀ ω.2)) = f₀
    rw [fitSample_wbz, fitSample_wbz]
  refine ⟨hset ▸ Upper.measurableSet_rejects hg' hlam'R, ?_⟩
  have hcompl : {ω : (Fin n → 𝒳) × (Fin m → 𝒳) | ¬ rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ
      (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} =
      univ ∩ {ω | ¬ rejects lam' (fun _ _ _ => f₀) bat A B (α j) δ ω.1 ω.2} := by
    rw [univ_inter, ← compl_setOf, ← compl_setOf, hset]
  rw [hcompl]
  refine (bet_power_frac.1 𝒳 P Q n m N lx ly bat A B (α j) δ (1 / 2) s2 (C / √(N : ℝ)) (fun _ _ _ => f₀) lam' univ hpair hα0
    hδ0 hδ1 (by norm_num) le_rfl hs20 hs24 hg' hlam'R (fun k x y z => ?_) ?_ MeasurableSet.univ fun ω _ k => ⟨?_, ?_⟩)
  · simp only [hlam']
    rw [hlam j k]
    exact PaperRun.fracFormula_le_lamHi (1 / 2) (α j) w0 hL.le hN hs20 _ _ _
  · have h4 : (1 + α j) ^ 2 ≤ 4 := by nlinarith
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  · unfold fracAt
    simp only [hlam']
    rw [hlam j k]
    have e : (fun _ : Fin k => (1 : ℝ)) = fun l => if l ∈ (Finset.univ : Finset (Fin k)) then 1 else 0 := by
      funext l; simp
    rw [e]
    refine PaperRun.lamLo_le_fracFormula (1 / 2) (α j) (Real.log (1 / δ)) N s2 w0 _ Finset.univ _ hw0
      ((hv0 j (bat k)).2.1 _ _).1 ((hv0 j (bat k)).2.1 _ _).2 hα0 hα1 (fun l => ?_) hs20 hL.le
    exact pairZ_mem (fun z => hF01 _ _ z) hpair.1 _ ω.1 ω.2
  · change α j + C / √(N : ℝ) ≤ (∫ z, f₀ z ∂P) - ∫ z, f₀ z ∂Q
    exact hexc

/-- **T46 (d), given batch 0.** -/
theorem betting_error_cond (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {α : Fin J → ℝ}
    {δ η s2 w0 h : ℝ} {F : (Fin (fitCard lx 1) → 𝒳) → (Fin (fitCard ly 1) → 𝒳) → 𝒳 → ℝ}
    {v0 : Fin J → ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → ℝ}
    {lam : Fin J → (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη0 : 0 < η) (hη1 : η < 1) (hs20 : 0 < s2) (hs24 : s2 ≤ 4)
    (hpair : IsBatchPairing lx ly bat A B) (hmono : StrictMono α) (hα0 : ∀ j, 0 ≤ α j)
    (hFm : Measurable (fun p : ((Fin (fitCard lx 1) → 𝒳) × (Fin (fitCard ly 1) → 𝒳)) × 𝒳 => F p.1.1 p.1.2 p.2))
    (hF01 : ∀ u v z, F u v z ∈ Icc (0 : ℝ) 1) (hw0 : 0 < w0) (hv0 : IsPriorRule lx ly v0)
    (hlam : ∀ (j : Fin J) (k : Fin N) (x : Fin n → 𝒳) (y : Fin m → 𝒳) (z : Fin k → ℝ),
      lam j k x y z = fracFormula (1 / 2) (α j) (Real.log (1 / δ)) N s2 w0 (v0 j (bat k) x y) (fun _ => 1) z)
    (hh : 0 ≤ h) (hN : 1 ≤ N) (x₀ : Fin n → 𝒳) (y₀ : Fin m → 𝒳)
    (hmesh : StatFormal.Wave31tl.MeshBelowLe α (fnDrift P Q lx ly F x₀ y₀) h) :
    ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧ ENNReal.ofReal (1 - η) ≤ sampleLaw P Q n m E ∧
      ∀ ω ∈ E, fnDrift P Q lx ly F x₀ y₀ - h - FnCert.betC δ η s2 J / √(N : ℝ) ≤
        fnAlpha lx ly bat A B F lam α δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2) := by
  classical
  haveI : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  set C := FnCert.betC δ η s2 J with hCdef
  obtain ⟨hC0, hC8, hCspec⟩ := FnCert.betC_spec (η := η) (s2 := s2) J hδ0 hδ1
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set Δ₀ := fnDrift P Q lx ly F x₀ y₀ with hΔ₀
  have hΔ1 : Δ₀ ≤ 1 := by
    have hd := fncert_drift_err_route 𝒳 P Q n m lx ly F hFm hF01 x₀ y₀
    have he := (StatFormal.Wave31to.newapprox_err 𝒳 P Q _ (measurable_section hFm (fitSample lx 1 x₀) (fitSample ly 1 y₀))
      fun z => ⟨(hF01 _ _ z).1, (hF01 _ _ z).2⟩).2.1
    have ht := StatFormal.Distances.tvDist_le_one (μ := P) (ν := Q)
    rw [hΔ₀, hd]
    linarith
  by_cases htriv : Δ₀ - h - C / √(N : ℝ) ≤ 0
  · refine ⟨univ, MeasurableSet.univ, ?_, fun ω _ => htriv.trans (FnCert.alphaLo_nonneg' hα0 _)⟩
    rw [measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  push Not at htriv
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
  have hCN0 : 0 ≤ C / √(N : ℝ) := div_nonneg hC0 hsN.le
  have hCN1 : C / √(N : ℝ) < 1 := by linarith
  have hN8 : 8 * Real.log (1 / δ) ≤ N := by
    have h1 : C < √(N : ℝ) := by rwa [div_lt_one hsN] at hCN1
    have h2 : √(8 * Real.log (1 / δ)) < √(N : ℝ) := lt_of_le_of_lt hC8 h1
    exact ((Real.sqrt_lt_sqrt_iff (by positivity)).1 h2).le
  have hCpos : 0 < C := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) hC8
  have hCNpos : 0 < C / √(N : ℝ) := div_pos hCpos hsN
  set a := Δ₀ - C / √(N : ℝ) with ha
  have ha0 : 0 ≤ a := by linarith
  have haΔ : a ≤ Δ₀ := by linarith
  have ha1 : a < 1 := by linarith
  have hfl := hmesh a ⟨ha0, haΔ⟩
  have hpos : 0 < StatFormal.Wave31tl.gridFloor α a := by linarith
  obtain ⟨j₀, hj₀a, hj₀eq⟩ := FnCert.exists_eq_gridFloor α hpos
  -- the levels `i ≤ j₀`
  have hlev : ∀ i ≤ j₀, α i ≤ a := fun i hi => (hmono.monotone hi).trans hj₀a
  have hpow := fun (i : Fin J) (hi : i ≤ j₀) => level_power_cond (A := A) (B := B) (C := C) P Q hpair hδ0 hδ1 hs20 hs24 hFm hF01
    hw0 hv0 hlam hN hN8 i (hα0 i) (lt_of_le_of_lt (hlev i hi) ha1) x₀ y₀ (by linarith [hlev i hi])
  set R : Fin J → Set ((Fin n → 𝒳) × (Fin m → 𝒳)) := fun i => {ω |
    rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2)} with hR
  set E := ⋂ i : Fin J, ⋂ (_ : i ≤ j₀), R i with hE
  have hEm : MeasurableSet E := MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => (hpow i hi).1
  set ε := η / ((J : ℝ) + 1) with hε
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := div_pos hη0 hJ1
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one hJ1]; have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; linarith
  have hRc : ∀ i ≤ j₀, sampleLaw P Q n m (R i)ᶜ ≤ ENNReal.ofReal ε := fun i hi => by
    have h1 := (hpow i hi).2
    rw [hR]
    simp only [compl_setOf]
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact FnCert.epsN_le_of_C hs20 hL (hα0 i) (lt_of_le_of_lt (hlev i hi) ha1) hN hε0 hε1 hCspec
  set s := Finset.univ.filter fun i : Fin J => i ≤ j₀ with hs
  have hEc : sampleLaw P Q n m Eᶜ ≤ ENNReal.ofReal η := by
    have hsub : Eᶜ ⊆ ⋃ i ∈ s, (R i)ᶜ := by
      intro ω hω
      simp only [hE, Set.mem_compl_iff, Set.mem_iInter, not_forall] at hω
      obtain ⟨i, hi, hni⟩ := hω
      simp only [Set.mem_iUnion]
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, hni⟩
    calc sampleLaw P Q n m Eᶜ ≤ sampleLaw P Q n m (⋃ i ∈ s, (R i)ᶜ) := measure_mono hsub
      _ ≤ ∑ i ∈ s, sampleLaw P Q n m (R i)ᶜ := measure_biUnion_finset_le s _
      _ ≤ ∑ _i ∈ s, ENNReal.ofReal ε := Finset.sum_le_sum fun i hi => hRc i (Finset.mem_filter.1 hi).2
      _ = ENNReal.ofReal (∑ _i ∈ s, ε) := (ENNReal.ofReal_sum_of_nonneg fun _ _ => hε0.le).symm
      _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (s.card : ℝ) ≤ J := by
          have := Finset.card_le_univ s
          rw [Fintype.card_fin] at this
          exact_mod_cast this
        have : (s.card : ℝ) * ε ≤ J * ε := mul_le_mul_of_nonneg_right hcard hε0.le
        have hJε : (J : ℝ) * ε ≤ η := by
          rw [hε, mul_div_assoc', div_le_iff₀ hJ1]
          nlinarith
        linarith
  refine ⟨E, hEm, FnCert.ge_of_measure_compl_le hEm hη0.le hEc, fun ω hω => ?_⟩
  have hrej : ∀ i ≤ j₀, rejects (lam i) (fnRamp lx ly F) bat A B (α i) δ (withBatchZero lx x₀ ω.1)
      (withBatchZero ly y₀ ω.2) := fun i hi => by
    have := Set.mem_iInter.1 (Set.mem_iInter.1 hω i) hi
    exact this
  have hge := FnCert.le_alphaLo_of_forall α j₀ hrej
  change Δ₀ - h - C / √(N : ℝ) ≤ StatFormal.TrimmedMMD.Lower.alphaLo α
    (fun j => rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ (withBatchZero lx x₀ ω.1) (withBatchZero ly y₀ ω.2))
  linarith

end Bet

/-- The pairs of the single split `π = (0, ½, 1)`: `N = min(n_[1], m_[1]) ≥ (n∧m)/2 − 1`. -/
theorem single_split_count : ∀ (n m N : ℕ) (lx : Fin n → ℕ) (ly : Fin m → ℕ) (bat : Fin N → ℕ) (A : Fin N → Finset (Fin n))
    (B : Fin N → Finset (Fin m)) (cx cy : ℕ → ℕ),
    IsBoundaries 1 n cx → IsBoundaries 1 m cy → (∀ i : Fin n, lx i = cutLabel 1 cx i) → (∀ j : Fin m, ly j = cutLabel 1 cy j) →
    IsPrintedPairing 1 lx ly bat A B →
    BoundariesNear 1 (fun b => (b : ℝ) / 2) n cx → BoundariesNear 1 (fun b => (b : ℝ) / 2) m cy →
      N = min (StatFormal.Wave31tl.batchCount lx 1) (StatFormal.Wave31tl.batchCount ly 1) ∧
        ((min n m : ℕ) : ℝ) / 2 - 1 ≤ N := by
  intro n m N lx ly bat A B cx cy hcx hcy hlx hly hpp hnx hny
  have hN : N = min (StatFormal.Wave31tl.batchCount lx 1) (StatFormal.Wave31tl.batchCount ly 1) := by
    have h := hpp.1
    simpa using h
  refine ⟨hN, ?_⟩
  have hcount : ∀ {p : ℕ} (l : Fin p → ℕ) (c : ℕ → ℕ), IsBoundaries 1 p c → (∀ i : Fin p, l i = cutLabel 1 c i) →
      BoundariesNear 1 (fun b => (b : ℝ) / 2) p c → (p : ℝ) / 2 - 1 ≤ StatFormal.Wave31tl.batchCount l 1 := by
    intro p l c hc hl hnear
    have hl' : l = fun i : Fin p => cutLabel 1 c i := funext hl
    have hb : StatFormal.Wave31tl.batchCount l 1 = p - c 1 := by
      rw [hl', PaperRun.batchCount_cutLabel hc le_rfl]
      simp [PaperRun.extBnd]
    have hc1 : c 1 ≤ p := hc.2 1 ⟨le_rfl, le_rfl⟩
    have hnr := hnear 1 ⟨le_rfl, le_rfl⟩
    simp only [Nat.cast_one] at hnr
    rw [hb, Nat.cast_sub hc1]
    have := (abs_le.1 hnr).2
    linarith
  have hx := hcount lx cx hcx hlx hnx
  have hy := hcount ly cy hcy hly hny
  have hmn := min_le_left (n : ℝ) m
  have hmm := min_le_right (n : ℝ) m
  rw [hN, Nat.cast_min, Nat.cast_min]
  exact le_min (by linarith) (by linarith)

theorem fncert_betting_error_route : Claims.fncert_betting_error := by
  refine ⟨fun δ η s2 J hδ0 hδ1 hη0 hη1 hs20 hs24 =>
    ⟨FnCert.betC δ η s2 J, (FnCert.betC_spec (η := η) (s2 := s2) J hδ0 hδ1).1, ?_⟩, single_split_count⟩
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α w0 h F v0 lam hpair hmono hα0 hFm hF01 hw0 hv0 hlam hh hN
  have : IsProbabilityMeasure (sampleLaw P Q n m) := by unfold sampleLaw; infer_instance
  set C := FnCert.betC δ η s2 J with hCdef
  have herr : ∀ (x : Fin n → 𝒳) (y : Fin m → 𝒳) (a : ℝ), fnDrift P Q lx ly F x y - h - C / √(N : ℝ) ≤ a →
      StatFormal.Distances.tvDist P Q - a ≤ errFn P Q (F (fitSample lx 1 x) (fitSample ly 1 y)) + h + C / √(N : ℝ) := by
    intro x y a ha
    have hd := fncert_drift_err_route 𝒳 P Q n m lx ly F hFm hF01 x y
    linarith
  refine ⟨fun x₀ y₀ hmesh => ?_, fun hmesh => ?_⟩
  · obtain ⟨E, hE, hPE, hEω⟩ := betting_error_cond (A := A) (B := B) P Q hδ0 hδ1 hη0 hη1 hs20 hs24 hpair hmono hα0 hFm
      hF01 hw0 hv0 hlam hh hN x₀ y₀ hmesh
    exact ⟨E, hE, hPE, fun ω hω => ⟨hEω ω hω, herr x₀ y₀ _ (hEω ω hω)⟩⟩
  · set E := {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
      fnDrift P Q lx ly F ω.1 ω.2 - h - C / √(N : ℝ) ≤ fnAlpha lx ly bat A B F lam α δ ω.1 ω.2} with hEdef
    have hlamR := isFracRule_of_formula hα0 hv0 hlam
    have hRm : ∀ j, MeasurableSet {ω : (Fin n → 𝒳) × (Fin m → 𝒳) |
        rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ ω.1 ω.2} := fun j =>
      Upper.measurableSet_rejects (isFitRule_fnRamp hpair hFm hF01) (hlamR j)
    have hαm0 := Upper.alphaLo_measurable α
      (fun j (ω : (Fin n → 𝒳) × (Fin m → 𝒳)) => rejects (lam j) (fnRamp lx ly F) bat A B (α j) δ ω.1 ω.2) hRm
    have hαm : Measurable fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) => fnAlpha lx ly bat A B F lam α δ ω.1 ω.2 := by
      unfold fnAlpha
      exact hαm0
    have hEm : MeasurableSet E :=
      measurableSet_le (((measurable_fnDrift P Q hFm).sub_const _).sub_const _) hαm
    have hEc : sampleLaw P Q n m Eᶜ ≤ ENNReal.ofReal η := by
      set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
      change μ Eᶜ ≤ _
      have hmap := StatFormal.Wave31tj.map_wbz_two P Q lx ly
      rw [hμ, ← hmap, Measure.map_apply (StatFormal.Wave31tj.measurable_wbz_pair lx ly) hEm.compl]
      refine prod_le_of_slices μ μ (StatFormal.Wave31tj.measurable_wbz_pair lx ly hEm.compl) fun z₀ => ?_
      obtain ⟨E₀, hE₀, hPE₀, hE₀ω⟩ := betting_error_cond (A := A) (B := B) P Q hδ0 hδ1 hη0 hη1 hs20 hs24 hpair hmono hα0
        hFm hF01 hw0 hv0 hlam hh hN z₀.1 z₀.2 (hmesh z₀.1 z₀.2)
      haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
      refine (measure_mono fun ω hω => ?_).trans (FnCert.measure_compl_le_of_ge hE₀ hη0.le hPE₀)
      intro hωE₀
      apply hω
      have := hE₀ω ω hωE₀
      change fnDrift P Q lx ly F (withBatchZero lx z₀.1 ω.1) (withBatchZero ly z₀.2 ω.2) - h - C / √(N : ℝ) ≤
        fnAlpha lx ly bat A B F lam α δ (withBatchZero lx z₀.1 ω.1) (withBatchZero ly z₀.2 ω.2)
      rw [fnDrift_wbz]
      exact this
    exact ⟨E, hEm, FnCert.ge_of_measure_compl_le hEm hη0.le hEc, fun ω hω => ⟨hω, herr ω.1 ω.2 _ hω⟩⟩

end StatFormal.Wave31tr.RouteCert
