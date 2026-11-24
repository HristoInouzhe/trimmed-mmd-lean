import StatFormal.Wave30tv.RouteClaims
import StatFormal.Wave30tz.Statements

/-!
# The wealth at the horizon is an e-value; Markov's inequality for averages of e-values (library)

Library component (untrusted). Setting of the sequential certificate (`Wave30tv`): data `ω = (x, y) ∈ 𝒳^n × 𝒳^m` under
`P^{⊗n} ⊗ Q^{⊗m}`, a batch pairing, ramps `G_b` (measurable, `[0,1]`-valued, functions of the batches before `b`) and fractions
`Λ_k ∈ [0, c/(1+α)]`, `c ≤ 1` (measurable, functions of the batches before that of pair `k` and of the earlier pair statistics).

* `horizon_wealth_evalue`: if `TV(P,Q) ≤ α`, the wealth at the horizon `K_N = ∏_{k<N}(1 + Λ_k(Z_k − α))` (no stopping) is
  measurable, nonnegative, integrable and `E K_N ≤ 1`. Proof: the wealth is a nonnegative supermartingale for the filtration of the
  coordinates known before each pair (`Lib/Betting/Predictable.lean`, `betting_supermartingale_pred`), so `E K_N ≤ E K_0 = 1`
  (`Supermartingale.setIntegral_le` on the whole space). The supermartingale hypotheses are established exactly as in the certified
  route `StatFormal.Wave30tv.core_level` (wave 30tv, `RouteSeq.lean`), whose proof is copied and adapted here (initial capital `1`
  instead of `1_s`, and the supermartingale inequality at the horizon instead of Ville's inequality).
* `fitRule_horizon_evalue`, `lintegral_horizon_wealth_le_one`: the same for the rules of `Wave30tz` (`IsFitRule`, `IsFracRule`, no
  auxiliary randomness), with `E` as a lower Lebesgue integral of `ENNReal.ofReal K_N`.
* `measure_avg_ge_le` (Markov): for `S ≥ 1` integrable nonnegative `K_s` with `E K_s ≤ 1` (any dependence between them),
  `μ{S⁻¹ Σ_s K_s ≥ 1/δ} ≤ δ` for `δ > 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.KernelRun

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Betting

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
variable {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)}
  {B : Fin N → Finset (Fin m)}

/-- **The wealth at the horizon is an e-value under `H_{0,α}`** (`TV(P,Q) ≤ α`): measurable, nonnegative, integrable, with mean at
most `1`. Copy-adapted from the certified route `StatFormal.Wave30tv.core_level` (same hypotheses, without the batch-0 event). -/
theorem horizon_wealth_evalue (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α c : ℝ} (hα : 0 ≤ α) (hc1 : c ≤ 1)
    (G : ℕ → (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ)
    (hGm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G (bat k) p.1 p.2)
    (hG01 : ∀ k : Fin N, ∀ ω z, G (bat k) ω z ∈ Icc (0 : ℝ) 1)
    (hGd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (G (bat k)))
    (Lam : (k : ℕ) → (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin k → ℝ) → ℝ)
    (hLm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => Lam k p.1 p.2)
    (hLb : ∀ k : Fin N, ∀ ω z, 0 ≤ Lam k ω z ∧ Lam k ω z ≤ c / (1 + α))
    (hLd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (Lam k))
    (hTV : StatFormal.Distances.tvDist P Q ≤ α) :
    Measurable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
        wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N) ∧
      (∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳), 0 ≤ wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N) ∧
      Integrable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
        wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N)
        ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ∧
      ∫ ω, wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N
        ∂((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) ≤ 1 := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have hmono : Monotone bat := hpair.2.1
  set 𝒢 := seqFiltration (𝒳 := 𝒳) lx ly bat A B hmono with h𝒢
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairZ (G (bat k) ω) A B ω.1 ω.2 k with hZ
  set Y : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Z k ω - α with hYdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Lam k ω (past (fun i => Z i ω) k) with hΛdef
  set W0 : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun _ => 1 with hW0def
  have h1α : 0 < 1 + α := by linarith
  -- measurability and dependence of the pair statistics (as in `core_level`)
  have hZm : ∀ k, Measurable (Z k) := fun k => by
    simp only [hZ]
    unfold pairZ blockMean
    refine Measurable.sub (Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _)
      (Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _)
    · exact (hGm k).comp (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))
    · exact (hGm k).comp (measurable_id.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hZd : ∀ k : Fin N, DepOn (predSet lx ly bat A B (k + 1)) (Z k) := fun k ω ω' h => by
    simp only [hZ]
    rw [hGd k ω ω' fun j hj => h j (before_subset_predSet_succ hmono k hj)]
    exact pairZ_congr k
      (fun i hi => h (Sum.inl i) (blockSet_subset_predSet_succ k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩)))
      (fun j hj => h (Sum.inr j) (blockSet_subset_predSet_succ k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩)))
  have hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k) := fun k =>
    measurable_coordSigma_of_depOn ((hZm k).sub_const α) fun ω ω' h => by
      simp only [hYdef]; rw [hZd k ω ω' h]
  have hΛm : ∀ k, Measurable (Λ k) := fun k =>
    (hLm k).comp (measurable_id.prodMk (Measurable.of_eval fun i => hZm _))
  have hΛd : ∀ k : Fin N, DepOn (predSet lx ly bat A B k) (Λ k) := fun k ω ω' h => by
    simp only [hΛdef]
    rw [hLd k ω ω' fun j hj => h j (before_subset_predSet k hj)]
    congr 1
    funext i
    simp only [past]
    refine hZd _ ω ω' fun j hj => h j (predSet_mono hmono ?_ hj)
    have := i.isLt
    simp only [Fin.val_castLE]
    omega
  have hΛ : ∀ k : Fin N, Measurable[𝒢 k] (Λ k) := fun k => measurable_coordSigma_of_depOn (hΛm k) (hΛd k)
  have hW0 : Measurable[𝒢 0] W0 := measurable_const
  have hW0b : ∀ ω, 0 ≤ W0 ω ∧ W0 ω ≤ 1 := fun ω => ⟨zero_le_one, le_rfl⟩
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairZ_mem (hG01 k ω) hpair.1 k ω.1 ω.2
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => hLb k ω _
  have hYb : ∀ k ω, |Y k ω| ≤ 1 + α := fun k ω => by
    have := hZb k ω
    rw [abs_le]; constructor <;> simp only [hYdef] <;> linarith [this.1, this.2]
  have hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω := fun k ω => by
    have hYlo : -(1 + α) ≤ Y k ω := by
      have := hZb k ω; simp only [hYdef]; linarith [this.1]
    have hl := hΛb k ω
    have hcap : Λ k ω * (1 + α) ≤ c := by
      have := mul_le_mul_of_nonneg_right hl.2 h1α.le
      rwa [div_mul_cancel₀ c h1α.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hYlo hl.1]
  -- the conditional mean of `Y_k` given the past is `≤ 0` (as in `core_level`)
  have hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) →
      (∃ C, ∀ ω, V ω ≤ C) → ∫ ω, V ω * Y k ω ∂μ ≤ 0 := by
    intro k V hV hV0 ⟨K, hK⟩
    have hVd : DepOn (predSet lx ly bat A B k) V := depOn_of_measurable hV
    have hVm : Measurable V := hV.mono (𝒢.le k) le_rfl
    have hVb : ∀ ω, |V ω| ≤ K := fun ω => by rw [abs_of_nonneg (hV0 ω)]; exact hK ω
    have hK0 : 0 ≤ K := (hV0 (nonempty_of_isProbabilityMeasure μ).some).trans (hK _)
    have hGdk : DepOn (predSet lx ly bat A B k) (G (bat k)) := (hGd k).mono (before_subset_predSet k)
    have hEq := integral_mul_pairZ P Q (C := predSet lx ly bat A B k) k (hpair.1.1 k) (hpair.1.2.1 k)
      (fun i hi => notMem_predSet_of_mem_blockSet hpair k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩))
      (fun j hj => notMem_predSet_of_mem_blockSet hpair k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩))
      hVm hVd hVb (hGm k) hGdk (hG01 k)
    have hintZ : Integrable (fun ω => V ω * Z k ω) μ :=
      integrable_of_abs_le (hVm.mul (hZm k)) (K * 1) fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hVb ω) (abs_le.2 ⟨(hZb k ω).1, (hZb k ω).2⟩) (abs_nonneg _) hK0
    have hintV : Integrable V μ := integrable_of_abs_le hVm K hVb
    have hsplit : (fun ω => V ω * Y k ω) = fun ω => V ω * Z k ω - α * V ω := by
      funext ω; simp only [hYdef]; ring
    rw [hsplit, integral_sub hintZ (hintV.const_mul α), integral_const_mul]
    have hIP : Measurable fun ω => ∫ t, G (bat k) ω t ∂P :=
      ((hGm k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have hIQ : Measurable fun ω => ∫ t, G (bat k) ω t ∂Q :=
      ((hGm k).stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
    have hle : ∫ ω, V ω * Z k ω ∂μ ≤ ∫ ω, α * V ω ∂μ := by
      simp only [hZ]
      rw [hEq]
      have hIb : ∀ (ν : Measure 𝒳) [IsProbabilityMeasure ν] ω, |∫ t, G (bat k) ω t ∂ν| ≤ 1 := fun ν _ ω => by
        have hGb : ∀ t, ‖G (bat k) ω t‖ ≤ 1 := fun t => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hG01 k ω t).1, (hG01 k ω t).2]
        have h := norm_integral_le_of_norm_le_const (μ := ν) (C := 1) (ae_of_all _ hGb)
        simpa [Real.norm_eq_abs] using h
      have hintD : Integrable (fun ω => V ω * ((∫ t, G (bat k) ω t ∂P) - ∫ t, G (bat k) ω t ∂Q)) μ :=
        integrable_of_abs_le (hVm.mul (hIP.sub hIQ)) (K * 2) fun ω => by
          rw [abs_mul]
          refine mul_le_mul (hVb ω) ((abs_sub _ _).trans ?_) (abs_nonneg _) hK0
          linarith [hIb P ω, hIb Q ω]
      refine integral_mono hintD (hintV.const_mul α) fun ω => ?_
      · have hgm : Measurable (G (bat k) ω) := (hGm k).comp (measurable_const.prodMk measurable_id)
        have hΔ := delta_le_tv P Q hgm (hG01 k ω)
        simp only
        rw [mul_comm α]
        exact mul_le_mul_of_nonneg_left (hΔ.trans hTV) (hV0 ω)
    rw [integral_const_mul] at hle
    linarith
  -- the supermartingale inequality at the horizon
  have hK := betting_supermartingale_pred 𝒢 W0 Λ Y hW0 hW0b hY hΛ hΛb hYb hfac hmean
  have hle := hK.setIntegral_le (Nat.zero_le N) (s := Set.univ) MeasurableSet.univ
  have hW : ∀ ω, wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N =
      W0 ω * wealthP Λ Y N ω := fun ω => by
    simp only [hW0def, one_mul]
    rfl
  have hWfun : (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
      wealth (fun k => Lam k ω) α (fun k => pairZ (G (bat k) ω) A B ω.1 ω.2 k) N) = fun ω => W0 ω * wealthP Λ Y N ω :=
    funext hW
  rw [setIntegral_univ, setIntegral_univ] at hle
  have hint1 : ∫ ω, W0 ω * wealthP Λ Y 0 ω ∂μ = 1 := by
    simp only [hW0def, wealthP_zero, mul_one, integral_const, smul_eq_mul, probReal_univ]
  refine ⟨?_, fun ω => ?_, ?_, ?_⟩
  · rw [hWfun]; exact (hK.1 N).measurable.mono (𝒢.le N) le_rfl
  · rw [hW ω]; exact mul_nonneg zero_le_one (wealthP_nonneg hfac N ω)
  · rw [hWfun]; exact hK.integrable N
  · rw [hWfun]; exact hle.trans hint1.le

/-- **The wealth at the horizon is an e-value** for the rules of `Wave30tz` (`IsFitRule`, `IsFracRule`). -/
theorem fitRule_horizon_evalue (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α c : ℝ} (hα : 0 ≤ α) (hc1 : c ≤ 1)
    {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ} {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hg : StatFormal.Wave30tz.IsFitRule lx ly bat g) (hlam : StatFormal.Wave30tz.IsFracRule lx ly bat α c lam)
    (hTV : StatFormal.Distances.tvDist P Q ≤ α) :
    Measurable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
        wealth (fun k => lam k ω.1 ω.2) α (StatFormal.Wave30tz.pairStat g bat A B ω.1 ω.2) N) ∧
      (∀ ω : (Fin n → 𝒳) × (Fin m → 𝒳),
        0 ≤ wealth (fun k => lam k ω.1 ω.2) α (StatFormal.Wave30tz.pairStat g bat A B ω.1 ω.2) N) ∧
      Integrable (fun ω : (Fin n → 𝒳) × (Fin m → 𝒳) =>
        wealth (fun k => lam k ω.1 ω.2) α (StatFormal.Wave30tz.pairStat g bat A B ω.1 ω.2) N) (StatFormal.Wave30tp.sampleLaw P Q n m) ∧
      ∫ ω, wealth (fun k => lam k ω.1 ω.2) α (StatFormal.Wave30tz.pairStat g bat A B ω.1 ω.2) N ∂(StatFormal.Wave30tp.sampleLaw P Q n m) ≤ 1 :=
  horizon_wealth_evalue (A := A) (B := B) P Q hpair hα hc1 (fun b ω => g b ω.1 ω.2)
    (fun k => (hg k).1.comp (((measurable_const (a := ())).prodMk measurable_fst).prodMk measurable_snd))
    (fun k ω z => (hg k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => g (bat k) x y) fun x x' y y' hx hy => (hg k).2.2 () x x' y y' hx hy)
    (fun k ω z => lam k ω.1 ω.2 z)
    (fun k => (hlam k).1.comp (((measurable_const (a := ())).prodMk measurable_fst).prodMk measurable_snd))
    (fun k ω z => (hlam k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => lam k x y) fun x x' y y' hx hy => (hlam k).2.2 () x x' y y' hx hy)
    hTV

/-- The e-value property as a lower Lebesgue integral: `∫⁻ ofReal K_N ≤ 1`. -/
theorem lintegral_horizon_wealth_le_one (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α c : ℝ} (hα : 0 ≤ α) (hc1 : c ≤ 1)
    {g : ℕ → (Fin n → 𝒳) → (Fin m → 𝒳) → 𝒳 → ℝ} {lam : (k : ℕ) → (Fin n → 𝒳) → (Fin m → 𝒳) → (Fin k → ℝ) → ℝ}
    (hg : StatFormal.Wave30tz.IsFitRule lx ly bat g) (hlam : StatFormal.Wave30tz.IsFracRule lx ly bat α c lam)
    (hTV : StatFormal.Distances.tvDist P Q ≤ α) :
    ∫⁻ ω, ENNReal.ofReal (wealth (fun k => lam k ω.1 ω.2) α (StatFormal.Wave30tz.pairStat g bat A B ω.1 ω.2) N)
      ∂(StatFormal.Wave30tp.sampleLaw P Q n m) ≤ 1 := by
  obtain ⟨-, h0, hint, hle⟩ := fitRule_horizon_evalue (A := A) (B := B) P Q hpair hα hc1 hg hlam hTV
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)]
  exact ENNReal.ofReal_le_one.mpr hle

/-- **Markov's inequality for an average of e-values**: for `S ≥ 1` nonnegative integrable `K_s` with `E K_s ≤ 1` (any dependence),
`μ{S⁻¹ Σ_s K_s ≥ 1/δ} ≤ δ`. -/
theorem measure_avg_ge_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {S : ℕ} (hS : 1 ≤ S)
    (K : Fin S → Ω → ℝ) (hK0 : ∀ s ω, 0 ≤ K s ω) (hKi : ∀ s, Integrable (K s) μ) (hK1 : ∀ s, ∫ ω, K s ω ∂μ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) : μ {ω | 1 / δ ≤ (∑ s, K s ω) / S} ≤ ENNReal.ofReal δ := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hint : Integrable (fun ω => (∑ s, K s ω) / S) μ := (integrable_finsetSum _ fun s _ => hKi s).div_const _
  have hnn : 0 ≤ᵐ[μ] fun ω => (∑ s, K s ω) / S :=
    ae_of_all _ fun ω => div_nonneg (Finset.sum_nonneg fun s _ => hK0 s ω) hS'.le
  have hmean : ∫ ω, (∑ s, K s ω) / S ∂μ ≤ 1 := by
    rw [integral_div, integral_finsetSum _ fun s _ => hKi s, div_le_one hS']
    calc ∑ s, ∫ ω, K s ω ∂μ ≤ ∑ _s : Fin S, (1 : ℝ) := Finset.sum_le_sum fun s _ => hK1 s
      _ = S := by simp
  set E := {ω | 1 / δ ≤ (∑ s, K s ω) / S} with hE
  have hM : 1 / δ * μ.real E ≤ ∫ ω, (∑ s, K s ω) / S ∂μ := mul_meas_ge_le_integral_of_nonneg hnn hint (1 / δ)
  have hreal : μ.real E ≤ δ := by
    have h1 := mul_le_mul_of_nonneg_left (hM.trans hmean) hδ.le
    rwa [← mul_assoc, mul_one_div_cancel hδ.ne', one_mul, mul_one] at h1
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end StatFormal.KernelRun
