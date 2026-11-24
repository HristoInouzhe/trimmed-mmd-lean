import StatFormal.Wave30tz.RouteKS
import StatFormal.Wave30tv.RouteClaims

/-!
# Route: Proposition 3, validity bound of the `α = 0` variant (untrusted proof material)

Proves the frozen claim `Claims.alpha0_valid` of `StatFormal.Wave30tz.Statements`.

Data `ω = (x, y)` under `P^{⊗n} ⊗ Q^{⊗m}` (no auxiliary randomness);
`Δ_k = E_P g_b − E_Q g_b`, `b = bat k`.

* `core_ind`: the supermartingale argument of `Wave30tv.core_level` with the outcomes
  `Y'_k = I_k (Z_k − α)`, where `I_k = 1{Δ_k ≤ α}` is a function of the batches before `bat k`
  (no TV assumption). Given the past, the mean of `Y'_k` is `I_k (Δ_k − α) ≤ 0` (freezing,
  `integral_mul_pairZ` with `V · I_k` in place of `V`), and Ville's inequality bounds the
  probability that `K'_t = ∏_{k<t}(1 + λ_k Y'_k)` reaches `1/δ` by `δ`.
* `alpha0_valid_route`: where `KS⁺(f_{bat k}) ≤ α` for every pair, Lemma 7 (`g_b = h ∘ f_b`,
  `h` nondecreasing with values in `[0,1]`) gives `Δ_k ≤ KS⁺(f_{bat k}) ≤ α`, so `I_k = 1` and
  `K' = K`. Hence `{reject} ⊆ {K' reaches 1/δ} ∪ {∃ k, KS⁺(f_{bat k}) > α}`, and the bound
  follows by subadditivity of the (outer) measure.
  The indicator `1{Δ_k ≤ α}` replaces the printed `1{KS⁺(f_b) ≤ α}`: it is `1` wherever the
  printed one is, and it is measurable with no argument about `KS⁺`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tz

open StatFormal.Wave30tq StatFormal.Wave30tv StatFormal.Betting StatFormal.Wave30tp

section Valid

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {n m N : ℕ}
  {lx : Fin n → ℕ} {ly : Fin m → ℕ} {bat : Fin N → ℕ} {A : Fin N → Finset (Fin n)} {B : Fin N → Finset (Fin m)}

/-- **The core with the predictable indicator**: with `I_k = 1{Δ_k ≤ α}`, the wealth `∏_{k<t}(1 + λ_k I_k (Z_k − α))`
reaches `1/δ` with probability at most `δ`, for every pair `(P, Q)`. -/
theorem core_ind (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hpair : IsBatchPairing lx ly bat A B) {α δ c : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hc1 : c ≤ 1)
    (G : ℕ → (Fin n → 𝒳) × (Fin m → 𝒳) → 𝒳 → ℝ)
    (hGm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => G (bat k) p.1 p.2)
    (hG01 : ∀ k : Fin N, ∀ ω z, G (bat k) ω z ∈ Icc (0 : ℝ) 1)
    (hGd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (G (bat k)))
    (Lam : (k : ℕ) → (Fin n → 𝒳) × (Fin m → 𝒳) → (Fin k → ℝ) → ℝ)
    (hLm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => Lam k p.1 p.2)
    (hLb : ∀ k : Fin N, ∀ ω z, 0 ≤ Lam k ω z ∧ Lam k ω z ≤ c / (1 + α))
    (hLd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (Lam k)) :
    ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real
        {ω | ∃ t ≤ N, 1 / δ ≤ wealthP
          (fun k ω => Lam k ω (past (fun i => pairZ (G (bat i) ω) A B ω.1 ω.2 i) k))
          (fun k ω => ({ω' | (∫ z, G (bat k) ω' z ∂P) - (∫ z, G (bat k) ω' z ∂Q) ≤ α}.indicator
            (fun _ => (1 : ℝ)) ω) * (pairZ (G (bat k) ω) A B ω.1 ω.2 k - α)) t ω} ≤ δ := by
  set μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q) with hμ
  have hmono : Monotone bat := hpair.2.1
  set 𝒢 := seqFiltration (𝒳 := 𝒳) lx ly bat A B hmono with h𝒢
  set Z : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => pairZ (G (bat k) ω) A B ω.1 ω.2 k with hZ
  set Δ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ :=
    fun k ω => (∫ z, G (bat k) ω z ∂P) - ∫ z, G (bat k) ω z ∂Q with hΔdef
  set I : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ :=
    fun k => {ω' | (∫ z, G (bat k) ω' z ∂P) - (∫ z, G (bat k) ω' z ∂Q) ≤ α}.indicator (fun _ => (1 : ℝ))
    with hIdef
  set Y : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => I k ω * (Z k ω - α) with hYdef
  set Λ : Fin N → (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun k ω => Lam k ω (past (fun i => Z i ω) k) with hΛdef
  have h1α : 0 < 1 + α := by linarith
  -- measurability and dependence of the pair statistics
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
  -- the conditional means `Δ_k` and the indicators `I_k`
  have hIP : ∀ k : Fin N, Measurable fun ω => ∫ t, G (bat k) ω t ∂P := fun k =>
    ((hGm k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hIQ : ∀ k : Fin N, Measurable fun ω => ∫ t, G (bat k) ω t ∂Q := fun k =>
    ((hGm k).stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
  have hΔm : ∀ k, Measurable (Δ k) := fun k => (hIP k).sub (hIQ k)
  have hΔd : ∀ k : Fin N, DepOn (before lx ly (bat k)) (Δ k) := fun k ω ω' h => by
    simp only [hΔdef]
    rw [hGd k ω ω' h]
  have hIeq : ∀ k ω, I k ω = if Δ k ω ≤ α then 1 else 0 := fun k ω => by
    simp only [hIdef, hΔdef, Set.indicator_apply, Set.mem_ofPred_eq]
  have hIm : ∀ k, Measurable (I k) := fun k =>
    measurable_const.indicator (measurableSet_le (hΔm k) measurable_const)
  have hId : ∀ k : Fin N, DepOn (before lx ly (bat k)) (I k) := fun k ω ω' h => by
    rw [hIeq, hIeq, hΔd k ω ω' h]
  have hI01 : ∀ k ω, 0 ≤ I k ω ∧ I k ω ≤ 1 := fun k ω => by
    rw [hIeq]
    split_ifs <;> norm_num
  have hY : ∀ k : Fin N, Measurable[𝒢 (k + 1)] (Y k) := fun k =>
    measurable_coordSigma_of_depOn ((hIm k).mul ((hZm k).sub_const α)) fun ω ω' h => by
      simp only [hYdef]
      rw [hId k ω ω' fun j hj => h j (before_subset_predSet_succ hmono k hj), hZd k ω ω' h]
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
  have hZb : ∀ k ω, Z k ω ∈ Icc (-1 : ℝ) 1 := fun k ω => pairZ_mem (hG01 k ω) hpair.1 k ω.1 ω.2
  have hΛb : ∀ k ω, 0 ≤ Λ k ω ∧ Λ k ω ≤ c / (1 + α) := fun k ω => hLb k ω _
  have hYb : ∀ k ω, |Y k ω| ≤ 1 + α := fun k ω => by
    have hz := hZb k ω
    have hzα : |Z k ω - α| ≤ 1 + α := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    simp only [hYdef]
    rw [abs_mul, abs_of_nonneg (hI01 k ω).1]
    calc I k ω * |Z k ω - α| ≤ 1 * (1 + α) :=
          mul_le_mul (hI01 k ω).2 hzα (abs_nonneg _) zero_le_one
      _ = 1 + α := one_mul _
  have hfac : ∀ k ω, 0 ≤ 1 + Λ k ω * Y k ω := fun k ω => by
    simp only [hYdef]
    rw [hIeq]
    split_ifs
    · have hYlo : -(1 + α) ≤ Z k ω - α := by linarith [(hZb k ω).1]
      have hl := hΛb k ω
      have hcap : Λ k ω * (1 + α) ≤ c := by
        have := mul_le_mul_of_nonneg_right hl.2 h1α.le
        rwa [div_mul_cancel₀ c h1α.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_left hYlo hl.1]
    · simp
  -- the conditional mean of `Y'_k` given the past is `≤ 0`
  have hmean : ∀ k : Fin N, ∀ V : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ, Measurable[𝒢 k] V → (∀ ω, 0 ≤ V ω) →
      (∃ C, ∀ ω, V ω ≤ C) → ∫ ω, V ω * Y k ω ∂μ ≤ 0 := by
    intro k V hV hV0 ⟨K, hK⟩
    have hVd : DepOn (predSet lx ly bat A B k) V := depOn_of_measurable hV
    have hVm : Measurable V := hV.mono (𝒢.le k) le_rfl
    have hK0 : 0 ≤ K := (hV0 (nonempty_of_isProbabilityMeasure μ).some).trans (hK _)
    set V' : (Fin n → 𝒳) × (Fin m → 𝒳) → ℝ := fun ω => V ω * I k ω with hV'def
    have hV'm : Measurable V' := hVm.mul (hIm k)
    have hV'd : DepOn (predSet lx ly bat A B k) V' := fun ω ω' h => by
      simp only [hV'def]
      rw [hVd ω ω' h, hId k ω ω' fun j hj => h j (before_subset_predSet k hj)]
    have hV'0 : ∀ ω, 0 ≤ V' ω := fun ω => mul_nonneg (hV0 ω) (hI01 k ω).1
    have hV'b : ∀ ω, |V' ω| ≤ K := fun ω => by
      rw [abs_of_nonneg (hV'0 ω)]
      calc V ω * I k ω ≤ V ω * 1 := mul_le_mul_of_nonneg_left (hI01 k ω).2 (hV0 ω)
        _ = V ω := mul_one _
        _ ≤ K := hK ω
    have hGdk : DepOn (predSet lx ly bat A B k) (G (bat k)) := (hGd k).mono (before_subset_predSet k)
    have hEq := integral_mul_pairZ P Q (C := predSet lx ly bat A B k) k (hpair.1.1 k) (hpair.1.2.1 k)
      (fun i hi => notMem_predSet_of_mem_blockSet hpair k (Or.inl ⟨i, by exact_mod_cast hi, rfl⟩))
      (fun j hj => notMem_predSet_of_mem_blockSet hpair k (Or.inr ⟨j, by exact_mod_cast hj, rfl⟩))
      hV'm hV'd hV'b (hGm k) hGdk (hG01 k)
    have hintZ : Integrable (fun ω => V' ω * Z k ω) μ :=
      integrable_of_abs_le (hV'm.mul (hZm k)) (K * 1) fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hV'b ω) (abs_le.2 ⟨(hZb k ω).1, (hZb k ω).2⟩) (abs_nonneg _) hK0
    have hintV : Integrable V' μ := integrable_of_abs_le hV'm K hV'b
    have hsplit : (fun ω => V ω * Y k ω) = fun ω => V' ω * Z k ω - α * V' ω := by
      funext ω; simp only [hYdef, hV'def]; ring
    rw [hsplit, integral_sub hintZ (hintV.const_mul α), integral_const_mul]
    have hle : ∫ ω, V' ω * Z k ω ∂μ ≤ ∫ ω, α * V' ω ∂μ := by
      simp only [hZ]
      rw [hEq]
      have hIb : ∀ (ν : Measure 𝒳) [IsProbabilityMeasure ν] ω, |∫ t, G (bat k) ω t ∂ν| ≤ 1 := fun ν _ ω => by
        have hGb : ∀ t, ‖G (bat k) ω t‖ ≤ 1 := fun t => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hG01 k ω t).1, (hG01 k ω t).2]
        have h := norm_integral_le_of_norm_le_const (μ := ν) (C := 1) (ae_of_all _ hGb)
        simpa [Real.norm_eq_abs] using h
      have hintD : Integrable (fun ω => V' ω * ((∫ t, G (bat k) ω t ∂P) - ∫ t, G (bat k) ω t ∂Q)) μ :=
        integrable_of_abs_le (hV'm.mul ((hIP k).sub (hIQ k))) (K * 2) fun ω => by
          rw [abs_mul]
          refine mul_le_mul (hV'b ω) ((abs_sub _ _).trans ?_) (abs_nonneg _) hK0
          linarith [hIb P ω, hIb Q ω]
      refine integral_mono hintD (hintV.const_mul α) fun ω => ?_
      have hΔω : V' ω * Δ k ω ≤ α * V' ω := by
        simp only [hV'def]
        rw [hIeq]
        split_ifs with hω
        · rw [mul_one, mul_comm α]
          exact mul_le_mul_of_nonneg_left hω (hV0 ω)
        · simp
      exact hΔω
    rw [integral_const_mul] at hle
    linarith
  -- Ville's inequality at `1/δ` for the wealth started at `1`
  have hV := betting_ville_pred 𝒢 (fun _ => (1 : ℝ)) Λ Y measurable_const (fun _ => ⟨zero_le_one, le_rfl⟩)
    hY hΛ hΛb hYb hfac hmean (a := 1 / δ) (by positivity)
  have hint1 : ∫ _, (1 : ℝ) ∂μ = 1 := by simp
  have key : ∀ x : ℝ, 1 / δ * x ≤ 1 → x ≤ δ := fun x hx => by
    rw [one_div, inv_mul_le_iff₀ hδ, mul_one] at hx
    exact hx
  rw [hint1] at hV
  simp only [one_mul] at hV
  exact key _ hV

end Valid

/-- **Proposition 3**, the validity bound of the `α = 0` variant: the certificate rejects `H_{0,α}` with probability at
most `δ + P(∃ k, KS⁺(f_{bat k}) > α)`, for every pair `(P, Q)`. -/
theorem alpha0_valid_route : Claims.alpha0_valid := by
  intro 𝒳 _ P Q _ _ n m N lx ly bat A B α δ c F g lam hpair hα hδ0 hδ1 hc0 hc1 hg hlam hFm hFd hh
  have hg' : IsBatchRule (U := Unit) lx ly bat (fun b _ => g b) := hg
  have hlam' : IsBatchBetRule (U := Unit) lx ly bat α c (fun k _ => lam k) := hlam
  have hGm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => g (bat k) p.1.1 p.1.2 p.2 := by
    intro k
    have hφ : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × 𝒳 => (((), p.1), p.2) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact (hg' k).1.comp hφ
  have hLm : ∀ k : Fin N, Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) =>
      lam k p.1.1 p.1.2 p.2 := by
    intro k
    have hφ : Measurable fun p : ((Fin n → 𝒳) × (Fin m → 𝒳)) × (Fin k → ℝ) => (((), p.1), p.2) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact (hlam' k).1.comp hφ
  have hcore := core_ind (A := A) (B := B) P Q hpair hα hδ0 hc1 (fun b ω => g b ω.1 ω.2) hGm
    (fun k ω z => (hg' k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => g (bat k) x y) fun x x' y y' hx hy => (hg' k).2.2 () x x' y y' hx hy)
    (fun k ω => lam k ω.1 ω.2) hLm (fun k ω z => (hlam' k).2.1 () ω.1 ω.2 z)
    (fun k => depOn_before (F := fun x y => lam k x y) fun x x' y y' hx hy => (hlam' k).2.2 () x x' y y' hx hy)
  -- `Δ_k ≤ KS⁺(f_{bat k})` (Lemma 7)
  have hΔks : ∀ (k : Fin N) (ω : (Fin n → 𝒳) × (Fin m → 𝒳)),
      (∫ z, g (bat k) ω.1 ω.2 z ∂P) - (∫ z, g (bat k) ω.1 ω.2 z ∂Q) ≤ ksPlus P Q (F (bat k) ω.1 ω.2) := by
    intro k ω
    obtain ⟨h, hmon, hI, hgeq⟩ := hh k ω.1 ω.2
    have hFk : Measurable (F (bat k) ω.1 ω.2) := by
      have := (hFm k).comp (measurable_prodMk_left (x := ω))
      exact this
    have h1 := monotone_sub_le_ksPlus P Q hFk hmon hI
    rw [hgeq]
    exact h1
  have hfinal : ∀ R : Set ((Fin n → 𝒳) × (Fin m → 𝒳)),
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)).real R ≤ δ →
      {ω | rejects lam g bat A B α δ ω.1 ω.2} ⊆ R ∪ {ω | ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)} →
      sampleLaw P Q n m {ω | rejects lam g bat A B α δ ω.1 ω.2} ≤
        ENNReal.ofReal δ + sampleLaw P Q n m {ω | ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)} := by
    intro R hR hsub
    unfold sampleLaw
    calc _ ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
          (R ∪ {ω | ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)}) := measure_mono hsub
      _ ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) R +
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q))
            {ω | ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)} := measure_union_le _ _
      _ ≤ _ := by
        gcongr
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal hR
  refine hfinal _ hcore fun ω hω => ?_
  by_cases hks : ∃ k : Fin N, α < ksPlus P Q (F (bat k) ω.1 ω.2)
  · exact Or.inr hks
  · left
    push Not at hks
    have hω' : ∃ t, t ≤ N ∧ 1 / δ ≤ wealth (fun k => lam k ω.1 ω.2) α
        (fun k => pairZ (g (bat k) ω.1 ω.2) A B ω.1 ω.2 k) t := hω
    obtain ⟨t, ht, hw⟩ := hω'
    rw [Set.mem_ofPred_eq]
    refine ⟨t, ht, le_of_le_of_eq hw ?_⟩
    unfold wealth wealthP
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : (∫ z, g (bat k) ω.1 ω.2 z ∂P) - (∫ z, g (bat k) ω.1 ω.2 z ∂Q) ≤ α := (hΔks k ω).trans (hks k)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hk, ite_true, one_mul]

end StatFormal.Wave30tz
