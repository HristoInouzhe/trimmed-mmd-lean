import StatFormal.Wave30ts.RouteLevel

/-!
# Route: the frozen claims of NOTE §3.3 (level, one event, coupled constants, Corollary C)

Untrusted proof material.

* `sharp_level`, `sharp_level_inf`, `sharp_level_zero`, `sharp_tau_level`: `eq:tvintersect` (certified `tvintersect`, via wave
  30tp's `exists_common_trim`) supplies the common trimming `R`; the cores of `RouteLevel` do the rest.
* `oneEvent_of_valid`: Lemma 1 (wave 30tp's `monotone_event`) for any valid, nonnegative, nondecreasing threshold.
* `coupled_sharp`: the true `u = ‖μ_R‖²`. If `u < κ²`, the cell threshold at `u` is valid. If `u = κ²`, then
  `tr Cov_R(φ) = 0`, so `A = B = 0` a.s. (zero second moments), and `t ≥ √(κ²+u')·min_f t_2(f)` for every `u' < κ²` forces
  `t ≥ ρ_R min_f t_2(f)`.
* Corollary C: the minimum of valid, nondecreasing thresholds is valid (the minimiser is a deterministic choice for each `α`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.Wave30ts

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.Wave30tp

/-! ### Generic threshold lemmas -/

section Generic

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem oneEvent_of_valid {φ : 𝒳 → H} {n m : ℕ} {δ : ℝ} {τ : ℝ → ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hτ0 : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ τ α) (hτm : MonotoneOn τ (Ico 0 1))
    (hval : IsValidThreshold φ n m δ τ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    OneEvent φ n m δ τ P Q := by
  rcases lt_or_ge (StatFormal.Distances.tvDist P Q) 1 with htv | htv
  · obtain ⟨⟨E, hEm, hEp, hEs⟩, hpath⟩ := monotone_event 𝒳 H φ τ δ n m P Q hδ0.le hn hm hτ0 hτm hval htv
    refine ⟨E, hEm, hEp, fun z hz => ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := hpath z (hEs hz)
    exact ⟨fun α hα htvα => h1 α ⟨htvα, hα.2⟩, fun _ => h2, h3⟩
  · refine ⟨univ, MeasurableSet.univ, by rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith),
      fun z _ => ⟨fun α hα htvα => absurd (htvα.trans_lt hα.2) (not_lt.2 htv), fun h => absurd h (not_lt.2 htv),
        fun α hα _ => lt_of_lt_of_le hα.2 htv⟩⟩

theorem valid_min {φ : 𝒳 → H} {n m : ℕ} {δ : ℝ} {τ1 τ2 : ℝ → ℝ} (h1 : IsValidThreshold φ n m δ τ1)
    (h2 : IsValidThreshold φ n m δ τ2) : IsValidThreshold φ n m δ (fun α => min (τ1 α) (τ2 α)) := by
  intro α hα P Q hP hQ htv
  rcases min_choice (τ1 α) (τ2 α) with h | h
  · simp only [h]; exact h1 α hα P Q hP hQ htv
  · simp only [h]; exact h2 α hα P Q hP hQ htv

end Generic

theorem mono_min {τ1 τ2 : ℝ → ℝ} (h1 : MonotoneOn τ1 (Ico 0 1)) (h2 : MonotoneOn τ2 (Ico 0 1)) :
    MonotoneOn (fun α => min (τ1 α) (τ2 α)) (Ico 0 1) :=
  fun _ ha _ hb hab => min_le_min (h1 ha hb hab) (h2 ha hb hab)

/-! ### The minimum over the five splits of `t_2` -/

/-- `min_{f ∈ F} g(f)`. -/
def min5 (g : ℝ → ℝ) : ℝ := min (g (1 / 2)) (min (g (3 / 5)) (min (g (7 / 10)) (min (g (4 / 5)) (g (9 / 10)))))

theorem min5_attained (g : ℝ → ℝ) : ∃ f, IsSplit f ∧ min5 g = g f := by
  unfold min5
  rcases min_choice (g (1/2)) (min (g (3/5)) (min (g (7/10)) (min (g (4/5)) (g (9/10))))) with h | h <;>
    rw [h]
  · exact ⟨1/2, Or.inl rfl, rfl⟩
  rcases min_choice (g (3/5)) (min (g (7/10)) (min (g (4/5)) (g (9/10)))) with h | h <;> rw [h]
  · exact ⟨3/5, Or.inr (Or.inl rfl), rfl⟩
  rcases min_choice (g (7/10)) (min (g (4/5)) (g (9/10))) with h | h <;> rw [h]
  · exact ⟨7/10, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  rcases min_choice (g (4/5)) (g (9/10)) with h | h <;> rw [h]
  · exact ⟨4/5, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  · exact ⟨9/10, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

theorem min5_le (g : ℝ → ℝ) {f : ℝ} (hf : IsSplit f) : min5 g ≤ g f := by
  unfold min5
  rcases hf with h | h | h | h | h <;> subst h
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

/-- `τ_{P'} ≥ ρ̄ · min_f t_2(β, (1−f)δ)` for `α > 0`. -/
theorem tauPs_ge_repair {D v ρbar α δ : ℝ} {n m : ℕ} (h0 : α ≠ 0) (hρ : 0 ≤ ρbar) :
    ρbar * min5 (fun f => rootR (1 / (1 - α)) ((1 - f) * δ) n m) ≤ tauPs D v ρbar α δ n m :=
  le_tauPs_pos h0 fun f hf => by
    unfold tauSplit
    have := mul_le_mul_of_nonneg_left (min5_le (fun f => rootR (1 / (1 - α)) ((1 - f) * δ) n m) hf) hρ
    linarith [rootH_nonneg D v ρbar (1 / (1 - α)) (f * δ) n m]

/-! ### Zero second moments -/

section Null

variable {β : Type*} [MeasurableSpace β]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem twoDev_null (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {ψ1 ψ2 : β → H}
    (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2) {K : ℝ} (hK1 : ∀ x, ‖ψ1 x‖ ≤ K)
    (hK2 : ∀ x, ‖ψ2 x‖ ≤ K) (h01 : ∫ x, ψ1 x ∂P = 0) (h02 : ∫ x, ψ2 x ∂Q = 0)
    (hz1 : ∫ x, ‖ψ1 x‖ ^ 2 ∂P = 0) (hz2 : ∫ x, ‖ψ2 x‖ ^ 2 ∂Q = 0) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    sampleLaw P Q n m {z | 0 < ‖twoDev ψ1 ψ2 z‖} = 0 := by
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hK1 x)
  have hsq := integral_norm_twoDev_sq P Q h1 h2 hK1 hK2 h01 h02 (by omega : n ≠ 0) (by omega : m ≠ 0)
  rw [hz1, hz2, zero_div, zero_div, add_zero] at hsq
  have hint : Integrable (fun z => ‖twoDev ψ1 ψ2 z‖ ^ 2) (sampleLaw P Q n m) :=
    Integrable.of_bound ((stronglyMeasurable_twoDev h1 h2 n m).norm.pow 2).aestronglyMeasurable ((2 * K) ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [twoDev_eq]
        exact (norm_sub_le _ _).trans (by linarith [norm_avg_le hK0 hK1 z.1, norm_avg_le hK0 hK2 z.2]))
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hint).1 hsq
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with z hz
  simp only [Pi.zero_apply] at hz
  simp only [mem_setOf_eq, not_lt]
  exact le_of_eq (pow_eq_zero_iff (by norm_num) |>.1 hz)

end Null

/-! ### The claims -/

theorem sharp_level : Claims.sharp_level := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ α δ1 δ2 t1 t2 l1 l2 l3 n m hφ hκ hK hα0 hα1 hn hm htv ht1 ht2 hl1 hl2
    hl3 hH hR
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim hα0 hα1 htv
  haveI := hR'
  exact core_lam hφ hκ hK.1 (hK.2.2.1 R hR') (hK.2.2.2 R hR') hα0 hα1 hn hm ha hb ht1 ht2 hl1 hl2 hl3 hH hR

theorem sharp_level_inf : Claims.sharp_level_inf := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ α δ1 δ2 t1 t2 n m hφ hκ hK hα0 hα1 hn hm htv ht1 ht2 hH hR
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim hα0 hα1 htv
  haveI := hR'
  exact core_inf hφ hκ hK.1 (hK.2.2.1 R hR') (hK.2.2.2 R hR') hα0 hα1 hn hm ha hb ht1 ht2 hH hR

theorem sharp_level_zero : Claims.sharp_level_zero := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ δ t n m hφ hκ hK hn hm htv ht hH
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim le_rfl zero_lt_one htv
  haveI := hR'
  obtain ⟨-, hPR⟩ := ae_density_eq_one ha
  obtain ⟨-, hQR⟩ := ae_density_eq_one hb
  rw [hPR, hQR]
  refine (measure_mono fun z hz => ?_).trans ((zero_part hφ hκ hK.1 (hK.2.2.1 R hR') (hK.2.2.2 R hR') hn hm ht).trans
    (ENNReal.ofReal_le_ofReal hH))
  simp only [mem_setOf_eq] at hz ⊢
  exact hz.trans_le (Demp_zero_le hφ _ hn hm z)

theorem sharp_tau_level : Claims.sharp_tau_level := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ α δ n m hφ hκ hK hα0 hα1 hδ0 hδ1 hn hm htv
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim hα0 hα1 htv
  haveI := hR'
  exact core_tau hφ hκ hK.1 hK.2.1 (hK.2.2.1 R hR') (hK.2.2.2 R hR') hα0 hα1 hδ0 hδ1 hn hm ha hb

theorem sharp_tau_valid {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} {κ D v ρbar δ : ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hK : KernelConsts φ D v ρbar) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsValidThreshold φ n m δ (fun α => tauPs D v ρbar α δ n m) := fun α hα P Q hP hQ htv => by
  haveI := hP; haveI := hQ
  exact sharp_tau_level 𝒳 H φ κ D v ρbar P Q α δ n m hφ hκ hK hα.1 hα.2 hδ0 hδ1 hn hm htv

theorem tauP_valid {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} {κ D v ρbar δ : ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (hK : KernelConsts φ D v ρbar) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsValidThreshold φ n m δ (fun α => tauP D v ρbar α δ n m) := fun α hα P Q hP hQ htv => by
  haveI := hP; haveI := hQ
  exact plugin_level 𝒳 H φ κ D v ρbar P Q α δ n m hφ hκ hK hα.1 hα.2 hδ0 hδ1 hn hm htv

theorem kernelConsts_nonneg {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nonempty 𝒳] {φ : 𝒳 → H} {D v ρbar : ℝ} (hK : KernelConsts φ D v ρbar) : 0 ≤ D ∧ 0 ≤ ρbar := by
  obtain ⟨x0⟩ := ‹Nonempty 𝒳›
  exact ⟨(norm_nonneg _).trans (hK.1 x0 x0), (norm_nonneg _).trans (hK.2.2.2 (Measure.dirac x0) inferInstance x0)⟩

theorem sharp_tau_one_event : Claims.sharp_tau_one_event := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ δ n m hφ hκ hK hδ0 hδ1 hn hm
  haveI : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure P
  obtain ⟨hD0, hρ0⟩ := kernelConsts_nonneg hK
  have hmono := sharp_tau_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  exact oneEvent_of_valid hδ0 hδ1 hn hm hmono.2 hmono.1 (sharp_tau_valid hφ hκ hK hδ0 hδ1 hn hm) P Q

theorem coupled_sharp : Claims.coupled_sharp := by
  intro 𝒳 H _ _ _ _ φ κ D t P Q _ _ α δ n m hφ hκ hD hk hdiag hα0 hα1 hδ0 hδ1 hn hm htv ht0 ht
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim hα0 hα1 htv
  haveI := hR'
  have hu0 : 0 ≤ ‖∫ y, φ y ∂R‖ ^ 2 := by positivity
  have huκ : ‖∫ y, φ y ∂R‖ ^ 2 ≤ κ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_bound (R := R) hκ) 2
  have hiv := (plugin_moments_iv 𝒳 H φ κ R hφ hκ).2 hk hdiag
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  rcases huκ.lt_or_eq with hlt | heq
  · -- the true `u` lies in `[0, κ²)`
    have hv : trCov φ R ≤ (√(κ ^ 2 - ‖∫ y, φ y ∂R‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by linarith), hiv.1]
    have hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ √(κ ^ 2 + ‖∫ y, φ y ∂R‖ ^ 2) := fun x =>
      (le_rhoR (R := R) hκ x).trans (Real.le_sqrt_of_sq_le hiv.2)
    refine (measure_mono fun z hz => ?_).trans
      (core_tau hφ hκ hD (Real.sqrt_nonneg _) hv hρ hα0 hα1 hδ0 hδ1 hn hm ha hb)
    simp only [mem_setOf_eq] at hz ⊢
    exact lt_of_le_of_lt (ht _ ⟨hu0, hlt⟩) hz
  -- `‖μ_R‖² = κ²`
  rcases (sq_nonneg κ).eq_or_lt with hk0 | hkpos
  · -- `κ = 0`: `φ = 0`
    have hφ0 : ∀ x, φ x = 0 := fun x => by
      have := hdiag x
      rw [real_inner_self_eq_norm_sq, ← hk0] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have hD' : ∀ x x', ‖φ x - φ x'‖ ≤ 0 := fun x x' => by simp [hφ0]
    have hempty : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | t < Demp φ z.1 z.2 α} = ∅ := by
      ext z
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (Demp_le_zero hφ hD' hα0 hα1 hn hm z.1 z.2).trans ht0
    rw [hempty, measure_empty]; exact zero_le
  have htr : trCov φ R = 0 := by rw [hiv.1, heq]; ring
  set μR := ∫ y, φ y ∂R
  have hψb : ∀ x, ‖φ x - μR‖ ≤ 2 * κ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])
  by_cases h0 : α = 0
  · -- `α = 0`: `P = Q = R` and `‖A − B‖ = 0` a.s.
    subst h0
    obtain ⟨-, hPR⟩ := ae_density_eq_one ha
    obtain ⟨-, hQR⟩ := ae_density_eq_one hb
    rw [hPR, hQR]
    have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
    have hψm : StronglyMeasurable (fun x => φ x - μR) := hφ.sub stronglyMeasurable_const
    have hψ0 : ∫ x, (φ x - μR) ∂R = 0 := by
      rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
    have hnull := twoDev_null R R hψm hψm hψb hψb hψ0 hψ0 htr htr hn hm
    refine le_of_eq_of_le (measure_mono_null (fun z hz => ?_) hnull) zero_le
    simp only [mem_setOf_eq] at hz ⊢
    exact lt_of_le_of_lt ht0 (hz.trans_le (Demp_zero_le hφ _ hn hm z))
  -- `α > 0`
  have hβ1 := one_le_beta hα0 hα1
  set β := 1 / (1 - α)
  have hβ0 : 0 ≤ β := by linarith
  set g := min5 (fun f => rootR β ((1 - f) * δ) n m) with hg
  obtain ⟨f0, hf0, hgf⟩ := min5_attained (fun f => rootR β ((1 - f) * δ) n m)
  obtain ⟨hf00, hf01⟩ := hf0.bounds
  have hg0 : 0 ≤ g := by rw [hg, hgf]; exact rootR_nonneg _ _ _ _
  -- every `u < κ²` gives `√(κ²+u) g ≤ t`, hence `ρ_R g ≤ t`
  have hut : ∀ u ∈ Ico (0 : ℝ) (κ ^ 2), √(κ ^ 2 + u) * g ≤ t := fun u hu =>
    (tauPs_ge_repair (D := D) (v := √(κ ^ 2 - u)) h0 (Real.sqrt_nonneg _)).trans (ht u hu)
  have hρR0 : 0 ≤ rhoR φ R := rhoR_nonneg (R := R) hκ
  have hρR2 : rhoR φ R ^ 2 ≤ κ ^ 2 + κ ^ 2 := by have := hiv.2; rw [heq] at this; exact this
  have hρg : rhoR φ R * g ≤ t := by
    by_contra hcon
    push_neg at hcon
    have hgpos : 0 < g := by
      rcases hg0.eq_or_lt with h | h
      · rw [← h, mul_zero] at hcon; linarith
      · exact h
    set c := t / g
    have hc0 : 0 ≤ c := div_nonneg ht0 hgpos.le
    have hcr : c < rhoR φ R := by rw [div_lt_iff₀ hgpos]; linarith
    have hc2 : c ^ 2 < κ ^ 2 + κ ^ 2 := lt_of_lt_of_le (pow_lt_pow_left₀ hcr hc0 (by norm_num)) hρR2
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = c ^ 2 - κ ^ 2 := ⟨_, rfl⟩
    obtain ⟨u, hu'⟩ : ∃ u : ℝ, u = (max x 0 + κ ^ 2) / 2 := ⟨_, rfl⟩
    have hmx : max x 0 < κ ^ 2 := max_lt (by linarith) hkpos
    have hu : u ∈ Ico (0 : ℝ) (κ ^ 2) :=
      ⟨by rw [hu']; have := le_max_right x 0; positivity, by rw [hu']; linarith⟩
    have hux : c ^ 2 < κ ^ 2 + u := by rw [hu']; linarith [le_max_left x 0]
    have hcs : c < √(κ ^ 2 + u) := Real.lt_sqrt hc0 |>.2 hux
    have := hut u hu
    have : t < √(κ ^ 2 + u) * g := by rw [← div_lt_iff₀ hgpos]; exact hcs
    linarith
  -- the moments vanish
  have hξm : StronglyMeasurable (fun x => a x • (φ x - μR)) :=
    ha.1.stronglyMeasurable.smul (hφ.sub stronglyMeasurable_const)
  have hζm : StronglyMeasurable (fun x => b x • (φ x - μR)) :=
    hb.1.stronglyMeasurable.smul (hφ.sub stronglyMeasurable_const)
  have hξb : ∀ x, ‖a x • (φ x - μR)‖ ≤ β * (2 * κ) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.2.1 x).1]
    exact mul_le_mul (ha.2.1 x).2 (hψb x) (norm_nonneg _) hβ0
  have hζb : ∀ x, ‖b x • (φ x - μR)‖ ≤ β * (2 * κ) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb.2.1 x).1]
    exact mul_le_mul (hb.2.1 x).2 (hψb x) (norm_nonneg _) hβ0
  have hm1 := plugin_moments_i 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha
  have hm1' := plugin_moments_i 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb
  have hz1 : ∫ x, ‖a x • (φ x - μR)‖ ^ 2 ∂P = 0 :=
    le_antisymm (by have := hm1.2.1; rw [htr, mul_zero] at this; exact this)
      (integral_nonneg fun _ => sq_nonneg _)
  have hz2 : ∫ x, ‖b x • (φ x - μR)‖ ^ 2 ∂Q = 0 :=
    le_antisymm (by have := hm1'.2.1; rw [htr, mul_zero] at this; exact this)
      (integral_nonneg fun _ => sq_nonneg _)
  have h0m : StronglyMeasurable (fun _ : 𝒳 => (0 : H)) := stronglyMeasurable_const
  have h0b : ∀ x : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x‖ ≤ β * (2 * κ) := fun x => by
    simp only [norm_zero]
    have : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
    positivity
  have n1 := twoDev_null P Q hξm hζm hξb hζb hm1.1 hm1'.1 hz1 hz2 hn hm
  have n2 := twoDev_null P Q hξm h0m hξb h0b hm1.1 (by simp) hz1 (by simp) hn hm
  have n3 := twoDev_null P Q h0m hζm h0b hζb (by simp) hm1'.1 (by simp) hz2 hn hm
  have hMnull : sampleLaw P Q n m {z | 0 < Mfun a b φ μR z} = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_union_null (measure_union_null n1 n2) n3)
    simp only [mem_setOf_eq, Mfun, lt_max_iff] at hz
    have e2 : twoDev (fun x => a x • (φ x - μR)) (fun _ : 𝒳 => (0 : H)) z = wMeanDev a φ μR z.1 := by
      simp [twoDev, wMeanDev]
    have e3 : ‖twoDev (fun _ : 𝒳 => (0 : H)) (fun x => b x • (φ x - μR)) z‖ = ‖wMeanDev b φ μR z.2‖ := by
      rw [show twoDev (fun _ : 𝒳 => (0 : H)) (fun x => b x • (φ x - μR)) z = -wMeanDev b φ μR z.2 by
        simp [twoDev, wMeanDev], norm_neg]
    simp only [mem_union, mem_setOf_eq, e2, e3]
    rcases hz with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | t < Demp φ z.1 z.2 α} ⊆
      {z | 0 < Mfun a b φ μR z} ∪ {z | g < Cfun a b z} := by
    intro z hz
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hcon hz
    have hdet := plugin_det 𝒳 H φ κ α P Q R a b n m hφ hκ hα0 hα1 hn hm ha hb z.1 z.2
    have : rhoR φ R * Cfun a b z ≤ rhoR φ R * g := mul_le_mul_of_nonneg_left hcon.2 hρR0
    unfold Mfun at hcon
    unfold Cfun at this
    linarith
  have hrep := repair_part_root (P := P) (Q := Q) (R := R) hα0 hα1 hn hm ha hb
    (show 0 ≤ (1 - f0) * δ by nlinarith) (n := n) (m := m)
  rw [show rootR (1 / (1 - α)) ((1 - f0) * δ) n m = g by rw [hg, hgf]] at hrep
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hMnull, zero_add]
  exact hrep.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

theorem coupled_cpl : Claims.coupled_cpl := by
  intro 𝒳 H _ _ _ _ φ κ D δ n m hφ hκ hD hk hdiag hD0 hδ0 hδ1 hn hm
  have hval : IsValidThreshold φ n m δ (fun α => tauCpl D κ α δ n m) := fun α hα P Q hP hQ htv => by
    haveI := hP; haveI := hQ
    exact coupled_sharp 𝒳 H φ κ D _ P Q α δ n m hφ hκ hD hk hdiag hα.1 hα.2 hδ0 hδ1 hn hm htv
      (tauCpl_nonneg _ _ _ _ _ _) fun u hu => le_tauCpl hD0 hα.1 hα.2 hδ0 hδ1 hn hm hu
  have hmono := tauCpl_monotone (κ := κ) hD0 hδ0 hδ1 hn hm
  have hnn : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauCpl D κ α δ n m := fun _ _ => tauCpl_nonneg _ _ _ _ _ _
  exact ⟨hval, hmono, hnn, fun P Q hP hQ => by
    haveI := hP; haveI := hQ; exact oneEvent_of_valid hδ0 hδ1 hn hm hnn hmono hval P Q⟩

theorem coupled_grid_level : Claims.coupled_grid_level := by
  intro 𝒳 H _ _ _ _ φ κ D J lo hi v ρ P Q _ _ α δ n m hφ hκ hD hk hdiag hcov hcell hα0 hα1 hδ0 hδ1 hn hm htv
  obtain ⟨R, a, b, hR', ha, hb⟩ := exists_common_trim hα0 hα1 htv
  haveI := hR'
  have hu0 : 0 ≤ ‖∫ y, φ y ∂R‖ ^ 2 := by positivity
  have huκ : ‖∫ y, φ y ∂R‖ ^ 2 ≤ κ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_bound (R := R) hκ) 2
  obtain ⟨j, hj, hlo, hhi⟩ := hcov _ ⟨hu0, huκ⟩
  obtain ⟨hv0, hvlo, hρhi⟩ := hcell j hj
  have hiv4 := plugin_moments_iv 𝒳 H φ κ R hφ hκ
  have hiv := hiv4.2 hk hdiag
  have hv : trCov φ R ≤ v j ^ 2 := by rw [hiv.1]; linarith
  have hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρ j := fun x => by
    refine le_trans (le_min ?_ ?_) hρhi
    · exact (le_rhoR (R := R) hκ x).trans (Real.le_sqrt_of_sq_le (hiv.2.trans (by linarith)))
    · exact (le_rhoR (R := R) hκ x).trans (hiv4.1 D hD).1
  refine (measure_mono fun z hz => ?_).trans (core_tau hφ hκ hD hv0 hv hρ hα0 hα1 hδ0 hδ1 hn hm ha hb)
  simp only [mem_setOf_eq] at hz ⊢
  exact lt_of_le_of_lt (le_tauGrid hj α δ n m) hz

theorem grid_valid {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : 𝒳 → H} {κ D : ℝ} {J : ℕ} {lo hi v ρ : ℕ → ℝ} {δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D)
    (hk : ∀ x y, 0 ≤ ⟪φ x, φ y⟫_ℝ) (hdiag : ∀ x, ⟪φ x, φ x⟫_ℝ = κ ^ 2)
    (hcov : ∀ u ∈ Icc (0 : ℝ) (κ ^ 2), ∃ j < J, lo j ≤ u ∧ u ≤ hi j)
    (hcell : ∀ j < J, 0 ≤ v j ∧ κ ^ 2 - lo j ≤ v j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρ j)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsValidThreshold φ n m δ (fun α => tauGrid D v ρ J α δ n m) := fun α hα P Q hP hQ htv => by
  haveI := hP; haveI := hQ
  exact coupled_grid_level 𝒳 H φ κ D J lo hi v ρ P Q α δ n m hφ hκ hD hk hdiag hcov hcell hα.1 hα.2 hδ0 hδ1 hn
    hm htv

theorem grid_vρ_nonneg {D κ : ℝ} {J : ℕ} {lo hi v ρ : ℕ → ℝ} (hD0 : 0 ≤ D)
    (hcell : ∀ j < J, 0 ≤ v j ∧ κ ^ 2 - lo j ≤ v j ^ 2 ∧ min (√(κ ^ 2 + hi j)) D ≤ ρ j) :
    ∀ j < J, 0 ≤ v j ∧ 0 ≤ ρ j := fun j hj =>
  ⟨(hcell j hj).1, (le_min (Real.sqrt_nonneg _) hD0).trans (hcell j hj).2.2⟩

theorem coupled_grid_one_event : Claims.coupled_grid_one_event := by
  refine ⟨fun D J v ρ δ n m hD hvρ hδ0 hδ1 hn hm => tauGrid_monotone hD hvρ hδ0 hδ1 hn hm, ?_⟩
  intro 𝒳 H _ _ _ _ φ κ D J lo hi v ρ P Q _ _ δ n m hφ hκ hD hk hdiag hcov hcell hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x0 x0)
  have hmono := tauGrid_monotone hD0 (grid_vρ_nonneg hD0 hcell) hδ0 hδ1 hn hm (J := J)
  exact oneEvent_of_valid hδ0 hδ1 hn hm hmono.2 hmono.1
    (grid_valid hφ hκ hD hk hdiag hcov hcell hδ0 hδ1 hn hm) P Q

theorem corollary_C : Claims.corollary_C := by
  intro 𝒳 H _ _ _ _ _ φ κ D v ρbar τA δ n m hφ hκ hK hδ0 hδ1 hn hm hA0 hAm hAv
  obtain ⟨hD0, hρ0⟩ := kernelConsts_nonneg hK
  have hmP := plugin_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  have hmPs := sharp_tau_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  have hval := valid_min hAv (valid_min (tauP_valid hφ hκ hK hδ0 hδ1 hn hm) (sharp_tau_valid hφ hκ hK hδ0 hδ1 hn hm))
  have hmono := mono_min hAm (mono_min hmP.1 hmPs.1)
  have hnn : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m) (tauPs D v ρbar α δ n m)) :=
    fun α hα => le_min (hA0 α hα) (le_min (hmP.2 α hα) (hmPs.2 α hα))
  exact ⟨hval, hmono, hnn, fun P Q hP hQ => by
    haveI := hP; haveI := hQ; exact oneEvent_of_valid hδ0 hδ1 hn hm hnn hmono hval P Q⟩

theorem corollary_C_coupled : Claims.corollary_C_coupled := by
  intro 𝒳 H _ _ _ _ _ φ κ D v ρbar τA δ n m hφ hκ hK hk hdiag hδ0 hδ1 hn hm hA0 hAm hAv
  obtain ⟨hD0, hρ0⟩ := kernelConsts_nonneg hK
  have hmP := plugin_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  have hmPs := sharp_tau_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  obtain ⟨hvC, hmC, hnC, -⟩ := coupled_cpl 𝒳 H φ κ D δ n m hφ hκ hK.1 hk hdiag hD0 hδ0 hδ1 hn hm
  have hval := valid_min hAv (valid_min (tauP_valid hφ hκ hK hδ0 hδ1 hn hm)
    (valid_min (sharp_tau_valid hφ hκ hK hδ0 hδ1 hn hm) hvC))
  have hmono := mono_min hAm (mono_min hmP.1 (mono_min hmPs.1 hmC))
  have hnn : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m)
      (min (tauPs D v ρbar α δ n m) (tauCpl D κ α δ n m))) :=
    fun α hα => le_min (hA0 α hα) (le_min (hmP.2 α hα) (le_min (hmPs.2 α hα) (hnC α hα)))
  exact ⟨hval, hmono, hnn, fun P Q hP hQ => by
    haveI := hP; haveI := hQ; exact oneEvent_of_valid hδ0 hδ1 hn hm hnn hmono hval P Q⟩

theorem corollary_C_grid : Claims.corollary_C_grid := by
  intro 𝒳 H _ _ _ _ _ φ κ D v ρbar J lo hi vg ρg τA δ n m hφ hκ hK hk hdiag hcov hcell hδ0 hδ1 hn hm hA0 hAm hAv
  obtain ⟨hD0, hρ0⟩ := kernelConsts_nonneg hK
  have hmP := plugin_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  have hmPs := sharp_tau_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
  have hmG := tauGrid_monotone hD0 (grid_vρ_nonneg hD0 hcell) hδ0 hδ1 hn hm (J := J)
  have hval := valid_min hAv (valid_min (tauP_valid hφ hκ hK hδ0 hδ1 hn hm)
    (valid_min (sharp_tau_valid hφ hκ hK hδ0 hδ1 hn hm) (grid_valid hφ hκ hK.1 hk hdiag hcov hcell hδ0 hδ1 hn hm)))
  have hmono := mono_min hAm (mono_min hmP.1 (mono_min hmPs.1 hmG.1))
  have hnn : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ min (τA α) (min (tauP D v ρbar α δ n m)
      (min (tauPs D v ρbar α δ n m) (tauGrid D vg ρg J α δ n m))) :=
    fun α hα => le_min (hA0 α hα) (le_min (hmP.2 α hα) (le_min (hmPs.2 α hα) (hmG.2 α hα)))
  exact ⟨hval, hmono, hnn, fun P Q hP hQ => by
    haveI := hP; haveI := hQ; exact oneEvent_of_valid hδ0 hδ1 hn hm hnn hmono hval P Q⟩

end StatFormal.Wave30ts
