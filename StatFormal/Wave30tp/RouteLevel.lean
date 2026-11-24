import StatFormal.Wave30tp.RouteDet
import StatFormal.Wave30tp.RouteBernstein2

/-!
# Route: NOTE Theorem P (closed form), its monotonicity, Lemma 1 and the corollaries

Untrusted proof material.

* `level_core`: the level bound for a **fixed** common trimming `R = a·P = b·Q` with `tr Cov_R ≤ v²` and
  `‖φ − μ_R‖ ≤ ρ̄` for this `R` only (so it also gives the coupled-constants version).
  - `α = 0`: `a = 1` a.e., `P = Q = R`; uniform weights give `D̂_0 ≤ ‖A − B‖` for every sample; one two-sample
    McDiarmid event at `δ` (`twoDev_tail`, `L = log(1/δ)`).
  - `α > 0`: Lemma P0; three two-sample McDiarmid events (`‖A − B‖`, `‖A‖`, `‖B‖`) and three one-sided Bernstein events
    (`1 − S_X`, `1 − S_Y`, their sum), each at `e^{−L} = δ/6`, `L = log(6/δ)`; union bound.
* Theorem P: `eq:tvintersect` (certified `ZeroSet.tvintersect`) supplies `R`.
* Lemma 1: nested regions (`α ↦ D̂_α` nonincreasing), `toMeasurable` of the rejection set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.Wave30tp

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang

/-! ### Lemma 1 -/

theorem Demp_antitoneOn {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : 𝒳 → H) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    AntitoneOn (Demp φ x y) (Ico 0 1) := by
  intro α hα α' hα' hle
  haveI := isProbabilityMeasure_empirical (by omega : n ≠ 0) x
  haveI := isProbabilityMeasure_empirical (by omega : m ≠ 0) y
  exact StatFormal.WaveP1a.setDist_anti (region_nonempty (φ := φ) _ hα.1 hα.2)
    (region_nonempty (φ := φ) _ hα.1 hα.2) (StatFormal.WaveP1a.region_mono hα'.2 hle)
    (StatFormal.WaveP1a.region_mono hα'.2 hle)

theorem monotone_event : Claims.monotone_event := by
  intro 𝒳 H _ _ _ φ τ δ n m P Q _ _ hδ0 hn hm _hτ0 hτmono hlevel htv
  set αs := StatFormal.Distances.tvDist P Q with hαs
  have hαs0 : 0 ≤ αs := StatFormal.Distances.tvDist_nonneg P Q
  have hmem : αs ∈ Ico (0 : ℝ) 1 := ⟨hαs0, htv⟩
  have hlev := hlevel αs hmem P Q inferInstance inferInstance le_rfl
  set μ := sampleLaw P Q n m
  set Bad := {z : (Fin n → 𝒳) × (Fin m → 𝒳) | τ αs < Demp φ z.1 z.2 αs}
  refine ⟨⟨(toMeasurable μ Bad)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩, fun z hz => ?_⟩
  · rw [prob_compl_eq_one_sub (measurableSet_toMeasurable _ _), measure_toMeasurable]
    calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_sub _ hδ0, ENNReal.ofReal_one]
      _ ≤ 1 - μ Bad := tsub_le_tsub_left hlev _
  · intro z hz
    have : z ∉ Bad := fun h => hz (subset_toMeasurable _ _ h)
    simpa [Bad, not_lt] using this
  · have hanti := Demp_antitoneOn φ hn hm z.1 z.2
    have hall : ∀ α ∈ Ico αs 1, Demp φ z.1 z.2 α ≤ τ α := fun α hα =>
      (hanti hmem ⟨hαs0.trans hα.1, hα.2⟩ hα.1).trans
        (hz.trans (hτmono hmem ⟨hαs0.trans hα.1, hα.2⟩ hα.1))
    refine ⟨hall, ?_, ?_, ?_⟩
    · exact csInf_le ⟨0, fun α hα => hα.1.1⟩ ⟨hmem, hz⟩
    · intro α hα hrej
      by_contra hc
      push_neg at hc
      exact absurd (hall α ⟨hc, hα.2⟩) (not_le.2 hrej)
    · intro G hG b hb
      by_contra hc
      push_neg at hc
      exact absurd (hall b ⟨hc, (hG hb.1.1).2⟩) (not_le.2 hb.1.2)

/-! ### Monotonicity of `τ_P` -/

theorem sNM_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < sNM n m := by
  have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  unfold sNM; positivity

theorem cNM_pos {n m : ℕ} (hn : 1 ≤ n) : 0 < cNM n m := by
  have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  exact lt_max_of_lt_left (by positivity)

theorem log_six_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Real.log (6 / δ) :=
  Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)

theorem log_inv_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 ≤ Real.log (1 / δ) :=
  Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)

theorem log_inv_le_log_six {δ : ℝ} (hδ0 : 0 < δ) : Real.log (1 / δ) ≤ Real.log (6 / δ) :=
  Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hδ0.le)

theorem T2_nonneg {α δ : ℝ} {n m : ℕ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 ≤ T2 α δ n m :=
  add_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg (cNM_pos hn).le (log_six_pos hδ0 hδ1).le) (by norm_num))

theorem T1_nonneg {D v α δ : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hα1 : α < 1) (hδ0 : 0 < δ) :
    0 ≤ T1 D v α δ n m := by
  have : 0 < 1 - α := by linarith
  exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (by positivity) hD) (Real.sqrt_nonneg _))

theorem beta_mono {α α' : ℝ} (hα'1 : α' < 1) (hle : α ≤ α') : 1 / (1 - α) ≤ 1 / (1 - α') :=
  one_div_le_one_div_of_le (by linarith) (by linarith)

theorem plugin_monotone : Claims.plugin_monotone := by
  intro D v ρbar δ n m hD hv hρ hδ0 hδ1 hn hm
  have hs := sNM_pos hn hm
  have hL := log_six_pos hδ0 hδ1
  have hL1 := log_inv_nonneg hδ0 hδ1
  have hLL := log_inv_le_log_six hδ0
  have hτ0 : ∀ α ∈ Ico (0 : ℝ) 1, 0 ≤ tauP D v ρbar α δ n m := fun α hα => by
    unfold tauP
    split_ifs
    · exact add_nonneg (mul_nonneg hv (Real.sqrt_nonneg _)) (mul_nonneg hD (Real.sqrt_nonneg _))
    · exact add_nonneg (T1_nonneg hD hα.2 hδ0) (mul_nonneg hρ (T2_nonneg hn hδ0 hδ1))
  refine ⟨fun α hα α' hα' hle => ?_, hτ0⟩
  have hβ := beta_mono hα'.2 hle
  have hβ1 : 1 ≤ 1 / (1 - α) := one_le_beta hα.1 hα.2
  by_cases h0 : α = 0
  · by_cases h0' : α' = 0
    · subst h0; subst h0'; exact le_rfl
    · simp only [tauP, h0, h0', if_true, if_false]
      have hβ1' : 1 ≤ 1 / (1 - α') := one_le_beta hα'.1 hα'.2
      have e1 : v * √(sNM n m) ≤ √(1 / (1 - α') * v ^ 2 * sNM n m) := by
        have hvs : v * √(sNM n m) = √(v ^ 2 * sNM n m) := by
          rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
        rw [hvs]
        refine Real.sqrt_le_sqrt ?_
        have h0 : 0 ≤ v ^ 2 * sNM n m := by positivity
        calc v ^ 2 * sNM n m = 1 * (v ^ 2 * sNM n m) := (one_mul _).symm
          _ ≤ 1 / (1 - α') * (v ^ 2 * sNM n m) := mul_le_mul_of_nonneg_right hβ1' h0
          _ = 1 / (1 - α') * v ^ 2 * sNM n m := by ring
      have e2 : D * √(sNM n m * Real.log (1 / δ) / 2) ≤
          1 / (1 - α') * D * √(sNM n m * Real.log (6 / δ) / 2) := by
        have : √(sNM n m * Real.log (1 / δ) / 2) ≤ √(sNM n m * Real.log (6 / δ) / 2) :=
          Real.sqrt_le_sqrt (by gcongr)
        calc D * √(sNM n m * Real.log (1 / δ) / 2) ≤ D * √(sNM n m * Real.log (6 / δ) / 2) :=
              mul_le_mul_of_nonneg_left this hD
          _ ≤ 1 / (1 - α') * D * √(sNM n m * Real.log (6 / δ) / 2) := by
              rw [mul_assoc]
              exact le_mul_of_one_le_left (mul_nonneg hD (Real.sqrt_nonneg _)) hβ1'
      have e3 : 0 ≤ ρbar * T2 α' δ n m := mul_nonneg hρ (T2_nonneg hn hδ0 hδ1)
      unfold T1
      linarith
  · have h0' : α' ≠ 0 := fun h => h0 (le_antisymm (h ▸ hle) hα.1)
    simp only [tauP, h0, h0', if_false]
    have e1 : T1 D v α δ n m ≤ T1 D v α' δ n m := by
      unfold T1
      have : 0 ≤ v ^ 2 * sNM n m := by positivity
      gcongr
    have e2 : T2 α δ n m ≤ T2 α' δ n m := by
      unfold T2
      gcongr
    have := mul_le_mul_of_nonneg_left e2 hρ
    linarith

/-! ### The level bound for a fixed common trimming -/

section Core

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem twoDev_avg_eq {φ : 𝒳 → H} (c : H) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    twoDev (fun x => φ x - c) (fun x => φ x - c) z =
      ∑ i, (n : ℝ)⁻¹ • φ (z.1 i) - ∑ j, (m : ℝ)⁻¹ • φ (z.2 j) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hsn : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hsm : ∑ _j : Fin m, (m : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have h1 := sum_smul_sub_eq _ hsn (fun i => φ (z.1 i)) c
  have h2 := sum_smul_sub_eq _ hsm (fun j => φ (z.2 j)) c
  simp only [twoDev, Finset.smul_sum]
  rw [← h1, ← h2]; abel

theorem Demp_zero_le {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (c : H) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (z : (Fin n → 𝒳) × (Fin m → 𝒳)) :
    Demp φ z.1 z.2 0 ≤ ‖twoDev (fun x => φ x - c) (fun x => φ x - c) z‖ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hwx : (fun _ : Fin n => (n : ℝ)⁻¹) ∈ capped n 0 := by
    refine ⟨fun i => ⟨by positivity, by simp [cap]⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hwy : (fun _ : Fin m => (m : ℝ)⁻¹) ∈ capped m 0 := by
    refine ⟨fun i => ⟨by positivity, by simp [cap]⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hX := polytope_mem_region hφ le_rfl zero_lt_one hn z.1 hwx
  have hY := polytope_mem_region hφ le_rfl zero_lt_one hm z.2 hwy
  rw [twoDev_avg_eq c hn hm z]
  exact setDist_le_norm hX hY

theorem integral_one_sub_sq_le {P R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    {α : ℝ} {a : 𝒳 → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (ha : IsDensityLe R P α a) :
    ∫ x, (1 - a x) ^ 2 ∂P ≤ 1 / (1 - α) - 1 := by
  set β := 1 / (1 - α)
  have h1 := integral_density_eq_one ha
  obtain ⟨ham, hab, -⟩ := ha
  have hai : Integrable a P := Integrable.of_bound ham.aestronglyMeasurable β
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hab x).1]; exact (hab x).2)
  have hsq : Integrable (fun x => (1 - a x) ^ 2) P :=
    Integrable.of_bound ((measurable_const.sub ham).pow_const 2).aestronglyMeasurable ((1 + β) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_le.2 ⟨by linarith [(hab x).2], by linarith [(hab x).1, (hab x).2]⟩) 2)
  have hpt : ∀ x, (1 - a x) ^ 2 ≤ 1 - 2 * a x + β * a x := fun x => by
    nlinarith [(hab x).1, (hab x).2]
  have jv1 : Integrable (fun x => 1 - 2 * a x) P := (integrable_const 1).sub (hai.const_mul 2)
  have jv : Integrable (fun x => 1 - 2 * a x + β * a x) P := jv1.add (hai.const_mul β)
  have := integral_mono hsq jv hpt
  rw [integral_add jv1 (hai.const_mul β), integral_sub (integrable_const 1) (hai.const_mul 2),
    integral_const_mul, integral_const_mul, h1] at this
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at this
  linarith

theorem exp_neg_log_six {δ : ℝ} (hδ0 : 0 < δ) : Real.exp (-Real.log (6 / δ)) = δ / 6 := by
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

theorem ofReal_six {δ : ℝ} (hδ0 : 0 < δ) :
    ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) +
      ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) = ENNReal.ofReal δ := by
  have h : (0 : ℝ) ≤ δ / 6 := by positivity
  rw [← ENNReal.ofReal_add h h, ← ENNReal.ofReal_add (by positivity) h, ← ENNReal.ofReal_add (by positivity) h,
    ← ENNReal.ofReal_add (by positivity) h, ← ENNReal.ofReal_add (by positivity) h]
  congr 1; ring

/-- `α = 0`: `P = Q = R` and one McDiarmid event at `δ`. -/
theorem level_zero {φ : 𝒳 → H} {κ D v ρbar : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv0 : 0 ≤ v)
    (hv : trCov φ R ≤ v ^ 2) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P 0 a) (hb : IsDensityLe R Q 0 b) :
    sampleLaw P Q n m {z | tauP D v ρbar 0 δ n m < Demp φ z.1 z.2 0} ≤ ENNReal.ofReal δ := by
  obtain ⟨-, hPR⟩ := ae_density_eq_one ha
  obtain ⟨-, hQR⟩ := ae_density_eq_one hb
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P; exact (norm_nonneg _).trans (hκ x)
  have hD0 : 0 ≤ D := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P; exact (norm_nonneg _).trans (hD x x)
  have hψb : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ 2 * κ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])
  have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
  have hψm : StronglyMeasurable (fun x => φ x - ∫ y, φ y ∂R) := hφ.sub stronglyMeasurable_const
  have hψ0 : ∫ x, (φ x - ∫ y, φ y ∂R) ∂R = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  have hψd : ∀ x x', ‖(φ x - ∫ y, φ y ∂R) - (φ x' - ∫ y, φ y ∂R)‖ ≤ D := fun x x' => by
    rw [sub_sub_sub_cancel_right]; exact hD x x'
  have hL := log_inv_nonneg hδ0 hδ1
  have htail := twoDev_tail R R hψm hψm hψb hψb hψ0 hψ0 hv hv hD0 hD0 hψd hψd hn hm hL
  have hthr : √(v ^ 2 / n + v ^ 2 / m) + √((D ^ 2 / n + D ^ 2 / m) * Real.log (1 / δ) / 2) =
      tauP D v ρbar 0 δ n m := by
    simp only [tauP, if_true, sNM]
    congr 1
    · rw [show v ^ 2 / n + v ^ 2 / m = v ^ 2 * (1 / n + 1 / m) by ring, Real.sqrt_mul (sq_nonneg v),
        Real.sqrt_sq hv0]
    · rw [show (D ^ 2 / n + D ^ 2 / m) * Real.log (1 / δ) / 2 =
          D ^ 2 * ((1 / n + 1 / m) * Real.log (1 / δ) / 2) by ring, Real.sqrt_mul (sq_nonneg D),
        Real.sqrt_sq hD0]
  rw [hthr, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at htail
  rw [hPR, hQR]
  refine (measure_mono fun z hz => ?_).trans htail
  simp only [Set.mem_setOf_eq] at hz ⊢
  exact hz.trans_le (Demp_zero_le hφ _ hn hm z)

theorem T1_eq {D v α δ : ℝ} {n m : ℕ} (hD0 : 0 ≤ D) (hα1 : α < 1) :
    √(1 / (1 - α) * v ^ 2 / n + 1 / (1 - α) * v ^ 2 / m) +
      √(((1 / (1 - α) * D) ^ 2 / n + (1 / (1 - α) * D) ^ 2 / m) * Real.log (6 / δ) / 2) =
      T1 D v α δ n m := by
  have hβD : 0 ≤ 1 / (1 - α) * D := mul_nonneg (div_nonneg zero_le_one (by linarith)) hD0
  simp only [T1, sNM]
  congr 1
  · congr 1; ring
  · rw [show ((1 / (1 - α) * D) ^ 2 / n + (1 / (1 - α) * D) ^ 2 / m) * Real.log (6 / δ) / 2 =
        (1 / (1 - α) * D) ^ 2 * ((1 / n + 1 / m) * Real.log (6 / δ) / 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβD]

/-- The three Hilbert-space events of Theorem P, each at `δ/6`. -/
theorem hilbert_events {φ : 𝒳 → H} {κ D v : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D)
    (hv : trCov φ R ≤ v ^ 2) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) :
    sampleLaw P Q n m {z | T1 D v α δ n m <
        ‖wMeanDev a φ (∫ y, φ y ∂R) z.1 - wMeanDev b φ (∫ y, φ y ∂R) z.2‖} ≤ ENNReal.ofReal (δ / 6) ∧
      sampleLaw P Q n m {z | T1 D v α δ n m < ‖wMeanDev a φ (∫ y, φ y ∂R) z.1‖} ≤ ENNReal.ofReal (δ / 6) ∧
      sampleLaw P Q n m {z | T1 D v α δ n m < ‖wMeanDev b φ (∫ y, φ y ∂R) z.2‖} ≤
        ENNReal.ofReal (δ / 6) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P; exact (norm_nonneg _).trans (hκ x)
  have hD0 : 0 ≤ D := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P; exact (norm_nonneg _).trans (hD x x)
  have hβ0 : 0 ≤ 1 / (1 - α) := div_nonneg zero_le_one (by linarith)
  have hβD : 0 ≤ 1 / (1 - α) * D := mul_nonneg hβ0 hD0
  have hL := log_six_pos hδ0 hδ1
  have hψb : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ 2 * κ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])
  have hξm : StronglyMeasurable (fun x => a x • (φ x - ∫ y, φ y ∂R)) :=
    ha.1.stronglyMeasurable.smul (hφ.sub stronglyMeasurable_const)
  have hζm : StronglyMeasurable (fun x => b x • (φ x - ∫ y, φ y ∂R)) :=
    hb.1.stronglyMeasurable.smul (hφ.sub stronglyMeasurable_const)
  have hξb : ∀ x, ‖a x • (φ x - ∫ y, φ y ∂R)‖ ≤ 1 / (1 - α) * (2 * κ) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.2.1 x).1]
    exact mul_le_mul (ha.2.1 x).2 (hψb x) (norm_nonneg _) hβ0
  have hζb : ∀ x, ‖b x • (φ x - ∫ y, φ y ∂R)‖ ≤ 1 / (1 - α) * (2 * κ) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb.2.1 x).1]
    exact mul_le_mul (hb.2.1 x).2 (hψb x) (norm_nonneg _) hβ0
  have hm1 := plugin_moments_i 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha
  have hm1' := plugin_moments_i 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb
  have hm2 := (plugin_moments_ii 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha).2 D hD
  have hm2' := (plugin_moments_ii 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb).2 D hD
  have hξ2 := hm1.2.1.trans (mul_le_mul_of_nonneg_left hv hβ0)
  have hζ2 := hm1'.2.1.trans (mul_le_mul_of_nonneg_left hv hβ0)
  have h0m : StronglyMeasurable (fun _ : 𝒳 => (0 : H)) := stronglyMeasurable_const
  have h0b : ∀ x : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x‖ ≤ 1 / (1 - α) * (2 * κ) := fun x => by
    simp only [norm_zero]; positivity
  have h00P : ∫ x, (fun _ : 𝒳 => (0 : H)) x ∂P = 0 := by simp
  have h00Q : ∫ x, (fun _ : 𝒳 => (0 : H)) x ∂Q = 0 := by simp
  have h02P : ∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂P ≤ 0 := by simp
  have h02Q : ∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂Q ≤ 0 := by simp
  have h0d : ∀ x x' : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x - (fun _ : 𝒳 => (0 : H)) x'‖ ≤ 0 := by simp
  have tE1 := twoDev_tail P Q hξm hζm hξb hζb hm1.1 hm1'.1 hξ2 hζ2 hβD hβD hm2 hm2' hn hm hL.le
  have tE2 := twoDev_tail P Q hξm h0m hξb h0b hm1.1 h00Q hξ2 h02Q hβD le_rfl hm2 h0d hn hm hL.le
  have tE3 := twoDev_tail P Q h0m hζm h0b hζb h00P hm1'.1 h02P hζ2 le_rfl hβD h0d hm2' hn hm hL.le
  rw [exp_neg_log_six hδ0] at tE1 tE2 tE3
  have thr := T1_eq (v := v) (δ := δ) (n := n) (m := m) hD0 hα1
  refine ⟨?_, ?_, ?_⟩
  · refine (measure_mono fun z hz => ?_).trans tE1
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [thr]; exact hz
  · refine (measure_mono fun z hz => ?_).trans tE2
    simp only [Set.mem_setOf_eq] at hz ⊢
    have e : twoDev (fun x => a x • (φ x - ∫ y, φ y ∂R)) (fun _ : 𝒳 => (0 : H)) z =
        wMeanDev a φ (∫ y, φ y ∂R) z.1 := by simp [twoDev, wMeanDev]
    rw [e]
    refine lt_of_le_of_lt ?_ hz
    rw [← thr]
    refine add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
    · have : (0 : ℝ) ≤ 1 / (1 - α) * v ^ 2 / m := by positivity
      simp only [zero_div, add_zero]; linarith
    · have : (0 : ℝ) ≤ (1 / (1 - α) * D) ^ 2 / m := by positivity
      have hL' : 0 ≤ Real.log (6 / δ) / 2 := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero]
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hL'
  · refine (measure_mono fun z hz => ?_).trans tE3
    simp only [Set.mem_setOf_eq] at hz ⊢
    have e : twoDev (fun _ : 𝒳 => (0 : H)) (fun x => b x • (φ x - ∫ y, φ y ∂R)) z =
        -wMeanDev b φ (∫ y, φ y ∂R) z.2 := by simp [twoDev, wMeanDev]
    rw [e, norm_neg]
    refine lt_of_le_of_lt ?_ hz
    rw [← thr]
    refine add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
    · have : (0 : ℝ) ≤ 1 / (1 - α) * v ^ 2 / n := by positivity
      simp only [zero_div, zero_add]; linarith
    · have : (0 : ℝ) ≤ (1 / (1 - α) * D) ^ 2 / n := by positivity
      have hL' : 0 ≤ Real.log (6 / δ) / 2 := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_add]
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hL'

theorem one_sub_wMass {𝒳' : Type*} {a : 𝒳' → ℝ} {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝒳') :
    1 - wMass a x = ∑ i, (1 - a (x i)) / n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  simp only [wMass, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- The three repair events of Theorem P (`α > 0`), each at `δ/6`. -/
theorem repair_events {P Q R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α δ : ℝ} {n m : ℕ} (hα0 : 0 ≤ α) (hα1 : α < 1) (h0 : α ≠ 0)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : IsDensityLe R P α a)
    (hb : IsDensityLe R Q α b) :
    sampleLaw P Q n m {z | T2 α δ n m ≤ 1 - wMass a z.1} ≤ ENNReal.ofReal (δ / 6) ∧
      sampleLaw P Q n m {z | T2 α δ n m ≤ 1 - wMass b z.2} ≤ ENNReal.ofReal (δ / 6) ∧
      sampleLaw P Q n m {z | T2 α δ n m ≤ (1 - wMass a z.1) + (1 - wMass b z.2)} ≤
        ENNReal.ofReal (δ / 6) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hβ1 : 1 < 1 / (1 - α) := by
    rw [lt_div_iff₀ (by linarith)]
    have : 0 < α := lt_of_le_of_ne hα0 (Ne.symm h0)
    linarith
  have hL := log_six_pos hδ0 hδ1
  have hs := sNM_pos hn hm
  have hc := cNM_pos (m := m) hn
  have hab := ha.2.1
  have hbb := hb.2.1
  have hW1m : Measurable fun x => (1 - a x) / n := (measurable_const.sub ha.1).div_const _
  have hW2m : Measurable fun y => (1 - b y) / m := (measurable_const.sub hb.1).div_const _
  have hW1b : ∀ x, |(1 - a x) / n| ≤ 1 / (1 - α) := fun x => by
    rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have : |1 - a x| ≤ 1 / (1 - α) := abs_le.2 ⟨by linarith [(hab x).2], by linarith [(hab x).1]⟩
    nlinarith [abs_nonneg (1 - a x), (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
  have hW2b : ∀ x, |(1 - b x) / m| ≤ 1 / (1 - α) := fun x => by
    rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
    have : |1 - b x| ≤ 1 / (1 - α) := abs_le.2 ⟨by linarith [(hbb x).2], by linarith [(hbb x).1]⟩
    nlinarith [abs_nonneg (1 - b x), (show (1 : ℝ) ≤ m by exact_mod_cast hm)]
  have h0W : ∀ x : 𝒳, |(fun _ : 𝒳 => (0 : ℝ)) x| ≤ 1 / (1 - α) := fun x => by simp; linarith
  have hm3 := plugin_moments_iii 𝒳 α P R a hα0 hα1 ha
  have hm3' := plugin_moments_iii 𝒳 α Q R b hα0 hα1 hb
  have hW10 : ∫ x, (1 - a x) / n ∂P = 0 := by rw [integral_div, hm3.1, zero_div]
  have hW20 : ∫ x, (1 - b x) / m ∂Q = 0 := by rw [integral_div, hm3'.1, zero_div]
  have hW1c : ∀ x, (1 - a x) / n ≤ cNM n m := fun x => by
    refine le_trans ?_ (le_max_left _ _)
    rw [div_le_div_iff_of_pos_right hnpos]; linarith [(hab x).1]
  have hW2c : ∀ x, (1 - b x) / m ≤ cNM n m := fun x => by
    refine le_trans ?_ (le_max_right _ _)
    rw [div_le_div_iff_of_pos_right hmpos]; linarith [(hbb x).1]
  have h0c : ∀ x : 𝒳, (fun _ : 𝒳 => (0 : ℝ)) x ≤ cNM n m := fun _ => hc.le
  have hV0 : 0 < (1 / (1 - α) - 1) * sNM n m := mul_pos (by linarith) hs
  have hvar1 : n * ∫ x, ((1 - a x) / n) ^ 2 ∂P ≤ (1 / (1 - α) - 1) / n := by
    have e : ∫ x, ((1 - a x) / n) ^ 2 ∂P = (∫ x, (1 - a x) ^ 2 ∂P) / (n : ℝ) ^ 2 := by
      simp only [div_pow]; rw [integral_div]
    rw [e, show (n : ℝ) * ((∫ x, (1 - a x) ^ 2 ∂P) / (n : ℝ) ^ 2) = (∫ x, (1 - a x) ^ 2 ∂P) / n by
      field_simp]
    exact div_le_div_of_nonneg_right (integral_one_sub_sq_le hα0 hα1 ha) hnpos.le
  have hvar2 : m * ∫ x, ((1 - b x) / m) ^ 2 ∂Q ≤ (1 / (1 - α) - 1) / m := by
    have e : ∫ x, ((1 - b x) / m) ^ 2 ∂Q = (∫ x, (1 - b x) ^ 2 ∂Q) / (m : ℝ) ^ 2 := by
      simp only [div_pow]; rw [integral_div]
    rw [e, show (m : ℝ) * ((∫ x, (1 - b x) ^ 2 ∂Q) / (m : ℝ) ^ 2) = (∫ x, (1 - b x) ^ 2 ∂Q) / m by
      field_simp]
    exact div_le_div_of_nonneg_right (integral_one_sub_sq_le hα0 hα1 hb) hmpos.le
  have hβm1 : 0 ≤ 1 / (1 - α) - 1 := by linarith
  have hsn : (1 : ℝ) / n ≤ sNM n m := by
    rw [sNM]; have : (0 : ℝ) ≤ 1 / m := by positivity
    linarith
  have hsm : (1 : ℝ) / m ≤ sNM n m := by
    rw [sNM]; have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hV1 : n * ∫ x, ((1 - a x) / n) ^ 2 ∂P + m * ∫ x, (fun _ : 𝒳 => (0 : ℝ)) x ^ 2 ∂Q ≤
      (1 / (1 - α) - 1) * sNM n m := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, mul_zero, add_zero]
    refine hvar1.trans ?_
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsn hβm1
  have hV2 : n * ∫ x, (fun _ : 𝒳 => (0 : ℝ)) x ^ 2 ∂P + m * ∫ x, ((1 - b x) / m) ^ 2 ∂Q ≤
      (1 / (1 - α) - 1) * sNM n m := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, mul_zero, zero_add]
    refine hvar2.trans ?_
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsm hβm1
  have hV3 : n * ∫ x, ((1 - a x) / n) ^ 2 ∂P + m * ∫ x, ((1 - b x) / m) ^ 2 ∂Q ≤
      (1 / (1 - α) - 1) * sNM n m := by
    refine (add_le_add hvar1 hvar2).trans (le_of_eq ?_)
    rw [sNM]; ring
  have hmeas0 : Measurable (fun _ : 𝒳 => (0 : ℝ)) := measurable_const
  have tF1 := bernstein_two_sample P Q (n := n) (m := m) hW1m hmeas0 hW1b h0W hW10 (by simp) hc hW1c h0c
    hV0 hV1 hL.le
  have tF2 := bernstein_two_sample P Q (n := n) (m := m) hmeas0 hW2m h0W hW2b (by simp) hW20 hc h0c hW2c
    hV0 hV2 hL.le
  have tF3 := bernstein_two_sample P Q (n := n) (m := m) hW1m hW2m hW1b hW2b hW10 hW20 hc hW1c hW2c
    hV0 hV3 hL.le
  have hT2 : √(2 * ((1 / (1 - α) - 1) * sNM n m) * Real.log (6 / δ)) + cNM n m * Real.log (6 / δ) / 3 =
      T2 α δ n m := by
    simp only [T2]; congr 2; ring
  rw [hT2, exp_neg_log_six hδ0] at tF1 tF2 tF3
  have mF : ∀ F : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), (sampleLaw P Q n m).real F ≤ δ / 6 →
      sampleLaw P Q n m F ≤ ENNReal.ofReal (δ / 6) :=
    fun F hF => by rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal hF
  refine ⟨(measure_mono fun z hz => ?_).trans (mF _ tF1), (measure_mono fun z hz => ?_).trans (mF _ tF2),
    (measure_mono fun z hz => ?_).trans (mF _ tF3)⟩
  · simp only [Set.mem_setOf_eq, Finset.sum_const_zero, add_zero] at hz ⊢
    rwa [one_sub_wMass hn] at hz
  · simp only [Set.mem_setOf_eq, Finset.sum_const_zero, zero_add] at hz ⊢
    rwa [one_sub_wMass hm] at hz
  · simp only [Set.mem_setOf_eq] at hz ⊢
    rwa [one_sub_wMass hn, one_sub_wMass hm] at hz

theorem union_six_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B C D E F : Set Ω) :
    μ (A ∪ B ∪ C ∪ D ∪ E ∪ F) ≤ μ A + μ B + μ C + μ D + μ E + μ F := by
  calc μ (A ∪ B ∪ C ∪ D ∪ E ∪ F) ≤ μ (A ∪ B ∪ C ∪ D ∪ E) + μ F := measure_union_le _ _
    _ ≤ μ (A ∪ B ∪ C ∪ D) + μ E + μ F := by gcongr; exact measure_union_le _ _
    _ ≤ μ (A ∪ B ∪ C) + μ D + μ E + μ F := by gcongr; exact measure_union_le _ _
    _ ≤ μ (A ∪ B) + μ C + μ D + μ E + μ F := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + μ B + μ C + μ D + μ E + μ F := by gcongr; exact measure_union_le _ _

/-- `0 < α < 1`: Lemma P0 and the six events. -/
theorem level_pos {φ : 𝒳 → H} {κ D v ρbar : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D)
    (hv : trCov φ R ≤ v ^ 2) (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (h0 : α ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) :
    sampleLaw P Q n m {z | tauP D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ := by
  obtain ⟨tE1, tE2, tE3⟩ := hilbert_events hφ hκ hD hv hα0 hα1 hδ0 hδ1 hn hm ha hb
  obtain ⟨tF1, tF2, tF3⟩ := repair_events hα0 hα1 h0 hδ0 hδ1 hn hm ha hb
  have hT2nn := T2_nonneg (α := α) (m := m) hn hδ0 hδ1
  have hρR : rhoR φ R ≤ ρbar := rhoR_le hρ
  have hρR0 : 0 ≤ rhoR φ R := rhoR_nonneg (R := R) hκ
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | tauP D v ρbar α δ n m < Demp φ z.1 z.2 α} ⊆
      {z | T1 D v α δ n m < ‖wMeanDev a φ (∫ y, φ y ∂R) z.1 - wMeanDev b φ (∫ y, φ y ∂R) z.2‖} ∪
      {z | T1 D v α δ n m < ‖wMeanDev a φ (∫ y, φ y ∂R) z.1‖} ∪
      {z | T1 D v α δ n m < ‖wMeanDev b φ (∫ y, φ y ∂R) z.2‖} ∪
      {z | T2 α δ n m ≤ 1 - wMass a z.1} ∪ {z | T2 α δ n m ≤ 1 - wMass b z.2} ∪
      {z | T2 α δ n m ≤ (1 - wMass a z.1) + (1 - wMass b z.2)} := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hcon
    obtain ⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hcon
    have hM : max (max ‖wMeanDev a φ (∫ y, φ y ∂R) z.1 - wMeanDev b φ (∫ y, φ y ∂R) z.2‖
        ‖wMeanDev a φ (∫ y, φ y ∂R) z.1‖) ‖wMeanDev b φ (∫ y, φ y ∂R) z.2‖ ≤ T1 D v α δ n m :=
      max_le (max_le n1 n2) n3
    have hrep : max (1 - wMass a z.1) 0 + max (1 - wMass b z.2) 0 ≤ T2 α δ n m := by
      rcases le_total (1 - wMass a z.1) 0 with h1 | h1 <;>
        rcases le_total (1 - wMass b z.2) 0 with h2 | h2
      · rw [max_eq_right h1, max_eq_right h2]; linarith
      · rw [max_eq_right h1, max_eq_left h2]; linarith
      · rw [max_eq_left h1, max_eq_right h2]; linarith
      · rw [max_eq_left h1, max_eq_left h2]; linarith
    have hdet := plugin_det 𝒳 H φ κ α P Q R a b n m hφ hκ hα0 hα1 hn hm ha hb z.1 z.2
    have hmul : rhoR φ R * (max (1 - wMass a z.1) 0 + max (1 - wMass b z.2) 0) ≤ ρbar * T2 α δ n m :=
      (mul_le_mul_of_nonneg_left hrep hρR0).trans (mul_le_mul_of_nonneg_right hρR hT2nn)
    have htau : tauP D v ρbar α δ n m = T1 D v α δ n m + ρbar * T2 α δ n m := by
      simp only [tauP, h0, if_false]
    simp only [Set.mem_setOf_eq] at hz
    rw [htau] at hz
    linarith
  refine (measure_mono hsub).trans ((union_six_le (sampleLaw P Q n m) _ _ _ _ _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) +
          ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) + ENNReal.ofReal (δ / 6) := by
        gcongr
    _ = ENNReal.ofReal δ := ofReal_six hδ0

/-- The level bound for a fixed common trimming `R` (constants needed for this `R` only). -/
theorem level_core {φ : 𝒳 → H} {κ D v ρbar : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α δ : ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv0 : 0 ≤ v)
    (hv : trCov φ R ≤ v ^ 2) (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) :
    sampleLaw P Q n m {z | tauP D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ := by
  by_cases h0 : α = 0
  · subst h0
    exact level_zero hφ hκ hD hv0 hv hδ0 hδ1 hn hm ha hb
  · exact level_pos hφ hκ hD hv hρ hα0 hα1 h0 hδ0 hδ1 hn hm ha hb

end Core

/-! ### Theorem P and the corollaries -/

theorem isProbabilityMeasure_withDensity_trim {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳}
    {α : ℝ} {g : 𝒳 → ℝ} (hg : StatFormal.TrimmedMMD.ZeroSet.IsTrimDensity P α g) :
    IsProbabilityMeasure (P.withDensity fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨hgm, hgb, hg1⟩ := hg
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable g P := by
    by_contra h
    rw [integral_undef h] at hg1
    exact zero_ne_one hg1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (hgb x).1), hg1, ENNReal.ofReal_one]

/-- The common trimming of `eq:tvintersect`, packaged for `level_core`. -/
theorem exists_common_trim {𝒳 : Type} [MeasurableSpace 𝒳] {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (htv : StatFormal.Distances.tvDist P Q ≤ α) :
    ∃ (R : Measure 𝒳) (a b : 𝒳 → ℝ), IsProbabilityMeasure R ∧ IsDensityLe R P α a ∧ IsDensityLe R Q α b := by
  obtain ⟨gP, gQ, hP, hQ, heq⟩ := (StatFormal.TrimmedMMD.ZeroSet.tvintersect 𝒳 P Q α hα0 hα1).1 htv
  exact ⟨_, gP, gQ, isProbabilityMeasure_withDensity_trim hP, ⟨hP.1, hP.2.1, rfl⟩, ⟨hQ.1, hQ.2.1, heq⟩⟩

theorem plugin_level : Claims.plugin_level := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ α δ n m hφ hκ hK hα0 hα1 hδ0 hδ1 hn hm htv
  obtain ⟨R, a, b, hR, ha, hb⟩ := exists_common_trim hα0 hα1 htv
  exact level_core hφ hκ hK.1 hK.2.1 (hK.2.2.1 R hR) (hK.2.2.2 R hR) hα0 hα1 hδ0 hδ1 hn hm ha hb

theorem plugin_level_explicit : Claims.plugin_level_explicit := by
  intro 𝒳 H _ _ _ _ φ κ D P Q _ _ α δ n m hφ hκ hD hα0 hα1 hδ0 hδ1 hn hm htv
  exact plugin_level 𝒳 H φ κ D _ D P Q α δ n m hφ hκ (kernel_consts 𝒳 H φ κ D hφ hκ hD).1 hα0 hα1 hδ0 hδ1
    hn hm htv

theorem plugin_coupled : Claims.plugin_coupled := by
  intro 𝒳 H _ _ _ _ φ κ D t P Q _ _ α δ n m hφ hκ hD hk hdiag hα0 hα1 hδ0 hδ1 hn hm htv ht
  obtain ⟨R, a, b, hR, ha, hb⟩ := exists_common_trim hα0 hα1 htv
  have hκ0 : 0 ≤ κ := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hκ x)
  set u := ‖∫ y, φ y ∂R‖ ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have huκ : u ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_bound (R := R) hκ) 2
  have hiv := (plugin_moments_iv 𝒳 H φ κ R hφ hκ).2 hk hdiag
  have hv : trCov φ R ≤ (√(κ ^ 2 - u)) ^ 2 := by
    rw [Real.sq_sqrt (by linarith), hiv.1]
  have hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ √(κ ^ 2 + u) := fun x =>
    (le_rhoR (R := R) hκ x).trans (Real.le_sqrt_of_sq_le hiv.2)
  have hcore := level_core (v := √(κ ^ 2 - u)) (ρbar := √(κ ^ 2 + u)) hφ hκ hD (Real.sqrt_nonneg _) hv hρ
    hα0 hα1 hδ0 hδ1 hn hm ha hb
  refine (measure_mono fun z hz => ?_).trans hcore
  simp only [Set.mem_setOf_eq] at hz ⊢
  exact lt_of_le_of_lt (ht u ⟨hu0, huκ⟩) hz

theorem plugin_one_event : Claims.plugin_one_event := by
  intro 𝒳 H _ _ _ _ φ κ D v ρbar P Q _ _ δ n m hφ hκ hK hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hK.1 x0 x0)
  have hρ0 : 0 ≤ ρbar := (norm_nonneg _).trans (hK.2.2.2 P inferInstance x0)
  rcases lt_or_ge (StatFormal.Distances.tvDist P Q) 1 with htv | htv
  · have hmono := plugin_monotone D v ρbar δ n m hD0 hK.2.1 hρ0 hδ0 hδ1 hn hm
    have hlev : ∀ α ∈ Ico (0 : ℝ) 1, ∀ P' Q' : Measure 𝒳, IsProbabilityMeasure P' → IsProbabilityMeasure Q' →
        StatFormal.Distances.tvDist P' Q' ≤ α →
          sampleLaw P' Q' n m {z | tauP D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ :=
      fun α hα P' Q' hP' hQ' htv' =>
        plugin_level 𝒳 H φ κ D v ρbar P' Q' α δ n m hφ hκ hK hα.1 hα.2 hδ0 hδ1 hn hm htv'
    obtain ⟨⟨E, hEm, hEp, hEs⟩, hpath⟩ := monotone_event 𝒳 H φ (fun α => tauP D v ρbar α δ n m) δ n m P Q
      hδ0.le hn hm hmono.2 hmono.1 hlev htv
    refine ⟨E, hEm, hEp, fun z hz => ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := hpath z (hEs hz)
    exact ⟨fun α hα htvα => h1 α ⟨htvα, hα.2⟩, fun _ => h2, h3⟩
  · refine ⟨univ, MeasurableSet.univ, by rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith),
      fun z _ => ⟨fun α hα htvα => absurd (htvα.trans_lt hα.2) (not_lt.2 htv), fun h => absurd h (not_lt.2 htv),
        fun α hα _ => lt_of_lt_of_le hα.2 htv⟩⟩

end StatFormal.Wave30tp
