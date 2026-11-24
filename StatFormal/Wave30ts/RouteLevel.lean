import StatFormal.Wave30ts.RoutePinelis

/-!
# Route: the level of the sharper threshold (NOTE §3.3)

Untrusted proof material.

For a **fixed** common trimming `R = a·P = b·Q` with constants valid for this `R` only:
* `det_split`: by Lemma P0, `{t₁ + ρ̄t₂ < D̂_α} ⊆ {t₁ < M} ∪ {t₂ < C}` with `M = max(‖A−B‖, ‖A‖, ‖B‖)` and
  `C = (1−S_X)_+ + (1−S_Y)_+` (for `t₂ ≥ 0`, `0 ≤ ρ_R ≤ ρ̄`);
* `hilbert_part`: `Pr(t < M) ≤ Ψ_H(t;β,s,c) + Ψ_H(t;β,1/n,1/n) + Ψ_H(t;β,1/m,1/m)` (each event: McDiarmid and Pinelis);
* `repair_part_lam`, `repair_part_inf`: `Pr(t < C) ≤` the three-event `Ψ_R` sum (two-point Chernoff, `Lemma P1(iii)`);
* `measure_sInf_lt_le`: continuity from below turns "every admissible `t` is valid" into "the infimum is valid" (the
  admissible sets need not be closed);
* `core_tau`: `Pr(D̂_α > τ_{P'}(α,δ)) ≤ δ` (a constant feature map, `D = 0`, gives `D̂_α = 0`).
Then the claims, with `eq:tvintersect` supplying `R`, and the coupled forms (`‖μ_R‖² = κ²` handled by `M = 0` a.s.).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.Wave30ts

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.Wave30tp

/-! ### Generic measure lemmas -/

theorem measure_sInf_lt_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) {S : Set ℝ}
    (hS : S.Nonempty) {c : ℝ≥0∞} (h : ∀ t ∈ S, μ {ω | t < F ω} ≤ c) : μ {ω | sInf S < F ω} ≤ c := by
  have hU : {ω | sInf S < F ω} = ⋃ k : ℕ, {ω | sInf S + 1 / ((k : ℝ) + 1) < F ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hω
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hω)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun k : ℕ => {ω | sInf S + 1 / ((k : ℝ) + 1) < F ω} := by
    intro k k' hkk ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkk 1)
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun k => ?_
  have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hS (show sInf S < sInf S + 1 / ((k : ℝ) + 1) by linarith)
  exact (measure_mono fun ω (hω : sInf S + 1 / ((k : ℝ) + 1) < F ω) =>
    (show t < F ω by linarith)).trans (h t htS)

theorem le_ofReal_of_forall_pos {x : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal (c + ε)) : x ≤ ENNReal.ofReal c := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have := h ε hε
  rwa [ENNReal.ofReal_add hc (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal] at this

theorem ofReal_add3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z = ENNReal.ofReal (x + y + z) := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) hz]

theorem measure_union3_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B C : Set Ω) :
    μ (A ∪ B ∪ C) ≤ μ A + μ B + μ C :=
  calc μ (A ∪ B ∪ C) ≤ μ (A ∪ B) + μ C := measure_union_le _ _
    _ ≤ μ A + μ B + μ C := by gcongr; exact measure_union_le _ _

section Core

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `M = max(‖A−B‖, ‖A‖, ‖B‖)`. -/
def Mfun (a b : 𝒳 → ℝ) (φ : 𝒳 → H) (μ : H) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  max (max ‖wMeanDev a φ μ z.1 - wMeanDev b φ μ z.2‖ ‖wMeanDev a φ μ z.1‖) ‖wMeanDev b φ μ z.2‖

/-- `C = (1−S_X)_+ + (1−S_Y)_+`. -/
def Cfun (a b : 𝒳 → ℝ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : ℝ :=
  max (1 - wMass a z.1) 0 + max (1 - wMass b z.2) 0

theorem Cfun_nonneg (a b : 𝒳 → ℝ) {n m : ℕ} (z : (Fin n → 𝒳) × (Fin m → 𝒳)) : 0 ≤ Cfun a b z :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- A constant feature map gives `D̂_α = 0`. -/
theorem Demp_le_zero {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ 0) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Fin n → 𝒳) (y : Fin m → 𝒳) :
    Demp φ x y α ≤ 0 := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hcap : ∀ k : ℕ, (0 : ℝ) < k → (1 : ℝ) / k ≤ cap k α := fun k hk => by
    unfold cap
    exact one_div_le_one_div_of_le (mul_pos hk (by linarith)) (by nlinarith)
  have hwx : (fun _ : Fin n => (1 : ℝ) / n) ∈ capped n α := by
    refine ⟨fun i => ⟨by positivity, hcap n hnpos⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hwy : (fun _ : Fin m => (1 : ℝ) / m) ∈ capped m α := by
    refine ⟨fun i => ⟨by positivity, hcap m hmpos⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hX := polytope_mem_region hφ hα0 hα1 hn x hwx
  have hY := polytope_mem_region hφ hα0 hα1 hm y hwy
  have hconst : ∀ x', φ x' = φ (y ⟨0, by omega⟩) := fun x' => sub_eq_zero.1 (norm_le_zero_iff.1 (hD _ _))
  refine (setDist_le_norm hX hY).trans (le_of_eq ?_)
  simp only [hconst, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (n : ℝ) * (1 / n) = 1 by field_simp, show (m : ℝ) * (1 / m) = 1 by field_simp]
  simp

/-- Lemma P0, split into a Hilbert part and a repair part. -/
theorem det_split {φ : 𝒳 → H} {κ α ρbar t1 t2 : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht2 : 0 ≤ t2) :
    {z : (Fin n → 𝒳) × (Fin m → 𝒳) | t1 + ρbar * t2 < Demp φ z.1 z.2 α} ⊆
      {z | t1 < Mfun a b φ (∫ y, φ y ∂R) z} ∪ {z | t2 < Cfun a b z} := by
  intro z hz
  by_contra hcon
  simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hcon hz
  have hdet := plugin_det 𝒳 H φ κ α P Q R a b n m hφ hκ hα0 hα1 hn hm ha hb z.1 z.2
  have hρR : rhoR φ R ≤ ρbar := rhoR_le hρ
  have hρR0 : 0 ≤ rhoR φ R := rhoR_nonneg (R := R) hκ
  have hC0 := Cfun_nonneg a b z
  have : rhoR φ R * Cfun a b z ≤ ρbar * t2 :=
    (mul_le_mul_of_nonneg_left hcon.2 hρR0).trans (mul_le_mul_of_nonneg_right hρR ht2)
  unfold Mfun at hcon
  unfold Cfun at this
  linarith

/-- The three Hilbert events: `Pr(t < M) ≤ Σ Ψ_H`. -/
theorem hilbert_part {φ : 𝒳 → H} {κ D v ρbar α t : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht : 0 ≤ t) :
    sampleLaw P Q n m {z | t < Mfun a b φ (∫ y, φ y ∂R) z} ≤
      ENNReal.ofReal (psiH3 D v ρbar (1 / (1 - α)) t n m) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x0 x0)
  have hρ0 : 0 ≤ ρbar := (norm_nonneg _).trans (hρ x0)
  set β := 1 / (1 - α) with hβdef
  have hβ0 : 0 ≤ β := div_nonneg zero_le_one (by linarith)
  have hβD : 0 ≤ β * D := mul_nonneg hβ0 hD0
  set μR := ∫ y, φ y ∂R
  have hψb : ∀ x, ‖φ x - μR‖ ≤ 2 * κ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])
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
  have hρR : rhoR φ R ≤ ρbar := rhoR_le hρ
  have hξρ : ∀ x, ‖a x • (φ x - μR)‖ ≤ β * ρbar := fun x =>
    ((plugin_moments_ii 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha).1 x).trans (mul_le_mul_of_nonneg_left hρR hβ0)
  have hζρ : ∀ x, ‖b x • (φ x - μR)‖ ≤ β * ρbar := fun x =>
    ((plugin_moments_ii 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb).1 x).trans (mul_le_mul_of_nonneg_left hρR hβ0)
  have hm1 := plugin_moments_i 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha
  have hm1' := plugin_moments_i 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb
  have hm2 := (plugin_moments_ii 𝒳 H φ κ α P R a hφ hκ hα0 hα1 ha).2 D hD
  have hm2' := (plugin_moments_ii 𝒳 H φ κ α Q R b hφ hκ hα0 hα1 hb).2 D hD
  have hξ2 : ∫ x, ‖a x • (φ x - μR)‖ ^ 2 ∂P ≤ β * v ^ 2 := hm1.2.1.trans (mul_le_mul_of_nonneg_left hv hβ0)
  have hζ2 : ∫ x, ‖b x • (φ x - μR)‖ ^ 2 ∂Q ≤ β * v ^ 2 := hm1'.2.1.trans (mul_le_mul_of_nonneg_left hv hβ0)
  have h0m : StronglyMeasurable (fun _ : 𝒳 => (0 : H)) := stronglyMeasurable_const
  have h0b : ∀ x : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x‖ ≤ β * (2 * κ) := fun x => by simp only [norm_zero]; positivity
  have h0b' : ∀ x : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x‖ ≤ 0 := fun x => by simp
  have h00P : ∫ x, (fun _ : 𝒳 => (0 : H)) x ∂P = 0 := by simp
  have h00Q : ∫ x, (fun _ : 𝒳 => (0 : H)) x ∂Q = 0 := by simp
  have h02P : ∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂P ≤ 0 := by simp
  have h02Q : ∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂Q ≤ 0 := by simp
  have h0d : ∀ x x' : 𝒳, ‖(fun _ : 𝒳 => (0 : H)) x - (fun _ : 𝒳 => (0 : H)) x'‖ ≤ 0 := by simp
  have hcn : β * ρbar / n ≤ β * ρbar * cNM n m := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg hβ0 hρ0)
  have hcm : β * ρbar / m ≤ β * ρbar * cNM n m := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hβ0 hρ0)
  have hn' : β * ρbar / n ≤ β * ρbar * (1 / n) := by rw [div_eq_mul_one_div]
  have hm' : β * ρbar / m ≤ β * ρbar * (1 / m) := by rw [div_eq_mul_one_div]
  have hsq0 : ∀ ψ : 𝒳 → H, 0 ≤ ∫ x, ‖ψ x‖ ^ 2 ∂P := fun ψ => integral_nonneg fun _ => sq_nonneg _
  -- event 1: `‖A − B‖`
  have tE1 : sampleLaw P Q n m {z | t < ‖twoDev (fun x => a x • (φ x - μR)) (fun x => b x • (φ x - μR)) z‖} ≤
      ENNReal.ofReal (psiH D v ρbar β (sNM n m) (cNM n m) t) := by
    refine psiH_of_two P Q ?_ ?_
    · exact twoDev_mcd P Q hξm hζm hξb hζb hm1.1 hm1'.1 hξ2 hζ2 hβD hβD hm2 hm2' hn hm
        (by unfold sNM; ring) (by unfold sNM; ring)
    · refine twoDev_pinelis P Q hξm hζm hm1.1 hm1'.1 hξρ hζρ hn hm hcn hcm
        (mul_nonneg (mul_nonneg hβ0 hρ0) (cNM_pos (m := m) hn).le)
        (mul_nonneg (mul_nonneg hβ0 (sq_nonneg v)) (sNM_pos hn hm).le) ?_ ht
      calc (∫ x, ‖a x • (φ x - μR)‖ ^ 2 ∂P) / n + (∫ x, ‖b x • (φ x - μR)‖ ^ 2 ∂Q) / m
          ≤ β * v ^ 2 / n + β * v ^ 2 / m := by gcongr
        _ = β * v ^ 2 * sNM n m := by unfold sNM; ring
  -- event 2: `‖A‖`
  have tE2 : sampleLaw P Q n m {z | t < ‖twoDev (fun x => a x • (φ x - μR)) (fun _ : 𝒳 => (0 : H)) z‖} ≤
      ENNReal.ofReal (psiH D v ρbar β (1 / (n : ℝ)) (1 / (n : ℝ)) t) := by
    refine psiH_of_two P Q ?_ ?_
    · exact twoDev_mcd P Q hξm h0m hξb h0b hm1.1 h00Q hξ2 h02Q hβD le_rfl hm2 h0d hn hm
        (by ring) (by ring)
    · refine twoDev_pinelis P Q hξm h0m hm1.1 h00Q hξρ h0b' hn hm hn'
        (by simp only [zero_div]; positivity) (by positivity) (by positivity) ?_ ht
      calc (∫ x, ‖a x • (φ x - μR)‖ ^ 2 ∂P) / n + (∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂Q) / m
          ≤ β * v ^ 2 / n + 0 / m := by gcongr
        _ = β * v ^ 2 * (1 / n) := by ring
  -- event 3: `‖B‖`
  have tE3 : sampleLaw P Q n m {z | t < ‖twoDev (fun _ : 𝒳 => (0 : H)) (fun x => b x • (φ x - μR)) z‖} ≤
      ENNReal.ofReal (psiH D v ρbar β (1 / (m : ℝ)) (1 / (m : ℝ)) t) := by
    refine psiH_of_two P Q ?_ ?_
    · exact twoDev_mcd P Q h0m hζm h0b hζb h00P hm1'.1 h02P hζ2 le_rfl hβD h0d hm2' hn hm
        (by ring) (by ring)
    · refine twoDev_pinelis P Q h0m hζm h00P hm1'.1 h0b' hζρ hn hm
        (by simp only [zero_div]; positivity) hm' (by positivity) (by positivity) ?_ ht
      calc (∫ x, ‖(fun _ : 𝒳 => (0 : H)) x‖ ^ 2 ∂P) / n + (∫ x, ‖b x • (φ x - μR)‖ ^ 2 ∂Q) / m
          ≤ 0 / n + β * v ^ 2 / m := by gcongr
        _ = β * v ^ 2 * (1 / m) := by ring
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | t < Mfun a b φ μR z} ⊆
      {z | t < ‖twoDev (fun x => a x • (φ x - μR)) (fun x => b x • (φ x - μR)) z‖} ∪
      {z | t < ‖twoDev (fun x => a x • (φ x - μR)) (fun _ : 𝒳 => (0 : H)) z‖} ∪
      {z | t < ‖twoDev (fun _ : 𝒳 => (0 : H)) (fun x => b x • (φ x - μR)) z‖} := by
    intro z hz
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
  refine (measure_mono hsub).trans ((measure_union3_le _ _ _ _).trans ?_)
  rw [psiH3, ← ofReal_add3 (psiH_nonneg _ _ _ _ _ _ _) (psiH_nonneg _ _ _ _ _ _ _) (psiH_nonneg _ _ _ _ _ _ _)]
  exact add_le_add (add_le_add tE1 tE2) tE3

/-- The two-point Chernoff bound for one repair sum. -/
theorem integral_exp_repair_le {P R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure R] {α l : ℝ}
    {a : 𝒳 → ℝ} {k : ℕ} (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α < 1) (ha : IsDensityLe R P α a) (hl : 0 ≤ l) :
    (∫ x, exp (l * ((1 - a x) / k)) ∂P) ^ k ≤ twoPt (1 / (1 - α)) (l / k) ^ k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have h3 := (plugin_moments_iii 𝒳 α P R a hα0 hα1 ha).2.2.2 (l / k) (div_nonneg hl hkpos.le)
  have e : (fun x => exp (l * ((1 - a x) / k))) = fun x => exp (l / k * (1 - a x)) := by
    funext x; congr 1; field_simp
  rw [e]
  exact pow_le_pow_left₀ (integral_nonneg fun _ => (exp_pos _).le) h3 k

/-- The three repair events at fixed `λ`'s. -/
theorem repair_part_lam {P Q R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α t l1 l2 l3 : ℝ} {n m : ℕ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht : 0 ≤ t)
    (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3) :
    sampleLaw P Q n m {z | t < Cfun a b z} ≤
      ENNReal.ofReal (psiRlam (1 / (1 - α)) l1 t [n] + psiRlam (1 / (1 - α)) l2 t [m] +
        psiRlam (1 / (1 - α)) l3 t [n, m]) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  set β := 1 / (1 - α)
  have hβ1 : 1 ≤ β := one_le_beta hα0 hα1
  have hab := ha.2.1
  have hbb := hb.2.1
  have hW1m : Measurable fun x => (1 - a x) / n := (measurable_const.sub ha.1).div_const _
  have hW2m : Measurable fun y => (1 - b y) / m := (measurable_const.sub hb.1).div_const _
  have hW1b : ∀ x, |(1 - a x) / n| ≤ β := fun x => by
    rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have : |1 - a x| ≤ β := abs_le.2 ⟨by linarith [(hab x).2], by linarith [(hab x).1]⟩
    nlinarith [abs_nonneg (1 - a x), (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
  have hW2b : ∀ x, |(1 - b x) / m| ≤ β := fun x => by
    rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
    have : |1 - b x| ≤ β := abs_le.2 ⟨by linarith [(hbb x).2], by linarith [(hbb x).1]⟩
    nlinarith [abs_nonneg (1 - b x), (show (1 : ℝ) ≤ m by exact_mod_cast hm)]
  have h0W : ∀ x : 𝒳, |(fun _ : 𝒳 => (0 : ℝ)) x| ≤ β := fun x => by simp; linarith
  have hmeas0 : Measurable (fun _ : 𝒳 => (0 : ℝ)) := measurable_const
  have hE1 := fun (l : ℝ) (hl : 0 ≤ l) => integral_exp_repair_le (P := P) (R := R) hn hα0 hα1 ha hl
  have hE2 := fun (l : ℝ) (hl : 0 ≤ l) => integral_exp_repair_le (P := Q) (R := R) hm hα0 hα1 hb hl
  have hone : ∀ (ν : Measure 𝒳) [IsProbabilityMeasure ν] (l : ℝ) (k : ℕ),
      (∫ x, exp (l * (fun _ : 𝒳 => (0 : ℝ)) x) ∂ν) ^ k = 1 := fun ν _ l k => by simp
  have hexp0 : ∀ l : ℝ, 0 ≤ exp (-(l * t)) := fun l => (exp_pos _).le
  have tF1 := chernoff_two_sample P Q (n := n) (m := m) hW1m hmeas0 hW1b h0W (t := t) hl1.le
  have tF2 := chernoff_two_sample P Q (n := n) (m := m) hmeas0 hW2m h0W hW2b (t := t) hl2.le
  have tF3 := chernoff_two_sample P Q (n := n) (m := m) hW1m hW2m hW1b hW2b (t := t) hl3.le
  rw [hone] at tF1
  rw [hone] at tF2
  have b1 : exp (-(l1 * t)) * ((∫ x, exp (l1 * ((1 - a x) / n)) ∂P) ^ n * 1) ≤ psiRlam β l1 t [n] := by
    simp only [psiRlam, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact mul_le_mul_of_nonneg_left (hE1 l1 hl1.le) (hexp0 _)
  have b2 : exp (-(l2 * t)) * (1 * (∫ y, exp (l2 * ((1 - b y) / m)) ∂Q) ^ m) ≤ psiRlam β l2 t [m] := by
    simp only [psiRlam, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
    exact mul_le_mul_of_nonneg_left (hE2 l2 hl2.le) (hexp0 _)
  have b3 : exp (-(l3 * t)) * ((∫ x, exp (l3 * ((1 - a x) / n)) ∂P) ^ n *
      (∫ y, exp (l3 * ((1 - b y) / m)) ∂Q) ^ m) ≤ psiRlam β l3 t [n, m] := by
    simp only [psiRlam, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    refine mul_le_mul_of_nonneg_left (mul_le_mul (hE1 l3 hl3.le) (hE2 l3 hl3.le)
      (pow_nonneg (integral_nonneg fun _ => (exp_pos _).le) _) (pow_nonneg (twoPt_nonneg hβ1 _) _)) (hexp0 _)
  have hsub : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | t < Cfun a b z} ⊆
      {z | t ≤ ∑ i, (fun x => (1 - a x) / n) (z.1 i) + ∑ j, (fun _ : 𝒳 => (0 : ℝ)) (z.2 j)} ∪
      {z | t ≤ ∑ i, (fun _ : 𝒳 => (0 : ℝ)) (z.1 i) + ∑ j, (fun y => (1 - b y) / m) (z.2 j)} ∪
      {z | t ≤ ∑ i, (fun x => (1 - a x) / n) (z.1 i) + ∑ j, (fun y => (1 - b y) / m) (z.2 j)} := by
    intro z hz
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or, not_le, Finset.sum_const_zero, add_zero, zero_add] at hcon hz
    rw [← one_sub_wMass hn, ← one_sub_wMass hm] at hcon
    obtain ⟨⟨n1, n2⟩, n3⟩ := hcon
    unfold Cfun at hz
    rcases le_total (1 - wMass a z.1) 0 with h1 | h1 <;> rcases le_total (1 - wMass b z.2) 0 with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2] at hz; linarith
    · rw [max_eq_right h1, max_eq_left h2] at hz; linarith
    · rw [max_eq_left h1, max_eq_right h2] at hz; linarith
    · rw [max_eq_left h1, max_eq_left h2] at hz; linarith
  refine (measure_mono hsub).trans ((measure_union3_le _ _ _ _).trans ?_)
  rw [← ofReal_add3 (psiRlam_nonneg hβ1 _ _ _) (psiRlam_nonneg hβ1 _ _ _) (psiRlam_nonneg hβ1 _ _ _)]
  exact add_le_add (add_le_add (tF1.trans (ENNReal.ofReal_le_ofReal b1))
    (tF2.trans (ENNReal.ofReal_le_ofReal b2))) (tF3.trans (ENNReal.ofReal_le_ofReal b3))

/-- The three repair events with the infimum over `λ`. -/
theorem repair_part_inf {P Q R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α t δ2 : ℝ} {n m : ℕ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht : 0 ≤ t)
    (hR : psiR3 (1 / (1 - α)) t n m ≤ δ2) :
    sampleLaw P Q n m {z | t < Cfun a b z} ≤ ENNReal.ofReal δ2 := by
  have hβ1 : 1 ≤ 1 / (1 - α) := one_le_beta hα0 hα1
  have hδ2 : 0 ≤ δ2 := (psiR3_nonneg hβ1 t n m).trans hR
  refine le_ofReal_of_forall_pos hδ2 fun ε hε => ?_
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨l1, hl1, h1⟩ := exists_psiRlam_lt hβ1 t [n] (lt_add_of_pos_right (psiR _ t [n]) hε3)
  obtain ⟨l2, hl2, h2⟩ := exists_psiRlam_lt hβ1 t [m] (lt_add_of_pos_right (psiR _ t [m]) hε3)
  obtain ⟨l3, hl3, h3⟩ := exists_psiRlam_lt hβ1 t [n, m] (lt_add_of_pos_right (psiR _ t [n, m]) hε3)
  refine (repair_part_lam hα0 hα1 hn hm ha hb ht hl1 hl2 hl3).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold psiR3 at hR
  linarith

theorem hilbert_part_root {φ : 𝒳 → H} {κ D v ρbar α δ1 : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b)
    (hne : (setH D v ρbar (1 / (1 - α)) δ1 n m).Nonempty) :
    sampleLaw P Q n m {z | rootH D v ρbar (1 / (1 - α)) δ1 n m < Mfun a b φ (∫ y, φ y ∂R) z} ≤
      ENNReal.ofReal δ1 :=
  measure_sInf_lt_le _ _ hne fun t ht =>
    (hilbert_part hφ hκ hD hv hρ hα0 hα1 hn hm ha hb ht.1).trans (ENNReal.ofReal_le_ofReal ht.2)

theorem repair_part_root {P Q R : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {α δ2 : ℝ} {n m : ℕ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (hδ2 : 0 ≤ δ2) :
    sampleLaw P Q n m {z | rootR (1 / (1 - α)) δ2 n m < Cfun a b z} ≤ ENNReal.ofReal δ2 :=
  measure_sInf_lt_le _ _ ⟨3, three_mem_setR (one_le_beta hα0 hα1) hδ2 n m⟩ fun t ht =>
    repair_part_inf hα0 hα1 hn hm ha hb ht.1 ht.2

/-- **Core, fixed `λ`'s**: the frozen `sharp_level` for a fixed common trimming. -/
theorem core_lam {φ : 𝒳 → H} {κ D v ρbar α δ1 δ2 t1 t2 l1 l2 l3 : ℝ} {P Q R : Measure 𝒳}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hl1 : 0 < l1)
    (hl2 : 0 < l2) (hl3 : 0 < l3) (hH : psiH3 D v ρbar (1 / (1 - α)) t1 n m ≤ δ1)
    (hR : psiRlam (1 / (1 - α)) l1 t2 [n] + psiRlam (1 / (1 - α)) l2 t2 [m] +
      psiRlam (1 / (1 - α)) l3 t2 [n, m] ≤ δ2) :
    sampleLaw P Q n m {z | t1 + ρbar * t2 < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal (δ1 + δ2) := by
  have hβ1 := one_le_beta hα0 hα1
  have hδ1 : 0 ≤ δ1 := (psiH3_nonneg _ _ _ _ _ _ _).trans hH
  have hδ2 : 0 ≤ δ2 := by
    have := psiRlam_nonneg hβ1 l1 t2 [n]; have := psiRlam_nonneg hβ1 l2 t2 [m]
    have := psiRlam_nonneg hβ1 l3 t2 [n, m]; linarith
  refine (measure_mono (det_split hφ hκ hρ hα0 hα1 hn hm ha hb ht2)).trans ((measure_union_le _ _).trans ?_)
  rw [ENNReal.ofReal_add hδ1 hδ2]
  exact add_le_add ((hilbert_part hφ hκ hD hv hρ hα0 hα1 hn hm ha hb ht1).trans (ENNReal.ofReal_le_ofReal hH))
    ((repair_part_lam hα0 hα1 hn hm ha hb ht2 hl1 hl2 hl3).trans (ENNReal.ofReal_le_ofReal hR))

theorem core_inf {φ : 𝒳 → H} {κ D v ρbar α δ1 δ2 t1 t2 : ℝ} {P Q R : Measure 𝒳}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hH : psiH3 D v ρbar (1 / (1 - α)) t1 n m ≤ δ1) (hR : psiR3 (1 / (1 - α)) t2 n m ≤ δ2) :
    sampleLaw P Q n m {z | t1 + ρbar * t2 < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal (δ1 + δ2) := by
  have hβ1 := one_le_beta hα0 hα1
  have hδ1 : 0 ≤ δ1 := (psiH3_nonneg _ _ _ _ _ _ _).trans hH
  have hδ2 : 0 ≤ δ2 := (psiR3_nonneg hβ1 _ _ _).trans hR
  refine (measure_mono (det_split hφ hκ hρ hα0 hα1 hn hm ha hb ht2)).trans ((measure_union_le _ _).trans ?_)
  rw [ENNReal.ofReal_add hδ1 hδ2]
  exact add_le_add ((hilbert_part hφ hκ hD hv hρ hα0 hα1 hn hm ha hb ht1).trans (ENNReal.ofReal_le_ofReal hH))
    (repair_part_inf hα0 hα1 hn hm ha hb ht2 hR)

/-- The `α = 0` event (`P = Q = R`): `Pr(t < ‖A − B‖) ≤ Ψ_H(t;1,s,c)`. -/
theorem zero_part {φ : 𝒳 → H} {κ D v ρbar t : ℝ} {R : Measure 𝒳} [IsProbabilityMeasure R] {n m : ℕ}
    (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hn : 1 ≤ n) (hm : 1 ≤ m) (ht : 0 ≤ t) :
    sampleLaw R R n m {z | t < ‖twoDev (fun x => φ x - ∫ y, φ y ∂R) (fun x => φ x - ∫ y, φ y ∂R) z‖} ≤
      ENNReal.ofReal (psiH D v ρbar 1 (sNM n m) (cNM n m) t) := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure R
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x0 x0)
  have hρ0 : 0 ≤ ρbar := (norm_nonneg _).trans (hρ x0)
  have hψb : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ 2 * κ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hκ x, norm_integral_le_bound (R := R) hκ])
  have hint := StatFormal.Concentration.integrable_of_bound (P := R) hφ hκ
  have hψm : StronglyMeasurable (fun x => φ x - ∫ y, φ y ∂R) := hφ.sub stronglyMeasurable_const
  have hψ0 : ∫ x, (φ x - ∫ y, φ y ∂R) ∂R = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  have hψd : ∀ x x', ‖(φ x - ∫ y, φ y ∂R) - (φ x' - ∫ y, φ y ∂R)‖ ≤ D := fun x x' => by
    rw [sub_sub_sub_cancel_right]; exact hD x x'
  have hcn : ρbar / n ≤ 1 * ρbar * cNM n m := by
    rw [one_mul, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hρ0
  have hcm : ρbar / m ≤ 1 * ρbar * cNM n m := by
    rw [one_mul, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hρ0
  refine psiH_of_two R R ?_ ?_
  · exact twoDev_mcd R R hψm hψm hψb hψb hψ0 hψ0 hv hv hD0 hD0 hψd hψd hn hm (by unfold sNM; ring)
      (by unfold sNM; ring)
  · refine twoDev_pinelis R R hψm hψm hψ0 hψ0 hρ hρ hn hm hcn hcm
      (mul_nonneg (mul_nonneg zero_le_one hρ0) (cNM_pos (m := m) hn).le)
      (mul_nonneg (mul_nonneg zero_le_one (sq_nonneg v)) (sNM_pos hn hm).le) ?_ ht
    calc (∫ x, ‖φ x - ∫ y, φ y ∂R‖ ^ 2 ∂R) / n + (∫ x, ‖φ x - ∫ y, φ y ∂R‖ ^ 2 ∂R) / m
        ≤ v ^ 2 / n + v ^ 2 / m := by gcongr <;> exact hv
      _ = 1 * v ^ 2 * sNM n m := by unfold sNM; ring

/-- **Core, the literal `τ_{P'}`**, for a fixed common trimming. -/
theorem core_tau {φ : 𝒳 → H} {κ D v ρbar α δ : ℝ} {P Q R : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] {a b : 𝒳 → ℝ} {n m : ℕ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) (hv0 : 0 ≤ v) (hv : trCov φ R ≤ v ^ 2)
    (hρ : ∀ x, ‖φ x - ∫ y, φ y ∂R‖ ≤ ρbar) (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : IsDensityLe R P α a) (hb : IsDensityLe R Q α b) :
    sampleLaw P Q n m {z | tauPs D v ρbar α δ n m < Demp φ z.1 z.2 α} ≤ ENNReal.ofReal δ := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x0 x0)
  have hρ0 : 0 ≤ ρbar := (norm_nonneg _).trans (hρ x0)
  rcases hD0.eq_or_lt with hDz | hDpos
  · -- constant feature map: `D̂_α ≤ 0 ≤ τ`
    subst hDz
    have hempty : {z : (Fin n → 𝒳) × (Fin m → 𝒳) | tauPs 0 v ρbar α δ n m < Demp φ z.1 z.2 α} = ∅ := by
      ext z
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (Demp_le_zero hφ hD hα0 hα1 hn hm z.1 z.2).trans (tauPs_nonneg hρ0)
    rw [hempty, measure_empty]; exact zero_le
  by_cases h0 : α = 0
  · subst h0
    obtain ⟨-, hPR⟩ := ae_density_eq_one ha
    obtain ⟨-, hQR⟩ := ae_density_eq_one hb
    rw [tauPs_zero_eq, hPR, hQR]
    refine (measure_mono fun z hz => ?_).trans (measure_sInf_lt_le (sampleLaw R R n m)
      (fun z => ‖twoDev (fun x => φ x - ∫ y, φ y ∂R) (fun x => φ x - ∫ y, φ y ∂R) z‖)
      (set0_nonempty hv0 hρ0 hδ0 hn hm (Or.inl hDpos)) fun t ht =>
        (zero_part hφ hκ hD hv hρ hn hm ht.1).trans (ENNReal.ofReal_le_ofReal ht.2))
    simp only [mem_setOf_eq] at hz ⊢
    exact hz.trans_le (Demp_zero_le hφ _ hn hm z)
  · obtain ⟨f, hf, hfe⟩ := tauPs_pos_attained (D := D) (v := v) (ρbar := ρbar) (δ := δ) (n := n) (m := m) h0
    obtain ⟨hf0, hf1⟩ := hf.bounds
    have hβ1 := one_le_beta hα0 hα1
    rw [hfe]
    unfold tauSplit
    have hne := setH_nonempty (D := D) (δ1 := f * δ) (n := n) (m := m) hv0 hρ0 hβ1 (by positivity) hn hm
      (Or.inl hDpos)
    refine (measure_mono (det_split hφ hκ hρ hα0 hα1 hn hm ha hb (rootR_nonneg _ _ _ _))).trans
      ((measure_union_le _ _).trans ?_)
    have e : ENNReal.ofReal δ = ENNReal.ofReal (f * δ) + ENNReal.ofReal ((1 - f) * δ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by nlinarith)]; congr 1; ring
    rw [e]
    exact add_le_add (hilbert_part_root hφ hκ hD hv hρ hα0 hα1 hn hm ha hb hne)
      (repair_part_root hα0 hα1 hn hm ha hb (by nlinarith))

end Core

end StatFormal.Wave30ts
