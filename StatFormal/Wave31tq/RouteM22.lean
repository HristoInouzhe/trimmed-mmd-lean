import StatFormal.Wave31tq.RouteM21
import StatFormal.Archive.Wave18b.RouteConsistency

/-!
# Wave 31tq, route M (Q22): Proposition 5.6 and "a margin of exponential type holds" (untrusted)

* `gauss_profile_facts`: the Gaussian profile is continuous and integrable;
* `gauss_upper`: Proposition S4.15 (b) with `2N` moments (`Claims.newmoments`, chunk T) and the Gaussian `M_{4N} < ∞`
  (`Claims.kernel_instances` (c), chunk A): `D̄_{α⋆−ε} ≤ Kε^{N+1}`;
* `gauss_lower`: Theorem S4.13 with its `ρ_ε` (`Claims.newgauss_thm_rho` (b), chunk G) at `θ = c′/m₁`, `ℓ = ℓ₀m₂/m₁ > ℓ₀`
  (`c′ = π²σ²ℓ₀/8 < m₁ < m₂ < c`), so that `σ²ℓπ²/(8θ) = m₂`, and the elementary `CrossLaws.exp_le_of_log_bound`:
  `e^{−c/ε} ≤ D̄_{α⋆−ε}` for small `ε`;
* `newgauss_of (h1 : Claims.tv_density) (hrho : Claims.newgauss_thm_rho) (hmom : Claims.newmoments)
  (hk : Claims.kernel_instances) : Claims.newgauss` (`ε^{N+1} ≤ ε^N`, `D̄ ≤ D ≤ D̄/(1 − α⋆)`);
* `newgauss_margin_of h1 hrho hmom hk : Claims.newgauss_margin`: (a) from the bound `D ≤ C_{N+1}ε^{N+1}`; (c) on `(0, ε₀]` from
  Proposition 5.6 and on `[ε₀, α⋆]` by the monotonicity of `α ↦ D_α` (certified `Wave18b.Dpop_anti`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional StatFormal.CrossLaws StatFormal.Distances

/-- The Gaussian profile `e^{−x²/(2σ²)}` is continuous and integrable. -/
theorem gauss_profile_facts {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ∧
      Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) := by
  refine ⟨by fun_prop, ?_⟩
  have h := integrable_exp_neg_mul_sq (b := 1 / (2 * σ ^ 2)) (by positivity)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  congr 1
  ring

/-- **The Gaussian upper bound** (Proposition S4.15 (b) with `2N` moments): `D̄_{α⋆−ε} ≤ Kε^{N+1}` for small `ε`. -/
theorem gauss_upper (hmom : Claims.newmoments) (hk : Claims.kernel_instances)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {σ : ℝ} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ}
    (hσ : 0 < σ) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2)))
    (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (N : ℕ) (hN : 1 ≤ N) :
    ∃ K ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₂,
      StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) ≤ K * ε ^ ((N : ℝ) + 1) := by
  have hpq := cross_zero hcross
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r₀, hr₀, hpc, hqc⟩, -, -, hd, hℓ⟩ := hcross
  obtain ⟨TN, wN, -, hwN, -, -, hB⟩ := hmom P Q p q x₀ r₀ ℓ₀ hpm hqm hp0 hq0 hP hQ hr₀ hpc hqc hd hℓ hpq hpx (2 * N)
    (by omega)
  obtain ⟨hkc, hki⟩ := gauss_profile_facts hσ
  have hint := ((hk.2.2.2 σ hσ).2.2 (2 * N)).1
  obtain ⟨K, hK⟩ := hB H φ (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) hkc hki hg hint
  refine ⟨K, ℓ₀ * wN ^ 2 / 8, by positivity, fun ε hε => ?_⟩
  obtain ⟨h1', h2'⟩ := hK ε hε
  have he : (1 : ℝ) + ((2 * N : ℕ) : ℝ) / 2 = (N : ℝ) + 1 := by push_cast; ring
  rw [he] at h2'
  exact h1'.trans h2'

/-- **The Gaussian lower bound** (Theorem S4.13 with its `ρ_ε`): for every `c > π²σ²ℓ₀/8`, `e^{−c/ε} ≤ D̄_{α⋆−ε}` for small `ε`. -/
theorem gauss_lower (h1 : Claims.tv_density) (hrho : Claims.newgauss_thm_rho)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {σ : ℝ} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ}
    (hσ : 0 < σ) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2)))
    (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTail P Q x₀) {c : ℝ}
    (hc : Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 < c) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
      Real.exp (-c / ε) ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) := by
  obtain ⟨htv0, -⟩ := cross_tv h1 hcross hpx
  have hℓ₀ : 0 < ℓ₀ := hcross.2.2.2.2.2.2.2.2.2.2
  set c' := Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 with hc'
  have hc'0 : 0 < c' := by positivity
  set m₁ := c' + (c - c') / 3 with hm₁
  set m₂ := c' + 2 * (c - c') / 3 with hm₂
  have hm₁0 : 0 < m₁ := by rw [hm₁]; linarith
  have hc'm₁ : c' < m₁ := by rw [hm₁]; linarith
  have hm₁m₂ : m₁ < m₂ := by rw [hm₁, hm₂]; linarith
  have hm₂c : m₂ < c := by rw [hm₂]; linarith
  set θ := c' / m₁ with hθ
  have hθ0 : 0 < θ := div_pos hc'0 hm₁0
  have hθ1 : θ < 1 := (div_lt_one hm₁0).mpr hc'm₁
  set ℓ := ℓ₀ * (m₂ / m₁) with hℓdef
  have hℓℓ₀ : ℓ₀ < ℓ := by
    rw [hℓdef]
    have : 1 < m₂ / m₁ := (one_lt_div hm₁0).mpr hm₁m₂
    nlinarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨w, hw, -, hlip⟩ := cross_lip hcross (sub_pos.mpr hℓℓ₀)
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -, hsR, hsL, -, -⟩ := hcross
  obtain ⟨CT, a, hCT, ha, htail⟩ := expTail_tailPlus hexp
  have hloc : ∀ᵐ x ∂volume, ENNReal.ofReal |x - x₀| ≤ ENNReal.ofReal w → |p x - q x| ≤ ℓ * |x - x₀| :=
    ae_of_all _ fun x hx => by
      have h := hlip x ((ENNReal.ofReal_le_ofReal_iff hw.le).mp hx)
      rwa [add_sub_cancel] at h
  obtain ⟨-, C, ε₃, hε₃, hε₃e, hε₃tv, hb⟩ := hrho H φ σ P Q p q x₀ ℓ (ENNReal.ofReal w) CT a θ hσ hg hpm hqm hp0 hq0
    hP hQ hsR hsL hℓ0 (ENNReal.ofReal_pos.mpr hw) hloc hCT ha htail hθ0 hθ1 htv0
  set ε₁ := min ε₃ (((c - m₂) / (2 * (1 + |C|))) ^ 2) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε₃ (pow_pos (div_pos (by linarith) (by positivity)) 2)
  refine ⟨ε₁, hε₁0, (min_le_left _ _).trans hε₃tv, fun ε hε => ?_⟩
  have hε3 : ε ≤ ε₃ := hε.2.trans (min_le_left _ _)
  obtain ⟨hu, hlog⟩ := hb ε ⟨hε.1, hε3⟩
  have heq : σ ^ 2 * ℓ * Real.pi ^ 2 / (8 * θ * ε) = m₂ / ε := by
    rw [hℓdef, hθ, hc']
    field_simp
  rw [heq] at hlog
  exact exp_le_of_log_bound hu hε.1 (lt_of_le_of_lt hε3 hε₃e) hm₂c (hε.2.trans (min_le_right _ _)) hlog

/-- `Kε^{N+1} ≤ max(K, 0)ε^N` for `0 < ε ≤ 1`. -/
theorem pow_succ_le {K ε : ℝ} (N : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    K * ε ^ ((N : ℝ) + 1) ≤ max K 0 * ε ^ N := by
  rw [Real.rpow_add hε, Real.rpow_one, Real.rpow_natCast]
  have hεN : 0 ≤ ε ^ N := pow_nonneg hε.le N
  calc K * (ε ^ N * ε) ≤ max K 0 * (ε ^ N * ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * ε ^ N := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        nlinarith

/-- Q22 `newgauss` (Proposition 5.6), from Q1 (`Claims.tv_density`, chunk A), Q17 (`Claims.newgauss_thm_rho`, chunk G),
Q20 (`Claims.newmoments`, chunk T) and Q7 (`Claims.kernel_instances`, chunk A). -/
theorem newgauss_of (h1 : Claims.tv_density) (hrho : Claims.newgauss_thm_rho) (hmom : Claims.newmoments)
    (hk : Claims.kernel_instances) : Claims.newgauss := by
  intro H _ _ _ _ φ σ P Q _ _ p q x₀ ℓ₀ hσ hg hcross hpx hexp c hc N hN
  obtain ⟨htv0, htv1⟩ := cross_tv h1 hcross hpx
  obtain ⟨ε₁, hε₁, hε₁tv, hlow⟩ := gauss_lower h1 hrho hσ hg hcross hpx hexp hc
  obtain ⟨K, ε₂, hε₂, hup⟩ := gauss_upper hmom hk hσ hg hcross hpx N hN
  have h1tv : 0 ≤ (1 - tvDist P Q)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨min ε₁ (min ε₂ 1), (1 - tvDist P Q)⁻¹ * max K 0, lt_min hε₁ (lt_min hε₂ one_pos),
    (min_le_left _ _).trans hε₁tv, fun ε hε => ⟨?_, ?_⟩⟩
  · have hε1 : ε ≤ ε₁ := hε.2.trans (min_le_left _ _)
    exact (hlow ε ⟨hε.1, hε1⟩).trans (uPath_le_Dpop φ P Q (by linarith))
  · have hε2 : ε ≤ ε₂ := hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεone : ε ≤ 1 := hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc Dpop φ P Q (tvDist P Q - ε) ≤ (1 - tvDist P Q)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) :=
          Dpop_le_uPath_div φ P Q htv1 hε.1.le
      _ ≤ (1 - tvDist P Q)⁻¹ * (max K 0 * ε ^ N) :=
          mul_le_mul_of_nonneg_left ((hup ε ⟨hε.1, hε2⟩).trans (pow_succ_le N hε.1 hεone)) h1tv
      _ = (1 - tvDist P Q)⁻¹ * max K 0 * ε ^ N := by ring

/-- Q22 `newgauss_margin` (main :138, :257-258), from the hypotheses of `newgauss_of`. -/
theorem newgauss_margin_of (h1 : Claims.tv_density) (hrho : Claims.newgauss_thm_rho) (hmom : Claims.newmoments)
    (hk : Claims.kernel_instances) : Claims.newgauss_margin := by
  intro H _ _ _ _ φ σ P Q _ _ p q x₀ ℓ₀ hσ hg hcross hpx hexp
  have hG := newgauss_of h1 hrho hmom hk H φ σ P Q p q x₀ ℓ₀ hσ hg hcross hpx hexp
  obtain ⟨htv0, htv1⟩ := cross_tv h1 hcross hpx
  refine ⟨fun N => ?_, fun c hc => ?_⟩
  · -- (a) faster than every power
    obtain ⟨ε₀, CN, hε₀, -, hb⟩ := hG (Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 + 1) (by linarith) (N + 1) (by omega)
    have hlim : Tendsto (fun ε : ℝ => CN * ε) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => CN * ε) (𝓝 0) (𝓝 (CN * 0)) := (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc (0 : ℝ) ε₀ := Ioc_mem_nhdsGT hε₀
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [hev] with ε hε
      exact div_nonneg (StatFormal.MomentTrim.Dpop_nonneg φ P Q _) (pow_nonneg hε.1.le N)
    · filter_upwards [hev] with ε hε
      have hpos : 0 < ε ^ N := pow_pos hε.1 N
      rw [div_le_iff₀ hpos]
      calc Dpop φ P Q (tvDist P Q - ε) ≤ CN * ε ^ (N + 1) := (hb ε hε).2
        _ = CN * ε * ε ^ N := by ring
  · -- (c) a margin of exponential type on `(0, α⋆]`
    have hℓ₀ : 0 < ℓ₀ := hcross.2.2.2.2.2.2.2.2.2.2
    have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
    obtain ⟨ε₀, _CN, hε₀, hε₀tv, hb⟩ := hG c hc 1 le_rfl
    refine ⟨min 1 (Real.exp (-c / ε₀)), lt_min one_pos (Real.exp_pos _), fun ε hε => ?_⟩
    have hexp1 : Real.exp (-c / ε) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.1.le)
    rcases le_or_gt ε ε₀ with hle | hgt
    · calc min 1 (Real.exp (-c / ε₀)) * Real.exp (-c / ε) ≤ 1 * Real.exp (-c / ε) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
        _ = Real.exp (-c / ε) := one_mul _
        _ ≤ Dpop φ P Q (tvDist P Q - ε) := (hb ε ⟨hε.1, hle⟩).1
    · have hmono : Dpop φ P Q (tvDist P Q - ε₀) ≤ Dpop φ P Q (tvDist P Q - ε) :=
        StatFormal.Wave18b.Dpop_anti P Q φ (by linarith [hε.2]) (by linarith) (by linarith)
      calc min 1 (Real.exp (-c / ε₀)) * Real.exp (-c / ε) ≤ min 1 (Real.exp (-c / ε₀)) * 1 :=
            mul_le_mul_of_nonneg_left hexp1 (le_min zero_le_one (Real.exp_pos _).le)
        _ ≤ Real.exp (-c / ε₀) := by rw [mul_one]; exact min_le_right _ _
        _ ≤ Dpop φ P Q (tvDist P Q - ε₀) := (hb ε₀ ⟨hε₀, le_rfl⟩).1
        _ ≤ Dpop φ P Q (tvDist P Q - ε) := hmono

end StatFormal.Wave31tq.RouteM
