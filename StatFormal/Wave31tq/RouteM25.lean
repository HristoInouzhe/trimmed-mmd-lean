import StatFormal.Wave31tq.RouteM22
import StatFormal.Wave31tq.RouteM26
import StatFormal.Wave31tl.Proofs
import StatFormal.Wave31to.Proofs

/-!
# Wave 31tq, route M (Q25): the split-sample rate under Proposition 5.5 and the `τ^A` converse (untrusted)

* `rate_sobolev_split_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) : Claims.rate_sobolev_split`: the margin
  `PolyMargin c (2s+3)/4` of Corollary S4.11 (`sobolev_lower`) in the certified `Wave31tl.same_rate`, `1/(2γ) = 2/(2s+3)`;
* `converse_poly_route : Claims.converse_poly`: the certified `Wave31to.newconverse` at `ε = min{α⋆, ε₀, (g_{n,m}/c₂)^{1/γ}}`
  (`D_{α⋆−ε} ≤ c₂ε^γ ≤ g_{n,m}`; at `ε = 0`, `D_{α⋆} ≤ g_{n,m}`);
* `lower_sobolev_A_of (h1) (hcor) (hmom : Claims.newmoments) (h5 : Claims.sobolev_angular) : Claims.lower_sobolev_A` and
  `slow_gauss_A_of (h1) (hrho : Claims.newgauss_thm_rho) (hmom) (hk : Claims.kernel_instances) : Claims.slow_gauss_A`: the converse
  with the upper bounds of Propositions 5.5 and 5.6, `g_{n,m} ≥ D L (2(n∧m))^{−1/2}` (`gNM_ge`) and `D > 0` (φ not constant:
  characteristic, Q5(b), resp. the Gaussian Gram); "not `O((n∧m)^{−a})`" from `c(n∧m)^{−1/(2N)}` with `1/(2N) < a`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.TrimmedMMD.Unconditional StatFormal.CrossLaws StatFormal.Distances

/-- Q25 (b) `rate_sobolev_split`, from Q1 (`Claims.tv_density`) and Q12 case 2 (`Claims.newsobolev_cor_line`). -/
theorem rate_sobolev_split_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) : Claims.rate_sobolev_split := by
  intro H _ _ _ _ φ k₀ c C s κ P Q _ _ p q x₀ ℓ₀ J δ s2 η hk hki hg hc hs hkb hcross hpx hexp hκ hJ hδ hδ1 hs2 hs24 hη hη1
  obtain ⟨-, htv1⟩ := cross_tv h1 hcross hpx
  obtain ⟨-, cm, hcm⟩ := sobolev_lower h1 hcor hk hki hg hc hs (fun ξ => (hkb ξ).1) hcross hpx hexp
  obtain ⟨-, hsm, -, -⟩ := StatFormal.Wave31tp.mmd_fourier ℝ H φ k₀ hk hki hg
  obtain ⟨K, hK0, hK⟩ := StatFormal.Wave31tl.same_rate ℝ H φ κ P Q cm ((2 * s + 3) / 4) J δ s2 η hsm hκ hcm htv1 hJ hδ hδ1
    hs2 hs24 hη hη1
  have hs3 : 2 * s + 3 ≠ 0 := by linarith
  have he : (1 : ℝ) / (2 * ((2 * s + 3) / 4)) = 2 / (2 * s + 3) := by field_simp; ring
  refine ⟨K, hK0, fun n m α R h hα hR hdef hn hm hmesh => ?_⟩
  obtain ⟨E, hE, hprob, hsub⟩ := hK n m α R h hα hR hdef hn hm hmesh
  rw [he] at hsub
  exact ⟨E, hE, hprob, hsub⟩

/-- Q25 (c1) `converse_poly` (general form), from the certified `Wave31to.newconverse`. -/
theorem converse_poly_route : Claims.converse_poly := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ D δ δ' c₂ γ ε₀ n m hsm hκ hD htv1 hδ hδδ' hδ'1 hn hm hc₂ hγ hε₀ hε₀tv hup
  obtain ⟨hD0, E, hE, hprob, hEz⟩ :=
    StatFormal.Wave31to.newconverse 𝒳 H P Q φ κ D δ δ' n m hsm hκ hD htv1 hδ hδδ' hδ'1 hn hm
  refine ⟨E, hE, hprob, fun z hz => ?_⟩
  set g := StatFormal.Wave31to.gNM D δ δ' n m with hgdef
  have hg0 : 0 ≤ g := (StatFormal.MomentTrim.Dpop_nonneg φ P Q _).trans hD0
  have hgc : 0 ≤ g / c₂ := div_nonneg hg0 hc₂.le
  set ε := min (tvDist P Q) (min ε₀ ((g / c₂) ^ (1 / γ))) with hεdef
  have hε0 : 0 ≤ ε := le_min (tvDist_nonneg P Q) (le_min hε₀.le (Real.rpow_nonneg hgc _))
  refine hEz z hz ε ⟨hε0, min_le_left _ _⟩ ?_
  rcases hε0.eq_or_lt with h0 | hpos
  · rw [← h0, sub_zero]; exact hD0
  · have hεε₀ : ε ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hεg : ε ≤ (g / c₂) ^ (1 / γ) := (min_le_right _ _).trans (min_le_right _ _)
    calc Dpop φ P Q (tvDist P Q - ε) ≤ c₂ * ε ^ γ := hup ε ⟨hpos, hεε₀⟩
      _ ≤ c₂ * ((g / c₂) ^ (1 / γ)) ^ γ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos.le hεg hγ.le) hc₂.le
      _ = g := by rw [one_div, Real.rpow_inv_rpow hgc hγ.ne']; field_simp

/-- `L = √log(1/δ) − √log(1/δ′) > 0` for `0 < δ < δ′ < 1`. -/
theorem sqrtLog_pos {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ < δ') (hδ'1 : δ' < 1) :
    0 < √(Real.log (1 / δ)) - √(Real.log (1 / δ')) := by
  have hδ'0 : 0 < δ' := hδ.trans hδδ'
  have h1 : 1 < 1 / δ' := by rw [lt_div_iff₀ hδ'0]; linarith
  have h2 : 1 / δ' < 1 / δ := one_div_lt_one_div_of_lt hδ hδδ'
  have hl1 : 0 < Real.log (1 / δ') := Real.log_pos h1
  have hl2 : Real.log (1 / δ') < Real.log (1 / δ) := Real.log_lt_log (by linarith) h2
  exact sub_pos.mpr (Real.sqrt_lt_sqrt hl1.le hl2)

/-- **`g_{n,m} ≥ D L (2(n∧m))^{−1/2}`** for `n, m ≥ 1`, `D, L ≥ 0`. -/
theorem gNM_ge {D δ δ' : ℝ} {n m : ℕ} (hD : 0 ≤ D) (hL : 0 ≤ √(Real.log (1 / δ)) - √(Real.log (1 / δ')))
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    D * (√(Real.log (1 / δ)) - √(Real.log (1 / δ'))) / √2 * (((min n m : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
      StatFormal.Wave31to.gNM D δ δ' n m := by
  set L := √(Real.log (1 / δ)) - √(Real.log (1 / δ')) with hLdef
  set x : ℝ := ((min n m : ℕ) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast (le_min hn hm : 1 ≤ min n m)
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hinv : 1 / x ≤ 1 / (n : ℝ) + 1 / (m : ℝ) := by
    rcases le_total n m with h | h
    · have : x = n := by rw [hx, Nat.min_eq_left h]
      rw [this]; have : 0 ≤ 1 / (m : ℝ) := by positivity
      linarith
    · have : x = m := by rw [hx, Nat.min_eq_right h]
      rw [this]; have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
  have hsq : (√2)⁻¹ * (√x)⁻¹ ≤ √((1 / (n : ℝ) + 1 / (m : ℝ)) / 2) := by
    rw [← mul_inv, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    have : (2 * x)⁻¹ = (1 / x) / 2 := by field_simp
    rw [this]
    linarith
  have hxr : x ^ (-(1 / 2 : ℝ)) = (√x)⁻¹ := by rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
  unfold StatFormal.Wave31to.gNM
  rw [hxr]
  calc D * L / √2 * (√x)⁻¹ = D * L * ((√2)⁻¹ * (√x)⁻¹) := by ring
    _ ≤ D * L * √((1 / (n : ℝ) + 1 / (m : ℝ)) / 2) := mul_le_mul_of_nonneg_left hsq (mul_nonneg hD hL)
    _ = D * √((1 / (n : ℝ) + 1 / (m : ℝ)) / 2) * L := by ring

/-- **The converse rate.** If `g ≥ (DL/√2)x^{−1/2}` with `x ≥ 1`, then
`C₁x^{−1/(2γ)} ≤ min{a⋆, ε₀, (g/c₂)^{1/γ}}` with `C₁ = min{a⋆, ε₀, (DL/(√2c₂))^{1/γ}} > 0`. -/
theorem converse_lower {aS ε₀ c₂ γ D L g x : ℝ} (haS : 0 ≤ aS) (hε₀ : 0 ≤ ε₀) (hc₂ : 0 < c₂) (hγ : 0 < γ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hx : 1 ≤ x)
    (hg : D * L / √2 * x ^ (-(1 / 2 : ℝ)) ≤ g) :
    min (min aS ε₀) ((D * L / (√2 * c₂)) ^ (1 / γ)) * x ^ (-(1 / (2 * γ))) ≤ min aS (min ε₀ ((g / c₂) ^ (1 / γ))) := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x ^ (-(1 / (2 * γ))) := Real.rpow_pos_of_pos hx0 _
  have hxle : x ^ (-(1 / (2 * γ))) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by
    have : 0 < 1 / (2 * γ) := by positivity
    linarith)
  set A := (D * L / (√2 * c₂)) ^ (1 / γ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  -- the third entry
  have hthird : A * x ^ (-(1 / (2 * γ))) ≤ (g / c₂) ^ (1 / γ) := by
    have hy0 : 0 ≤ D * L / (√2 * c₂) := by positivity
    have hpow : A * x ^ (-(1 / (2 * γ))) = (D * L / (√2 * c₂) * x ^ (-(1 / 2 : ℝ))) ^ (1 / γ) := by
      rw [Real.mul_rpow hy0 (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
      congr 2
      field_simp
    rw [hpow]
    apply Real.rpow_le_rpow (mul_nonneg hy0 (Real.rpow_nonneg hx0.le _)) _ (by positivity)
    rw [le_div_iff₀ hc₂]
    calc D * L / (√2 * c₂) * x ^ (-(1 / 2 : ℝ)) * c₂ = D * L / √2 * x ^ (-(1 / 2 : ℝ)) := by
          field_simp
      _ ≤ g := hg
  set C₁ := min (min aS ε₀) A with hC₁
  have hC₁0 : 0 ≤ C₁ := le_min (le_min haS hε₀) hA0
  have hC₁x : C₁ * x ^ (-(1 / (2 * γ))) ≤ C₁ := mul_le_of_le_one_right hC₁0 hxle
  refine le_min (hC₁x.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (le_min (hC₁x.trans ((min_le_left _ _).trans (min_le_right _ _))) ?_)
  calc C₁ * x ^ (-(1 / (2 * γ))) ≤ A * x ^ (-(1 / (2 * γ))) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hxp.le
    _ ≤ _ := hthird

/-- A feature map that separates finite measures is not constant: `D > 0` for every bound `‖φ x − φ x′‖ ≤ D`. -/
theorem D_pos_of_inj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {φ : ℝ → H}
    (hinj : ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν], ∫ x, φ x ∂μ = ∫ x, φ x ∂ν → μ = ν)
    {D : ℝ} (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) : 0 < D := by
  have hne : φ 0 ≠ φ 1 := by
    intro heq
    have h := hinj (Measure.dirac 0) (Measure.dirac 1) (by rw [integral_dirac, integral_dirac, heq])
    have h0 := congrArg (fun μ : Measure ℝ => μ {0}) h
    simp at h0
  exact lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (hD 0 1)

/-- The Gaussian feature map is not constant: `D > 0` for every bound `‖φ x − φ x′‖ ≤ D`. -/
theorem D_pos_gauss {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {φ : ℝ → H} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-(x - y) ^ 2 / (2 * σ ^ 2))) {D : ℝ} (hD : ∀ x x', ‖φ x - φ x'‖ ≤ D) :
    0 < D := by
  have hne : φ 0 ≠ φ 1 := by
    intro heq
    have h01 := hg 0 1
    have h11 := hg 1 1
    rw [heq] at h01
    have hlt : Real.exp (-(0 - 1) ^ 2 / (2 * σ ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 2 * σ ^ 2 := by positivity
      rw [div_neg_iff]; right; constructor <;> nlinarith)
    have h1 : Real.exp (-(1 - 1) ^ 2 / (2 * σ ^ 2)) = 1 := by simp
    linarith
  exact lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (hD 0 1)

/-- Q25 (c3) `lower_sobolev_A`, from Q1, Q12 case 2, Q20 (through `newsobolev_of`) and Q5 (`Claims.sobolev_angular`). -/
theorem lower_sobolev_A_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments)
    (h5 : Claims.sobolev_angular) : Claims.lower_sobolev_A := by
  intro H _ _ _ _ φ k₀ c C s κ D δ δ' P Q _ _ p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp hκ hD hδ hδδ' hδ'1
  obtain ⟨htv0, htv1, c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hε₀tv, hb⟩ :=
    newsobolev_of h1 hcor hmom H φ k₀ c C s P Q p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  have hDpos : 0 < D := D_pos_of_inj (sobolev_char h5 hk hki hg hc (fun ξ => (hkb ξ).1)).2 hD
  obtain ⟨-, hsm, -, -⟩ := StatFormal.Wave31tp.mmd_fourier ℝ H φ k₀ hk hki hg
  have hγ : 0 < (2 * s + 3) / 4 := by linarith
  have hL := sqrtLog_pos hδ hδδ' hδ'1
  have hs3 : 2 * s + 3 ≠ 0 := by linarith
  have he : (1 : ℝ) / (2 * ((2 * s + 3) / 4)) = 2 / (2 * s + 3) := by field_simp; ring
  set A := (D * (√(Real.log (1 / δ)) - √(Real.log (1 / δ'))) / (√2 * c₂)) ^ (1 / ((2 * s + 3) / 4)) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min (min (tvDist P Q) ε₀) A, 1, lt_min (lt_min htv0 hε₀) hA0, fun n m hnm => ?_⟩
  have hn : 1 ≤ n := (le_min_iff.mp hnm).1
  have hm : 1 ≤ m := (le_min_iff.mp hnm).2
  obtain ⟨E, hE, hprob, hEz⟩ := converse_poly_route ℝ H P Q φ κ D δ δ' c₂ ((2 * s + 3) / 4) ε₀ n m hsm hκ hD htv1 hδ
    hδδ' hδ'1 hn hm hc₂ hγ hε₀ hε₀tv (fun ε hε => (hb ε hε).2)
  refine ⟨E, hE, hprob, fun z hz => ?_⟩
  have hx1 : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast (le_min hn hm : 1 ≤ min n m)
  have hbound := converse_lower (tvDist_nonneg P Q) hε₀.le hc₂ hγ hDpos.le hL.le hx1 (gNM_ge hDpos.le hL.le hn hm)
  rw [he] at hbound
  exact hbound.trans (hEz z hz)

/-- Q25 (e) `slow_gauss_A`, from Q1, Q17 (`Claims.newgauss_thm_rho`), Q20 and Q7 (through `newgauss_of`). -/
theorem slow_gauss_A_of (h1 : Claims.tv_density) (hrho : Claims.newgauss_thm_rho) (hmom : Claims.newmoments)
    (hk : Claims.kernel_instances) : Claims.slow_gauss_A := by
  intro H _ _ _ _ φ σ κ D δ δ' P Q _ _ p q x₀ ℓ₀ hσ hg hcross hpx hexp hκ hD hδ hδδ' hδ'1
  obtain ⟨htv0, htv1⟩ := cross_tv h1 hcross hpx
  have hℓ₀ : 0 < ℓ₀ := hcross.2.2.2.2.2.2.2.2.2.2
  have hG := newgauss_of h1 hrho hmom hk H φ σ P Q p q x₀ ℓ₀ hσ hg hcross hpx hexp
  have hDpos : 0 < D := D_pos_gauss hσ hg hD
  obtain ⟨hkc, hki⟩ := gauss_profile_facts hσ
  obtain ⟨-, hsm, -, -⟩ := StatFormal.Wave31tp.mmd_fourier ℝ H φ (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) hkc hki hg
  have hL := sqrtLog_pos hδ hδδ' hδ'1
  have part1 : ∀ N : ℕ, 1 ≤ N → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ min n m →
      ∃ E : Set ((Fin n → ℝ) × (Fin m → ℝ)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ') ≤ StatFormal.Wave30tp.sampleLaw P Q n m E ∧
        E ⊆ {z | c * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * (N : ℝ)))) ≤ tvDist P Q -
              StatFormal.TrimmedMMD.alphaHat (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m)} := by
    intro N hN
    obtain ⟨ε₀, CN, hε₀, hε₀tv, hb⟩ := hG (Real.pi ^ 2 * σ ^ 2 * ℓ₀ / 8 + 1) (by linarith) N hN
    set c₂ := max CN 1 with hc₂def
    have hc₂ : 0 < c₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hγ : 0 < (N : ℝ) := by exact_mod_cast hN
    have hup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, Dpop φ P Q (tvDist P Q - ε) ≤ c₂ * ε ^ (N : ℝ) := fun ε hε => by
      rw [Real.rpow_natCast]
      exact (hb ε hε).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hε.1.le N))
    set A := (D * (√(Real.log (1 / δ)) - √(Real.log (1 / δ'))) / (√2 * c₂)) ^ (1 / (N : ℝ)) with hA
    have hA0 : 0 < A := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨min (min (tvDist P Q) ε₀) A, lt_min (lt_min htv0 hε₀) hA0, 1, fun n m hnm => ?_⟩
    have hn : 1 ≤ n := (le_min_iff.mp hnm).1
    have hm : 1 ≤ m := (le_min_iff.mp hnm).2
    obtain ⟨E, hE, hprob, hEz⟩ := converse_poly_route ℝ H P Q φ κ D δ δ' c₂ (N : ℝ) ε₀ n m hsm hκ hD htv1 hδ
      hδδ' hδ'1 hn hm hc₂ hγ hε₀ hε₀tv hup
    refine ⟨E, hE, hprob, fun z hz => ?_⟩
    have hx1 : (1 : ℝ) ≤ ((min n m : ℕ) : ℝ) := by exact_mod_cast (le_min hn hm : 1 ≤ min n m)
    exact (converse_lower (tvDist_nonneg P Q) hε₀.le hc₂ hγ hDpos.le hL.le hx1 (gNM_ge hDpos.le hL.le hn hm)).trans
      (hEz z hz)
  refine ⟨part1, fun a C ha hC => ?_⟩
  -- `N` with `1/(2N) < a`
  set N := ⌈1 / a⌉₊ + 1 with hNdef
  have hN : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNa : 1 / (2 * (N : ℝ)) < a := by
    have h1 : 1 / a < (N : ℝ) := by
      rw [hNdef]; push_cast; linarith [Nat.le_ceil (1 / a)]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha] at h1
    nlinarith
  obtain ⟨c, hc, n₀, hn₀⟩ := part1 N hN
  set b := a - 1 / (2 * (N : ℝ)) with hb
  have hb0 : 0 < b := by linarith
  refine ⟨max n₀ (⌈(C / c) ^ (1 / b)⌉₊ + 1), fun n m hnm => ?_⟩
  obtain ⟨E, hE, hprob, hsub⟩ := hn₀ n m ((le_max_left _ _).trans hnm)
  refine ⟨E, hE, hprob, fun z hz => ?_⟩
  set x : ℝ := ((min n m : ℕ) : ℝ) with hx
  have hxbig : (C / c) ^ (1 / b) < x := by
    have h1 : ((⌈(C / c) ^ (1 / b)⌉₊ + 1 : ℕ) : ℝ) ≤ x := by
      rw [hx]; exact_mod_cast (le_max_right _ _).trans hnm
    push_cast at h1
    linarith [Nat.le_ceil ((C / c) ^ (1 / b))]
  have hx0 : 0 < x := lt_of_le_of_lt (Real.rpow_nonneg (by positivity) _) hxbig
  have hxb : C / c < x ^ b := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) hxbig hb0
    rwa [one_div, Real.rpow_inv_rpow (by positivity) hb0.ne'] at h
  have hsplit : x ^ (-(1 / (2 * (N : ℝ)))) = x ^ b * x ^ (-a) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hb]; ring
  have hxa : 0 < x ^ (-a) := Real.rpow_pos_of_pos hx0 _
  have hlt : C * x ^ (-a) < c * x ^ (-(1 / (2 * (N : ℝ)))) := by
    rw [hsplit]
    have : C < c * x ^ b := by rwa [div_lt_iff₀' hc] at hxb
    nlinarith
  exact lt_of_lt_of_le hlt (hsub hz)

end StatFormal.Wave31tq.RouteM
