import StatFormal.Wave31tq.RouteSThm
import StatFormal.Lib.MollifierNorm.Margin
import StatFormal.Lib.MollifierNorm.Intervals
import StatFormal.Wave31ti.Proofs

/-!
# Wave 31tq, route S: Corollary S4.11, the exponent of the Sobolev margin (untrusted proof file)

Q12 `newsobolev_cor_bounded` and `newsobolev_cor_line`, with the cross-chunk hypotheses of Theorem S4.10 (Q1 `tv_density`,
Q5 `sobolev_angular`). The mollifier `b` and the integer `m` of the theorem are constructed (`MollifierNorm.exists_mollifier`,
a normalized `ContDiffBump`; `exists_nat_four_mul_gt`). Route (printed, S4 :632-648): the width `w(ε) = (ε/A)^{1/(r+1)}` makes
the error of `f_w` at most `ε/2`; the denominator of Theorem S4.10 is at most `K w^{1−2s}` (case 1: `w^{1−2s} ≥ 1`; case 2:
`ρ(ε) = 1 + a log⁺(4C_T/ε)`, `T(ρ(ε)) ≤ ε/4`, `Π = V = 2` by `MollifierNorm.volume_symmDiff_translate_le` and the tube
`[x₀ − t, x₀ + t]`, and the logarithm is dominated, `MollifierNorm.log_div_le_rpow`); `MollifierNorm.margin_rpow_eq` turns the
bound into `c₁ε^γ`; for `ε ∈ [ε₁, α⋆]` the path is nonincreasing (certified `Wave31ti.pathconvex`), and `D ≥ D̄` (certified
`Wave31to.newapproxgen_iii_a`) gives Assumption 5.1 with `c₀ = c₁(ε₁/α⋆)^γ` (`polyMargin_of_small`).
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff symmDiff InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tq.RouteS

open StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional

section Margin

variable {𝒳 H : Type} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {φ : 𝒳 → H} {κ : ℝ}

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- `ξ_ℋ(ε) ≥ 0` (a supremum of nonnegative numbers, `sSup ∅ = 0`). -/
theorem xiH_nonneg (ε : ℝ) : 0 ≤ StatFormal.Wave31to.xiH φ P Q ε :=
  Real.sSup_nonneg fun _ ⟨_, _, _, ht⟩ => ht ▸ div_nonneg (le_max_right _ _) (norm_nonneg _)

/-- **From a small-`ε` bound to Assumption 5.1**: if `D̄_{α⋆−ε} ≥ c₁ε^γ` for `ε ∈ (0, ε₁]`, then
`D_{α⋆−e} ≥ c₁(ε₁/α⋆)^γ e^γ` for every `e ∈ [0, α⋆]` (monotonicity of `D̄` beyond `ε₁`, and `D ≥ D̄`). -/
theorem polyMargin_of_small (hφm : StronglyMeasurable φ) (hφb : ∀ x, ‖φ x‖ ≤ κ)
    (htv0 : 0 < StatFormal.Distances.tvDist P Q) (htv1 : StatFormal.Distances.tvDist P Q < 1) {c₁ ε₁ γ : ℝ}
    (hc₁ : 0 < c₁) (hε₁ : 0 < ε₁) (hε₁' : ε₁ ≤ StatFormal.Distances.tvDist P Q) (hγ : 1 ≤ γ)
    (hsmall : ∀ ε ∈ Ioc (0 : ℝ) ε₁,
      c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) :
    StatFormal.Wave31ti.PolyMargin φ P Q (c₁ * (ε₁ / StatFormal.Distances.tvDist P Q) ^ γ) γ := by
  set α := StatFormal.Distances.tvDist P Q with hα
  have hq : 0 < ε₁ / α := div_pos hε₁ htv0
  have hq1 : ε₁ / α ≤ 1 := (div_le_one htv0).2 hε₁'
  have hqγ : (ε₁ / α) ^ γ ≤ 1 := Real.rpow_le_one hq.le hq1 (by linarith)
  obtain ⟨-, hiii⟩ := StatFormal.Wave31to.newapproxgen_iii_a 𝒳 H P Q φ κ hφm hφb htv0 htv1
  obtain ⟨-, hanti⟩ := StatFormal.Wave31ti.pathconvex 𝒳 H P Q φ κ hφm hφb
  refine ⟨mul_pos hc₁ (Real.rpow_pos_of_pos hq γ), hγ, fun e he => ?_⟩
  obtain ⟨-, hUD, hxi, -⟩ := hiii e he
  refine le_trans ?_ hUD
  rcases le_or_gt e ε₁ with heε | heε
  · rcases he.1.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith), mul_zero]
      exact (xiH_nonneg 0).trans (h0 ▸ hxi)
    · calc c₁ * (ε₁ / α) ^ γ * e ^ γ ≤ c₁ * 1 * e ^ γ := by gcongr
        _ = c₁ * e ^ γ := by ring
        _ ≤ _ := hsmall e ⟨hpos, heε⟩
  · have hmono : StatFormal.Wave31ti.uPath φ P Q (α - ε₁) ≤ StatFormal.Wave31ti.uPath φ P Q (α - e) :=
      hanti ⟨by linarith [he.2], by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hx : ε₁ / α * e ≤ ε₁ := by
      calc ε₁ / α * e ≤ ε₁ / α * α := mul_le_mul_of_nonneg_left he.2 hq.le
        _ = ε₁ := div_mul_cancel₀ _ htv0.ne'
    calc c₁ * (ε₁ / α) ^ γ * e ^ γ = c₁ * (ε₁ / α * e) ^ γ := by
          rw [mul_assoc, ← Real.mul_rpow hq.le he.1]
      _ ≤ c₁ * ε₁ ^ γ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_nonneg hq.le he.1) hx (by linarith)) hc₁.le
      _ ≤ StatFormal.Wave31ti.uPath φ P Q (α - ε₁) := hsmall ε₁ ⟨hε₁, le_rfl⟩
      _ ≤ _ := hmono

/-- **The conclusion of Corollary S4.11** from the balanced bound `√c (ε/2)/√(K w(ε)^{1−2s}) ≤ D̄_{α⋆−ε}` on `(0, ε₁]`,
`w(ε) = (ε/A)^{1/(r+1)}`. -/
theorem cor_conclusion (hφm : StronglyMeasurable φ) (hφb : ∀ x, ‖φ x‖ ≤ κ)
    (htv0 : 0 < StatFormal.Distances.tvDist P Q) (htv1 : StatFormal.Distances.tvDist P Q < 1) {c s r : ℝ}
    (hc : 0 < c) (hs : 1 / 2 < s) (hr : 0 < r) {ε₁ A K : ℝ} (hε₁ : 0 < ε₁)
    (hε₁' : ε₁ ≤ StatFormal.Distances.tvDist P Q) (hA : 0 < A) (hK : 0 < K)
    (hsmall : ∀ ε ∈ Ioc (0 : ℝ) ε₁, √c * (ε / 2) / √(K * ((ε / A) ^ (1 / (r + 1))) ^ (1 - 2 * s)) ≤
      StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) :
    let γ := 1 + (2 * s - 1) / (2 * (r + 1))
    (∃ c₁ ε₁ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ ε₁ ≤ StatFormal.Distances.tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
        c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε)) ∧
    (∃ cm : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q cm γ) ∧
    1 / (2 * γ) = (r + 1) / (2 * (r + 1) + 2 * s - 1) ∧ (r = 1 → 1 / (2 * γ) = 2 / (2 * s + 3)) := by
  intro γ
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hsK : 0 < √K := Real.sqrt_pos.2 hK
  set c₁ : ℝ := √c / (2 * √K) * A ^ (1 - γ) with hc₁def
  have hc₁ : 0 < c₁ := mul_pos (div_pos hsc (by positivity)) (Real.rpow_pos_of_pos hA _)
  have hb : ∀ ε ∈ Ioc (0 : ℝ) ε₁,
      c₁ * ε ^ γ ≤ StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) := fun ε hε =>
    (le_of_eq (MollifierNorm.margin_rpow_eq (c := c) (s := s) hK hA hr hε.1).symm).trans (hsmall ε hε)
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ (2 * s - 1) / (2 * (r + 1)) := div_nonneg (by linarith) (by positivity)
    show 1 ≤ 1 + (2 * s - 1) / (2 * (r + 1)); linarith
  refine ⟨⟨c₁, ε₁, hc₁, hε₁, hε₁', hb⟩, ⟨_, polyMargin_of_small hφm hφb htv0 htv1 hc₁ hε₁ hε₁' hγ1 hb⟩, ?_, ?_⟩
  · show 1 / (2 * (1 + (2 * s - 1) / (2 * (r + 1)))) = (r + 1) / (2 * (r + 1) + 2 * s - 1)
    have h1 : 0 < 2 * (r + 1) + 2 * s - 1 := by linarith
    field_simp
    ring
  · intro hr1
    show 1 / (2 * (1 + (2 * s - 1) / (2 * (r + 1)))) = 2 / (2 * s + 3)
    rw [hr1]
    have : 2 * (1 + (2 * s - 1) / (2 * (1 + 1))) = (2 * s + 3) / 2 := by ring
    rw [this, one_div_div]

end Margin

/-- The kernel facts used by the corollaries: `φ` is continuous, strongly measurable and bounded by `√(k₀ 0)`. -/
theorem feature_facts {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : V → H} {k₀ : V → ℝ} (hk₀c : Continuous k₀) (hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) :
    StronglyMeasurable φ ∧ ∀ x, ‖φ x‖ ≤ √(k₀ 0) :=
  ⟨(TIKernel.phi_continuous hφ hk₀c).stronglyMeasurable, fun x => by
    rw [← TIKernel.gram_norm_sq hφ x, Real.sqrt_sq (norm_nonneg _)]⟩

/-- Facts about the width `w(ε) = (ε/A)^{1/(r+1)}`: positive, `w^{r+1} = ε/A`, `w ≤ w₀` when `ε ≤ A w₀^{r+1}`, and
`w^{1−2s} ≥ 1` when `w ≤ 1`. -/
theorem width_facts {ε A r w₀ s : ℝ} (hε : 0 < ε) (hA : 0 < A) (hr : 0 < r) (hw₀ : 0 < w₀) (hw₀1 : w₀ ≤ 1)
    (hs : 1 / 2 < s) (hεw : ε ≤ A * w₀ ^ (r + 1)) :
    0 < (ε / A) ^ (1 / (r + 1)) ∧ ((ε / A) ^ (1 / (r + 1))) ^ (r + 1) = ε / A ∧ (ε / A) ^ (1 / (r + 1)) ≤ w₀ ∧
      1 ≤ ((ε / A) ^ (1 / (r + 1))) ^ (1 - 2 * s) := by
  have hεA : 0 < ε / A := div_pos hε hA
  have hr1 : (r + 1) ≠ 0 := by linarith
  have hpos : 0 < (ε / A) ^ (1 / (r + 1)) := Real.rpow_pos_of_pos hεA _
  have hle : (ε / A) ^ (1 / (r + 1)) ≤ w₀ := by
    have h1 : ε / A ≤ w₀ ^ (r + 1) := by rw [div_le_iff₀ hA]; linarith
    calc (ε / A) ^ (1 / (r + 1)) ≤ (w₀ ^ (r + 1)) ^ (1 / (r + 1)) :=
          Real.rpow_le_rpow hεA.le h1 (by positivity)
      _ = w₀ := by rw [one_div, Real.rpow_rpow_inv hw₀.le hr1]
  refine ⟨hpos, ?_, hle, Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos (hle.trans hw₀1) (by linarith)⟩
  rw [one_div, Real.rpow_inv_rpow hεA.le hr1]

theorem newsobolev_cor_line_of (h1 : Claims.tv_density) (h5 : Claims.sobolev_angular) :
    Claims.newsobolev_cor_line := by
  intro H _ _ _ _ φ k₀ c s P Q _ _ p q x₀ r ℓ w₀ CT a hk₀c hk₀i hφ hc hs hspec hp hq hp0 hq0 hP hQ htv0 htv1 hGp hGq
    hr hℓ hw₀ hw₀1 hG3 hCT ha htail
  obtain ⟨b, hb, hb0, hb1, hbs⟩ := MollifierNorm.exists_mollifier ℝ
  obtain ⟨m, hm⟩ := MollifierNorm.exists_nat_four_mul_gt s
  obtain ⟨hφm, hφb⟩ := feature_facts hk₀c hφ
  have hcd : 0 < cJ 1 := by unfold cJ; linarith [StatFormal.JBall.sSup_jBall_Ici_one_lt_one (d := 1)]
  set α := StatFormal.Distances.tvDist P Q with hα
  set C : ℝ := sobConst (cJ 1) s (lapC m b) m with hCdef
  have hC : 0 < C := sobConst_pos hcd hs hm
  set β : ℝ := (2 * s - 1) / (r + 1) with hβdef
  have hβ : 0 < β := div_pos (by linarith) (by linarith)
  set Mβ : ℝ := (CT / (2 * ℓ)) ^ β / β with hMβ
  have hMβ0 : 0 ≤ Mβ := by positivity
  set K : ℝ := 2 ^ s * 2 * (1 + a * Mβ) + C * 2 with hKdef
  have hK : 0 < K := by positivity
  set A : ℝ := 8 * ℓ with hAdef
  have hA : 0 < A := by positivity
  have hAw : 0 < A * w₀ ^ (r + 1) := mul_pos hA (Real.rpow_pos_of_pos hw₀ _)
  refine cor_conclusion hφm hφb htv0 htv1 hc hs hr (ε₁ := min α (A * w₀ ^ (r + 1))) (lt_min htv0 hAw)
    (min_le_left _ _) hA hK (fun ε hε => ?_)
  have hε0 : 0 < ε := hε.1
  have hεw : ε ≤ A * w₀ ^ (r + 1) := hε.2.trans (min_le_right _ _)
  obtain ⟨hw0, hwr, hww₀, hw1s⟩ := width_facts hε0 hA hr hw₀ hw₀1 hs hεw
  set w : ℝ := (ε / A) ^ (1 / (r + 1)) with hwdef
  set L : ℝ := max 0 (Real.log (4 * CT / ε)) with hLdef
  have hL0 : 0 ≤ L := le_max_left _ _
  set ρ : ℝ := 1 + a * L with hρdef
  have hρ1 : 1 ≤ ρ := by have := mul_nonneg ha.le hL0; linarith
  -- the tail at `ρ(ε)`
  have hT : tailOut P Q x₀ ρ ≤ ε / 4 := by
    refine (htail ρ hρ1).trans ?_
    have hx : 0 < 4 * CT / ε := by positivity
    have hexp : Real.exp (-ρ / a) ≤ Real.exp (-Real.log (4 * CT / ε)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : -ρ / a = -(1 / a) - L := by rw [hρdef]; field_simp; ring
      rw [h1]
      have : Real.log (4 * CT / ε) ≤ L := le_max_right _ _
      have : 0 < 1 / a := by positivity
      linarith
    rw [Real.exp_neg, Real.exp_log hx] at hexp
    calc CT * Real.exp (-ρ / a) ≤ CT * (4 * CT / ε)⁻¹ := mul_le_mul_of_nonneg_left hexp hCT.le
      _ = ε / 4 := by field_simp
  -- the hypotheses (G1)-(G3) of Theorem S4.10 on the line
  have hI : (Ioi x₀ ∩ ball x₀ ρ).OrdConnected := by rw [Real.ball_eq_Ioo]; infer_instance
  have hG1 : ∀ h : ℝ, volume (symmDiff (Ioi x₀ ∩ ball x₀ ρ) ((· - h) ⁻¹' (Ioi x₀ ∩ ball x₀ ρ))) ≤
      ENNReal.ofReal (2 * ‖h‖) := fun h => by
    rw [Real.norm_eq_abs]; exact MollifierNorm.volume_symmDiff_translate_le hI h
  have hfr : ∀ x : ℝ, Metric.infDist x (frontier (Ioi x₀)) = |x - x₀| := fun x => by
    rw [frontier_Ioi, Metric.infDist_singleton, Real.dist_eq]
  have hG2 : ∀ t ∈ Ioc (0 : ℝ) w₀, volume {x | x ∈ ball x₀ ρ ∧ Metric.infDist x (frontier (Ioi x₀)) ≤ t} ≤
      ENNReal.ofReal (2 * t) := fun t _ => by
    rw [← Real.volume_closedBall x₀ t]
    refine measure_mono fun x hx => ?_
    rw [mem_closedBall, Real.dist_eq, ← hfr]; exact hx.2
  have hG3' : ∀ᵐ x ∂volume, x ∈ ball x₀ ρ → Metric.infDist x (frontier (Ioi x₀)) ≤ w₀ →
      |p x - q x| ≤ ℓ * Metric.infDist x (frontier (Ioi x₀)) ^ r := by
    filter_upwards [hG3] with x hx
    intro _ hd
    rw [hfr] at hd ⊢
    exact hx hd
  have hspec' : ∀ ξ : ℝ, c * (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ kHat k₀ ξ := fun ξ => by
    rw [Real.norm_eq_abs, sq_abs]; exact hspec ξ
  have hthm := newsobolev_thm_of h1 h5 1 ℝ (Module.finrank_self ℝ) H φ k₀ c s P Q p q (Ioi x₀) x₀ ρ r ℓ w₀ 2 2 b m
    hk₀c hk₀i hφ hc (by norm_num; linarith) hspec' hp hq hp0 hq0 hP hQ htv0 htv1 isOpen_Ioi
    (hGp.mono fun x hx h => hx h) (hGq.mono fun x hx h => hx (not_lt.1 h)) hρ1 hr hℓ hw₀ hw₀1 zero_le_two
    zero_le_two hG1 hG2 hG3' hb hb0 hb1 hbs hm w ⟨hw0, hww₀⟩
  dsimp only at hthm
  obtain ⟨-, -, -, hpath⟩ := hthm
  obtain ⟨-, hbound⟩ := hpath ε ⟨hε0.le, hε.2.trans (min_le_left _ _)⟩
  refine le_trans ?_ hbound
  -- numerator and denominator
  have hnum : ε / 2 ≤ max (ε - ℓ * 2 * w ^ (r + 1) - tailOut P Q x₀ ρ) 0 := by
    refine le_max_of_le_left ?_
    rw [hwr, hAdef]
    have : ℓ * 2 * (ε / (8 * ℓ)) = ε / 4 := by field_simp; ring
    linarith
  have hwβ : w ^ (1 - 2 * s) = (ε / (8 * ℓ)) ^ (-β) := by
    rw [hwdef, ← Real.rpow_mul (div_pos hε0 hA).le, hAdef]
    congr 1; rw [hβdef]; field_simp; ring
  have hρK : ρ ≤ (1 + a * Mβ) * w ^ (1 - 2 * s) := by
    have hlog := MollifierNorm.log_div_le_rpow hCT hℓ hβ hε0
    rw [← hMβ, ← hwβ] at hlog
    rw [hρdef]
    have : a * L ≤ a * (Mβ * w ^ (1 - 2 * s)) := mul_le_mul_of_nonneg_left hlog ha.le
    nlinarith
  have hvol : (volume (ball x₀ ρ)).toReal = 2 * ρ := by
    rw [Real.volume_ball, ENNReal.toReal_ofReal (by linarith)]
  have hB : 2 ^ s * (volume (ball x₀ ρ)).toReal + C * 2 * w ^ (1 - 2 * s) ≤ K * w ^ (1 - 2 * s) := by
    rw [hvol, hKdef]
    have h2s : 0 < (2 : ℝ) ^ s := by positivity
    have := mul_le_mul_of_nonneg_left hρK (by positivity : (0 : ℝ) ≤ 2 ^ s * 2)
    nlinarith
  have hBpos : 0 < 2 ^ s * (volume (ball x₀ ρ)).toReal + C * 2 * w ^ (1 - 2 * s) := by
    rw [hvol]; have := Real.rpow_pos_of_pos hw0 (1 - 2 * s); positivity
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  calc √c * (ε / 2) / √(K * w ^ (1 - 2 * s))
      ≤ √c * max (ε - ℓ * 2 * w ^ (r + 1) - tailOut P Q x₀ ρ) 0 / √(K * w ^ (1 - 2 * s)) := by
        gcongr
    _ ≤ √c * max (ε - ℓ * 2 * w ^ (r + 1) - tailOut P Q x₀ ρ) 0 /
          √(2 ^ s * (volume (ball x₀ ρ)).toReal + C * 2 * w ^ (1 - 2 * s)) := by
        refine div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hBpos) (Real.sqrt_le_sqrt hB)

theorem newsobolev_cor_bounded_of (h1 : Claims.tv_density) (h5 : Claims.sobolev_angular) :
    Claims.newsobolev_cor_bounded := by
  intro d _ V _ _ _ _ _ hd H _ _ _ _ φ k₀ c s P Q _ _ p q G c₀ ρ r ℓ w₀ Piρ Vρ hk₀c hk₀i hφ hc hs hspec hp hq hp0
    hq0 hP hQ htv0 htv1 hG hGp hGq hρ hr hℓ hw₀ hw₀1 hPi hV hG1 hG2 hG3 hT0
  obtain ⟨b, hb, hb0, hb1, hbs⟩ := MollifierNorm.exists_mollifier V
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hs' : 1 / 2 < s := by linarith
  obtain ⟨m, hm⟩ := MollifierNorm.exists_nat_four_mul_gt s
  obtain ⟨hφm, hφb⟩ := feature_facts hk₀c hφ
  have hcd : 0 < cJ d := by unfold cJ; linarith [StatFormal.JBall.sSup_jBall_Ici_one_lt_one (d := d)]
  set α := StatFormal.Distances.tvDist P Q with hα
  set C : ℝ := sobConst (cJ d) s (lapC m b) m with hCdef
  have hC : 0 < C := sobConst_pos hcd hs' hm
  set V' : ℝ := Vρ + 1 with hV'def
  have hV' : 0 < V' := by linarith
  have hG2' : ∀ t ∈ Ioc (0 : ℝ) w₀, volume {x | x ∈ ball c₀ ρ ∧ Metric.infDist x (frontier G) ≤ t} ≤
      ENNReal.ofReal (V' * t) := fun t ht =>
    (hG2 t ht).trans (ENNReal.ofReal_le_ofReal (by nlinarith [ht.1]))
  have hball : 0 < (volume (ball c₀ ρ)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos _ _ (by linarith)).ne' measure_ball_lt_top.ne
  set K : ℝ := 2 ^ s * (volume (ball c₀ ρ)).toReal + C * Piρ with hKdef
  have hK : 0 < K := by have : 0 ≤ C * Piρ := mul_nonneg hC.le hPi; positivity
  set A : ℝ := 2 * ℓ * V' with hAdef
  have hA : 0 < A := by positivity
  have hAw : 0 < A * w₀ ^ (r + 1) := mul_pos hA (Real.rpow_pos_of_pos hw₀ _)
  refine cor_conclusion hφm hφb htv0 htv1 hc hs' hr (ε₁ := min α (A * w₀ ^ (r + 1))) (lt_min htv0 hAw)
    (min_le_left _ _) hA hK (fun ε hε => ?_)
  have hε0 : 0 < ε := hε.1
  have hεw : ε ≤ A * w₀ ^ (r + 1) := hε.2.trans (min_le_right _ _)
  obtain ⟨hw0, hwr, hww₀, hw1s⟩ := width_facts hε0 hA hr hw₀ hw₀1 hs' hεw
  set w : ℝ := (ε / A) ^ (1 / (r + 1)) with hwdef
  have hthm := newsobolev_thm_of h1 h5 d V hd H φ k₀ c s P Q p q G c₀ ρ r ℓ w₀ Piρ V' b m hk₀c hk₀i hφ hc hs hspec
    hp hq hp0 hq0 hP hQ htv0 htv1 hG hGp hGq hρ hr hℓ hw₀ hw₀1 hPi hV'.le hG1 hG2' hG3 hb hb0 hb1 hbs hm w
    ⟨hw0, hww₀⟩
  dsimp only at hthm
  obtain ⟨-, -, -, hpath⟩ := hthm
  obtain ⟨-, hbound⟩ := hpath ε ⟨hε0.le, hε.2.trans (min_le_left _ _)⟩
  refine le_trans ?_ hbound
  have hnum : ε / 2 ≤ max (ε - ℓ * V' * w ^ (r + 1) - tailOut P Q c₀ ρ) 0 := by
    refine le_max_of_le_left ?_
    rw [hT0, hwr, hAdef]
    have : ℓ * V' * (ε / (2 * ℓ * V')) = ε / 2 := by field_simp
    linarith
  have hB : 2 ^ s * (volume (ball c₀ ρ)).toReal + C * Piρ * w ^ (1 - 2 * s) ≤ K * w ^ (1 - 2 * s) := by
    rw [hKdef]
    have h2 : 0 ≤ 2 ^ s * (volume (ball c₀ ρ)).toReal := by positivity
    have := mul_le_mul_of_nonneg_left hw1s h2
    nlinarith
  have hBpos : 0 < 2 ^ s * (volume (ball c₀ ρ)).toReal + C * Piρ * w ^ (1 - 2 * s) := by
    have : 0 ≤ C * Piρ * w ^ (1 - 2 * s) := mul_nonneg (mul_nonneg hC.le hPi) (Real.rpow_nonneg hw0.le _)
    have : 0 < 2 ^ s * (volume (ball c₀ ρ)).toReal := by positivity
    linarith
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  calc √c * (ε / 2) / √(K * w ^ (1 - 2 * s))
      ≤ √c * max (ε - ℓ * V' * w ^ (r + 1) - tailOut P Q c₀ ρ) 0 / √(K * w ^ (1 - 2 * s)) := by
        gcongr
    _ ≤ √c * max (ε - ℓ * V' * w ^ (r + 1) - tailOut P Q c₀ ρ) 0 /
          √(2 ^ s * (volume (ball c₀ ρ)).toReal + C * Piρ * w ^ (1 - 2 * s)) := by
        refine div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hBpos) (Real.sqrt_le_sqrt hB)

end StatFormal.Wave31tq.RouteS
