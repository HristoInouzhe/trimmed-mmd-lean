import StatFormal.Wave31tq.Statements
import StatFormal.Lib.CrossLaws.Basic

/-!
# Wave 31tq, route M (Q21): Proposition 5.5 and "Assumption 5.1 holds with `γ = (2s+3)/4` and no smaller exponent" (untrusted)

* `cross_zero`, `cross_tv`, `cross_lip`, `expTail_tailOut`, `expTail_tailPlus`: the facts the proof of Proposition 5.5 draws
  from its laws (L55) (`IsCross`, `p(x₀) > 0`, `ExpTail`): `p(x₀) = q(x₀)`, `0 < α⋆ < 1` (from Q1(b), `Claims.tv_density`),
  `|p − q| ≤ (ℓ₀ + η)|x − x₀|` near `x₀`, and the tails `T(ρ) ≤ C_Te^{−ρ/a}`, `T₊(t) ≤ C′e^{−t/C′}`;
* `sobolev_lower`: Corollary S4.11, case 2, with `r = 1`, `ℓ = 2ℓ₀` (`Claims.newsobolev_cor_line`, chunk S);
* `sobolev_upper`: Proposition S4.15 (a) with `N = ⌈s⌉ > s − 1/2` (`Claims.newmoments`, chunk T);
* `newsobolev_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments) : Claims.newsobolev`:
  `D̄ ≤ D ≤ D̄/(1 − α⋆)`;
* `newsobolev_E1_of h1 hcor hmom : Claims.newsobolev_E1`: the margin of Corollary S4.11, and no `γ′ < (2s+3)/4` since
  `c₀′ε^{γ′} ≤ D_{α⋆−ε} ≤ c₂ε^{(2s+3)/4}` fails as `ε ↓ 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteM

open StatFormal StatFormal.Wave31tp StatFormal.TrimmedMMD.Unconditional StatFormal.CrossLaws StatFormal.Distances

/-- Under `IsCross`, `p(x₀) = q(x₀)` (continuity at `x₀` and the a.e. signs). -/
theorem cross_zero {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) : p x₀ = q x₀ := by
  obtain ⟨-, -, -, -, -, -, -, hsR, hsL, hd, -⟩ := hc
  have h := StatFormal.MomentTrim.eq_zero_of_signs (e := fun x => p x - q x) (x₀ := x₀) hd.continuousAt
    (hsR.mono fun x hx h => sub_nonneg.mpr (hx h)) (hsL.mono fun x hx h => sub_nonpos.mpr (hx h))
  exact sub_eq_zero.mp h

/-- `cross_tv`: under `IsCross` and `p(x₀) > 0`, `0 < α⋆ < 1` (from Q1(b): `α⋆ = ∫(p − q)₊`, `P ∧ Q = min(p, q)·Leb`, and Q1(a):
`(P ∧ Q)(ℝ) = 1 − α⋆`). -/
theorem cross_tv (h1 : Claims.tv_density) {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : ℝ → ℝ}
    {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) : 0 < tvDist P Q ∧ tvDist P Q < 1 := by
  have hpq := cross_zero hc
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r, hr, hpc, hqc⟩, -, -, hd, hℓ⟩ := hc
  obtain ⟨-, hmin, -, htv, -⟩ := h1.2 ℝ P Q p q hpm hqm hp0 hq0 hP hQ
  have hmass := (h1.1 ℝ P Q).2.2.2.2
  have he0 : (fun x => p x - q x) x₀ = 0 := sub_eq_zero.mpr hpq
  obtain ⟨δ1, hδ1, hR, -⟩ := StatFormal.MomentTrim.exists_linear_lower hd he0 hℓ
  obtain ⟨δ2, hδ2, hp2⟩ := StatFormal.MomentTrim.exists_half_lower hr hpc hpx
  have hqx : 0 < q x₀ := hpq ▸ hpx
  obtain ⟨δ3, hδ3, hq3⟩ := StatFormal.MomentTrim.exists_half_lower hr hqc hqx
  set δ := min δ1 (min δ2 δ3) with hδ
  have hδ0 : 0 < δ := lt_min hδ1 (lt_min hδ2 hδ3)
  refine tv_pos_lt_one hpm hqm hp0 hq0 hP htv hmin hmass (a := x₀) (δ := δ) (ℓ := ℓ₀ / 2) (m := min (p x₀ / 2) (q x₀ / 2))
    hδ0 (half_pos hℓ) (lt_min (half_pos hpx) (half_pos hqx)) (fun x hx => ?_) (fun x hx => ?_)
  · exact hR x ⟨hx.1, hx.2.trans_le (by linarith [min_le_left δ1 (min δ2 δ3)])⟩
  · have hx' : |x - x₀| < δ := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.2]
    have h2 := hp2 x (hx'.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have h3 := hq3 x (hx'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact min_le_min h2.le h3.le

/-- Under `IsCross`, for every `η > 0`, `|p − q| ≤ (ℓ₀ + η)|x − x₀|` for `|x − x₀| ≤ w`, some `w ∈ (0, 1]`. -/
theorem cross_lip {P Q : Measure ℝ} {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hc : IsCross P Q p q x₀ ℓ₀) {η : ℝ} (hη : 0 < η) :
    ∃ w : ℝ, 0 < w ∧ w ≤ 1 ∧ ∀ x, |x - x₀| ≤ w → |p x - q x| ≤ (ℓ₀ + η) * |x - x₀| := by
  have hpq := cross_zero hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, hℓ⟩ := hc
  exact abs_le_of_hasDerivAt (e := fun x => p x - q x) hd (sub_eq_zero.mpr hpq) hℓ.le hη

/-- `|P − Q|` is a finite measure. -/
instance absPQ_finite {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    IsFiniteMeasure (absPQ P Q) := by
  unfold absPQ; infer_instance

/-- `ExpTail` gives `T(ρ) ≤ C_Te^{−ρ/a}` for `ρ ≥ 1` (balls about `x₀`). -/
theorem expTail_tailOut {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x₀ : ℝ} (h : ExpTail P Q x₀) :
    ∃ CT a : ℝ, 0 < CT ∧ 0 < a ∧ ∀ ρ : ℝ, 1 ≤ ρ → tailOut P Q x₀ ρ ≤ CT * Real.exp (-ρ / a) := by
  obtain ⟨C', hC', ht⟩ := h
  exact tailOut_le (absPQ P Q) hC' ht

/-- `ExpTail` gives `T₊(t) ≤ C′e^{−t/C′}` for `t > 0`. -/
theorem expTail_tailPlus {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x₀ : ℝ} (h : ExpTail P Q x₀) :
    ∃ CT a : ℝ, 0 < CT ∧ 0 < a ∧ ∀ t : ℝ, 0 < t → tailPlus P Q x₀ t ≤ CT * Real.exp (-t / a) := by
  obtain ⟨C', hC', ht⟩ := h
  exact ⟨C', C', hC', hC', tailPlus_le (absPQ P Q) hC' ht⟩

/-- The `≤ x₀` form of the left sign (a null set apart). -/
theorem sign_le_of_lt {p q : ℝ → ℝ} {x₀ : ℝ} (hsL : ∀ᵐ x ∂volume, x < x₀ → p x ≤ q x) :
    ∀ᵐ x ∂volume, x ≤ x₀ → p x ≤ q x := by
  have hne : ∀ᵐ x ∂volume, x ≠ x₀ := compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [hsL, hne] with x hx hx' hle
  exact hx (lt_of_le_of_ne hle hx')

/-- **The lower half of Proposition 5.5** (Corollary S4.11, case 2, `r = 1`, `ℓ = 2ℓ₀`): `c₁ε^{(2s+3)/4} ≤ D̄_{α⋆−ε}` for small
`ε`, and the margin `PolyMargin c (2s+3)/4`. -/
theorem sobolev_lower (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {k₀ : ℝ → ℝ} {c s : ℝ} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ}
    (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) (hc : 0 < c) (hs : 1 / 2 < s)
    (hkb : ∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ)
    (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) (hexp : ExpTail P Q x₀) :
    (∃ c₁ ε₁ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ ε₁ ≤ tvDist P Q ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₁,
        c₁ * ε ^ ((2 * s + 3) / 4) ≤ StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε)) ∧
      ∃ cm : ℝ, StatFormal.Wave31ti.PolyMargin φ P Q cm ((2 * s + 3) / 4) := by
  obtain ⟨htv0, htv1⟩ := cross_tv h1 hcross hpx
  have hℓ : 0 < ℓ₀ := hcross.2.2.2.2.2.2.2.2.2.2
  obtain ⟨w₀, hw₀, hw₀1, hlip⟩ := cross_lip hcross hℓ
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, -, hsR, hsL, -, -⟩ := hcross
  obtain ⟨CT, a, hCT, ha, htail⟩ := expTail_tailOut hexp
  have hup : ∀ᵐ x ∂volume, |x - x₀| ≤ w₀ → |p x - q x| ≤ (ℓ₀ + ℓ₀) * |x - x₀| ^ (1 : ℝ) :=
    ae_of_all _ fun x hx => by rw [Real.rpow_one]; exact hlip x hx
  have hcor' := hcor H φ k₀ c s P Q p q x₀ 1 (ℓ₀ + ℓ₀) w₀ CT a hk hki hg hc hs hkb hpm hqm hp0 hq0 hP hQ htv0 htv1 hsR
    (sign_le_of_lt hsL) one_pos (by linarith) hw₀ hw₀1 hup hCT ha htail
  obtain ⟨⟨c₁, ε₁, hc₁, hε₁, hε₁tv, hlow⟩, ⟨cm, hcm⟩, -, -⟩ := hcor'
  have hγ : (1 : ℝ) + (2 * s - 1) / (2 * (1 + 1)) = (2 * s + 3) / 4 := by ring
  rw [hγ] at hlow hcm
  exact ⟨⟨c₁, ε₁, hc₁, hε₁, hε₁tv, hlow⟩, cm, hcm⟩

/-- **The upper half of Proposition 5.5 for `D̄`** (Proposition S4.15 (a) with `N = ⌈s⌉ > s − 1/2`). -/
theorem sobolev_upper (hmom : Claims.newmoments)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {φ : ℝ → H} {k₀ : ℝ → ℝ} {C s : ℝ} {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} {x₀ ℓ₀ : ℝ}
    (hk : Continuous k₀) (hki : Integrable k₀) (hg : ∀ x y, ⟪φ x, φ y⟫_ℝ = k₀ (x - y)) (hC : 0 < C) (hs : 1 / 2 < s)
    (hkb : ∀ ξ, kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s))
    (hcross : IsCross P Q p q x₀ ℓ₀) (hpx : 0 < p x₀) :
    ∃ K ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₂,
      StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) ≤ K * ε ^ ((2 * s + 3) / 4) := by
  have hpq := cross_zero hcross
  obtain ⟨hpm, hqm, hp0, hq0, hP, hQ, ⟨r₀, hr₀, hpc, hqc⟩, -, -, hd, hℓ⟩ := hcross
  set N := ⌈s⌉₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hNs : s - 1 / 2 < (N : ℝ) := lt_of_lt_of_le (by linarith) (Nat.le_ceil s)
  obtain ⟨TN, wN, -, hwN, -, hA, -⟩ := hmom P Q p q x₀ r₀ ℓ₀ hpm hqm hp0 hq0 hP hQ hr₀ hpc hqc hd hℓ hpq hpx N hN1
  obtain ⟨-, K, hK⟩ := hA H φ k₀ C s hk hki hg hC hs hNs hkb
  refine ⟨K, ℓ₀ * wN ^ 2 / 8, by positivity, fun ε hε => ?_⟩
  obtain ⟨h1', h2'⟩ := hK ε hε
  exact h1'.trans h2'

/-- `c ≤ C` from the two-sided spectral bound at `ξ = 0`. -/
theorem spec_le {k₀ : ℝ → ℝ} {c C s : ℝ} (hkb : ∀ ξ, c * (1 + ξ ^ 2) ^ (-s) ≤ kHat k₀ ξ ∧ kHat k₀ ξ ≤ C * (1 + ξ ^ 2) ^ (-s)) :
    c ≤ C := by
  have h := hkb 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.one_rpow, mul_one] at h
  exact h.1.trans h.2

/-- Q21 `newsobolev` (Proposition 5.5), from Q1 (`Claims.tv_density`, chunk A), Q12 case 2 (`Claims.newsobolev_cor_line`,
chunk S) and Q20 (`Claims.newmoments`, chunk T). -/
theorem newsobolev_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments) :
    Claims.newsobolev := by
  intro H _ _ _ _ φ k₀ c C s P Q _ _ p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  obtain ⟨htv0, htv1⟩ := cross_tv h1 hcross hpx
  obtain ⟨⟨c₁, ε₁, hc₁, hε₁, hε₁tv, hlow⟩, -⟩ :=
    sobolev_lower h1 hcor hk hki hg hc hs (fun ξ => (hkb ξ).1) hcross hpx hexp
  have hC : 0 < C := lt_of_lt_of_le hc (spec_le hkb)
  obtain ⟨K, ε₂, hε₂, hup⟩ := sobolev_upper hmom hk hki hg hC hs (fun ξ => (hkb ξ).2) hcross hpx
  set ε₀ := min ε₁ ε₂ with hε₀
  have h1tv : 0 ≤ (1 - tvDist P Q)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨htv0, htv1, c₁, max c₁ ((1 - tvDist P Q)⁻¹ * K), ε₀, hc₁, le_max_left _ _, lt_min hε₁ hε₂,
    (min_le_left _ _).trans hε₁tv, fun ε hε => ⟨?_, ?_⟩⟩
  · have hε1 : ε ≤ ε₁ := hε.2.trans (min_le_left _ _)
    exact (hlow ε ⟨hε.1, hε1⟩).trans (uPath_le_Dpop φ P Q (by linarith))
  · have hε2 : ε ≤ ε₂ := hε.2.trans (min_le_right _ _)
    calc Dpop φ P Q (tvDist P Q - ε) ≤ (1 - tvDist P Q)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (tvDist P Q - ε) :=
          Dpop_le_uPath_div φ P Q htv1 hε.1.le
      _ ≤ (1 - tvDist P Q)⁻¹ * (K * ε ^ ((2 * s + 3) / 4)) := mul_le_mul_of_nonneg_left (hup ε ⟨hε.1, hε2⟩) h1tv
      _ = (1 - tvDist P Q)⁻¹ * K * ε ^ ((2 * s + 3) / 4) := by ring
      _ ≤ max c₁ ((1 - tvDist P Q)⁻¹ * K) * ε ^ ((2 * s + 3) / 4) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hε.1.le _)

/-- Q21 `newsobolev_E1` (main :119-120), from the same hypotheses as `newsobolev_of`. -/
theorem newsobolev_E1_of (h1 : Claims.tv_density) (hcor : Claims.newsobolev_cor_line) (hmom : Claims.newmoments) :
    Claims.newsobolev_E1 := by
  intro H _ _ _ _ φ k₀ c C s P Q _ _ p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  obtain ⟨-, -, c₁, c₂, ε₀, -, -, hε₀, hε₀tv, hb⟩ :=
    newsobolev_of h1 hcor hmom H φ k₀ c C s P Q p q x₀ ℓ₀ hk hki hg hc hs hkb hcross hpx hexp
  obtain ⟨-, hmar⟩ := sobolev_lower h1 hcor hk hki hg hc hs (fun ξ => (hkb ξ).1) hcross hpx hexp
  refine ⟨hmar, fun γ' c₀' hγ' hpm => ?_⟩
  obtain ⟨hc₀', -, hm⟩ := hpm
  exact false_of_lower_upper (f := fun e => Dpop φ P Q (tvDist P Q - e)) hc₀' hγ' hε₀
    (fun e he => hm e ⟨he.1.le, he.2.trans hε₀tv⟩) (fun e he => (hb e he).2)

end StatFormal.Wave31tq.RouteM
