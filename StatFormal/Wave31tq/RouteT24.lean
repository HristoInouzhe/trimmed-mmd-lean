import StatFormal.Wave31tq.RouteT21

/-!
# Wave 31tq, route T (Q24): "sharp on the line at least when `s < 3/2`" (main :124-126) (untrusted)

`sharp_line_of (h12 : Claims.newsobolev_cor_line) (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) :
Claims.sharp_line`. The lower bound `c₁ε^γ ≤ D̄_{α⋆−ε}` and the margin are Corollary S4.11, case 2 (`Claims.newsobolev_cor_line`,
chunk S, a hypothesis; its `≤ w₀` and `x ≤ x₀` forms differ from the claim's by null sets); the upper bound is Proposition
S4.14 (`newupperone_of`) with `r₀ = w₀` (the two-sided local bound and the signs give the one-sided lower bounds), where
`2εW_ε^{s−1/2} = 2((r+1)/ℓ′)^{(2s−1)/(2(r+1))} ε^γ`. No `γ′ < γ` works: `c₀′ε^{γ′} ≤ D_{α⋆−ε} ≤ (1−α⋆)⁻¹c₂ε^γ` fails as `ε ↓ 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- The algebra of Proposition S4.14: `2ε((r+1)ε/ℓ′)^{(s−1/2)/(r+1)} R = 2((r+1)/ℓ′)^{(2s−1)/(2(r+1))} R ε^γ`. -/
lemma alg_d {ε ℓ' r s R : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ') (hr : 0 < r) :
    2 * ε * (((r + 1) * ε / ℓ') ^ (1 / (r + 1))) ^ (s - 1 / 2) * R =
      2 * ((r + 1) / ℓ') ^ ((2 * s - 1) / (2 * (r + 1))) * R * ε ^ (1 + (2 * s - 1) / (2 * (r + 1))) := by
  have hr1 : r + 1 ≠ 0 := by linarith
  have e1 : (r + 1) * ε / ℓ' = (r + 1) / ℓ' * ε := by ring
  rw [e1, ← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) hε.le,
    show 1 / (r + 1) * (s - 1 / 2) = (2 * s - 1) / (2 * (r + 1)) by field_simp,
    Real.rpow_add hε, Real.rpow_one]
  ring

/-- The null-set conversions: `|x − x₀| ≤ w₀` a.e. means `|x − x₀| < w₀`, and `x ≤ x₀` a.e. means `x < x₀`. -/
lemma ae_lt_of_le_abs {x₀ w₀ : ℝ} (hw : 0 < w₀) : ∀ᵐ x ∂volume, |x - x₀| ≤ w₀ → |x - x₀| < w₀ := by
  have h1 : ∀ᵐ x ∂volume, x ≠ x₀ + w₀ := compl_mem_ae_iff.mpr (measure_singleton _)
  have h2 : ∀ᵐ x ∂volume, x ≠ x₀ - w₀ := compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [h1, h2] with x hx1 hx2 hle
  refine lt_of_le_of_ne hle fun heq => ?_
  rcases (abs_eq hw.le).mp heq with h | h
  · exact hx1 (by linarith)
  · exact hx2 (by linarith)

/-- Q24 `sharp_line`, from Q12 case 2 (`Claims.newsobolev_cor_line`), Q1(b) and Q4 (through Q19). -/
theorem sharp_line_of (h12 : Claims.newsobolev_cor_line) (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) :
    Claims.sharp_line := by
  intro H _ _ _ _ φ k₀ c C s P Q _ _ p q x₀ r w₀ ℓ' ℓ CT a hk hki hg hc hC hs hs3 hklow hkup hpm hqm hp0 hq0 hP hQ
    htv0 htv1 hsR hsL hr hw₀ hw₀1 hℓ' hℓℓ hloc hCT ha htail
  dsimp only
  set γ := 1 + (2 * s - 1) / (2 * (r + 1)) with hγ
  have hℓ : 0 < ℓ := lt_of_lt_of_le hℓ' hℓℓ
  -- the lower half: Corollary S4.11, case 2
  have hsL' : ∀ᵐ x ∂volume, x ≤ x₀ → p x ≤ q x := by
    have hne : ∀ᵐ x ∂volume, x ≠ x₀ := compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hsL, hne] with x hx hx' hle
    exact hx (lt_of_le_of_ne hle hx')
  have hup : ∀ᵐ x ∂volume, |x - x₀| ≤ w₀ → |p x - q x| ≤ ℓ * |x - x₀| ^ r := by
    filter_upwards [hloc, ae_lt_of_le_abs (x₀ := x₀) hw₀] with x hx hlt hle
    exact (hx (hlt hle)).2
  have hcor := h12 H φ k₀ c s P Q p q x₀ r ℓ w₀ CT a hk hki hg hc hs hklow hpm hqm hp0 hq0 hP hQ htv0 htv1 hsR hsL'
    hr hℓ hw₀ hw₀1 hup hCT ha htail
  obtain ⟨⟨c₁, ε₁, hc₁, hε₁, hε₁tv, hlow⟩, ⟨cm, hcm⟩, -, -⟩ := hcor
  -- the upper half: Proposition S4.14 with `r₀ = w₀`
  have hR : ∀ᵐ x ∂volume, x ∈ Ioo x₀ (x₀ + w₀) → ℓ' * (x - x₀) ^ r ≤ p x - q x := by
    filter_upwards [hloc, hsR] with x hx hs' hmem
    have hlt : |x - x₀| < w₀ := by rw [abs_of_pos (by linarith [hmem.1])]; linarith [hmem.2]
    have h := (hx hlt).1
    rwa [abs_of_pos (by linarith [hmem.1] : 0 < x - x₀), abs_of_nonneg (sub_nonneg.mpr (hs' hmem.1))] at h
  have hL : ∀ᵐ x ∂volume, x ∈ Ioo (x₀ - w₀) x₀ → ℓ' * (x₀ - x) ^ r ≤ q x - p x := by
    filter_upwards [hloc, hsL] with x hx hs' hmem
    have hlt : |x - x₀| < w₀ := by rw [abs_of_neg (by linarith [hmem.2])]; linarith [hmem.1]
    have h := (hx hlt).1
    rwa [abs_of_neg (by linarith [hmem.2] : x - x₀ < 0), abs_of_nonpos (sub_nonpos.mpr (hs' hmem.2)), neg_sub, neg_sub] at h
  have hQ19 := newupperone_of h1 h4 H φ k₀ C s P Q p q x₀ ℓ' r w₀ hk hki hg hC hs hs3 hkup hpm hqm hp0 hq0 hP hQ
    hℓ' hr hw₀ hR hL
  set R := √(C / (2 * Real.pi) * (2 / (3 - 2 * s) + 2 / (2 * s - 1))) with hRdef
  set K := 2 * ((r + 1) / ℓ') ^ ((2 * s - 1) / (2 * (r + 1))) * R with hK
  have hK0 : 0 ≤ K := by positivity
  set ε₂ := ℓ' * w₀ ^ (r + 1) / (r + 1) with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  have hupper : ∀ ε ∈ Ioc (0 : ℝ) ε₂,
      StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤ K * ε ^ γ := by
    intro ε hε
    obtain ⟨-, hu, -⟩ := hQ19 ε hε
    exact hu.trans (le_of_eq (alg_d hε.1 hℓ' hr))
  set ε₀ := min ε₁ ε₂ with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₁ hε₂0
  refine ⟨⟨c₁, max c₁ K, ε₀, hc₁, le_max_left _ _, hε₀0, (min_le_left _ _).trans hε₁tv, fun ε hε => ⟨?_, ?_⟩⟩,
    ⟨cm, hcm⟩, ?_⟩
  · exact hlow ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  · exact (hupper ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))
  -- no smaller exponent
  · intro γ' c₀' hγ' hpm'
    obtain ⟨hc₀', -, hmar⟩ := hpm'
    set D := (1 - StatFormal.Distances.tvDist P Q)⁻¹ * K with hD
    have hδ : 0 < γ - γ' := by linarith
    have hlim : Tendsto (fun e : ℝ => D * e ^ (γ - γ')) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (γ - γ') (Or.inr hδ.le)).tendsto
      rw [Real.zero_rpow hδ.ne'] at h
      simpa using (h.mono_left nhdsWithin_le_nhds).const_mul D
    have hev1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), D * e ^ (γ - γ') < c₀' := hlim.eventually (gt_mem_nhds hc₀')
    have hev2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), e ∈ Ioc (0 : ℝ) ε₀ := Ioc_mem_nhdsGT hε₀0
    obtain ⟨e, he1, he2⟩ := (hev1.and hev2).exists
    have hm := hmar e ⟨he2.1.le, he2.2.trans ((min_le_left _ _).trans hε₁tv)⟩
    have hDp := Dpop_le_uPath_div φ P Q htv1 he2.1.le
    have hu := hupper e ⟨he2.1, he2.2.trans (min_le_right _ _)⟩
    have hpow : e ^ γ = e ^ (γ - γ') * e ^ γ' := by rw [← Real.rpow_add he2.1, sub_add_cancel]
    have hγ'pos : 0 < e ^ γ' := Real.rpow_pos_of_pos he2.1 _
    have h1tv : 0 ≤ (1 - StatFormal.Distances.tvDist P Q)⁻¹ := inv_nonneg.mpr (by linarith)
    have hchain : c₀' * e ^ γ' ≤ D * e ^ (γ - γ') * e ^ γ' := by
      calc c₀' * e ^ γ' ≤ StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q (StatFormal.Distances.tvDist P Q - e) := hm
        _ ≤ (1 - StatFormal.Distances.tvDist P Q)⁻¹ * StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - e) := hDp
        _ ≤ (1 - StatFormal.Distances.tvDist P Q)⁻¹ * (K * e ^ γ) := mul_le_mul_of_nonneg_left hu h1tv
        _ = D * e ^ (γ - γ') * e ^ γ' := by rw [hpow, hD]; ring
    have := lt_of_le_of_lt hchain (mul_lt_mul_of_pos_right he1 hγ'pos)
    exact lt_irrefl _ this

end StatFormal.Wave31tq.RouteT
