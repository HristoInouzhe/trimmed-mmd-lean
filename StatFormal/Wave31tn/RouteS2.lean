import StatFormal.Wave31tn.RouteS1

/-!
# Wave 31tn route: S2 `lem:twopointmargin` (untrusted proof material)

For `z = E_{P_s}[gφ] ∈ 𝒞_α(P_s)` (`P_s = (1−s)R + sP₀`, `f = 0` `R`-a.e., `f = 1` `P₀`-a.e.): `⟪f,z⟫ = 1 − (1−s)E_R g =: A` (the certified
`Wave31tb.inner_mix`) with `A = sE_{P₀}g ≥ 0` and `(1−α)A ≥ s − α` (`g ≤ (1−α)⁻¹`); symmetrically `⟪f,w⟫ = −B` on `𝒞_α(Q_t)`, `B ≥ 0`,
`(1−α)B ≥ t − α`. Hence `‖f‖‖z − w‖ ≥ A + B ≥ max(s,t) − α` for `α ∈ [0, max(s,t)]`, and `D_α ≥ (max(s,t) − α)/‖f‖` (`le_csInf`); `dTrim`
by the certified `Wave8a.georep_dist`. At `α = α⋆ − ε`, `α⋆ = max(s,t) = a + h`, this is `ε/‖f‖`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tn

namespace RouteS2

open RouteTV StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An element of `𝒞_α(P_s)` paired with `f`: `c(1 − (1−s)t)` with `t ≤ (1−α)⁻¹` and `(1−s)t ≤ 1`. -/
lemma region_inner' (φ : 𝒳 → H) {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (R P₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f : H) (c : ℝ) (hf0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0) (hf1 : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = c) (α : ℝ) {z : H}
    (hz : z ∈ region φ α (mixAt R P₀ s)) :
    ∃ t, t ≤ 1 / (1 - α) ∧ (1 - s) * t ≤ 1 ∧ ⟪f, z⟫_ℝ = c * (1 - (1 - s) * t) := by
  obtain ⟨g, hg, hgB, hg1, rfl⟩ := hz
  refine ⟨∫ x, g x ∂R, StatFormal.Wave31tb.integral_le_bound R g hg hgB, ?_,
    StatFormal.Wave31tb.inner_mix φ hφ hκ R P₀ hs0 hs1 f c hf0 hf1 g hg hgB hg1⟩
  have hgabs : ∀ x, ‖g x‖ ≤ 1 / (1 - α) := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgB x).1]; exact (hgB x).2
  have hg1' := hg1
  unfold mixAt at hg1'
  rw [StatFormal.Wave31tb.integral_mix R P₀ hs0 hs1 g (StatFormal.Wave31tb.integrable_bdd R hg.stronglyMeasurable hgabs)
    (StatFormal.Wave31tb.integrable_bdd P₀ hg.stronglyMeasurable hgabs)] at hg1'
  have hP : 0 ≤ ∫ x, g x ∂P₀ := integral_nonneg fun x => (hgB x).1
  nlinarith

/-- `D_α((1−s)R + sP₀, (1−t)R + tQ₀) ≥ (max(s,t) − α)/‖f‖` for `α ∈ [0, max(s,t)]`, `s, t ∈ [0,1)`. -/
lemma dpop_bound2 (φ : 𝒳 → H) {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (R P₀ Q₀ : Measure 𝒳) [IsProbabilityMeasure R] [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q₀] {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) (f : H) (hfpos : 0 < ‖f‖) (hf0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0)
    (hfP : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = 1) (hfQ : ∀ᵐ x ∂Q₀, ⟪f, φ x⟫_ℝ = -1) {α : ℝ} (hα0 : 0 ≤ α) (hαM : α ≤ max s t) :
    (max s t - α) / ‖f‖ ≤ Dpop φ (mixAt R P₀ s) (mixAt R Q₀ t) α := by
  have := mixAt_isProb R P₀ hs0 hs1.le
  have := mixAt_isProb R Q₀ ht0 ht1.le
  have hα1 : α < 1 := lt_of_le_of_lt hαM (max_lt hs1 ht1)
  have h1α : 0 < 1 - α := by linarith
  unfold Dpop setDist
  refine le_csInf ⟨_, _, StatFormal.Wave31tb.region_nonempty φ _ hα0 hα1, _,
    StatFormal.Wave31tb.region_nonempty φ _ hα0 hα1, rfl⟩ ?_
  rintro r ⟨z, hz, w, hw, rfl⟩
  obtain ⟨t₁, ht₁, ht₁', hz'⟩ := region_inner' φ hφ hκ R P₀ hs0 hs1.le f 1 hf0 hfP α hz
  obtain ⟨t₂, ht₂, ht₂', hw'⟩ := region_inner' φ hφ hκ R Q₀ ht0 ht1.le f (-1) hf0 hfQ α hw
  have hcs : ⟪f, z - w⟫_ℝ ≤ ‖f‖ * ‖z - w‖ := real_inner_le_norm f (z - w)
  rw [inner_sub_right, hz', hw'] at hcs
  set A := 1 - (1 - s) * t₁ with hA
  set B := 1 - (1 - t) * t₂ with hB
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hAα : s - α ≤ (1 - α) * A := by
    rw [hA]; rw [le_div_iff₀ h1α] at ht₁; nlinarith
  have hBα : t - α ≤ (1 - α) * B := by
    rw [hB]; rw [le_div_iff₀ h1α] at ht₂; nlinarith
  have hAB : max s t - α ≤ A + B := by
    rcases le_total s t with hst | hst
    · rw [max_eq_right hst]; nlinarith [mul_nonneg hα0 hB0]
    · rw [max_eq_left hst]; nlinarith [mul_nonneg hα0 hA0]
  rw [div_le_iff₀ hfpos]
  nlinarith

/-- `‖f‖ > 0` when `f = 1` on a set carrying a probability measure. -/
lemma norm_pos_of (φ : 𝒳 → H) (P₀ : Measure 𝒳) [IsProbabilityMeasure P₀] {SP : Set 𝒳} (hP₀ : P₀ SPᶜ = 0) (f : H)
    (hfP : ∀ x ∈ SP, ⟪f, φ x⟫_ℝ = 1) : 0 < ‖f‖ := by
  have hSPne : SP.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hP₀
    exact one_ne_zero hP₀
  obtain ⟨x, hx⟩ := hSPne
  have hx1 := hfP x hx
  rw [norm_pos_iff]
  rintro rfl
  simp at hx1

theorem twopointmargin_route : Claims.twopointmargin := by
  intro 𝒳 H _ _ _ _ φ κ R P₀ Q₀ _ _ _ SR SP SQ a h f hφ hκ hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hh0 hh1
    hfR hfP hfQ
  have hfpos := norm_pos_of φ P₀ hP₀ f hfP
  have hR0 : ∀ᵐ x ∂R, ⟪f, φ x⟫_ℝ = 0 := by
    filter_upwards [(ae_iff.2 hR : ∀ᵐ x ∂R, x ∈ SR)] with x hx using hfR x hx
  have hP1 : ∀ᵐ x ∂P₀, ⟪f, φ x⟫_ℝ = 1 := by
    filter_upwards [(ae_iff.2 hP₀ : ∀ᵐ x ∂P₀, x ∈ SP)] with x hx using hfP x hx
  have hQ1 : ∀ᵐ x ∂Q₀, ⟪f, φ x⟫_ℝ = -1 := by
    filter_upwards [(ae_iff.2 hQ₀ : ∀ᵐ x ∂Q₀, x ∈ SQ)] with x hx using hfQ x hx
  have hTV := RouteS1.lower2pt_tv_route 𝒳 R P₀ Q₀ SR SP SQ a h hSR hSP hSQ hRP hRQ hPQ hR hP₀ hQ₀ ha0 ha1 hh0 hh1
  have := mixAt_isProb R P₀ ha0.le ha1.le
  have := mixAt_isProb R Q₀ ha0.le ha1.le
  have := mixAt_isProb R P₀ (t := a + h) (by linarith) (by linarith)
  have := mixAt_isProb R Q₀ (t := a + h) (by linarith) (by linarith)
  have hb1 : a + h < 1 := by linarith
  -- the two bounds at level `a + h − ε`
  have hD1 : ∀ ε ∈ Icc (0 : ℝ) (a + h), ε / ‖f‖ ≤ Dpop φ (mixAt R P₀ (a + h)) (mixAt R Q₀ a) (a + h - ε) := by
    intro ε hε
    have := dpop_bound2 φ hφ hκ R P₀ Q₀ (s := a + h) (t := a) (by linarith) hb1 ha0.le ha1 f hfpos hR0 hP1 hQ1
      (α := a + h - ε) (by linarith [hε.2]) (by rw [max_eq_left (by linarith)]; linarith [hε.1])
    rwa [max_eq_left (by linarith), show a + h - (a + h - ε) = ε by ring] at this
  have hD2 : ∀ ε ∈ Icc (0 : ℝ) (a + h), ε / ‖f‖ ≤ Dpop φ (mixAt R P₀ a) (mixAt R Q₀ (a + h)) (a + h - ε) := by
    intro ε hε
    have := dpop_bound2 φ hφ hκ R P₀ Q₀ (s := a) (t := a + h) ha0.le ha1 (by linarith) hb1 f hfpos hR0 hP1 hQ1
      (α := a + h - ε) (by linarith [hε.2]) (by rw [max_eq_right (by linarith)]; linarith [hε.1])
    rwa [max_eq_right (by linarith), show a + h - (a + h - ε) = ε by ring] at this
  have hgeo := fun (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) (a + h)) =>
    StatFormal.Wave8a.georep_dist 𝒳 H P Q φ κ (a + h - ε) hφ hκ (by linarith [hε.2]) (by linarith [hε.1])
  have hpm : ∀ (P Q : Measure 𝒳), StatFormal.Distances.tvDist P Q = a + h →
      (∀ ε ∈ Icc (0 : ℝ) (a + h), ε / ‖f‖ ≤ Dpop φ P Q (a + h - ε)) →
      StatFormal.Wave31ti.PolyMargin φ P Q (1 / ‖f‖) 1 := by
    intro P Q hPQtv hD
    refine ⟨by positivity, le_rfl, ?_⟩
    rw [hPQtv]
    intro e he
    rw [Real.rpow_one, one_div_mul_eq_div]
    exact hD e he
  refine ⟨hfpos, hTV.2.1, hTV.2.2, fun ε hε => ⟨?_, hD1 ε hε, ?_, hD2 ε hε⟩, hpm _ _ hTV.2.1 hD1, hpm _ _ hTV.2.2 hD2⟩
  · rw [hgeo _ _ ε hε]; exact hD1 ε hε
  · rw [hgeo _ _ ε hε]; exact hD2 ε hε

end RouteS2

end StatFormal.Wave31tn
