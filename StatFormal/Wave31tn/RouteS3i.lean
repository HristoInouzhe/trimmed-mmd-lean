import StatFormal.Wave31tn.RouteS2

/-!
# Wave 31tn route: S3 (i) `cor:minimax`, the lower bound (untrusted proof material)

S1 (c) at `a = a₀` with `R, P₀, Q₀` the point masses at `x₂, x₁, x₃` and `S_R, S_P, S_Q` the level sets `{f = 0}, {f = 1}, {f = −1}`
(measurable since `φ` is strongly measurable; no measurable singletons needed). `h = hStar δ a₀ N = c_lo/√N ≤ a₁ − a₀` from
`N ≥ c_lo²/(a₁ − a₀)²`. All three pairs lie in `𝓜`: TV by S1 (a), the margin by S2 with `1/‖f‖ ≥ c₀` (`PolyMargin` is monotone in `c₀`).
Validity is used only at `(P_{a₀}, Q_{a₀})`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tn

namespace RouteS3i

open RouteTV

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `PolyMargin` with `γ = 1` is monotone in `c₀`. -/
lemma polyMargin_mono {φ : 𝒳 → H} {P Q : Measure 𝒳} {c c' : ℝ} (h : StatFormal.Wave31ti.PolyMargin φ P Q c 1)
    (hc' : 0 < c') (hcc' : c' ≤ c) : StatFormal.Wave31ti.PolyMargin φ P Q c' 1 :=
  ⟨hc', le_rfl, fun e he => (mul_le_mul_of_nonneg_right hcc' (Real.rpow_nonneg he.1 _)).trans (h.2.2 e he)⟩

/-- `hStar δ a N = c_lo/√N`. -/
lemma hStar_eq (δ a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) : hStar δ a N = clo δ a / √(N : ℝ) := by
  unfold hStar clo
  rw [Real.sqrt_div (by nlinarith)]
  ring

theorem minimax_i_route : Claims.minimax_i := by
  intro 𝒳 H _ _ _ _ φ κ x₁ x₂ x₃ f a₀ a₁ c₀ δ n m Ξ _ ρ _ T hφ hκ hf1 hf2 hf3 ha0 ha01 ha1 hc0 hcf hδ0 hδ1 hN hT hval
  set g : 𝒳 → ℝ := fun x => ⟪f, φ x⟫_ℝ with hgdef
  have hg : Measurable g := ((continuous_const.inner continuous_id).comp_stronglyMeasurable hφ).measurable
  have hSR : MeasurableSet (g ⁻¹' {0}) := hg (measurableSet_singleton _)
  have hSP : MeasurableSet (g ⁻¹' {1}) := hg (measurableSet_singleton _)
  have hSQ : MeasurableSet (g ⁻¹' {-1}) := hg (measurableSet_singleton _)
  have hdis : ∀ u v : ℝ, u ≠ v → Disjoint (g ⁻¹' {u}) (g ⁻¹' {v}) := fun u v huv =>
    Set.disjoint_left.2 fun x hx hy => huv ((Set.mem_singleton_iff.1 hx).symm.trans (Set.mem_singleton_iff.1 hy))
  have hdirac : ∀ (x : 𝒳) (u : ℝ), g x = u → Measure.dirac x (g ⁻¹' {u})ᶜ = 0 := fun x u hx => by
    rw [Measure.dirac_apply' x (hg (measurableSet_singleton u)).compl]
    exact Set.indicator_of_notMem (by simp [hx]) _
  -- sample size and the perturbation
  have h1a0 : 0 < 1 - a₀ := by linarith
  have hclo : 0 < clo δ a₀ := by unfold clo; exact mul_pos (by linarith) (Real.sqrt_pos.2 (by positivity))
  have hNpos : (0 : ℝ) < ((min n m : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hn : 1 ≤ n := by
    have : 0 < min n m := by exact_mod_cast hNpos
    omega
  have hm : 1 ≤ m := by
    have : 0 < min n m := by exact_mod_cast hNpos
    omega
  set h := hStar δ a₀ (min n m) with hhdef
  have hheq : h = clo δ a₀ / √((min n m : ℕ) : ℝ) := hStar_eq δ a₀ ha0.le (by linarith) _
  have hsqN : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  have hh0 : 0 ≤ h := by rw [hheq]; positivity
  have hha : h ≤ a₁ - a₀ := by
    rw [hheq, div_le_iff₀ hsqN]
    have h2 : clo δ a₀ ^ 2 ≤ (a₁ - a₀) ^ 2 * ((min n m : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by nlinarith)] at hN; linarith
    calc clo δ a₀ = √(clo δ a₀ ^ 2) := (Real.sqrt_sq hclo.le).symm
      _ ≤ √((a₁ - a₀) ^ 2 * ((min n m : ℕ) : ℝ)) := Real.sqrt_le_sqrt h2
      _ = (a₁ - a₀) * √((min n m : ℕ) : ℝ) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have hh1 : h < 1 - a₀ := by linarith
  -- the three pairs
  have hd2 := hdirac x₂ 0 hf2
  have hd1 := hdirac x₁ 1 hf1
  have hd3 := hdirac x₃ (-1) hf3
  have hRP := hdis 0 1 (by norm_num)
  have hRQ := hdis 0 (-1) (by norm_num)
  have hPQ := hdis 1 (-1) (by norm_num)
  have hfR : ∀ x ∈ g ⁻¹' {0}, ⟪f, φ x⟫_ℝ = 0 := fun x hx => Set.mem_singleton_iff.1 hx
  have hfP : ∀ x ∈ g ⁻¹' {1}, ⟪f, φ x⟫_ℝ = 1 := fun x hx => Set.mem_singleton_iff.1 hx
  have hfQ : ∀ x ∈ g ⁻¹' {-1}, ⟪f, φ x⟫_ℝ = -1 := fun x hx => Set.mem_singleton_iff.1 hx
  have hS2 := RouteS2.twopointmargin_route 𝒳 H φ κ (Measure.dirac x₂) (Measure.dirac x₁) (Measure.dirac x₃) _ _ _ a₀ h f
    hφ hκ hSR hSP hSQ hRP hRQ hPQ hd2 hd1 hd3 ha0 (by linarith) hh0 hh1 hfR hfP hfQ
  have hS20 := RouteS2.twopointmargin_route 𝒳 H φ κ (Measure.dirac x₂) (Measure.dirac x₁) (Measure.dirac x₃) _ _ _ a₀ 0 f
    hφ hκ hSR hSP hSQ hRP hRQ hPQ hd2 hd1 hd3 ha0 (by linarith) le_rfl (by linarith) hfR hfP hfQ
  rw [add_zero] at hS20
  have hc' : c₀ ≤ 1 / ‖f‖ := hcf
  have hPa := mixAt_isProb (Measure.dirac x₂) (Measure.dirac x₁) ha0.le (by linarith : a₀ ≤ 1)
  have hQa := mixAt_isProb (Measure.dirac x₂) (Measure.dirac x₃) ha0.le (by linarith : a₀ ≤ 1)
  have hPh := mixAt_isProb (Measure.dirac x₂) (Measure.dirac x₁) (t := a₀ + h) (by linarith) (by linarith)
  have hQh := mixAt_isProb (Measure.dirac x₂) (Measure.dirac x₃) (t := a₀ + h) (by linarith) (by linarith)
  have hM0 : InM φ a₀ a₁ c₀ (mixAt (Measure.dirac x₂) (Measure.dirac x₁) a₀) (mixAt (Measure.dirac x₂) (Measure.dirac x₃) a₀) :=
    ⟨hPa, hQa, by rw [hS20.2.1], by rw [hS20.2.1]; linarith, polyMargin_mono hS20.2.2.2.2.1 hc0 hc'⟩
  have hM1 : InM φ a₀ a₁ c₀ (mixAt (Measure.dirac x₂) (Measure.dirac x₁) (a₀ + h)) (mixAt (Measure.dirac x₂) (Measure.dirac x₃) a₀) :=
    ⟨hPh, hQa, by rw [hS2.2.1]; linarith, by rw [hS2.2.1]; linarith, polyMargin_mono hS2.2.2.2.2.1 hc0 hc'⟩
  have hM2 : InM φ a₀ a₁ c₀ (mixAt (Measure.dirac x₂) (Measure.dirac x₁) a₀) (mixAt (Measure.dirac x₂) (Measure.dirac x₃) (a₀ + h)) :=
    ⟨hPa, hQh, by rw [hS2.2.2.1]; linarith, by rw [hS2.2.2.1]; linarith, polyMargin_mono hS2.2.2.2.2.2 hc0 hc'⟩
  -- validity at the unperturbed pair
  have hv := hval _ _ hM0
  rw [hS20.2.1] at hv
  have hc := RouteS1.lower2pt_c_route 𝒳 (Measure.dirac x₂) (Measure.dirac x₁) (Measure.dirac x₃) _ _ _ a₀ δ n m Ξ ρ T
    hSR hSP hSQ hRP hRQ hPQ hd2 hd1 hd3 ha0 (by linarith) hδ0.le hδ1.le hn hm hT hv hh1
  rcases le_total n m with hnm | hmn
  · refine ⟨_, _, hM1, ?_⟩
    rw [← hheq]
    exact hc.1 hnm
  · refine ⟨_, _, hM2, ?_⟩
    rw [← hheq]
    exact hc.2 hmn

end RouteS3i

end StatFormal.Wave31tn
