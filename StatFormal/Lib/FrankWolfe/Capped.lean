import StatFormal.Lib.PaperRun.QPMeas
import StatFormal.Wave30tz.RouteFit

/-!
# Linear minimization over the capped simplex; empirical regions as capped combinations (library)

Library component (untrusted). The capped simplex `Δ_α(n) = {w : 0 ≤ w_i ≤ [n(1−α)]⁻¹, Σ w_i = 1}` (the frozen
`Wave30tz.IsCapped`), `φ : 𝒳 → H` a feature map:

* `isCapped_params`: a capped vector exists only for `n ≥ 1` and `0 ≤ α < 1`;
* `exists_isLeast_capped`, `exists_isGreatest_capped`: the linear minimization (maximization) oracle of Frank–Wolfe —
  `w ↦ Σ w_i h_i` attains its minimum and its maximum on a nonempty `Δ_α(n)` (compact: `PaperRun.isCompact_capped`);
* `polytope_eq_image`: the polytope `{Σ_i w_i φ(x_i) : w ∈ Δ_α(n)}` of `Wave8a` is the image of `Δ_α(n)` under `wsum φ x`;
* `region_empirical_eq_image`: for strongly measurable `φ` and a nonempty `Δ_α(n)`, the trimmed region `𝒞_α(P_n)` of the
  empirical measure is that image (the certified `Wave8a.georep_empirical`: a strongly measurable `φ` is constant on
  measurably inseparable points, so averaging the weights over such ties loses nothing);
* `image_inner_wsum`: `⟪f, Σ w_i φ(x_i)⟫ = Σ w_i ⟪f, φ(x_i)⟫` as an identity of image sets.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.FrankWolfe

open StatFormal.Wave30tz

/-- A capped vector forces `n ≥ 1` and `0 ≤ α < 1` (the sum `1` is at most `n · [n(1−α)]⁻¹`, and the cap is `≤ 0` when
`α ≥ 1`). -/
theorem isCapped_params {α : ℝ} {n : ℕ} {w : Fin n → ℝ} (hw : IsCapped α w) : 1 ≤ n ∧ 0 ≤ α ∧ α < 1 := by
  obtain ⟨hb, hs⟩ := hw
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hs
    · exact h0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hα1 : α < 1 := by
    by_contra hcon
    have hcap : 1 / ((n : ℝ) * (1 - α)) ≤ 0 :=
      one_div_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos hn'.le (by linarith))
    have h0 : ∀ i, w i = 0 := fun i => le_antisymm ((hb i).2.trans hcap) (hb i).1
    simp [h0] at hs
  refine ⟨hn, ?_, hα1⟩
  have hsum : ∑ i, w i ≤ ∑ _i : Fin n, 1 / ((n : ℝ) * (1 - α)) := Finset.sum_le_sum fun i _ => (hb i).2
  rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h1α : 0 < 1 - α := by linarith
  have : (n : ℝ) * (1 / (n * (1 - α))) = 1 / (1 - α) := by field_simp
  rw [this, le_div_iff₀ h1α] at hsum
  linarith

/-- **Linear minimization over the capped simplex** (the Frank–Wolfe oracle): on a nonempty `Δ_α(n)`, `w ↦ Σ w_i h_i`
attains its minimum. -/
theorem exists_isLeast_capped {α : ℝ} {n : ℕ} {w : Fin n → ℝ} (hw : IsCapped α w) (h : Fin n → ℝ) :
    ∃ w₀, IsCapped α w₀ ∧
      IsLeast ((fun w' : Fin n → ℝ => ∑ i, w' i * h i) '' {w' | IsCapped α w'}) (∑ i, w₀ i * h i) := by
  have hcont : Continuous fun w' : Fin n → ℝ => ∑ i, w' i * h i := by fun_prop
  obtain ⟨w₀, hw₀, hmin⟩ := (PaperRun.isCompact_capped n α).exists_isMinOn ⟨w, hw⟩ hcont.continuousOn
  exact ⟨w₀, hw₀, ⟨w₀, hw₀, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmin hu⟩

/-- **Linear maximization over the capped simplex**: on a nonempty `Δ_α(n)`, `w ↦ Σ w_i h_i` attains its maximum. -/
theorem exists_isGreatest_capped {α : ℝ} {n : ℕ} {w : Fin n → ℝ} (hw : IsCapped α w) (h : Fin n → ℝ) :
    ∃ w₀, IsCapped α w₀ ∧
      IsGreatest ((fun w' : Fin n → ℝ => ∑ i, w' i * h i) '' {w' | IsCapped α w'}) (∑ i, w₀ i * h i) := by
  have hcont : Continuous fun w' : Fin n → ℝ => ∑ i, w' i * h i := by fun_prop
  obtain ⟨w₀, hw₀, hmax⟩ := (PaperRun.isCompact_capped n α).exists_isMaxOn ⟨w, hw⟩ hcont.continuousOn
  exact ⟨w₀, hw₀, ⟨w₀, hw₀, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩

section Feature

variable {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `⟪f, Σ w_i φ(x_i)⟫ = Σ w_i ⟪f, φ(x_i)⟫`, as an identity of images of any set of weights. -/
theorem image_inner_wsum (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (f : H) (S : Set (Fin n → ℝ)) :
    (fun w' : Fin n → ℝ => ⟪f, wsum φ x w'⟫_ℝ) '' S = (fun w' : Fin n → ℝ => ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ) '' S := by
  congr 1
  funext w'
  exact Fit.inner_wsum φ x w' f

/-- The image of a set of weights under `wsum φ x`, read through `⟪f, ·⟫`. -/
theorem image_inner_image_wsum (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (f : H) (S : Set (Fin n → ℝ)) :
    (fun a : H => ⟪f, a⟫_ℝ) '' (wsum φ x '' S) = (fun w' : Fin n → ℝ => ∑ i, w' i * ⟪f, φ (x i)⟫_ℝ) '' S := by
  rw [Set.image_image]
  exact image_inner_wsum φ x f S

variable [MeasurableSpace 𝒳]

omit [MeasurableSpace 𝒳] in
/-- The `Wave8a` polytope `{Σ_i w_i φ(x_i) : w ∈ Δ_α(n)}` is the image of the capped simplex under `wsum φ x`. -/
theorem polytope_eq_image (φ : 𝒳 → H) {n : ℕ} (x : Fin n → 𝒳) (α : ℝ) :
    StatFormal.Wave8a.polytope φ x α = wsum φ x '' {w | IsCapped α w} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

/-- **Empirical regions as capped combinations**: for strongly measurable `φ` (`H` complete) and a nonempty capped simplex,
`𝒞_α(P_n) = {Σ_i w_i φ(x_i) : w ∈ Δ_α(n)}` (the certified `Wave8a.georep_empirical`). -/
theorem region_empirical_eq_image [CompleteSpace H] {φ : 𝒳 → H} (hφ : StronglyMeasurable φ) {α : ℝ} {n : ℕ}
    (x : Fin n → 𝒳) {w : Fin n → ℝ} (hw : IsCapped α w) :
    StatFormal.TrimmedMMD.Concentration.region φ α (StatFormal.TrimmedMMD.Concentration.empirical x) =
      wsum φ x '' {w | IsCapped α w} := by
  obtain ⟨hn, hα0, hα1⟩ := isCapped_params hw
  rw [StatFormal.Wave8a.region_empirical hφ hα0 hα1 (by omega) x, polytope_eq_image]

end Feature

end StatFormal.FrankWolfe
