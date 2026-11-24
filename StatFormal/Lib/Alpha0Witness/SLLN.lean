import StatFormal.Lib.Alpha0Witness.Basic
import Mathlib.Probability.StrongLaw

/-!
# Uniform almost-sure convergence of normalized empirical mean embeddings (library)

Library component (untrusted).

* `ae_tendsto_sampleMean`: **strong law for mean embeddings** — `X_1, X_2, …` pairwise independent with law `P`, `φ` strongly
  measurable and bounded into a complete Borel normed space: almost surely `n⁻¹ Σ_{i<n} φ(X_i) → ∫ φ dP` (Mathlib's Etemadi
  `ProbabilityTheory.strong_law_ae` applied to `φ ∘ X_i`);
* `abs_inner_normalize_sub_le_of_tendsto`: if `a_n → A`, `b_m → B` with `A ≠ B`, then
  `sup_z |⟪(a_n − b_m)/‖a_n − b_m‖, φ z⟫ − ⟪(A − B)/‖A − B‖, φ z⟫| → 0` as `n, m → ∞` jointly, for `‖φ‖ ≤ κ` (normalization is
  Lipschitz away from `0`, `Alpha0Witness.norm_normalize_sub_le`, and Cauchy–Schwarz).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Alpha0Witness

/-- **Strong law for mean embeddings** (Etemadi, pairwise independence): almost surely `n⁻¹ Σ_{i<n} φ(X_i) → ∫ φ dP`. -/
theorem ae_tendsto_sampleMean {Ω 𝒳 E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace 𝒳] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure 𝒳} {X : ℕ → Ω → 𝒳} {φ : 𝒳 → E} {κ : ℝ} (hX : ∀ i, Measurable (X i))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ) (hlaw : ∀ i, μ.map (X i) = P) (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i : Fin n, φ (X i ω)) atTop (𝓝 (∫ x, φ x ∂P)) := by
  have hφm : Measurable φ := hφ.measurable
  set Z : ℕ → Ω → E := fun i ω => φ (X i ω) with hZ
  have hint : Integrable (Z 0) μ :=
    Integrable.of_bound (hφ.comp_measurable (hX 0)).aestronglyMeasurable κ (ae_of_all _ fun ω => hκ _)
  have hindZ : Pairwise (Function.onFun (fun f g => IndepFun f g μ) Z) := fun i j hij => (hind hij).comp hφm hφm
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := fun i =>
    (⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩ : IdentDistrib (X i) (X 0) μ μ).comp hφm
  have hmean : ∫ ω, Z 0 ω ∂μ = ∫ x, φ x ∂P := by
    rw [← hlaw 0, integral_map (hX 0).aemeasurable hφ.aestronglyMeasurable]
  filter_upwards [strong_law_ae Z hint hindZ hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => Z i ω) n]

/-- **Uniform convergence of normalized differences**: if `a_n → A`, `b_m → B`, `A ≠ B` and `‖φ‖ ≤ κ`, then for every `ε > 0`,
eventually in `n` and `m` jointly, `|⟪(a_n − b_m)/‖a_n − b_m‖, φ z⟫ − ⟪(A − B)/‖A − B‖, φ z⟫| ≤ ε` for all `z`. -/
theorem abs_inner_normalize_sub_le_of_tendsto {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℕ → H} {A B : H} (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hAB : 0 < ‖A - B‖)
    {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ z, ‖φ z‖ ≤ κ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m → ∀ z,
      |⟪‖a n - b m‖⁻¹ • (a n - b m), φ z⟫_ℝ - ⟪‖A - B‖⁻¹ • (A - B), φ z⟫_ℝ| ≤ ε := by
  intro ε hε
  set K : ℝ := |κ| + 1 with hK
  have hK0 : 0 < K := by positivity
  set η : ℝ := ε * ‖A - B‖ / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 ha η hη0
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hb η hη0
  refine ⟨max N₁ N₂, fun n m hn hm z => ?_⟩
  have h1 : ‖a n - A‖ < η := by rw [← dist_eq_norm]; exact hN₁ n (le_of_max_le_left hn)
  have h2 : ‖b m - B‖ < η := by rw [← dist_eq_norm]; exact hN₂ m (le_of_max_le_right hm)
  have hd : ‖(a n - b m) - (A - B)‖ ≤ 2 * η := by
    calc ‖(a n - b m) - (A - B)‖ = ‖(a n - A) - (b m - B)‖ := by congr 1; abel
      _ ≤ ‖a n - A‖ + ‖b m - B‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  have hAB0 : A - B ≠ 0 := norm_pos_iff.1 hAB
  have hz : ‖φ z‖ ≤ K := (hκ z).trans ((le_abs_self κ).trans (by linarith))
  calc |⟪‖a n - b m‖⁻¹ • (a n - b m), φ z⟫_ℝ - ⟪‖A - B‖⁻¹ • (A - B), φ z⟫_ℝ|
      ≤ ‖‖a n - b m‖⁻¹ • (a n - b m) - ‖A - B‖⁻¹ • (A - B)‖ * ‖φ z‖ := abs_inner_sub_le _ _ _
    _ ≤ (2 * ‖(a n - b m) - (A - B)‖ / ‖A - B‖) * K :=
        mul_le_mul (norm_normalize_sub_le hAB0 _) hz (norm_nonneg _) (by positivity)
    _ ≤ (2 * (2 * η) / ‖A - B‖) * K := by gcongr
    _ = ε := by rw [hη]; field_simp; ring

end StatFormal.Alpha0Witness
