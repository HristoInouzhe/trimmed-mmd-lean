import StatFormal.Archive.OTFD.WaveL6.Statements
import StatFormal.Lib.ConvexH.SubgradLimit

/-!
# Route (wave L6): glue between the frozen sieve objects and `Foundations/ConvexH`

Untrusted route file. Subgradient graphs are cyclically monotone; `P`-a.e. subgradient selections are
`IsCMMapAE`; the chain rule `z ∈ ∂φ(Π_K x) ⇒ ι_K z ∈ ∂(φ ∘ Π_K)(x)`; Lipschitz bounds through `Π_K`; and the core
lemma turning a mean-square limit of the embedded selections into the hypotheses of
`StatFormal.ConvexH.eventually_abs_inner_le` / `eventually_norm_le`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL6

open StatFormal.OTFD.WaveL1 (CycMon IsCMMapAE Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave22a (IsSubgrad)

section CM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cycMon_subgrad_graph {f : E → ℝ} {G : E → E} {S : Set E}
    (hS : ∀ x ∈ S, IsSubgrad f x (G x)) : CycMon {z : E × E | z.1 ∈ S ∧ z.2 = G z.1} := by
  intro m z hz
  have hle : ∀ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤
      f (z (finRotate m i)).1 - f (z i).1 := by
    intro i
    obtain ⟨h1, h2⟩ := hz i
    have := hS _ h1 (z (finRotate m i)).1
    rw [h2]; linarith
  refine (Finset.sum_le_sum fun i _ => hle i).trans (le_of_eq ?_)
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) (fun i => f (z i).1), sub_self]

theorem isCMMapAE_of_ae_subgrad [MeasurableSpace E] {μ : Measure E} {f : E → ℝ} {G : E → E}
    (h : ∀ᵐ x ∂μ, IsSubgrad f x (G x)) : IsCMMapAE μ G := by
  set N := {x | ¬ IsSubgrad f x (G x)} with hN
  have hN0 : μ N = 0 := ae_iff.mp h
  refine ⟨(toMeasurable μ N)ᶜ, (measurableSet_toMeasurable μ N).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable, hN0]
  · refine cycMon_subgrad_graph (f := f) fun x hx => ?_
    by_contra hc
    exact hx (subset_toMeasurable μ N hc)

end CM

section Sieve
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem truncK_sub' (e : ℕ → H) (K : ℕ) (x y : H) :
    truncK e K (x - y) = truncK e K x - truncK e K y := by
  ext k; simp [truncK, inner_sub_right]

theorem inner_embed_truncK (e : ℕ → H) (K : ℕ) (z : Euc K) (w : H) :
    ⟪embed e K z, w⟫ = ⟪z, truncK e K w⟫ := by
  simp only [embed, truncK, sum_inner, real_inner_smul_left, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem continuous_truncK'' (e : ℕ → H) (K : ℕ) : Continuous (truncK e K) := by
  unfold truncK
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_const.inner continuous_id)

theorem continuous_embed' (e : ℕ → H) (K : ℕ) : Continuous (embed e K) := by
  unfold embed; fun_prop

theorem norm_truncK_le' {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) (x : H) :
    ‖truncK e K x‖ ≤ ‖x‖ := by
  have hb := he.sum_inner_products_le (s := Finset.range K) (x := x)
  have h1 : ‖truncK e K x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine le_trans (le_of_eq ?_) hb
    rw [← Fin.sum_univ_eq_sum_range (fun i => ‖⟪e i, x⟫_ℝ‖ ^ 2)]
    rfl
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- Chain rule (one inclusion): `z ∈ ∂φ(Π_K x) ⇒ ι_K z ∈ ∂(φ ∘ Π_K)(x)`. -/
theorem subgrad_comp_truncK {e : ℕ → H} {K : ℕ} {φ : Euc K → ℝ} {x : H} {z : Euc K}
    (hz : IsSubgrad φ (truncK e K x) z) :
    IsSubgrad (fun x' => φ (truncK e K x')) x (embed e K z) := by
  intro w
  have := hz (truncK e K w)
  rw [inner_embed_truncK, truncK_sub']
  exact this

theorem lip_comp_truncK {e : ℕ → H} (he : Orthonormal ℝ e) {K : ℕ} {φ : Euc K → ℝ} {L : ℝ}
    (hL : ∀ z z', |φ z - φ z'| ≤ L * ‖z - z'‖) (x x' : H) :
    |φ (truncK e K x) - φ (truncK e K x')| ≤ max L 0 * ‖x - x'‖ := by
  refine (hL _ _).trans ?_
  rw [← truncK_sub']
  have h1 := norm_truncK_le' he K (x - x')
  calc L * ‖truncK e K (x - x')‖ ≤ max L 0 * ‖truncK e K (x - x')‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max L 0 * ‖x - x'‖ := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The embedded sieve selection `x ↦ ι_K F_{+,K}(Π_K x)` turns a mean-square limit into the three hypotheses of
`Foundations/ConvexH`: uniform subgradient bound, `A`-a.e. subgradient selection, convergence in `A`-measure. -/
theorem sieve_core {e : ℕ → H} (he : Orthonormal ℝ e) (A : Measure H) {φ : (K : ℕ) → Euc K → ℝ}
    {FK : (K : ℕ) → Euc K → Euc K} {F : H → H} {Lφ : ℝ}
    (hlip : ∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) (hFK : ∀ K, Measurable (FK K))
    (hF : Measurable F) (hsub : ∀ K, ∀ᵐ z ∂(A.map (truncK e K)), IsSubgrad (φ K) z (FK K z))
    (hL2 : Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂A) atTop (𝓝 0)) :
    (∀ K x y, ConvexH.Subgrad (fun x' => φ K (truncK e K x')) x y → ‖y‖ ≤ max (max Lφ 0) 0) ∧
    (∀ K, ∀ᵐ x ∂A, ConvexH.Subgrad (fun x' => φ K (truncK e K x')) x
      (embed e K (FK K (truncK e K x)))) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun K => A {x | δ ≤ ‖embed e K (FK K (truncK e K x)) - F x‖})
      atTop (𝓝 0)) := by
  refine ⟨fun K x y hy => ConvexH.norm_le_of_subgrad (lip_comp_truncK he (hlip K)) hy, fun K => ?_, ?_⟩
  · have hm : AEMeasurable (truncK e K) A := (continuous_truncK'' e K).measurable.aemeasurable
    filter_upwards [ae_of_ae_map hm (hsub K)] with x hx
    exact subgrad_comp_truncK hx
  · refine ConvexH.tendsto_meas_of_lintegral_sq (fun K => ?_) hL2
    have hG : Measurable fun x => embed e K (FK K (truncK e K x)) :=
      (continuous_embed' e K).measurable.comp ((hFK K).comp (continuous_truncK'' e K).measurable)
    exact ((hG.sub hF).enorm.pow_const 2).aemeasurable

end Sieve

end StatFormal.OTFD.WaveL6
