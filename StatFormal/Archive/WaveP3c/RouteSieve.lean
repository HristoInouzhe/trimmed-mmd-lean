import StatFormal.Archive.WaveP3c.RouteLip
import StatFormal.Archive.OTFD.WaveL8.RouteSieve
import StatFormal.Archive.OTFD.Wave1.RoutePullback

/-!
# Route (wave P3c), part 6: A `thm:sieve-convergence` with its potentials discharged (untrusted)

The projected laws `Π_K#P` stay Lipschitz-null (the pullback of a Lipschitz hypersurface of `ℝ^K` is one of `H`,
certified wave-1 route `isLipHyp_preimage`), and `Π_K#μ` stays in `B(0, M)` (Bessel); `exists_lipschitz_potential`
(RouteLip) at every level gives the potentials; the frozen wave-L8 `sieve_conv_weak`, `sieve_conv_norm` give the second
conjuncts.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3c

open StatFormal.OTFD.WaveL1 (LipNull Euc)
open StatFormal.OTFD.Wave1 (truncK IsLipHyp)
open StatFormal.OTFD.Wave22a (IsSubgrad)

section H
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem lipNull_map_truncK {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) {P : Measure H} (hP : LipNull P) :
    LipNull (P.map (truncK e K)) := by
  have hmeas : Measurable (truncK e K) := (StatFormal.OTFD.Wave1.lipschitz_truncK he K).continuous.measurable
  intro S hS
  have hcl : IsClosed S := by
    obtain ⟨w, hw, τ, ⟨L, hL⟩, rfl⟩ := hS
    exact StatFormal.OTFD.Wave1.isClosed_lipHyp hw hL
  rw [Measure.map_apply hmeas hcl.measurableSet]
  exact hP _ (StatFormal.OTFD.Wave1.isLipHyp_preimage he K hS)

theorem map_truncK_ball {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) {μ : Measure H} {M : ℝ}
    (hμ : μ (Metric.closedBall 0 M)ᶜ = 0) : (μ.map (truncK e K)) (Metric.closedBall 0 M)ᶜ = 0 := by
  have hmeas : Measurable (truncK e K) := (StatFormal.OTFD.Wave1.lipschitz_truncK he K).continuous.measurable
  rw [Measure.map_apply hmeas Metric.isClosed_closedBall.measurableSet.compl]
  refine measure_mono_null (fun x hx => ?_) hμ
  simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx ⊢
  exact lt_of_lt_of_le hx (StatFormal.OTFD.Wave1.norm_truncK_le he K x)

theorem exists_sieve_potentials (e : ℕ → H) (P μ : ProbabilityMeasure H) (M : ℝ) (he : Orthonormal ℝ e)
    (hP : LipNull (P : Measure H)) (hμ : (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0) :
    ∃ (ψ : H → ℝ) (F : H → H) (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K),
      ConvexOn ℝ univ ψ ∧ (∀ x x', |ψ x - ψ x'| ≤ M * ‖x - x'‖) ∧
      Measurable F ∧ (P : Measure H).map F = μ ∧ (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) ∧
      (∀ K, ConvexOn ℝ univ (φ K)) ∧ (∀ K z z', |φ K z - φ K z'| ≤ M * ‖z - z'‖) ∧ (∀ K, Measurable (FK K)) ∧
      (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) ∧
      (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z)) := by
  obtain ⟨ψ, F, hψc, hψL, hFm, hmap, hsub⟩ := exists_lipschitz_potential P μ M hP hμ
  have hK : ∀ K : ℕ, ∃ (φ : Euc K → ℝ) (G : Euc K → Euc K), ConvexOn ℝ univ φ ∧
      (∀ z z', |φ z - φ z'| ≤ M * ‖z - z'‖) ∧ Measurable G ∧
      ((P : Measure H).map (truncK e K)).map G = (μ : Measure H).map (truncK e K) ∧
      ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad φ z (G z) := fun K =>
    exists_lipschitz_potential (P.map (truncK e K)) (μ.map (truncK e K)) M
      (lipNull_map_truncK he K hP) (map_truncK_ball he K hμ)
  choose φ FK hφc hφL hFKm hFKmap hFKsub using hK
  exact ⟨ψ, F, φ, FK, hψc, hψL, hFm, hmap, hsub, hφc, hφL, hFKm, hFKmap, hFKsub⟩

end H

theorem sieve_conv_weak_mccann : Claims.sieve_conv_weak_mccann := by
  intro H _ _ _ _ _ _ e P μ M he hP hμ
  refine ⟨exists_sieve_potentials e P μ M he hP hμ, fun ψ F Lψ Lφ φ FK K₀ h hspan hψc hψL hFm hmap hsub hφL hFKm
    hFKmap hFKsub hK₀ hK₀i hder => ?_⟩
  exact StatFormal.OTFD.WaveL8.sieve_conv_weak H e P μ ψ F M Lψ Lφ φ FK K₀ h he hspan hP hμ hψc hψL hFm hmap hsub hφL
    hFKm hFKmap hFKsub hK₀ hK₀i hder

theorem sieve_conv_norm_mccann : Claims.sieve_conv_norm_mccann := by
  intro H _ _ _ _ _ _ e P μ M he hP hμ
  refine ⟨exists_sieve_potentials e P μ M he hP hμ, fun ψ F Lψ Lφ φ FK K₀ C hspan hψc hψL hFm hmap hsub hφL hFKm
    hFKmap hFKsub hK₀ hK₀i hder hC hCK hFC => ?_⟩
  exact StatFormal.OTFD.WaveL8.sieve_conv_norm H e P μ ψ F M Lψ Lφ φ FK K₀ C he hspan hP hμ hψc hψL hFm hmap hsub hφL
    hFKm hFKmap hFKsub hK₀ hK₀i hder hC hCK hFC

end StatFormal.WaveP3c
