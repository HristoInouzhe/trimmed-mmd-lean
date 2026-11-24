import StatFormal.Archive.OTFD.Wave1.Statements
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Route: A `lem:app-pullback` (pullback of `𝒫^ℓ(H)` under truncation)

Proof of `Claims.pullback` (`otfd/papers/A_sieves/supplement.tex:1318-1331`).
`Π_K⁻¹(A_w) = A_{ι_K w}` with height function `τ ∘ Π_K` (Lipschitz with the same constant, since
`Π_K` is 1-Lipschitz by Bessel), and `‖Π_K x‖ ≤ ‖x‖` preserves the second moment. Lipschitz
hypersurfaces are closed, hence measurable.
-/

noncomputable section
open MeasureTheory Finset
open scoped ENNReal InnerProductSpace

namespace StatFormal.OTFD.Wave1

section General
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Lipschitz hypersurface is the zero set `⟨x,w⟩ = ‖w‖² τ(p x)` with `p` the projection on `w^⊥`. -/
lemma lipHyp_eq_setOf {w : H} (hw : w ≠ 0) (τ : H → ℝ) :
    lipHyp w τ = {x | ⟪x, w⟫_ℝ = ‖w‖ ^ 2 * τ (x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w)} := by
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hww : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  ext x
  simp only [lipHyp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hx : ⟪z + τ z • w, w⟫_ℝ = τ z * ‖w‖ ^ 2 := by
      rw [inner_add_left, hz, inner_smul_left, hww]; simp
    rw [hx]
    have : τ z * ‖w‖ ^ 2 / ‖w‖ ^ 2 = τ z := by field_simp
    rw [this, add_sub_cancel_right]; ring
  · intro hx
    refine ⟨x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w, ?_, ?_⟩
    · rw [inner_sub_left, inner_smul_left, hww]; simp; field_simp; ring
    · have : τ (x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w) = ⟪x, w⟫_ℝ / ‖w‖ ^ 2 := by
        rw [eq_div_iff hn, mul_comm]; exact hx.symm
      rw [this, sub_add_cancel]

lemma isClosed_lipHyp {w : H} (hw : w ≠ 0) {τ : H → ℝ} {L : NNReal}
    (hτ : LipschitzOnWith L τ {z | ⟪z, w⟫_ℝ = 0}) : IsClosed (lipHyp w τ) := by
  rw [lipHyp_eq_setOf hw]
  have hww : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hp : Continuous fun x : H => x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w := by fun_prop
  have hmaps : ∀ x : H, x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w ∈ {z | ⟪z, w⟫_ℝ = 0} := by
    intro x
    simp only [Set.mem_ofPred_eq]
    rw [inner_sub_left, inner_smul_left, hww]; simp; field_simp; ring
  have hc : Continuous fun x : H => τ (x - (⟪x, w⟫_ℝ / ‖w‖ ^ 2) • w) :=
    hτ.continuousOn.comp_continuous hp hmaps
  exact isClosed_eq (by fun_prop) (continuous_const.mul hc)

variable (e : ℕ → H)

/-- `ι_K w = Σ_k w_k e_k`. -/
def embK (K : ℕ) (w : EuclideanSpace ℝ (Fin K)) : H := ∑ k : Fin K, w k • e k

lemma truncK_apply (K : ℕ) (x : H) (k : Fin K) : truncK e K x k = ⟪e k, x⟫_ℝ := rfl

lemma truncK_add_smul (K : ℕ) (x y : H) (c : ℝ) :
    truncK e K (x + c • y) = truncK e K x + c • truncK e K y := by
  ext k
  simp [truncK_apply, inner_add_right, inner_smul_right]

lemma truncK_sub (K : ℕ) (x y : H) : truncK e K (x - y) = truncK e K x - truncK e K y := by
  ext k
  simp [truncK_apply, inner_sub_right]

lemma inner_truncK (K : ℕ) (y : H) (w : EuclideanSpace ℝ (Fin K)) :
    ⟪truncK e K y, w⟫_ℝ = ⟪y, embK e K w⟫_ℝ := by
  simp only [PiLp.inner_apply, truncK_apply, embK, inner_sum, inner_smul_right]
  refine sum_congr rfl fun k _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [real_inner_comm]

variable {e}

lemma truncK_embK (he : Orthonormal ℝ e) (K : ℕ) (w : EuclideanSpace ℝ (Fin K)) :
    truncK e K (embK e K w) = w := by
  ext j
  rw [truncK_apply, embK, inner_sum]
  simp only [inner_smul_right, orthonormal_iff_ite.mp he]
  rw [sum_eq_single j]
  · simp
  · intro k _ hk
    have : ¬ ((j : ℕ) = k) := fun h => hk (Fin.ext h).symm
    simp [this]
  · simp

lemma norm_truncK_le (he : Orthonormal ℝ e) (K : ℕ) (x : H) : ‖truncK e K x‖ ≤ ‖x‖ := by
  have hb := he.sum_inner_products_le (s := range K) (x := x)
  have h1 : ‖truncK e K x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine le_trans (le_of_eq ?_) hb
    rw [← Fin.sum_univ_eq_sum_range (fun i => ‖⟪e i, x⟫_ℝ‖ ^ 2)]
    rfl
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

lemma lipschitz_truncK (he : Orthonormal ℝ e) (K : ℕ) : LipschitzWith 1 (truncK e K) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← truncK_sub, NNReal.coe_one, one_mul]
    exact norm_truncK_le he K _

lemma preimage_lipHyp (he : Orthonormal ℝ e) (K : ℕ) (w : EuclideanSpace ℝ (Fin K))
    (τ : EuclideanSpace ℝ (Fin K) → ℝ) :
    truncK e K ⁻¹' lipHyp w τ = lipHyp (embK e K w) (τ ∘ truncK e K) := by
  ext x
  simp only [Set.mem_preimage, lipHyp, Set.mem_ofPred_eq, Function.comp]
  constructor
  · rintro ⟨z', hz', hx⟩
    refine ⟨x - τ z' • embK e K w, ?_, ?_⟩
    · rw [← inner_truncK, truncK_sub, hx]
      have : truncK e K (τ z' • embK e K w) = τ z' • w := by
        have := truncK_add_smul e K 0 (embK e K w) (τ z')
        rw [zero_add] at this
        rw [this, truncK_embK he]
        simp [truncK]; rfl
      rw [this, add_sub_cancel_right, hz']
    · have : truncK e K (x - τ z' • embK e K w) = z' := by
        rw [truncK_sub, hx]
        have := truncK_add_smul e K 0 (embK e K w) (τ z')
        rw [zero_add] at this
        rw [this, truncK_embK he]
        have h0 : truncK e K 0 = 0 := by ext k; simp [truncK_apply]
        rw [h0, zero_add, add_sub_cancel_right]
      rw [this, sub_add_cancel]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨truncK e K z, ?_, ?_⟩
    · rw [inner_truncK]; exact hz
    · rw [truncK_add_smul, truncK_embK he]

lemma isLipHyp_preimage (he : Orthonormal ℝ e) (K : ℕ) {S : Set (EuclideanSpace ℝ (Fin K))}
    (hS : IsLipHyp S) : IsLipHyp (truncK e K ⁻¹' S) := by
  obtain ⟨w, hw, τ, ⟨L, hL⟩, rfl⟩ := hS
  refine ⟨embK e K w, ?_, τ ∘ truncK e K, ⟨L * 1, ?_⟩, preimage_lipHyp he K w τ⟩
  · intro h
    apply hw
    have := truncK_embK he K w
    rw [h] at this
    rw [← this]; ext k; simp [truncK_apply]
  · refine hL.comp (lipschitz_truncK he K).lipschitzOnWith ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [inner_truncK]; exact hz

end General

theorem pullback_proof : Claims.pullback := by
  intro H _ _ _ _ e he P ⟨hP, hmom, hhyp⟩ K
  have hmeas : Measurable (truncK e K) := (lipschitz_truncK he K).continuous.measurable
  have := hP
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [lintegral_map (by fun_prop) hmeas]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hmom
    gcongr
    exact enorm_le_iff_norm_le.mpr (norm_truncK_le he K x)
  · intro S hS
    have hcl : IsClosed S := by
      obtain ⟨w, hw, τ, ⟨L, hL⟩, rfl⟩ := hS
      exact isClosed_lipHyp hw hL
    rw [Measure.map_apply hmeas hcl.measurableSet]
    exact hhyp _ (isLipHyp_preimage he K hS)

end StatFormal.OTFD.Wave1
