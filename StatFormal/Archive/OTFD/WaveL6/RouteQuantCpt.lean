import StatFormal.Archive.OTFD.WaveL6.RouteQuantile
import StatFormal.Lib.ConvexH.Projections

/-!
# Route (wave L6): quantile norm clause for a strongly compact target support

Untrusted route file. (⋆) with `𝒞 = cl conv (T ∪ ⋃_N P_N(T))` (compact by `ConvexH.isCompact_closure_convexHull_projN`,
Mazur): every subgradient `y` of `χ_K = χ'_K ∘ Π_K` equals `ι_K Π_K y` with `Π_K y ∈ ∂χ'_K(Π_K u) ⊆ cl conv Π_K(T)`
(frozen `ghs_lip_subgrad` in `ℝ^K`), and `ι_K` is linear and continuous; `𝕼_P(u) ∈ cl conv S ⊆ 𝒞`. Then
`sieve_quant_norm`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL6

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave22a (IsSubgrad supAff)

section Lin
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem truncK_embed' {e : ℕ → H} (he : Orthonormal ℝ e) (K : ℕ) (z : Euc K) :
    truncK e K (embed e K z) = z := by
  have he' : Orthonormal ℝ (fun k : Fin K => e k) := he.comp _ Fin.val_injective
  ext k
  simp only [truncK, embed, PiLp.toLp_apply]
  exact he'.inner_right_fintype (fun j => z j) k

theorem embed_truncK_eq_projN (e : ℕ → H) (K : ℕ) (x : H) :
    embed e K (truncK e K x) = ConvexH.projN e K x := by
  simp only [embed, truncK, PiLp.toLp_apply, ConvexH.projN]
  exact (Finset.sum_range (fun k => ⟪e k, x⟫ • e k)).symm

theorem truncK_add_smul' (e : ℕ → H) (K : ℕ) (u w : H) (s : ℝ) :
    truncK e K (u + s • w) = truncK e K u + s • truncK e K w := by
  ext k; simp [truncK, inner_add_right, inner_smul_right]

/-- `ι_K` as a linear map. -/
noncomputable def embedL (e : ℕ → H) (K : ℕ) : Euc K →ₗ[ℝ] H where
  toFun := embed e K
  map_add' a b := by simp only [embed, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp only [embed, PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

/-- Subgradients of `φ ∘ Π_K`: `y = ι_K Π_K y` and `Π_K y ∈ ∂φ(Π_K u)`. -/
theorem subgrad_comp_truncK_range {e : ℕ → H} (he : Orthonormal ℝ e) {K : ℕ} {φ : Euc K → ℝ}
    {u y : H} (hy : IsSubgrad (fun u' => φ (truncK e K u')) u y) :
    y = embed e K (truncK e K y) ∧ IsSubgrad φ (truncK e K u) (truncK e K y) := by
  constructor
  · set w := y - embed e K (truncK e K y) with hw
    have hTw : truncK e K w = 0 := by rw [hw, truncK_sub', truncK_embed' he, sub_self]
    have hs : ∀ s : ℝ, s * ⟪y, w⟫ ≤ 0 := by
      intro s
      have := hy (u + s • w)
      simp only at this
      rw [truncK_add_smul', hTw, smul_zero, add_zero, add_sub_cancel_left, real_inner_smul_right]
        at this
      linarith
    have h0 : ⟪y, w⟫ = 0 := by
      have h1 := hs 1; have h2 := hs (-1); linarith
    have h3 : ⟪embed e K (truncK e K y), w⟫ = 0 := by
      rw [inner_embed_truncK, hTw, inner_zero_right]
    have : ⟪w, w⟫ = 0 := by rw [hw, inner_sub_left] at *; linarith
    rw [inner_self_eq_zero, hw, sub_eq_zero] at this
    exact this
  · intro z'
    have := hy (u + embed e K (z' - truncK e K u))
    simp only at this
    have hT : truncK e K (u + embed e K (z' - truncK e K u)) = z' := by
      have := truncK_add_smul' e K u (embed e K (z' - truncK e K u)) 1
      rw [one_smul, one_smul, truncK_embed' he] at this
      rw [this]; abel
    rw [hT, add_sub_cancel_left, real_inner_comm, inner_embed_truncK, real_inner_comm] at this
    exact this

end Lin

theorem sieve_quant_norm_cpt : Claims.sieve_quant_norm_cpt := by
  intro H _ _ _ _ _ _ e P μ T S b x₀ Q M SK bK zK QK K₀ he htot hPell hμM hT hS hST hbdd hQm hmap hQsub
    hSK hSKT hbddK hQK hpush hsub hK hKs hd ε hε
  obtain ⟨R, hR⟩ := hT.isBounded.subset_closedBall 0
  have hTR : ∀ x ∈ T, ‖x‖ ≤ R := fun x hx => by simpa using hR hx
  have hSR : ∀ y ∈ S, ‖y‖ ≤ R := fun y hy => hTR y (hST hy)
  have hSKR : ∀ K, ∀ z ∈ SK K, ‖z‖ ≤ R := by
    intro K z hz
    obtain ⟨x, hx, rfl⟩ := hSKT K hz
    exact (norm_truncK_le' he K x).trans (hTR x hx)
  obtain ⟨hχc, hχL⟩ := Wave22a.ghs_lip H S b R x₀ hS hSR hbdd
  have hφL : ∀ K z z', |supAff (SK K) (bK K) z - supAff (SK K) (bK K) z'| ≤ R * ‖z - z'‖ :=
    fun K => (Wave22a.ghs_lip (Euc K) (SK K) (bK K) R (zK K) (hSK K) (hSKR K) (hbddK K)).2
  set D := T ∪ ⋃ N, ConvexH.projN e N '' T with hD
  have hC := ConvexH.isCompact_closure_convexHull_projN he htot hT
  have hrange : ∀ K, ∀ u ∈ K₀, ∀ y, IsSubgrad (fun u' => supAff (SK K) (bK K) (truncK e K u')) u y →
      y ∈ closure (convexHull ℝ D) := by
    intro K u _ y hy
    obtain ⟨hyeq, hsg⟩ := subgrad_comp_truncK_range he hy
    have hz := Wave22a.ghs_lip_subgrad (Euc K) (SK K) (bK K) R (zK K) (hSK K) (hSKR K) (hbddK K) _ _ hsg
    have hz' : truncK e K y ∈ closure (convexHull ℝ (truncK e K '' T)) :=
      closure_mono (convexHull_mono (hSKT K)) hz
    have himg : embed e K '' closure (convexHull ℝ (truncK e K '' T)) ⊆ closure (convexHull ℝ D) := by
      refine (image_closure_subset_closure_image (continuous_embed' e K)).trans (closure_mono ?_)
      have : embed e K '' convexHull ℝ (truncK e K '' T) =
          convexHull ℝ (embed e K '' (truncK e K '' T)) := (embedL e K).image_convexHull _
      rw [this]
      refine convexHull_mono ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact Or.inr (mem_iUnion.2 ⟨K, x, hx, (embed_truncK_eq_projN e K x).symm⟩)
    rw [hyeq]
    exact himg ⟨_, hz', rfl⟩
  have hQC : ∀ u ∈ K₀, Q u ∈ closure (convexHull ℝ D) := by
    intro u hu
    have hsg : IsSubgrad (supAff S b) u (Q u) := ConvexH.subgrad_of_hasLineDerivAt hχc (hd u hu)
    have := Wave22a.ghs_lip_subgrad H S b R x₀ hS hSR hbdd u (Q u) hsg
    exact closure_mono (convexHull_mono (hST.trans subset_union_left)) this
  exact sieve_quant_norm H e P μ (supAff S b) Q M R R (fun K => supAff (SK K) (bK K)) QK K₀
    (closure (convexHull ℝ D)) he htot hPell hμM hχc hχL hQm hmap hQsub hφL hQK hpush hsub hK hKs hd
    hC hrange hQC ε hε

end StatFormal.OTFD.WaveL6
